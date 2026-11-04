import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.UntypedBufHelpers
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmHtabStep
import InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue

/-! # Warm-access and address-masking helpers (`to_address_masked`, `warm_address`,
`warm_after_charge`, `is_warm_storage_key`, `warm_storage_key`) -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards (evmInvAt_of_htab_step evaluate_be_eq)
open InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue
open InitECandidate.Solver.Wave8Contracts.M23

/-! ## 1. Installed lookups -/

private theorem evmInv_head_ev_bounds {F : Type} {s : PanSemStateFiniteExact 64 F} (hInv : EvmInv s) :
    0 < globN s "ev" ∧ globN s "ev" + 280 ≤ heapEnd ∧ globN s "ev" + 280 ≤ 2 ^ 64 := by
  obtain ⟨hAs, S, _, _, _, _, hFW_all, _⟩ := hInv
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    unfold evmChain
    have hpos : ∃ m, Wave8GuestInv.maxChain + 1 = m + 1 := ⟨Wave8GuestInv.maxChain, rfl⟩
    obtain ⟨m, hm⟩ := hpos; rw [hm, evmChainFrom]; exact List.mem_cons_self
  have hFW0 := hFW_all _ hhead
  have hin1 := (hFW0.1 (globN s "ev", 280) (by simp)).1.1
  have hin2 := (hFW0.1 (globN s "ev", 280) (by simp)).1.2
  dsimp only at hin1 hin2
  have hfm1 := hAs.2.2.2.1
  have hfm2 := hAs.2.2.2.2.1
  rw [R11Shards.scratchStart_val] at hfm1
  rw [R11Shards.scratchEnd_val] at hin2
  rw [R11Shards.heapEnd_val]
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
  rw [h264]
  exact ⟨by omega, by omega, by omega⟩

theorem lookup_to_address_masked :
    originalRuntimeCode.lookup (ofString "to_address_masked") =
      some ([(ofString "v", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_to_address_masked, .one) :=
  lookup_of_guestAst_getElem 444 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_to_address_masked) rfl

theorem lookup_warm_address :
    originalRuntimeCode.lookup (ofString "warm_address") =
      some ([(ofString "addr", .one)],
        sourceFnBody Guest.Software.guestFn_warm_address, .one) :=
  lookup_of_guestAst_getElem 472 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_warm_address) rfl

theorem lookup_warm_after_charge :
    originalRuntimeCode.lookup (ofString "warm_after_charge") =
      some ([(ofString "addr", .one), (ofString "c", .one)],
        sourceFnBody Guest.Software.guestFn_warm_after_charge, .one) :=
  lookup_of_guestAst_getElem 474 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_warm_after_charge) rfl

theorem lookup_is_warm_storage_key :
    originalRuntimeCode.lookup (ofString "is_warm_storage_key") =
      some ([(ofString "addr", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_is_warm_storage_key, .one) :=
  lookup_of_guestAst_getElem 525 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_is_warm_storage_key) rfl

theorem lookup_warm_storage_key :
    originalRuntimeCode.lookup (ofString "warm_storage_key") =
      some ([(ofString "addr", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_warm_storage_key, .one) :=
  lookup_of_guestAst_getElem 526 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_warm_storage_key) rfl

/-! ## 2. Closed non-catching callee set for warm-access helpers -/

def warmAccessNcrCallees (f : MlS) : Bool :=
  htabMutCallees f ||
  f == ofString "bswap64" ||
  f == ofString "st_be32" ||
  f == ofString "st_be64" ||
  f == ofString "sk_make" ||
  f == ofString "htab_has" ||
  f == ofString "warm_address"

private theorem ncr_mono_wa {g1 g2 : MlS → Bool} (himp : ∀ f, g1 f = true → g2 f = true) :
    ∀ p : ProgHOL 64, noCatchableRaise g1 p = true → noCatchableRaise g2 p = true
  | .skip, _ | .«break», _ | .«continue», _ | .annot _ _, _ | .«return» _, _
  | .assign _ _ _, _ | .store _ _, _ | .storeByte _ _, _ | .store32 _ _, _
  | .shMemStore _ _ _, _ | .extCall _ _ _ _ _, _ => rfl
  | .raise _ _, hp => hp
  | .dec _ _ _ b, hp => ncr_mono_wa himp b hp
  | .seq a b, hp => by
      simp only [noCatchableRaise, Bool.and_eq_true] at hp ⊢
      exact ⟨ncr_mono_wa himp a hp.1, ncr_mono_wa himp b hp.2⟩
  | .ite _ a b, hp => by
      simp only [noCatchableRaise, Bool.and_eq_true] at hp ⊢
      exact ⟨ncr_mono_wa himp a hp.1, ncr_mono_wa himp b hp.2⟩
  | .while _ b, hp => ncr_mono_wa himp b hp
  | .decCall _ _ fn _ cont, hp => by
      simp only [noCatchableRaise, Bool.and_eq_true] at hp ⊢
      exact ⟨himp fn hp.1, ncr_mono_wa himp cont hp.2⟩
  | .call tail fn _, hp => by
      rcases tail with _ | ⟨_, hdl⟩
      · simp [noCatchableRaise] at hp
      · rcases hdl with _ | _
        · exact himp fn hp
        · simp [noCatchableRaise] at hp
  | .shMemLoad _ _ _ _, hp => by simp [noCatchableRaise] at hp

theorem warmAccessNcrCallees_good :
    ∀ f, warmAccessNcrCallees f = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      noCatchableRaise warmAccessNcrCallees body = true := by
  intro f hf values body callee rs hfound
  simp only [warmAccessNcrCallees, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with (((((hm | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
  · exact ncr_mono_wa (fun g hg => by simp [warmAccessNcrCallees, hg]) body
      (htabMutCallees_good f hm values body callee rs hfound)
  · obtain ⟨_, _, hinst⟩ := lookupCode_installed hfound
    rw [lookup_bswap64_b] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · obtain ⟨_, _, hinst⟩ := lookupCode_installed hfound
    rw [lookup_st_be32_b] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · obtain ⟨_, _, hinst⟩ := lookupCode_installed hfound
    rw [lookup_st_be64_b] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · obtain ⟨_, _, hinst⟩ := lookupCode_installed hfound
    have hl := lookup_of_guestAst_getElem 360 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_sk_make) rfl
    change originalRuntimeCode.lookup (ofString "sk_make") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · obtain ⟨_, _, hinst⟩ := lookupCode_installed hfound
    have hl := lookup_of_guestAst_getElem 133 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_htab_has) rfl
    change originalRuntimeCode.lookup (ofString "htab_has") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · obtain ⟨_, _, hinst⟩ := lookupCode_installed hfound
    rw [lookup_warm_address] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide

/-! ## 3. `st_be32`, `st_be64`, and `eps_to_address_masked` -/

private theorem bv_add_off_nat_wa (base : BitVec 64) (off : Nat)
    (hbase : base.toNat < heapEnd) (hoff : off ≤ 32) :
    (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
  rw [R11Shards.heapEnd_val] at hbase
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
  have ho_lt : off < 18446744073709551616 := by omega
  have hsum_lt : base.toNat + off < 18446744073709551616 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, h264, Nat.mod_eq_of_lt ho_lt, Nat.mod_eq_of_lt hsum_lt]

private theorem eval_var_local_zero_wa {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : String) (base : BitVec 64)
    (hloc : s.locals.lookup (ofString nm) = some (.val (.word base))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString nm)) =
      some (.val (.word (base + BitVec.ofNat 64 0))) := by
  have hz : base + BitVec.ofNat 64 0 = base := BitVec.add_zero base
  rw [hz]; exact hloc

private theorem eval_add_local_const_wa {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : String) (base : BitVec 64) (off : Nat)
    (hloc : s.locals.lookup (ofString nm) = some (.val (.word base))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString nm), .const (BitVec.ofNat 64 off)]) =
      some (.val (.word (base + BitVec.ofNat 64 off))) := by
  simp only [evalHOLExact, evalListHOLExact, hloc, wordOpHOL, wordOp, valueIsWord, valueWord,
    List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
  have hz : BitVec.ofNat 64 off + (0 : BitVec 64) = BitVec.ofNat 64 off := BitVec.add_zero _
  exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word (base + w)))) hz

private theorem eval_align8_eq0_wa {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : String) (base : BitVec 64)
    (hloc : s.locals.lookup (ofString nm) = some (.val (.word base))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.op .and [.var .local (ofString nm), .const 7#64]) (.const 0#64)) =
      some (.val (.word (if (base &&& 7#64) = 0#64 then 1 else 0))) := by
  simp only [evalHOLExact, evalListHOLExact, hloc, wordOpHOL, wordOp, valueIsWord, valueWord,
    List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
    Compiler.Encoders.Asm.wordCmpHOL]
  have h7 : (7#64 : BitVec 64) &&& 18446744073709551615#64 = 7#64 := by decide
  change some (ValueHOL.val (HolWordLab.word (if decide ((base &&& (7#64 &&& 18446744073709551615#64)) = 0#64) = true then 1 else 0))) = _
  rw [h7]
  by_cases hc : (base &&& 7#64) = 0#64 <;> simp [hc]

private theorem return_eff_wa {F : Type} (s : PanSemStateFiniteExact 64 F) (ex : ExpHOL 64) (Rl : List Ivl) :
    ByteRegionEffect s (evaluateHOLFiniteState s (.return ex)).2 Rl := by
  have hret : (evaluateHOLFiniteState s (.return ex)).2 =
      { s with locals := (evaluateHOLFiniteState s (.return ex)).2.locals } := by
    rw [evaluateHOLFiniteState_return]
    split
    · rfl
    · split <;> rfl
  conv => arg 2; rw [hret]
  exact (ByteRegionEffect.refl s Rl).with_locals_clock _ s.clock

private theorem bswap64_body_ro_wa {F : Type} (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl) :
    ByteRegionEffect s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_bswap64)).2 Rl := by
  have hb : sourceFnBody Guest.Software.guestFn_bswap64 =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_bswap64).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_bswap64,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  have hasgn : ∀ (st : PanSemStateFiniteExact 64 F) (nm : MlS) (ex : ExpHOL 64),
      (evaluateHOLFiniteState st (.assign .local nm ex)).2 =
        { st with locals := (evaluateHOLFiniteState st (.assign .local nm ex)).2.locals } := by
    intro st nm ex; rw [evaluateHOLFiniteState_assign]; split <;> [rfl; (split <;> rfl)]
  have hseq_ro : ∀ (st : PanSemStateFiniteExact 64 F) (a b : ProgHOL 64),
      ByteRegionEffect st (evaluateHOLFiniteState st a).2 Rl →
      (∀ m, ByteRegionEffect st m Rl → ByteRegionEffect st (evaluateHOLFiniteState m b).2 Rl) →
      ByteRegionEffect st (evaluateHOLFiniteState st (.seq a b)).2 Rl := by
    intro st a b ha hb'
    rw [evaluateHOLFiniteState_seq_line780]
    rcases h1 : evaluateHOLFiniteState st a with ⟨r1, s1⟩
    rw [h1] at ha
    cases r1 with
    | none => exact hb' s1 ha
    | some _ => exact ha
  have hasgn_eff : ∀ (st : PanSemStateFiniteExact 64 F) (nm : MlS) (ex : ExpHOL 64),
      ByteRegionEffect st (evaluateHOLFiniteState st (.assign .local nm ex)).2 Rl := by
    intro st nm ex
    conv => arg 2; rw [hasgn st nm ex]
    exact (ByteRegionEffect.refl st Rl).with_locals_clock _ st.clock
  refine hseq_ro s _ _ (hasgn_eff s _ _) fun s1 hs1 => ?_
  exact hs1.trans (hseq_ro s1 _ _ (hasgn_eff s1 _ _) (fun s2 hs2 => hs2.trans (return_eff_wa s2 _ Rl)))

private theorem seq_storeByte_known_eff_wa {F : Type} {s : PanSemStateFiniteExact 64 F}
    {dstExp valExp : ExpHOL 64} {base : BitVec 64} {off len : Nat} {cont : ProgHOL 64}
    (hbase_lt : base.toNat < heapEnd) (hlen : len ≤ 32) (hoff : off < len)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word (base + BitVec.ofNat 64 off))))
    (hcont : ∀ s1 : PanSemStateFiniteExact 64 F,
      s1.code = s.code → s1.memaddrs = s.memaddrs → s1.locals = s.locals →
      ByteRegionEffect s1 (evaluateHOLFiniteState s1 cont).2 [(base.toNat, len)]) :
    ByteRegionEffect s (evaluateHOLFiniteState s (.seq (.storeByte dstExp valExp) cont)).2 [(base.toNat, len)] := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases h1 : evaluateHOLFiniteState s (.storeByte dstExp valExp) with ⟨r1, s1⟩
  cases r1 with
  | some _ =>
    have h1' := h1
    rw [evaluateHOLFiniteState_storeByte, hdst] at h1'
    rcases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp with _ | vv
    · rw [hv] at h1'; dsimp only at h1'; injection h1' with _ hs1; subst hs1; exact ByteRegionEffect.refl s _
    · rw [hv] at h1'
      rcases vv with ⟨⟨v⟩⟩ | _ | _
      · dsimp only at h1'; split at h1'
        · cases h1'
        · injection h1' with _ hs1; subst hs1; exact ByteRegionEffect.refl s _
      · dsimp only at h1'; injection h1' with _ hs1; subst hs1; exact ByteRegionEffect.refl s _
      · dsimp only at h1'; injection h1' with _ hs1; subst hs1; exact ByteRegionEffect.refl s _
  | none =>
    have heff1 := ByteRegionEffect.of_storeByte (Rl := [(base.toNat, len)]) h1
      (fun addr ha _ => by
        rw [hdst] at ha
        injection ha with e1; injection e1 with e2; injection e2 with e3; subst e3
        have hnat := bv_add_off_nat_wa base off hbase_lt (by omega)
        exact ⟨(base.toNat, len), List.mem_singleton.2 rfl, by rw [hnat]; omega, by rw [hnat]; omega⟩)
    exact heff1.1.trans (hcont s1 heff1.1.code heff1.1.memaddrs heff1.2)

private theorem st_be32_known_eff_wa {F : Type} (s : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (hp_lt : p.toNat < heapEnd)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p))) :
    ByteRegionEffect s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_be32)).2 [(p.toNat, 4)] := by
  have hb : sourceFnBody Guest.Software.guestFn_st_be32 =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_st_be32).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_st_be32,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    List.map]
  refine seq_storeByte_known_eff_wa hp_lt (by omega) (by omega)
    (eval_var_local_zero_wa s "p" p hp) fun s1 _ _ hl1 => ?_
  have hp1 : s1.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hl1]; exact hp
  refine seq_storeByte_known_eff_wa (s := s1) hp_lt (by omega) (by omega)
    (eval_add_local_const_wa s1 "p" p 1 hp1) fun s2 _ _ hl2 => ?_
  have hp2 : s2.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hl2]; exact hp1
  refine seq_storeByte_known_eff_wa (s := s2) hp_lt (by omega) (by omega)
    (eval_add_local_const_wa s2 "p" p 2 hp2) fun s3 _ _ hl3 => ?_
  have hp3 : s3.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hl3]; exact hp2
  refine seq_storeByte_known_eff_wa (s := s3) hp_lt (by omega) (by omega)
    (eval_add_local_const_wa s3 "p" p 3 hp3) fun s4 _ _ _ => return_eff_wa s4 _ _

private theorem lookup_two_words_reject_nonword_wa {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (fname p1 p2 : MlS) (body : ProgHOL width) (w1 : BitVec width) (v2 : ValueHOL width)
    (hlook : code fname = some ([(p1, .one), (p2, .one)], body, .one))
    (hnot : ∀ w2 : BitVec width, v2 ≠ .val (.word w2)) :
    lookupCodeHOLFinite code fname [.val (.word w1), v2] = none := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rfl
  · rename_i eb el es hraw
    unfold lookupCodeHOLExact at hraw; rw [hlook] at hraw
    rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      [exact absurd rfl (hnot w2); simp [shapeOfHOLExact, shapeEqHOL] at hraw; simp [shapeOfHOLExact, shapeEqHOL] at hraw]

private theorem seq_call_st_be32_known_wa {F : Type} {s : PanSemStateFiniteExact 64 F}
    {pExp vExp : ExpHOL 64} {base : BitVec 64} {off len : Nat} {cont : ProgHOL 64}
    (hcode : s.code = originalRuntimeCode) (hbase_lt : base.toNat + len ≤ heapEnd)
    (hlen : len ≤ 32) (hoff : off + 4 ≤ len)
    (hp_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pExp =
      some (.val (.word (base + BitVec.ofNat 64 off))))
    (hcont : ∀ s1 : PanSemStateFiniteExact 64 F,
      s1.code = originalRuntimeCode → s1.memaddrs = s.memaddrs → s1.locals = s.locals →
      ByteRegionEffect s1 (evaluateHOLFiniteState s1 cont).2 [(base.toNat, len)]) :
    ByteRegionEffect s
      (evaluateHOLFiniteState s (.seq (.call (some (none, none)) (ofString "st_be32") [pExp, vExp]) cont)).2
      [(base.toNat, len)] := by
  let pArg := base + BitVec.ofNat 64 off
  have hbase_lt0 : base.toNat < heapEnd := by omega
  have hpArg_nat : pArg.toNat = base.toNat + off := bv_add_off_nat_wa base off hbase_lt0 (by omega)
  have hpArg_lt : pArg.toNat < heapEnd := by rw [hpArg_nat]; omega
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hc : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "st_be32") [pExp, vExp]) with ⟨rc, sc⟩
  rw [evaluateHOLFiniteState_call] at hc
  rcases hv_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) vExp with _ | vv
  · have hnone : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [pExp, vExp] = none := by
      simp [evalListHOLFinite, evalListHOLExact, hp_ev, hv_ev]
    rw [hnone] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s _
  · have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [pExp, vExp] =
        some [.val (.word pArg), vv] := by
      simp [evalListHOLFinite, evalListHOLExact, hp_ev, hv_ev, pArg]
    rw [hargs] at hc; dsimp only at hc
    by_cases hvw : ∃ vW : BitVec 64, vv = .val (.word vW)
    · obtain ⟨vW, rfl⟩ := hvw
      have hl := pan_two_word_lookup s.code.lookup (ofString "st_be32") (ofString "p") (ofString "v")
        (sourceFnBody Guest.Software.guestFn_st_be32) pArg vW (by decide) (by rw [hcode]; exact lookup_st_be32_b)
      rw [hl] at hc; dsimp only at hc
      split at hc
      · injection hc with hr hsc; subst hr hsc; exact (ByteRegionEffect.refl s _).with_locals_clock _ _
      · let entry := callEntryStateHOLFinite s
          ((HolFiniteMapExact.empty.update (ofString "p", .val (.word pArg))).update (ofString "v", .val (.word vW)))
        have hp_in : entry.locals.lookup (ofString "p") = some (.val (.word pArg)) := by
          simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "v" ≠ ofString "p" by decide]
        have heff_b := st_be32_known_eff_wa entry pArg hpArg_lt hp_in
        rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_st_be32) with ⟨rb, sb⟩
        have hb_entry : evaluateHOLFiniteState
            (callEntryStateHOLFinite s
              ((HolFiniteMapExact.empty.update (ofString "p", .val (.word pArg))).update (ofString "v", .val (.word vW))))
            (sourceFnBody Guest.Software.guestFn_st_be32) = (rb, sb) := hb
        rw [hb_entry] at hc; rw [hb] at heff_b; dsimp only at heff_b
        have heff_entry : ByteRegionEffect s entry [(base.toNat, len)] :=
          (ByteRegionEffect.refl s _).with_locals_clock _ _
        have heff_sb : ByteRegionEffect s sb [(base.toNat, len)] :=
          heff_entry.trans (heff_b.mono fun i hi => by
            simp only [List.mem_singleton] at hi; subst hi
            exact ⟨(base.toNat, len), List.mem_singleton.2 rfl, by rw [hpArg_nat]; omega, by rw [hpArg_nat]; omega⟩)
        cases rb with
        | none => injection hc with hr hsc; subst hr hsc; exact heff_sb
        | some r =>
          cases r with
          | returned rv =>
            dsimp only at hc; split at hc
            · injection hc with hr hsc; subst hr hsc; dsimp only
              let s1 : PanSemStateFiniteExact 64 F := { sb with locals := s.locals }
              have heff_s1 : ByteRegionEffect s s1 [(base.toNat, len)] := heff_sb.with_locals_clock _ _
              exact heff_s1.trans (hcont s1 (heff_s1.code.trans hcode) heff_s1.memaddrs rfl)
            · injection hc with hr hsc; subst hr hsc; exact heff_sb
          | timeOut | error | exception _ _ | finalFfi _ =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb.with_locals_clock _ _
          | «break» | «continue» =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb
    · have hln := lookup_two_words_reject_nonword_wa s.code.lookup (ofString "st_be32") (ofString "p") (ofString "v")
        _ pArg vv (by rw [hcode]; exact lookup_st_be32_b) (fun w hw => hvw ⟨w, hw⟩)
      rw [hln] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s _

private theorem st_be64_known_eff_wa {F : Type} (s : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (hcode : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hp_lt : p.toNat + 8 ≤ heapEnd)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p))) :
    ByteRegionEffect s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_be64)).2 [(p.toNat, 8)] := by
  have hb : sourceFnBody Guest.Software.guestFn_st_be64 =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_st_be64).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_st_be64,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    List.map, Option.map]
  have hcond := eval_align8_eq0_wa s "p" p hp
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcond]
  by_cases hal : (p &&& 7#64) = 0#64
  · simp only [hal, ↓reduceIte]
    have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    rw [if_neg h10]
    let yesProg : ProgHOL 64 :=
      .decCall (ofString "w") .one (ofString "bswap64") [.var .local (ofString "v")]
        (.seq (.store (.var .local (ofString "p")) (.var .local (ofString "w")))
          (.return (.const 0#64)))
    have hnn_eff : (evaluateHOLFiniteState s yesProg).1 ≠ none ∧
        ByteRegionEffect s (evaluateHOLFiniteState s yesProg).2 [(p.toNat, 8)] := by
      dsimp only [yesProg]
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
      rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.var .local (ofString "v")] with _ | vals
      · exact ⟨by simp, ByteRegionEffect.refl s _⟩
      · dsimp only
        rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "bswap64") vals with _ | ⟨b', cal', rs'⟩
        · exact ⟨by simp, ByteRegionEffect.refl s _⟩
        · dsimp only
          have hinst := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "bswap64")
            _ _ b' _ rs' vals cal' (by rw [hcode]; exact lookup_bswap64_b) hl
          subst hinst
          have hrs_eq : rs' = .one := by
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
            split at hl
            · cases hl
            · rename_i eb el es hraw
              have hinj := Option.some.inj hl
              rcases Prod.mk.inj hinj with ⟨_, hr2⟩; rcases Prod.mk.inj hr2 with ⟨_, rfl⟩
              unfold lookupCodeHOLExact at hraw; rw [hcode, lookup_bswap64_b] at hraw; dsimp only at hraw
              split at hraw <;> [ (injection hraw with h'; exact (Prod.mk.inj (Prod.mk.inj h').2).2.symm); cases hraw ]
          subst hrs_eq
          split
          · exact ⟨by simp, (ByteRegionEffect.refl s _).with_locals_clock _ _⟩
          · have heff_ent : ByteRegionEffect s (callEntryStateHOLFinite s cal') [(p.toNat, 8)] :=
              (ByteRegionEffect.refl s _).with_locals_clock _ _
            have heff_b := bswap64_body_ro_wa (callEntryStateHOLFinite s cal') [(p.toNat, 8)]
            rcases hb_run : evaluateHOLFiniteState (callEntryStateHOLFinite s cal')
                (sourceFnBody Guest.Software.guestFn_bswap64) with ⟨rb, sb⟩
            rw [hb_run] at heff_b; dsimp only at heff_b ⊢
            have heff_sb := heff_ent.trans heff_b
            cases rb with
            | none => exact ⟨by simp, heff_sb⟩
            | some r =>
              cases r with
              | returned v =>
                dsimp only; split
                · rename_i hsh_v
                  have hvw : ∃ wv : BitVec 64, v = .val (.word wv) := by
                    rcases v with ⟨⟨wv⟩⟩ | _ | _ <;>
                      [exact ⟨wv, rfl⟩; simp [shapeOfHOLExact, shapeEqHOL] at hsh_v; simp [shapeOfHOLExact, shapeEqHOL] at hsh_v]
                  obtain ⟨wv, rfl⟩ := hvw
                  let mid := setVarHOLFinite (ofString "w") (.val (.word wv)) { sb with locals := s.locals }
                  have heff_mid : ByteRegionEffect s mid [(p.toNat, 8)] := heff_sb.with_locals_clock _ _
                  have hp_mid : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
                      (.var .local (ofString "p")) = some (.val (.word p)) := by
                    simp [evalHOLExact, mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp,
                      show ofString "w" ≠ ofString "p" by decide]
                  have hw_mid : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
                      (.var .local (ofString "w")) = some (.val (.word wv)) := by
                    simp [evalHOLExact, mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  rw [evaluateHOLFiniteState_seq_line780]
                  rcases hst_pair : evaluateHOLFiniteState mid
                      (.store (.var .local (ofString "p")) (.var .local (ofString "w"))) with ⟨rst, sst⟩
                  cases rst with
                  | some _ =>
                    have hst' := hst_pair
                    rw [evaluateHOLFiniteState_store, hp_mid, hw_mid] at hst'; dsimp only at hst'
                    split at hst'
                    · cases hst'
                    · injection hst' with _ hsst; subst hsst; exact ⟨by simp, heff_mid.with_locals_clock _ _⟩
                  | none =>
                    have heff_st := ByteRegionEffect.of_store_word (Rl := [(p.toNat, 8)])
                      (heff_mid.memaddrs.trans hma) hst_pair
                      (fun v hv => by rw [hw_mid] at hv; injection hv with h; exact ⟨wv, h.symm⟩)
                      (fun addr ha _ => by
                        rw [hp_mid] at ha
                        injection ha with e1; injection e1 with e2; injection e2 with e3; subst e3
                        exact ⟨(p.toNat, 8), List.mem_singleton.2 rfl, le_refl _, le_refl _⟩)
                    dsimp only
                    have hret0 : (evaluateHOLFiniteState sst (.return (.const 0#64))).1 = some (.returned (.val (.word 0))) := by
                      rw [evaluateHOLFiniteState_return]
                      have he : @evalHOLExact 64 F _ sst.toExact (fun a => Classical.propDecidable (sst.memaddrs a))
                          (.const 0#64) = some (.val (.word 0)) := rfl
                      rw [he]
                      have hsz : sizeOfShapeWithContextHOL sst.structs (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
                        simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
                      dsimp only; rw [if_pos hsz]
                    rw [hret0]
                    exact ⟨by simp, (heff_mid.trans (heff_st.1.trans (return_eff_wa sst _ _))).with_locals_clock _ _⟩
                · exact ⟨by simp, heff_sb.with_locals_clock _ _⟩
              | timeOut | error | exception _ _ | finalFfi _ | «break» | «continue» =>
                exact ⟨by simp, heff_sb.with_locals_clock _ _⟩
    rcases hy : evaluateHOLFiniteState s yesProg with ⟨ry, sy⟩
    rw [hy] at hnn_eff
    cases ry with
    | none => exact absurd rfl hnn_eff.1
    | some _ => exact hnn_eff.2
  · simp only [hal, ↓reduceIte, evaluateHOLFiniteState_skip]
    refine seq_call_st_be32_known_wa hcode hp_lt (by omega) (by omega)
      (eval_var_local_zero_wa s "p" p hp) fun s1 hc1 _ hl1 => ?_
    have hp1 : s1.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hl1]; exact hp
    refine seq_call_st_be32_known_wa (s := s1) hc1 hp_lt (by omega) (by omega)
      (eval_add_local_const_wa s1 "p" p 4 hp1) fun s2 _ _ _ => return_eff_wa s2 _ _

private theorem seq_call_st_be64_known_wa {F : Type} {s : PanSemStateFiniteExact 64 F}
    {pExp vExp : ExpHOL 64} {base : BitVec 64} {off len : Nat} {cont : ProgHOL 64}
    (hcode : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hbase_lt : base.toNat + len ≤ heapEnd) (hlen : len ≤ 32) (hoff : off + 8 ≤ len)
    (hp_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pExp =
      some (.val (.word (base + BitVec.ofNat 64 off))))
    (hcont : ∀ s1 : PanSemStateFiniteExact 64 F,
      s1.code = originalRuntimeCode → s1.memaddrs = ordinaryDomain → s1.locals = s.locals →
      ByteRegionEffect s1 (evaluateHOLFiniteState s1 cont).2 [(base.toNat, len)]) :
    ByteRegionEffect s
      (evaluateHOLFiniteState s (.seq (.call (some (none, none)) (ofString "st_be64") [pExp, vExp]) cont)).2
      [(base.toNat, len)] := by
  let pArg := base + BitVec.ofNat 64 off
  have hbase_lt0 : base.toNat < heapEnd := by omega
  have hpArg_nat : pArg.toNat = base.toNat + off := bv_add_off_nat_wa base off hbase_lt0 (by omega)
  have hpArg_lt : pArg.toNat + 8 ≤ heapEnd := by rw [hpArg_nat]; omega
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hc : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "st_be64") [pExp, vExp]) with ⟨rc, sc⟩
  rw [evaluateHOLFiniteState_call] at hc
  rcases hv_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) vExp with _ | vv
  · have hnone : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [pExp, vExp] = none := by
      simp [evalListHOLFinite, evalListHOLExact, hp_ev, hv_ev]
    rw [hnone] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s _
  · have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [pExp, vExp] =
        some [.val (.word pArg), vv] := by
      simp [evalListHOLFinite, evalListHOLExact, hp_ev, hv_ev, pArg]
    rw [hargs] at hc; dsimp only at hc
    by_cases hvw : ∃ vW : BitVec 64, vv = .val (.word vW)
    · obtain ⟨vW, rfl⟩ := hvw
      have hl := pan_two_word_lookup s.code.lookup (ofString "st_be64") (ofString "p") (ofString "v")
        (sourceFnBody Guest.Software.guestFn_st_be64) pArg vW (by decide) (by rw [hcode]; exact lookup_st_be64_b)
      rw [hl] at hc; dsimp only at hc
      split at hc
      · injection hc with hr hsc; subst hr hsc; exact (ByteRegionEffect.refl s _).with_locals_clock _ _
      · let entry := callEntryStateHOLFinite s
          ((HolFiniteMapExact.empty.update (ofString "p", .val (.word pArg))).update (ofString "v", .val (.word vW)))
        have hp_in : entry.locals.lookup (ofString "p") = some (.val (.word pArg)) := by
          simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "v" ≠ ofString "p" by decide]
        have heff_b := st_be64_known_eff_wa entry pArg hcode hma hpArg_lt hp_in
        rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_st_be64) with ⟨rb, sb⟩
        have hb_entry : evaluateHOLFiniteState
            (callEntryStateHOLFinite s
              ((HolFiniteMapExact.empty.update (ofString "p", .val (.word pArg))).update (ofString "v", .val (.word vW))))
            (sourceFnBody Guest.Software.guestFn_st_be64) = (rb, sb) := hb
        rw [hb_entry] at hc; rw [hb] at heff_b; dsimp only at heff_b
        have heff_entry : ByteRegionEffect s entry [(base.toNat, len)] :=
          (ByteRegionEffect.refl s _).with_locals_clock _ _
        have heff_sb : ByteRegionEffect s sb [(base.toNat, len)] :=
          heff_entry.trans (heff_b.mono fun i hi => by
            simp only [List.mem_singleton] at hi; subst hi
            exact ⟨(base.toNat, len), List.mem_singleton.2 rfl, by rw [hpArg_nat]; omega, by rw [hpArg_nat]; omega⟩)
        cases rb with
        | none => injection hc with hr hsc; subst hr hsc; exact heff_sb
        | some r =>
          cases r with
          | returned rv =>
            dsimp only at hc; split at hc
            · injection hc with hr hsc; subst hr hsc; dsimp only
              let s1 : PanSemStateFiniteExact 64 F := { sb with locals := s.locals }
              have heff_s1 : ByteRegionEffect s s1 [(base.toNat, len)] := heff_sb.with_locals_clock _ _
              exact heff_s1.trans (hcont s1 (heff_s1.code.trans hcode) (heff_s1.memaddrs.trans hma) rfl)
            · injection hc with hr hsc; subst hr hsc; exact heff_sb
          | timeOut | error | exception _ _ | finalFfi _ =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb.with_locals_clock _ _
          | «break» | «continue» =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb
    · have hln := lookup_two_words_reject_nonword_wa s.code.lookup (ofString "st_be64") (ofString "p") (ofString "v")
        _ pArg vv (by rw [hcode]; exact lookup_st_be64_b) (fun w hw => hvw ⟨w, hw⟩)
      rw [hln] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s _

theorem eps_to_address_masked :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => post.globals = s.globals ∧ evmR post = evmR s)
      (ofString "to_address_masked") := by
  refine ⟨_, _, _, lookup_to_address_masked, ?_⟩
  intro F s hcode hInv _ _ hnt
  have hnc := evaluate_noCatchableRaise warmAccessNcrCallees warmAccessNcrCallees_good
    (sourceFnBody Guest.Software.guestFn_to_address_masked) (by decide) s hcode
  dsimp only
  refine ⟨?_, fun ⟨ev, hev⟩ => False.elim (hnc (ofString "EvmErr") ev (by decide) hev)⟩
  intro v hv
  have hma : s.memaddrs = ordinaryDomain := hInv.1.1.memaddrs
  obtain ⟨hev_pos, hev_he, hb_ev⟩ := evmInv_head_ev_bounds hInv
  obtain ⟨evw, hevw_lk, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
  let aW : BitVec 64 := evw + BitVec.ofNat 64 240
  have haW_nat : aW.toNat = globN s "ev" + 240 := by
    have hev_lt : evw.toNat < heapEnd := by rw [hevw_nat]; omega
    rw [R11Shards.heapEnd_val] at hev_lt
    have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat, h264,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have haW_he : aW.toNat + 20 ≤ heapEnd := by rw [haW_nat]; omega
  have hev_init : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 240)]) =
      some (.val (.word aW)) := by
    simp only [evalHOLExact, evalListHOLExact, hevw_lk, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
    have hz : (240#64 : BitVec 64) + 0 = 240#64 := BitVec.add_zero _
    exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word (evw + w)))) hz
  have heff : ByteRegionEffect s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_to_address_masked)).2
      [(globN s "ev" + 240, 20)] := by
    have hb : sourceFnBody Guest.Software.guestFn_to_address_masked =
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
          (extractFn Guest.Software.guestFn_to_address_masked).body := rfl
    rw [hb]
    dsimp only [extractFn, Guest.Software.guestFn_to_address_masked,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      List.map, Option.map]
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    rw [hev_init]
    dsimp only
    have hsh_ok : shapeEqHOL .one (shapeOfHOLExact (.val (.word aW) : ValueHOL 64)) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    rw [if_pos hsh_ok]
    dsimp only
    let s0 := setVarHOLFinite (ofString "a") (.val (.word aW)) s
    have hs0_eff : ByteRegionEffect s s0 [(aW.toNat, 20)] :=
      (ByteRegionEffect.refl s _).with_locals_clock _ _
    have ha_s0 : s0.locals.lookup (ofString "a") = some (.val (.word aW)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hbody_eff : ByteRegionEffect s0
        (evaluateHOLFiniteState s0
          (.seq
            (.call (some (none, none)) (ofString "st_be32")
              [.var .local (ofString "a"), .rfield 2 (.var .local (ofString "v"))])
            (.seq
              (.call (some (none, none)) (ofString "st_be64")
                [.op .add [.var .local (ofString "a"), .const 4#64],
                 .rfield 1 (.var .local (ofString "v"))])
              (.seq
                (.call (some (none, none)) (ofString "st_be64")
                  [.op .add [.var .local (ofString "a"), .const 12#64],
                   .rfield 0 (.var .local (ofString "v"))])
                (.return (.var .local (ofString "a"))))))).2
        [(aW.toNat, 20)] := by
      refine seq_call_st_be32_known_wa hcode haW_he (by omega) (by omega)
        (eval_var_local_zero_wa s0 "a" aW ha_s0) fun s1 hc1 hm1 hl1 => ?_
      have ha1 : s1.locals.lookup (ofString "a") = some (.val (.word aW)) := by rw [hl1]; exact ha_s0
      refine seq_call_st_be64_known_wa (s := s1) hc1 (hm1.trans hma) haW_he (by omega) (by omega)
        (eval_add_local_const_wa s1 "a" aW 4 ha1) fun s2 hc2 hm2 hl2 => ?_
      have ha2 : s2.locals.lookup (ofString "a") = some (.val (.word aW)) := by rw [hl2]; exact ha1
      refine seq_call_st_be64_known_wa (s := s2) hc2 hm2 haW_he (by omega) (by omega)
        (eval_add_local_const_wa s2 "a" aW 12 ha2) fun s3 _ _ _ => return_eff_wa s3 _ _
    rw [← haW_nat]
    exact (hs0_eff.trans hbody_eff).with_locals_clock _ _
  let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_to_address_masked)).2
  have hGp : GuestInv post :=
    guestInv_congr (s := s) (t := post) heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hInv.1.1
  have hmem_out : ∀ x : BitVec 64,
      (∀ off ∈ nonStructFrameOffs, x ≠ BitVec.ofNat 64 (globN s "ev" + off)) →
      post.memory x = s.memory x := by
    intro x hne
    by_cases hx_dom : s.memaddrs x
    · have hx8 : x.toNat % 8 = 0 := by
        rw [hma, ordinaryDomain_iff] at hx_dom; exact hx_dom.2.2
      have hev8 : globN s "ev" % 8 = 0 := by
        obtain ⟨_, _, _, _, _, _, hFW_all, _⟩ := hInv
        have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
          unfold evmChain
          have hpos : ∃ m, Wave8GuestInv.maxChain + 1 = m + 1 := ⟨Wave8GuestInv.maxChain, rfl⟩
          obtain ⟨m, hm⟩ := hpos; rw [hm, evmChainFrom]; exact List.mem_cons_self
        exact ((hFW_all _ hhead).1 (globN s "ev", 280) (by simp)).2.1
      apply heff.cell_frame x
      intro i hi hch
      simp only [List.mem_singleton] at hi; subst hi
      obtain ⟨hc1, hc2⟩ := hch
      dsimp only at hc1 hc2
      have hk : x.toNat = globN s "ev" + 240 ∨ x.toNat = globN s "ev" + 248 ∨ x.toNat = globN s "ev" + 256 := by
        omega
      rcases hk with h240 | h248 | h256
      · exact hne 240 (by decide) (BitVec.eq_of_toNat_eq (by
          rw [h240, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]))
      · exact hne 248 (by decide) (BitVec.eq_of_toNat_eq (by
          rw [h248, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]))
      · exact hne 256 (by decide) (BitVec.eq_of_toNat_eq (by
          rw [h256, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]))
    · exact heff.out_dom x hx_dom
  obtain ⟨hInv_p, hch_p, hR_p⟩ := evmInv_of_head_nonstruct hInv hGp heff.globals heff.be hmem_out
  exact ⟨hInv_p, hch_p, le_of_eq hR_p, heff.globals, hR_p⟩

/-! ## 4. Role properties for `ev + 168` (`frame.addr`) and `ev + 176` (`frame.key`) -/

private theorem head_frame_addr_role_props {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hInv : EvmInvAt s S) :
    let t0 := memW s (globN s "ev" + 168)
    t0 ∈ S ∧
    (∀ (i : Nat) (_hi : i + 1 < (evmChain s).length), ¬ DelExclusive s S (evmChain s) i t0) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    globN s "bal_accounts" ≠ t0 ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) := by
  dsimp only
  set t0 := memW s (globN s "ev" + 168)
  obtain ⟨⟨hT, _, _, _⟩, hch_ne, _, _, hFW_all, _, _, _, _, _, _, hRoles, _⟩ := hInv
  have hch_cons : ∃ tail, evmChain s = (globN s "ev", globN s "cur_cont") :: tail := by
    unfold evmChain
    have hpos : ∃ m, Wave8GuestInv.maxChain + 1 = m + 1 := ⟨Wave8GuestInv.maxChain, rfl⟩
    obtain ⟨m, hm⟩ := hpos; rw [hm, evmChainFrom]; exact ⟨_, rfl⟩
  obtain ⟨chTail, hch⟩ := hch_cons
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by rw [hch]; exact List.mem_cons_self
  have ht0_S : t0 ∈ S := (hFW_all _ hhead).2.2.2.2.2.2.2.2.1
  have ht0_pos : 0 < t0 := by
    have := ((hT.2.1 t0 ht0_S).1.1 (t0, 88) (by simp [htabFootprint])).1.1
    have hsb : 0 < sourceBase := by decide
    dsimp at this; omega
  have hnot_world_role : ∀ rname : String, rname ≠ "frame.addr" → (t0, rname) ∉ worldRoleSlots s := by
    intro rname hr_ne hmem
    have hpw : (worldRoleSlots s ++ frameRoleSlots s (evmChain s)).Pairwise
        (fun a b => a.1 = b.1 → a.2 = b.2 ∧ a.2 ∈ sharedRoles) := hRoles.2.1
    have hcross := (List.pairwise_append.1 hpw).2.2 (t0, rname) hmem (t0, "frame.addr")
      (by
        unfold frameRoleSlots
        exact List.mem_flatMap.2 ⟨(globN s "ev", globN s "cur_cont"), hhead, by simp [t0]⟩)
      rfl
    exact hr_ne hcross.1
  refine ⟨ht0_S, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi hdel
    have h0_lt : 0 < (evmChain s).length := by omega
    have hch0 : (evmChain s)[0].1 = globN s "ev" := by simp [hch]
    have h168 := hdel.2 0 h0_lt 168 (by decide) (by rw [hch0])
    omega
  · intro hws heq
    apply hnot_world_role "ws+32" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    unfold recRoles; simp [hws, heq]
  · intro hbs heq
    apply hnot_world_role "bs+32" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    unfold recRoles; simp [hbs, heq]
  · intro heq
    apply hnot_world_role "bal_accounts" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_right; simp [heq]
  · intro ad had heq
    apply hnot_world_role "bal.stor" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_right
    exact List.mem_flatMap.2 ⟨ad, had, by simp [heq]⟩
  · intro hts heq
    apply hnot_world_role "ts+32" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_right
    unfold recRoles; simp [hts, heq]

private theorem head_frame_key_role_props {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hInv : EvmInvAt s S) :
    let t0 := memW s (globN s "ev" + 176)
    t0 ∈ S ∧
    (∀ (i : Nat) (_hi : i + 1 < (evmChain s).length), ¬ DelExclusive s S (evmChain s) i t0) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    globN s "bal_accounts" ≠ t0 ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) := by
  dsimp only
  set t0 := memW s (globN s "ev" + 176)
  obtain ⟨⟨hT, _, _, _⟩, hch_ne, _, _, hFW_all, _, _, _, _, _, _, hRoles, _⟩ := hInv
  have hch_cons : ∃ tail, evmChain s = (globN s "ev", globN s "cur_cont") :: tail := by
    unfold evmChain
    have hpos : ∃ m, Wave8GuestInv.maxChain + 1 = m + 1 := ⟨Wave8GuestInv.maxChain, rfl⟩
    obtain ⟨m, hm⟩ := hpos; rw [hm, evmChainFrom]; exact ⟨_, rfl⟩
  obtain ⟨chTail, hch⟩ := hch_cons
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by rw [hch]; exact List.mem_cons_self
  have ht0_S : t0 ∈ S := (hFW_all _ hhead).2.2.2.2.2.2.2.2.2.1
  have ht0_pos : 0 < t0 := by
    have := ((hT.2.1 t0 ht0_S).1.1 (t0, 88) (by simp [htabFootprint])).1.1
    have hsb : 0 < sourceBase := by decide
    dsimp at this; omega
  have hnot_world_role : ∀ rname : String, rname ≠ "frame.key" → (t0, rname) ∉ worldRoleSlots s := by
    intro rname hr_ne hmem
    have hpw : (worldRoleSlots s ++ frameRoleSlots s (evmChain s)).Pairwise
        (fun a b => a.1 = b.1 → a.2 = b.2 ∧ a.2 ∈ sharedRoles) := hRoles.2.1
    have hcross := (List.pairwise_append.1 hpw).2.2 (t0, rname) hmem (t0, "frame.key")
      (by
        unfold frameRoleSlots
        exact List.mem_flatMap.2 ⟨(globN s "ev", globN s "cur_cont"), hhead, by simp [t0]⟩)
      rfl
    exact hr_ne hcross.1
  refine ⟨ht0_S, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi hdel
    have h0_lt : 0 < (evmChain s).length := by omega
    have hch0 : (evmChain s)[0].1 = globN s "ev" := by simp [hch]
    have h176 := hdel.2 0 h0_lt 176 (by decide) (by rw [hch0])
    omega
  · intro hws heq
    apply hnot_world_role "ws+32" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    unfold recRoles; simp [hws, heq]
  · intro hbs heq
    apply hnot_world_role "bs+32" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    unfold recRoles; simp [hbs, heq]
  · intro heq
    apply hnot_world_role "bal_accounts" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_right; simp [heq]
  · intro ad had heq
    apply hnot_world_role "bal.stor" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_right
    exact List.mem_flatMap.2 ⟨ad, had, by simp [heq]⟩
  · intro hts heq
    apply hnot_world_role "ts+32" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_right
    unfold recRoles; simp [hts, heq]

/-! ## 5. Shared `seq (htab_set(*(ev + off), keyVar, 1)) (return 0)` stepping -/

private theorem three_one_word_call_args_wa {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fn : MlS) (e1 e2 e3 : ExpHOL 64)
    (body : ProgHOL 64) (retShape : ShapeHOL)
    (p1 p2 p3 : MlS)
    (hcode : s.code.lookup fn = some ([(p1, .one), (p2, .one), (p3, .one)], body, retShape))
    (hok : (evaluateHOLFiniteState s (.call (some (none, none)) fn [e1, e2, e3])).1 ≠ some .error) :
    ∃ w1 w2 w3 : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 = some (.val (.word w1)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 = some (.val (.word w2)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e3 = some (.val (.word w3)) := by
  rw [evaluateHOLFiniteState_call] at hok
  rcases hv1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
  · simp [evalListHOLFinite, evalListHOLExact, hv1] at hok
  · rcases hv2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | v2
    · simp [evalListHOLFinite, evalListHOLExact, hv1, hv2] at hok
    · rcases hv3 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e3 with _ | v3
      · simp [evalListHOLFinite, evalListHOLExact, hv1, hv2, hv3] at hok
      · have hevl : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1, e2, e3] =
            some [v1, v2, v3] := by
          simp [evalListHOLFinite, evalListHOLExact, hv1, hv2, hv3]
        rw [hevl] at hok; dsimp only at hok
        rcases hl : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fn [v1, v2, v3] with _ | ⟨b, c, rs⟩
        · rw [hl] at hok; exact absurd rfl hok
        · have hraw : lookupCodeHOLExact s.code.lookup fn [v1, v2, v3] ≠ none := by
            intro hn
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
            split at hl
            · simp at hl
            · rename_i hsome; rw [hn] at hsome; simp at hsome
          simp only [lookupCodeHOLExact, hcode, List.length_cons, List.length_nil, ↓reduceIte,
            List.zip, List.zipWith, List.all, Bool.and_true, Bool.and_eq_true] at hraw
          have hshapes : shapeEqHOL .one (shapeOfHOLExact v1) = true ∧
              shapeEqHOL .one (shapeOfHOLExact v2) = true ∧
              shapeEqHOL .one (shapeOfHOLExact v3) = true := by
            by_contra hns; simp [hns] at hraw
          have hw : ∀ v : ValueHOL 64, shapeEqHOL .one (shapeOfHOLExact v) = true → ∃ w, v = .val (.word w) := by
            intro v hsv
            rcases v with ⟨⟨w⟩⟩ | _ | _
            · exact ⟨w, rfl⟩
            · simp [shapeOfHOLExact, shapeEqHOL] at hsv
            · simp [shapeOfHOLExact, shapeEqHOL] at hsv
          obtain ⟨w1, rfl⟩ := hw v1 hshapes.1
          obtain ⟨w2, rfl⟩ := hw v2 hshapes.2.1
          obtain ⟨w3, rfl⟩ := hw v3 hshapes.2.2
          exact ⟨w1, w2, w3, rfl, rfl, rfl⟩

private theorem eval_seq_htab_set_ev_slot_return {F : Type}
    (s : PanSemStateFiniteExact 64 F) (off : Nat) (keyVar : MlS) (v_ret : ValueHOL 64)
    (hoff : off < 280)
    (hcode : s.code = originalRuntimeCode)
    (hInv : EvmInv s)
    (hroles : ∀ S, EvmInvAt s S →
      let t0 := memW s (globN s "ev" + off)
      t0 ∈ S ∧
      (∀ (i : Nat) (_hi : i + 1 < (evmChain s).length), ¬ DelExclusive s S (evmChain s) i t0) ∧
      (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) ∧
      (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
      globN s "bal_accounts" ≠ t0 ∧
      (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
      (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0))
    (hret : (evaluateHOLFiniteState s
      (.seq
        (.call (some (none, none)) (ofString "htab_set")
          [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]),
           .var .local keyVar, .const (BitVec.ofNat 64 1)])
        (.return (.const (BitVec.ofNat 64 0))))).1 = some (.returned v_ret)) :
    let post := (evaluateHOLFiniteState s
      (.seq
        (.call (some (none, none)) (ofString "htab_set")
          [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]),
           .var .local keyVar, .const (BitVec.ofNat 64 1)])
        (.return (.const (BitVec.ofNat 64 0))))).2
    EvmInv post ∧ evmChain post = evmChain s ∧ evmR post = evmR s ∧
      GlobalsKept ["heap_ptr"] s post := by
  dsimp only
  obtain ⟨hAs, S, hW, hrest⟩ := hInv
  have hInvAt : EvmInvAt s S := ⟨hW, hrest⟩
  rcases hrun_c : evaluateHOLFiniteState s
      (.seq
        (.call (some (none, none)) (ofString "htab_set")
          [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]),
           .var .local keyVar, .const (BitVec.ofNat 64 1)])
        (.return (.const (BitVec.ofNat 64 0)))) with ⟨res_c, post_c⟩
  have hret' : res_c = some (.returned v_ret) := by
    have := hret; rw [hrun_c] at this; exact this
  subst hret'
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780] at hrun_c
  rcases hc_set : evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]),
         .var .local keyVar, .const (BitVec.ofNat 64 1)]) with ⟨r_set, s2⟩
  rw [hc_set] at hrun_c
  cases r_set with
  | some rs =>
    dsimp only at hrun_c
    exfalso
    have hrs_ret : rs = .returned v_ret := Option.some.inj (Prod.mk.inj hrun_c).1
    rw [evaluateHOLFiniteState_call] at hc_set
    split at hc_set
    · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
    · split at hc_set
      · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
      · split at hc_set
        · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
        · split at hc_set
          · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · split at hc_set
            · simp at hc_set
            · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · rename_i other _ _ heq_other _ _
            have h1 := Option.some.inj (Prod.mk.inj hc_set).1
            rw [hrs_ret] at h1; subst h1; exact heq_other v_ret rfl
  | none =>
    dsimp only at hrun_c
    rw [evaluateHOLFiniteState_return] at hrun_c
    have hev0_s2 : @evalHOLExact 64 F _ s2.toExact
        (fun a => Classical.propDecidable (s2.memaddrs a)) (.const (BitVec.ofNat 64 0)) =
        some (.val (.word 0)) := rfl
    have hsz0_s2 : sizeOfShapeWithContextHOL s2.structs
        (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
      simp [shapeOfHOLExact]
    rw [hev0_s2] at hrun_c; dsimp only at hrun_c; rw [if_pos hsz0_s2] at hrun_c
    injection hrun_c with _ hpost_c
    obtain ⟨tw, kw, vw, htw_ev, hkw_ev, hvw_ev⟩ :=
      three_one_word_call_args_wa s (ofString "htab_set")
        (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]))
        (.var .local keyVar) (.const (BitVec.ofNat 64 1))
        _ _ (ofString "t") (ofString "key") (ofString "value")
        (by rw [hcode]; exact SoloHtabSet.lookup_htab_set)
        (by rw [hc_set]; simp)
    obtain ⟨hev_pos, _, hb_ev⟩ := evmInv_head_ev_bounds ⟨hAs, S, hInvAt⟩
    obtain ⟨evw, hevw_lk, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
    have htw_nat : tw.toNat = memW s (globN s "ev" + off) := by
      have had_eq : @evalHOLExact 64 F _ s.toExact
          (fun a => Classical.propDecidable (s.memaddrs a))
          (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) =
          some (.val (.word (BitVec.ofNat 64 (globN s "ev" + off)))) := by
        simp only [evalHOLExact, evalListHOLExact, hevw_lk, wordOpHOL, wordOp, valueIsWord, valueWord,
          List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, BitVec.add_zero]
        congr 3
        apply BitVec.eq_of_toNat_eq
        have hz0 : (0 : BitVec 64).toNat = 0 := rfl
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat, hz0, Nat.add_zero,
          Nat.mod_eq_of_lt (show off < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show globN s "ev" + off < 2 ^ 64 by omega)]
      unfold evalHOLExact at htw_ev
      rw [had_eq] at htw_ev; dsimp only at htw_ev
      unfold memLoadHOLExact at htw_ev
      split at htw_ev
      · split at htw_ev
        · injection htw_ev with htw_m
          unfold memW
          cases hm_cell : s.memory (BitVec.ofNat 64 (globN s "ev" + off)) with
          | word cw =>
            change ValueHOL.val (s.memory (BitVec.ofNat 64 (globN s "ev" + off))) = .val (.word tw) at htw_m
            rw [hm_cell] at htw_m
            injection htw_m with htw_m; injection htw_m with htw_m; subst htw_m; rfl
        · cases htw_ev
      · cases htw_ev
    rw [evaluateHOLFiniteState_call] at hc_set
    have hargs_set : evalListHOLFinite s
        (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]),
         .var .local keyVar, .const (BitVec.ofNat 64 1)] =
        some [.val (.word tw), .val (.word kw), .val (.word vw)] := by
      simp [evalListHOLFinite, evalListHOLExact, htw_ev, hkw_ev, hvw_ev]
    have hlook_set := pan_three_word_lookup s.code.lookup (ofString "htab_set")
      (ofString "t") (ofString "key") (ofString "value")
      (sourceFnBody Guest.Software.guestFn_htab_set) tw kw vw
      (by decide) (by decide) (by decide)
      (by rw [hcode]; exact SoloHtabSet.lookup_htab_set)
    rw [hargs_set] at hc_set; dsimp only at hc_set
    rw [hlook_set] at hc_set; dsimp only at hc_set
    by_cases hclk_s : s.clock = 0
    · rw [if_pos hclk_s] at hc_set; simp at hc_set
    · rw [if_neg hclk_s] at hc_set
      let cmap_s : HolFiniteMapExact MlS (ValueHOL 64) :=
        ((HolFiniteMapExact.empty.update (ofString "t", ValueHOL.val (.word tw))).update
          (ofString "key", ValueHOL.val (.word kw))).update (ofString "value", ValueHOL.val (.word vw))
      let entry_s := callEntryStateHOLFinite s cmap_s
      rcases hb_set : evaluateHOLFiniteState entry_s (sourceFnBody Guest.Software.guestFn_htab_set) with
        ⟨r_bs, cpost_s⟩
      have hb_set' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap_s)
          (sourceFnBody Guest.Software.guestFn_htab_set) = (r_bs, cpost_s) := hb_set
      rw [hb_set'] at hc_set
      have hr_bs_ret : ∃ rv_bs, r_bs = some (.returned rv_bs) ∧ s2 = { cpost_s with locals := s.locals } := by
        cases r_bs with
        | none => simp at hc_set
        | some rbi =>
          cases rbi with
          | returned rv_bs =>
            dsimp only at hc_set
            split at hc_set
            · exact ⟨rv_bs, rfl, (Prod.mk.inj hc_set).2.symm⟩
            · simp at hc_set
          | _ => simp at hc_set
      obtain ⟨rv_bs, rfl, hs2_eq⟩ := hr_bs_ret
      obtain ⟨ht0_S, ht0_ndel, ht0_nws32, ht0_nbs32, ht0_nba, ht0_nad, ht0_nts32⟩ :=
        hroles S hInvAt
      have hcal_t : entry_s.locals.lookup (ofString "t") = some (.val (.word tw)) := by
        have h1 : ofString "value" ≠ ofString "t" := by decide
        have h2 : ofString "key" ≠ ofString "t" := by decide
        simp [entry_s, cmap_s, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2, Ne.symm h1, Ne.symm h2]
      have hloc_ts : locN entry_s "t" = memW s (globN s "ev" + off) := by
        simp [locN, hcal_t, htw_nat]
      have hArg_s : HtabArgWF entry_s := by
        refine ⟨⟨guestInv_congr (s := s) rfl rfl rfl rfl hAs.1, hAs.2⟩, ?_, ?_⟩
        · rw [hloc_ts]
          exact (htabWF_lc s entry_s.locals s.globals entry_s.clock _).mpr
            (hInvAt.1.1.2.1 _ ht0_S).1
        · rw [hloc_ts]
          intro i hi
          exact ((hInvAt.1.1.2.1 _ ht0_S).2 i hi).1
      have hhl_entry : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "htab_set")
          [.val (.word tw), .val (.word kw), .val (.word vw)] =
          some (sourceFnBody Guest.Software.guestFn_htab_set, entry_s.locals, .one) := by
        rw [← hcode]; exact hlook_set
      obtain ⟨params_sp, body_sp, rs_sp, hlk_spec, hfn_spec⟩ := SoloHtabSet.htab_set_spec_proof
      have hbody_eq : ([(ofString "t", ShapeHOL.one), (ofString "key", ShapeHOL.one), (ofString "value", ShapeHOL.one)],
          sourceFnBody Guest.Software.guestFn_htab_set, ShapeHOL.one) = (params_sp, body_sp, rs_sp) :=
        Option.some.inj (SoloHtabSet.lookup_htab_set.symm.trans hlk_spec)
      rcases Prod.mk.inj hbody_eq with ⟨_, hbr⟩
      rcases Prod.mk.inj hbr with ⟨hb_eq, hrs_eq⟩
      subst hb_eq hrs_eq
      have hexit_s := hfn_spec entry_s hcode hArg_s ⟨_, hhl_entry⟩
        (by rw [hb_set]; simp) rv_bs (by rw [hb_set])
      have hbe_s : cpost_s.be = s.be := by
        have hbe0 := evaluate_be_eq entry_s (sourceFnBody Guest.Software.guestFn_htab_set)
        rw [hb_set] at hbe0; exact hbe0
      have hcpost_eq : (evaluateHOLFiniteState entry_s (sourceFnBody Guest.Software.guestFn_htab_set)).2 = cpost_s := by
        rw [hb_set]
      rw [hcpost_eq] at hexit_s
      unfold HtabExit at hexit_s; dsimp only at hexit_s
      rw [hloc_ts] at hexit_s
      obtain ⟨hAp_s, hwf_s, hhdr0_s, _, hhp_s, hfp_s, hfr_s, hg_s⟩ := hexit_s
      obtain ⟨hInv_cs, hch_cs, hR_cs, _⟩ := evmInvAt_of_htab_step
        hAs hInvAt hAp_s hbe_s hwf_s hhdr0_s hhp_s hfp_s hfr_s
        (fun k hk => hg_s k (fun h => hk (by simp at h; simp [h])))
        (by
          have hjn : globN cpost_s "journal_n" = globN entry_s "journal_n" :=
            globN_eq_of_lookup_eq (hg_s (ofString "journal_n") (by decide)).symm
          have hjn_ent : globN entry_s "journal_n" = globN s "journal_n" := rfl
          omega)
        ht0_S ht0_ndel ht0_nws32 ht0_nbs32 ht0_nba ht0_nad (Or.inl ht0_nts32)
      have hcpost_inv : EvmInv cpost_s := ⟨hAp_s, S, hInv_cs⟩
      have hpost_eq : post_c = { cpost_s with locals := post_c.locals, clock := cpost_s.clock } := by
        rw [← hpost_c, hs2_eq]; rfl
      have hch_p : evmChain post_c = evmChain cpost_s := by
        rw [hpost_eq]; exact evmChain_lc cpost_s _ _
      have hR_p : evmR post_c = R16Shards.evmR cpost_s := by
        rw [hpost_eq]; exact evmR_lc cpost_s _ _
      refine ⟨?_, ?_, ?_, ?_⟩
      · have h := localsFree_evmInv cpost_s post_c.locals cpost_s.clock hcpost_inv
        rwa [← hpost_eq] at h
      · exact hch_p.trans hch_cs
      · exact hR_p.trans hR_cs
      · intro k hk
        rw [hpost_eq]
        exact hg_s k hk

/-! ## 6. `eps_warm_address`, `eps_warm_after_charge`, `eps_is_warm_storage_key`, `eps_warm_storage_key` -/

theorem eps_warm_address :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr"] s post ∧ evmR post = evmR s)
      (ofString "warm_address") := by
  refine ⟨_, _, _, lookup_warm_address, ?_⟩
  intro F s hcode hInv _ _ hnt
  have hnc := evaluate_noCatchableRaise warmAccessNcrCallees warmAccessNcrCallees_good
    (sourceFnBody Guest.Software.guestFn_warm_address) (by decide) s hcode
  dsimp only
  refine ⟨?_, fun ⟨ev, hev⟩ => False.elim (hnc (ofString "EvmErr") ev (by decide) hev)⟩
  intro v hv
  have hb : sourceFnBody Guest.Software.guestFn_warm_address =
      .seq
        (.call (some (none, none)) (ofString "htab_set")
          [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 168)]),
           .var .local (ofString "addr"), .const (BitVec.ofNat 64 1)])
        (.return (.const (BitVec.ofNat 64 0))) := rfl
  rw [hb] at hv ⊢
  obtain ⟨hInv_p, hch_p, hR_p, hg_p⟩ := eval_seq_htab_set_ev_slot_return s 168 (ofString "addr") v
    (by omega) hcode hInv (fun _ hIA => head_frame_addr_role_props hIA) hv
  exact ⟨hInv_p, hch_p, le_of_eq hR_p, hg_p, hR_p⟩

theorem eps_warm_after_charge :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr"] s post ∧ evmR post = evmR s)
      (ofString "warm_after_charge") := by
  refine ⟨_, _, _, lookup_warm_after_charge, ?_⟩
  intro F s hcode hInv _ _ hnt
  have hnc := evaluate_noCatchableRaise warmAccessNcrCallees warmAccessNcrCallees_good
    (sourceFnBody Guest.Software.guestFn_warm_after_charge) (by decide) s hcode
  dsimp only
  refine ⟨?_, fun ⟨ev, hev⟩ => False.elim (hnc (ofString "EvmErr") ev (by decide) hev)⟩
  intro v hv
  have hb : sourceFnBody Guest.Software.guestFn_warm_after_charge =
      .seq
        (.ite (.cmp .equal (.var .local (ofString "c")) (.const (BitVec.ofNat 64 3000)))
          (.call (some (none, none)) (ofString "warm_address") [.var .local (ofString "addr")])
          .skip)
        (.return (.const (BitVec.ofNat 64 0))) := rfl
  rcases hrun : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_warm_after_charge) with ⟨res, post⟩
  rw [hrun] at hv hnt; dsimp only at hv hnt ⊢
  subst hv
  rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hrun
  rcases hcond : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString "c")) (.const (BitVec.ofNat 64 3000))) with _ | cv
  · rw [hcond] at hrun; simp at hrun
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _
    · rw [hcond] at hrun; dsimp only at hrun
      by_cases hcw0 : cw = 0
      · subst hcw0; simp only [↓reduceIte, evaluateHOLFiniteState_skip] at hrun
        rw [evaluateHOLFiniteState_return] at hrun
        have hev0 : @evalHOLExact 64 F _ s.toExact
            (fun a => Classical.propDecidable (s.memaddrs a)) (.const (BitVec.ofNat 64 0)) =
            some (.val (.word 0)) := rfl
        have hsz0 : sizeOfShapeWithContextHOL s.structs
            (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
          simp [shapeOfHOLExact]
        rw [hev0] at hrun; dsimp only at hrun; rw [if_pos hsz0] at hrun
        injection hrun with _ hp_eq
        rw [← hp_eq]
        have hInv_el : EvmInv s.emptyLocalsHOLFinite := localsFree_evmInv s _ s.clock hInv
        have hch_el : evmChain s.emptyLocalsHOLFinite = evmChain s := evmChain_lc s _ _
        have hR_el : evmR s.emptyLocalsHOLFinite = evmR s := evmR_lc s _ _
        exact ⟨hInv_el, hch_el, le_of_eq hR_el, fun _ _ => rfl, hR_el⟩
      · simp only [hcw0, ↓reduceIte] at hrun
        rcases hc_wa : evaluateHOLFiniteState s
            (.call (some (none, none)) (ofString "warm_address") [.var .local (ofString "addr")]) with ⟨r_wa, s1⟩
        rw [hc_wa] at hrun; dsimp only at hrun
        cases r_wa with
        | none =>
          rw [evaluateHOLFiniteState_call] at hc_wa
          rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
              [.var .local (ofString "addr")] with _ | vals
          · rw [hargs] at hc_wa; simp at hc_wa
          · rw [hargs] at hc_wa; dsimp only at hc_wa
            rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "warm_address") vals with _ | ⟨b_wa, cal_wa, rs_wa⟩
            · rw [hl] at hc_wa; simp at hc_wa
            · rw [hl] at hc_wa; dsimp only at hc_wa
              by_cases hz : s.clock = 0
              · rw [if_pos hz] at hc_wa; simp at hc_wa
              · rw [if_neg hz] at hc_wa
                obtain ⟨params_wa, body_wa, ret_wa, hlook_wa, hspec_wa⟩ := eps_warm_address
                have hbody_eq := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "warm_address")
                  params_wa body_wa b_wa ret_wa rs_wa vals cal_wa (by rw [hcode]; exact hlook_wa) hl
                subst b_wa
                have hret_eq : rs_wa = ret_wa := by
                  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
                    s.code.lookup (ofString "warm_address") vals body_wa cal_wa rs_wa hl
                  rw [hcode] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook_wa] at hx
                  split at hx
                  · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
                  · cases hx
                subst rs_wa
                have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "warm_address") vals =
                    some (body_wa, cal_wa, ret_wa) := by rwa [← hcode]
                let ce := callEntryStateHOLFinite s cal_wa
                have hInv_ce : EvmInv ce := localsFree_evmInv s cal_wa (s.clock - 1) hInv
                rcases hrun_wa : evaluateHOLFiniteState (callEntryStateHOLFinite s cal_wa) body_wa with ⟨res_wa, cpost⟩
                rw [hrun_wa] at hc_wa
                cases res_wa with
                | none => simp at hc_wa
                | some rw0 =>
                  cases rw0 with
                  | returned v_wa =>
                    dsimp only at hc_wa
                    split at hc_wa
                    · injection hc_wa with _ hs1
                      rw [evaluateHOLFiniteState_return] at hrun
                      have hev0 : @evalHOLExact 64 F _ s1.toExact
                          (fun a => Classical.propDecidable (s1.memaddrs a)) (.const (BitVec.ofNat 64 0)) =
                          some (.val (.word 0)) := rfl
                      have hsz0 : sizeOfShapeWithContextHOL s1.structs
                          (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
                        simp [shapeOfHOLExact]
                      rw [hev0] at hrun; dsimp only at hrun; rw [if_pos hsz0] at hrun
                      injection hrun with _ hp_eq
                      have hs_wa := (hspec_wa ce hcode hInv_ce trivial ⟨vals, hl_orig⟩
                        (by rw [hrun_wa]; simp)).1 v_wa (by rw [hrun_wa])
                      dsimp only at hs_wa; rw [hrun_wa] at hs_wa
                      obtain ⟨hInv_cp, hch_cp, _, hg_cp, hR_cp⟩ := hs_wa
                      have hp_cp : post = { cpost with locals := post.locals, clock := cpost.clock } := by
                        rw [← hp_eq, ← hs1]; rfl
                      have hInv_p : EvmInv post := by
                        have h := localsFree_evmInv cpost post.locals cpost.clock hInv_cp
                        rwa [← hp_cp] at h
                      have hch_p : evmChain post = evmChain s := by
                        rw [hp_cp]
                        exact (evmChain_lc cpost _ _).trans (hch_cp.trans (evmChain_lc s _ _))
                      have hR_p : evmR post = evmR s := by
                        rw [hp_cp]
                        exact (evmR_lc cpost _ _).trans (hR_cp.trans (evmR_lc s _ _))
                      exact ⟨hInv_p, hch_p, le_of_eq hR_p, fun k hk => by rw [hp_cp]; exact hg_cp k hk, hR_p⟩
                    · simp at hc_wa
                  | _ => simp at hc_wa
        | some r0 =>
          cases r0 with
          | returned _ =>
            rw [evaluateHOLFiniteState_call] at hc_wa
            rcases hargs2 : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
                [.var .local (ofString "addr")] with _ | vals
            · rw [hargs2] at hc_wa; simp at hc_wa
            · rw [hargs2] at hc_wa; dsimp only at hc_wa
              rcases hl2 : lookupCodeHOLFinite s.code.lookup (ofString "warm_address") vals with _ | ⟨b_wa, cal_wa, rs_wa⟩
              · rw [hl2] at hc_wa; simp at hc_wa
              · rw [hl2] at hc_wa; dsimp only at hc_wa
                split at hc_wa
                · simp at hc_wa
                · rcases hrun2 : evaluateHOLFiniteState (callEntryStateHOLFinite s cal_wa) b_wa with ⟨rw1, _⟩
                  rw [hrun2] at hc_wa
                  cases rw1 with
                  | none => simp at hc_wa
                  | some rw2 =>
                    cases rw2 with
                    | returned _ => dsimp only at hc_wa; split at hc_wa <;> simp at hc_wa
                    | _ => simp at hc_wa
          | _ => simp at hrun
    · rw [hcond] at hrun; simp at hrun
    · rw [hcond] at hrun; simp at hrun

theorem eps_is_warm_storage_key :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => post.globals = s.globals ∧ evmR post = evmR s)
      (ofString "is_warm_storage_key") := by
  refine ⟨_, _, _, lookup_is_warm_storage_key, ?_⟩
  intro F s hcode hInv _ _ hnt
  have hnc := evaluate_noCatchableRaise warmAccessNcrCallees warmAccessNcrCallees_good
    (sourceFnBody Guest.Software.guestFn_is_warm_storage_key) (by decide) s hcode
  dsimp only
  refine ⟨?_, fun ⟨ev, hev⟩ => False.elim (hnc (ofString "EvmErr") ev (by decide) hev)⟩
  intro v hv
  have hbody : sourceFnBody Guest.Software.guestFn_is_warm_storage_key =
      .decCall (ofString "k") .one (ofString "sk_make")
        [.var .local (ofString "addr"), .var .local (ofString "key")]
        (.decCall (ofString "h") .one (ofString "htab_has")
          [.load .one (.op .add [.var .global (ofString "ev"), .const 176]),
           .var .local (ofString "k")]
          (.return (.var .local (ofString "h")))) := rfl
  let tailProg : ProgHOL 64 :=
    .decCall (ofString "h") .one (ofString "htab_has")
      [.load .one (.op .add [.var .global (ofString "ev"), .const 176]),
       .var .local (ofString "k")]
      (.return (.var .local (ofString "h")))
  rcases hrun_all : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_is_warm_storage_key) with ⟨res_all, post⟩
  rw [hrun_all] at hv hnt; dsimp only at hv hnt ⊢
  subst hv
  rw [hbody, evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun_all
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "addr"), .var .local (ofString "key")] with _ | vals
  · rw [hargs] at hrun_all; simp at hrun_all
  · rw [hargs] at hrun_all; dsimp only at hrun_all
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "sk_make") vals with _ | ⟨body_sk, cal_sk, ret_sk⟩
    · rw [hl] at hrun_all; simp at hrun_all
    · rw [hl] at hrun_all; dsimp only at hrun_all
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hrun_all; simp at hrun_all
      · rw [if_neg hz] at hrun_all
        obtain ⟨params_sk, body_sk0, ret_sk0, hlook_sk, hspec_sk⟩ := eps_sk_make
        have hbody_eq : body_sk = body_sk0 :=
          lookupCodeHOLFinite_installed_body s.code.lookup (ofString "sk_make")
            params_sk body_sk0 body_sk ret_sk0 ret_sk vals cal_sk (by rw [hcode]; exact hlook_sk) hl
        subst body_sk
        have hret_eq : ret_sk = ret_sk0 := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
            s.code.lookup (ofString "sk_make") vals body_sk0 cal_sk ret_sk hl
          rw [hcode] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook_sk] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst ret_sk
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "sk_make") vals =
            some (body_sk0, cal_sk, ret_sk0) := by rwa [← hcode]
        let ce := callEntryStateHOLFinite s cal_sk
        have hInv_ce : EvmInv ce := localsFree_evmInv s cal_sk (s.clock - 1) hInv
        have hmeta_sk := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s cal_sk) body_sk0).1
        rcases hrun_sk : evaluateHOLFiniteState (callEntryStateHOLFinite s cal_sk) body_sk0 with ⟨res_sk, cpost⟩
        rw [hrun_sk] at hmeta_sk hrun_all
        cases res_sk with
        | none => simp at hrun_all
        | some r0 =>
          cases r0 with
          | returned kv =>
            dsimp only at hrun_all
            by_cases hsh_kv : (shapeEqHOL (shapeOfHOLExact kv) .one && shapeEqHOL (shapeOfHOLExact kv) ret_sk0) = true
            · rw [if_pos hsh_kv] at hrun_all
              have hs_sk := (hspec_sk ce hcode hInv_ce trivial ⟨vals, hl_orig⟩
                (by rw [hrun_sk]; simp)).1 kv (by rw [hrun_sk])
              dsimp only at hs_sk; rw [hrun_sk] at hs_sk
              obtain ⟨hInv_cp, hch_cp, _, hg_cp, hR_cp⟩ := hs_sk
              let s1 := setVarHOLFinite (ofString "k") kv { cpost with locals := s.locals }
              have hs1_code : s1.code = originalRuntimeCode := hmeta_sk.trans hcode
              change (let out2 := evaluateHOLFiniteState s1 tailProg;
                (out2.1, { out2.2 with locals := out2.2.locals.resVarEq (ofString "k", s.locals.lookup (ofString "k")) })) =
                (some (.returned v), post) at hrun_all
              rcases htail : evaluateHOLFiniteState s1 tailProg with ⟨rtail, stail⟩
              rw [htail] at hrun_all; dsimp only at hrun_all
              injection hrun_all with hrt hp_eq
              have hsafe_tail := evaluate_readOnlyProg opRoCallees opRoCallees_good
                tailProg (by decide) s1 hs1_code
              have hlf_tail : LocFrame s1 stail := by
                have h := hsafe_tail.to_resumes (by rw [htail, hrt]; exact Or.inl ⟨v, rfl⟩)
                rwa [htail] at h
              have hp_cp : post = { cpost with locals := post.locals, clock := stail.clock } := by
                rw [← hp_eq]
                unfold LocFrame at hlf_tail
                rw [hlf_tail]; rfl
              have hInv_p : EvmInv post := by
                have h := localsFree_evmInv cpost post.locals stail.clock hInv_cp
                rwa [← hp_cp] at h
              have hg_s : post.globals = s.globals := (by rw [hp_cp] : post.globals = cpost.globals).trans hg_cp
              have hch_s : evmChain post = evmChain s := by
                rw [hp_cp]
                exact (evmChain_lc cpost _ _).trans (hch_cp.trans (evmChain_lc s _ _))
              have hR_s : evmR post = evmR s := by
                rw [hp_cp]
                exact (evmR_lc cpost _ _).trans (hR_cp.trans (evmR_lc s _ _))
              exact ⟨hInv_p, hch_s, le_of_eq hR_s, hg_s, hR_s⟩
            · rw [if_neg hsh_kv] at hrun_all; simp at hrun_all
          | _ => simp at hrun_all

theorem eps_warm_storage_key :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr"] s post ∧ evmR post = evmR s)
      (ofString "warm_storage_key") := by
  refine ⟨_, _, _, lookup_warm_storage_key, ?_⟩
  intro F s hcode hInv _ _ hnt
  have hnc := evaluate_noCatchableRaise warmAccessNcrCallees warmAccessNcrCallees_good
    (sourceFnBody Guest.Software.guestFn_warm_storage_key) (by decide) s hcode
  dsimp only
  refine ⟨?_, fun ⟨ev, hev⟩ => False.elim (hnc (ofString "EvmErr") ev (by decide) hev)⟩
  intro v hv
  have hbody : sourceFnBody Guest.Software.guestFn_warm_storage_key =
      .decCall (ofString "k") .one (ofString "sk_make")
        [.var .local (ofString "addr"), .var .local (ofString "key")]
        (.seq
          (.call (some (none, none)) (ofString "htab_set")
            [.load .one (.op .add [.var .global (ofString "ev"), .const 176]),
             .var .local (ofString "k"), .const 1])
          (.return (.const 0))) := rfl
  let contProg : ProgHOL 64 :=
    .seq
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "ev"), .const 176]),
         .var .local (ofString "k"), .const 1])
      (.return (.const 0))
  rcases hrun_all : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_warm_storage_key) with ⟨res_all, post⟩
  rw [hrun_all] at hv hnt; dsimp only at hv hnt ⊢
  subst hv
  rw [hbody, evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun_all
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "addr"), .var .local (ofString "key")] with _ | vals
  · rw [hargs] at hrun_all; simp at hrun_all
  · rw [hargs] at hrun_all; dsimp only at hrun_all
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "sk_make") vals with _ | ⟨body_sk, cal_sk, ret_sk⟩
    · rw [hl] at hrun_all; simp at hrun_all
    · rw [hl] at hrun_all; dsimp only at hrun_all
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hrun_all; simp at hrun_all
      · rw [if_neg hz] at hrun_all
        obtain ⟨params_sk, body_sk0, ret_sk0, hlook_sk, hspec_sk⟩ := eps_sk_make
        have hbody_eq : body_sk = body_sk0 :=
          lookupCodeHOLFinite_installed_body s.code.lookup (ofString "sk_make")
            params_sk body_sk0 body_sk ret_sk0 ret_sk vals cal_sk (by rw [hcode]; exact hlook_sk) hl
        subst body_sk
        have hret_eq : ret_sk = ret_sk0 := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
            s.code.lookup (ofString "sk_make") vals body_sk0 cal_sk ret_sk hl
          rw [hcode] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook_sk] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst ret_sk
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "sk_make") vals =
            some (body_sk0, cal_sk, ret_sk0) := by rwa [← hcode]
        let ce := callEntryStateHOLFinite s cal_sk
        have hInv_ce : EvmInv ce := localsFree_evmInv s cal_sk (s.clock - 1) hInv
        have hmeta_sk := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s cal_sk) body_sk0).1
        rcases hrun_sk : evaluateHOLFiniteState (callEntryStateHOLFinite s cal_sk) body_sk0 with ⟨res_sk, cpost⟩
        rw [hrun_sk] at hmeta_sk hrun_all
        cases res_sk with
        | none => simp at hrun_all
        | some r0 =>
          cases r0 with
          | returned kv =>
            dsimp only at hrun_all
            by_cases hsh_kv : (shapeEqHOL (shapeOfHOLExact kv) .one && shapeEqHOL (shapeOfHOLExact kv) ret_sk0) = true
            · rw [if_pos hsh_kv] at hrun_all
              have hs_sk := (hspec_sk ce hcode hInv_ce trivial ⟨vals, hl_orig⟩
                (by rw [hrun_sk]; simp)).1 kv (by rw [hrun_sk])
              dsimp only at hs_sk; rw [hrun_sk] at hs_sk
              obtain ⟨hInv_cp, hch_cp, _, hg_cp, hR_cp⟩ := hs_sk
              let s1 := setVarHOLFinite (ofString "k") kv { cpost with locals := s.locals }
              have hs1_code : s1.code = originalRuntimeCode := hmeta_sk.trans hcode
              have hInv_s1 : EvmInv s1 := localsFree_evmInv cpost s1.locals cpost.clock hInv_cp
              change (let out2 := evaluateHOLFiniteState s1 contProg;
                (out2.1, { out2.2 with locals := out2.2.locals.resVarEq (ofString "k", s.locals.lookup (ofString "k")) })) =
                (some (.returned v), post) at hrun_all
              rcases hcont : evaluateHOLFiniteState s1 contProg with ⟨rcont, scont⟩
              rw [hcont] at hrun_all; dsimp only at hrun_all
              injection hrun_all with hrc hp_eq
              obtain ⟨hInv_c, hch_c, hR_c, hg_c⟩ := eval_seq_htab_set_ev_slot_return s1 176 (ofString "k") v
                (by omega) hs1_code hInv_s1 (fun _ hIA => head_frame_key_role_props hIA)
                (by change (evaluateHOLFiniteState s1 contProg).1 = _; rw [hcont, hrc])
              change EvmInv (evaluateHOLFiniteState s1 contProg).2 at hInv_c
              change evmChain (evaluateHOLFiniteState s1 contProg).2 = evmChain s1 at hch_c
              change evmR (evaluateHOLFiniteState s1 contProg).2 = evmR s1 at hR_c
              change GlobalsKept ["heap_ptr"] s1 (evaluateHOLFiniteState s1 contProg).2 at hg_c
              rw [hcont] at hInv_c hch_c hR_c hg_c
              have hp_sc : post = { scont with locals := post.locals, clock := scont.clock } := by
                rw [← hp_eq]
              have hInv_p : EvmInv post := by
                have h := localsFree_evmInv scont post.locals scont.clock hInv_c
                rwa [← hp_sc] at h
              have hch_p : evmChain post = evmChain s := by
                rw [hp_sc]
                exact (evmChain_lc scont _ _).trans
                  (hch_c.trans ((evmChain_lc cpost s1.locals cpost.clock).trans
                    (hch_cp.trans (evmChain_lc s _ _))))
              have hR_p : evmR post = evmR s := by
                rw [hp_sc]
                exact (evmR_lc scont _ _).trans
                  (hR_c.trans ((evmR_lc cpost s1.locals cpost.clock).trans
                    (hR_cp.trans (evmR_lc s _ _))))
              have hg_p : GlobalsKept ["heap_ptr"] s post := by
                intro k hk
                have hg_s_s1 : s.globals = s1.globals := hg_cp.symm
                rw [hg_s_s1, hp_sc]
                exact hg_c k hk
              exact ⟨hInv_p, hch_p, le_of_eq hR_p, hg_p, hR_p⟩
            · rw [if_neg hsh_kv] at hrun_all; simp at hrun_all
          | _ => simp at hrun_all

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
