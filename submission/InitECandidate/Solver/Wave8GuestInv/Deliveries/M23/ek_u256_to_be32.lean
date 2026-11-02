import InitECandidate.Solver.Wave8GuestInv.Deliveries.M23.EvmLemmas

/-! `ek_u256_to_be32`: `u256_to_be32(a, out)` (AST line 2265, index 87) satisfies
`EvmKeeps (EvmAvoids (fun s => [(locN s "out", 32)])) [] (ofString "u256_to_be32")`.
Checked against frozen spec revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`). -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8Contracts.M23

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

private theorem lookup_bswap64 :
    originalRuntimeCode.lookup (ofString "bswap64") =
      some ([(ofString "x", .one)], sourceFnBody Guest.Software.guestFn_bswap64, .one) :=
  lookup_of_guestAst_getElem 23 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bswap64) rfl

private theorem lookup_st_be32 :
    originalRuntimeCode.lookup (ofString "st_be32") =
      some ([(ofString "p", .one), (ofString "v", .one)], sourceFnBody Guest.Software.guestFn_st_be32, .one) :=
  lookup_of_guestAst_getElem 27 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_st_be32) rfl

private theorem lookup_st_be64 :
    originalRuntimeCode.lookup (ofString "st_be64") =
      some ([(ofString "p", .one), (ofString "v", .one)], sourceFnBody Guest.Software.guestFn_st_be64, .one) :=
  lookup_of_guestAst_getElem 28 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_st_be64) rfl

private theorem lookup_u256_to_be32 :
    originalRuntimeCode.lookup (ofString "u256_to_be32") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_u256_to_be32, .one) :=
  lookup_of_guestAst_getElem 87 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_to_be32) rfl

private theorem not_resumes_error : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

private theorem byteAlign_lt_heapEnd {s_ma : BitVec 64 → Prop} (hma : s_ma = ordinaryDomain)
    (addr : BitVec 64) (hdom : s_ma (panByteAlignHOL addr)) :
    addr.toNat < heapEnd := by
  rw [hma, ordinaryDomain_iff] at hdom
  have hal := panByteAlign_toNat64 addr
  rw [heapEnd_val]
  omega

private theorem word_dom_lt_heapEnd {s_ma : BitVec 64 → Prop} (hma : s_ma = ordinaryDomain)
    (addr : BitVec 64) (hdom : s_ma addr) :
    addr.toNat + 8 ≤ heapEnd := by
  rw [hma, ordinaryDomain_iff] at hdom
  rw [heapEnd_val]
  omega

private theorem bv_add_off_nat (base : BitVec 64) (off : Nat)
    (hbase : base.toNat < heapEnd) (hoff : off ≤ 32) :
    (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
  rw [heapEnd_val] at hbase
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
  have ho_lt : off < 18446744073709551616 := by omega
  have hsum_lt : base.toNat + off < 18446744073709551616 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, h264, Nat.mod_eq_of_lt ho_lt, Nat.mod_eq_of_lt hsum_lt]

private theorem eval_var_local {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : String) (w : BitVec 64)
    (hloc : s.locals.lookup (ofString nm) = some (.val (.word w))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString nm)) =
      some (.val (.word w)) := hloc

private theorem eval_var_local_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : String) (base : BitVec 64)
    (hloc : s.locals.lookup (ofString nm) = some (.val (.word base))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString nm)) =
      some (.val (.word (base + BitVec.ofNat 64 0))) := by
  have hz : base + BitVec.ofNat 64 0 = base := BitVec.add_zero base
  rw [hz]
  exact hloc

private theorem eval_add_local_const {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : String) (base : BitVec 64) (off : Nat)
    (hloc : s.locals.lookup (ofString nm) = some (.val (.word base))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString nm), .const (BitVec.ofNat 64 off)]) =
      some (.val (.word (base + BitVec.ofNat 64 off))) := by
  simp only [evalHOLExact, evalListHOLExact, hloc, wordOpHOL, wordOp, valueIsWord, valueWord,
    List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
  have hz : BitVec.ofNat 64 off + (0 : BitVec 64) = BitVec.ofNat 64 off := BitVec.add_zero _
  exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word (base + w)))) hz

private theorem eval_align8_eq0 {F : Type} (s : PanSemStateFiniteExact 64 F)
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

private theorem return_const0_step {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s (.return (.const 0#64))).1 = some (.returned (.val (.word 0))) ∧
    (evaluateHOLFiniteState s (.return (.const 0#64))).2 = emptyLocalsHOLFinite s := by
  rw [evaluateHOLFiniteState_return]
  have he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.const 0#64) = some (.val (.word 0)) := rfl
  rw [he]
  have hsz : sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
  dsimp only
  rw [if_pos hsz]
  exact ⟨rfl, rfl⟩

private theorem return_eff {F : Type} (s : PanSemStateFiniteExact 64 F) (ex : ExpHOL 64) (Rl : List Ivl) :
    ByteRegionEffect s (evaluateHOLFiniteState s (.return ex)).2 Rl := by
  have hret : (evaluateHOLFiniteState s (.return ex)).2 =
      { s with locals := (evaluateHOLFiniteState s (.return ex)).2.locals } := by
    rw [evaluateHOLFiniteState_return]
    split
    · rfl
    · split <;> rfl
  conv => arg 2; rw [hret]
  exact (ByteRegionEffect.refl s Rl).with_locals_clock _ s.clock

private theorem ByteRegionEffect.of_mem_globals_eq {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (Rl : List Ivl)
    (hg : post.globals = s.globals)
    (hm : post.memory = s.memory)
    (hc : post.code = s.code)
    (hma : post.memaddrs = s.memaddrs)
    (hsh : post.shMemaddrs = s.shMemaddrs)
    (hba : post.baseAddr = s.baseAddr)
    (hbe : post.be = s.be) :
    ByteRegionEffect s post Rl :=
  ⟨hc, hma, hsh, hba, hbe, hg, fun _ _ => by rw [hm], fun _ _ => by rw [hm],
   fun _ _ _ => by simp [memB, hm, hbe]⟩

/-! ### 1. `bswap64` read-only effect and call wrappers -/

private theorem bswap64_body_ro {F : Type} (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl) :
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
    intro st nm ex
    rw [evaluateHOLFiniteState_assign]
    split
    · rfl
    · split <;> rfl
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
  exact hs1.trans (hseq_ro s1 _ _ (hasgn_eff s1 _ _) (fun s2 hs2 => hs2.trans (return_eff s2 _ Rl)))

private theorem bswap64_body_mem_eq {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_bswap64)).2.memory = s.memory := by
  have h := bswap64_body_ro s []
  funext a
  exact h.cell_frame a (fun _ hi => by simp at hi)

private theorem decCall_bswap64_eff {F : Type} {s : PanSemStateFiniteExact 64 F}
    {argExp : ExpHOL 64} {cont : ProgHOL 64} {Rl : List Ivl}
    (hcode : s.code = originalRuntimeCode)
    (hcont : ∀ mid : PanSemStateFiniteExact 64 F,
      mid.code = originalRuntimeCode →
      mid.memaddrs = s.memaddrs →
      mid.locals.lookup (ofString "out") = s.locals.lookup (ofString "out") →
      mid.locals.lookup (ofString "p") = s.locals.lookup (ofString "p") →
      mid.locals.lookup (ofString "a") = s.locals.lookup (ofString "a") →
      (∃ wv : BitVec 64, mid.locals.lookup (ofString "w") = some (.val (.word wv))) →
      ByteRegionEffect mid (evaluateHOLFiniteState mid cont).2 Rl) :
    ByteRegionEffect s
      (evaluateHOLFiniteState s (.decCall (ofString "w") .one (ofString "bswap64") [argExp] cont)).2
      Rl := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [argExp] with _ | vals
  · exact ByteRegionEffect.refl s Rl
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "bswap64") vals with _ | ⟨body', callee, ret'⟩
    · exact ByteRegionEffect.refl s Rl
    · dsimp only
      have hinst := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "bswap64")
        _ _ body' _ ret' vals callee (by rw [hcode]; exact lookup_bswap64) hl
      subst hinst
      have hret_eq : ret' = .one := by
        unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
        split at hl
        · cases hl
        · rename_i eb el es hraw
          have hinj := Option.some.inj hl
          rcases Prod.mk.inj hinj with ⟨_, hr2⟩
          rcases Prod.mk.inj hr2 with ⟨_, rfl⟩
          unfold lookupCodeHOLExact at hraw
          rw [hcode, lookup_bswap64] at hraw
          dsimp only at hraw
          split at hraw <;> [ (injection hraw with h'; exact (Prod.mk.inj (Prod.mk.inj h').2).2.symm); cases hraw ]
      subst hret_eq
      split
      · exact (ByteRegionEffect.refl s Rl).with_locals_clock _ _
      · have heff_entry : ByteRegionEffect s (callEntryStateHOLFinite s callee) Rl :=
          (ByteRegionEffect.refl s Rl).with_locals_clock _ _
        have heff_b := bswap64_body_ro (callEntryStateHOLFinite s callee) Rl
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_bswap64) with ⟨rb, sb⟩
        rw [hb] at heff_b
        dsimp only at heff_b ⊢
        have heff_sb : ByteRegionEffect s sb Rl := heff_entry.trans heff_b
        cases rb with
        | none => exact heff_sb
        | some r =>
          cases r with
          | returned v =>
            dsimp only
            split
            · rename_i hsh
              have hvw : ∃ wv : BitVec 64, v = .val (.word wv) := by
                rcases v with ⟨⟨wv⟩⟩ | _ | _
                · exact ⟨wv, rfl⟩
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh
              obtain ⟨wv, rfl⟩ := hvw
              let mid := setVarHOLFinite (ofString "w") (.val (.word wv)) { sb with locals := s.locals }
              have heff_mid : ByteRegionEffect s mid Rl := heff_sb.with_locals_clock _ _
              have hc_mid : mid.code = originalRuntimeCode := heff_mid.code.trans hcode
              have hm_mid : mid.memaddrs = s.memaddrs := heff_mid.memaddrs
              have hout_mid : mid.locals.lookup (ofString "out") = s.locals.lookup (ofString "out") := by
                simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "w" ≠ ofString "out" by decide]
              have hp_mid : mid.locals.lookup (ofString "p") = s.locals.lookup (ofString "p") := by
                simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "w" ≠ ofString "p" by decide]
              have ha_mid : mid.locals.lookup (ofString "a") = s.locals.lookup (ofString "a") := by
                simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "w" ≠ ofString "a" by decide]
              have hw_mid : ∃ wv : BitVec 64, mid.locals.lookup (ofString "w") = some (.val (.word wv)) :=
                ⟨wv, by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
              have heff_c := hcont mid hc_mid hm_mid hout_mid hp_mid ha_mid hw_mid
              exact (heff_mid.trans heff_c).with_locals_clock _ _
            · exact heff_sb
          | timeOut | error | exception _ _ | finalFfi _ => exact heff_sb.with_locals_clock _ _
          | «break» | «continue» => exact heff_sb

private theorem seq_call_bswap64_eff {F : Type} {s : PanSemStateFiniteExact 64 F}
    {argExp : ExpHOL 64} {cont : ProgHOL 64} {Rl : List Ivl}
    (hcode : s.code = originalRuntimeCode)
    (hcont : ∀ mid : PanSemStateFiniteExact 64 F,
      mid.code = originalRuntimeCode →
      mid.memaddrs = s.memaddrs →
      mid.locals.lookup (ofString "out") = s.locals.lookup (ofString "out") →
      mid.locals.lookup (ofString "a") = s.locals.lookup (ofString "a") →
      (∃ wv : BitVec 64, mid.locals.lookup (ofString "w") = some (.val (.word wv))) →
      ByteRegionEffect mid (evaluateHOLFiniteState mid cont).2 Rl) :
    ByteRegionEffect s
      (evaluateHOLFiniteState s
        (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [argExp]) cont)).2
      Rl := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hc : evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [argExp]) with ⟨rc, sc⟩
  rw [evaluateHOLFiniteState_call] at hc
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [argExp] with _ | vals
  · rw [hargs] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s Rl
  · rw [hargs] at hc; dsimp only at hc
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "bswap64") vals with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s Rl
    · rw [hl] at hc; dsimp only at hc
      have hinst := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "bswap64")
        _ _ body' _ ret' vals callee (by rw [hcode]; exact lookup_bswap64) hl
      subst hinst
      have hret_eq : ret' = .one := by
        unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
        split at hl
        · cases hl
        · rename_i eb el es hraw
          have hinj := Option.some.inj hl
          rcases Prod.mk.inj hinj with ⟨_, hr2⟩
          rcases Prod.mk.inj hr2 with ⟨_, rfl⟩
          unfold lookupCodeHOLExact at hraw
          rw [hcode, lookup_bswap64] at hraw
          dsimp only at hraw
          split at hraw <;> [ (injection hraw with h'; exact (Prod.mk.inj (Prod.mk.inj h').2).2.symm); cases hraw ]
      subst hret_eq
      split at hc
      · injection hc with hr hsc; subst hr hsc; exact (ByteRegionEffect.refl s Rl).with_locals_clock _ _
      · have heff_entry : ByteRegionEffect s (callEntryStateHOLFinite s callee) Rl :=
          (ByteRegionEffect.refl s Rl).with_locals_clock _ _
        have heff_b := bswap64_body_ro (callEntryStateHOLFinite s callee) Rl
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_bswap64) with ⟨rb, sb⟩
        rw [hb] at hc heff_b
        dsimp only at heff_b
        have heff_sb : ByteRegionEffect s sb Rl := heff_entry.trans heff_b
        cases rb with
        | none => injection hc with hr hsc; subst hr hsc; exact heff_sb
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hc
            split at hc
            · rename_i hsh
              have hvw : ∃ wv : BitVec 64, v = .val (.word wv) := by
                rcases v with ⟨⟨wv⟩⟩ | _ | _
                · exact ⟨wv, rfl⟩
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh
              obtain ⟨wv, rfl⟩ := hvw
              split at hc
              · injection hc with hr hsc; subst hr hsc
                dsimp only
                let mid := setKvarHOLFinite .local (ofString "w") (.val (.word wv)) { sb with locals := s.locals }
                have heff_mid : ByteRegionEffect s mid Rl := heff_sb.with_locals_clock _ _
                have hc_mid : mid.code = originalRuntimeCode := heff_mid.code.trans hcode
                have hm_mid : mid.memaddrs = s.memaddrs := heff_mid.memaddrs
                have hout_mid : mid.locals.lookup (ofString "out") = s.locals.lookup (ofString "out") := by
                  simp [mid, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "w" ≠ ofString "out" by decide]
                have ha_mid : mid.locals.lookup (ofString "a") = s.locals.lookup (ofString "a") := by
                  simp [mid, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "w" ≠ ofString "a" by decide]
                have hw_mid : ∃ wv : BitVec 64, mid.locals.lookup (ofString "w") = some (.val (.word wv)) :=
                  ⟨wv, by simp [mid, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
                exact heff_mid.trans (hcont mid hc_mid hm_mid hout_mid ha_mid hw_mid)
              · injection hc with hr hsc; subst hr hsc; exact heff_sb
            · injection hc with hr hsc; subst hr hsc; exact heff_sb
          | timeOut | error | exception _ _ | finalFfi _ =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb.with_locals_clock _ _
          | «break» | «continue» =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb

/-! ### 2. `seq_store_word_eff` and `seq_storeByte_eff` -/

private theorem seq_store_word_eff {F : Type} {s : PanSemStateFiniteExact 64 F}
    {dstExp valExp : ExpHOL 64} {base w : BitVec 64} {off len : Nat} {cont : ProgHOL 64}
    (hma : s.memaddrs = ordinaryDomain)
    (hlen : len ≤ 32)
    (hoff : off + 8 ≤ len)
    (hprev : off > 0 → base.toNat < heapEnd)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word (base + BitVec.ofNat 64 off))))
    (hval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some (.val (.word w)))
    (hcont : ∀ s1 : PanSemStateFiniteExact 64 F,
      base.toNat < heapEnd →
      s1.code = s.code →
      s1.memaddrs = s.memaddrs →
      s1.locals = s.locals →
      ByteRegionEffect s1 (evaluateHOLFiniteState s1 cont).2 [(base.toNat, len)]) :
    ByteRegionEffect s (evaluateHOLFiniteState s (.seq (.store dstExp valExp) cont)).2 [(base.toNat, len)] := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases h1 : evaluateHOLFiniteState s (.store dstExp valExp) with ⟨r1, s1⟩
  cases r1 with
  | some _ =>
    have h1' := h1
    rw [evaluateHOLFiniteState_store, hdst, hval] at h1'
    dsimp only at h1'
    split at h1'
    · cases h1'
    · injection h1' with _ hs1; subst hs1; exact ByteRegionEffect.refl s _
  | none =>
    have hbase_lt : base.toNat < heapEnd := by
      have hrun' := h1
      rw [evaluateHOLFiniteState_store, hdst, hval] at hrun'
      dsimp only at hrun'
      split at hrun'
      · rename_i m' hst
        unfold flattenHOL panMemStoresHOL panMemStoreHOL at hst
        by_cases hd : s.memaddrs (base + BitVec.ofNat 64 off)
        · by_cases hz : off = 0
          · subst hz; have h0 : base + BitVec.ofNat 64 0 = base := by simp
            rw [h0] at hd; have := word_dom_lt_heapEnd hma base hd; omega
          · exact hprev (by omega)
        · simp [hd] at hst
      · cases hrun'
    have heff1 := ByteRegionEffect.of_store_word (Rl := [(base.toNat, len)]) hma h1
      (fun v hv => by rw [hval] at hv; injection hv with h; exact ⟨w, h.symm⟩)
      (fun addr ha hdom => by
        rw [hdst] at ha
        injection ha with e1; injection e1 with e2; injection e2 with e3; subst e3
        have hnat := bv_add_off_nat base off hbase_lt (by omega)
        exact ⟨(base.toNat, len), List.mem_singleton.2 rfl, by rw [hnat]; omega, by rw [hnat]; omega⟩)
    exact heff1.1.trans (hcont s1 hbase_lt heff1.1.code heff1.1.memaddrs heff1.2)

private theorem seq_storeByte_eff {F : Type} {s : PanSemStateFiniteExact 64 F}
    {dstExp valExp : ExpHOL 64} {base : BitVec 64} {off len : Nat} {cont : ProgHOL 64}
    (hma : s.memaddrs = ordinaryDomain)
    (hlen : len ≤ 32)
    (hoff : off < len)
    (hprev : off > 0 → base.toNat < heapEnd)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word (base + BitVec.ofNat 64 off))))
    (hcont : ∀ s1 : PanSemStateFiniteExact 64 F,
      base.toNat < heapEnd →
      s1.code = s.code →
      s1.memaddrs = s.memaddrs →
      s1.locals = s.locals →
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
      · dsimp only at h1'
        split at h1'
        · cases h1'
        · injection h1' with _ hs1; subst hs1; exact ByteRegionEffect.refl s _
      · dsimp only at h1'; injection h1' with _ hs1; subst hs1; exact ByteRegionEffect.refl s _
      · dsimp only at h1'; injection h1' with _ hs1; subst hs1; exact ByteRegionEffect.refl s _
  | none =>
    have hbase_lt_of_dom : s.memaddrs (panByteAlignHOL (base + BitVec.ofNat 64 off)) → base.toNat < heapEnd := by
      intro hd
      by_cases hz : off = 0
      · subst hz; have h0 : base + BitVec.ofNat 64 0 = base := by simp
        rw [h0] at hd; exact byteAlign_lt_heapEnd hma base hd
      · exact hprev (by omega)
    have hbase_lt : base.toNat < heapEnd := by
      have hrun' := h1
      rw [evaluateHOLFiniteState_storeByte, hdst] at hrun'
      rcases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp with _ | vv
      · rw [hv] at hrun'; simp at hrun'
      · rw [hv] at hrun'
        rcases vv with ⟨⟨v⟩⟩ | _ | _
        · dsimp only at hrun'
          split at hrun'
          · rename_i m' hst
            unfold panMemStoreByteWord8HOL at hst
            rcases hm : s.memory (panByteAlignHOL (base + BitVec.ofNat 64 off)) with ⟨cell⟩
            have hm' : (s.6 (panByteAlignHOL (base + BitVec.ofNat 64 off))).1 = cell := by rw [hm]
            dsimp only at hst; rw [hm'] at hst
            by_cases hd : s.memaddrs (panByteAlignHOL (base + BitVec.ofNat 64 off))
            · exact hbase_lt_of_dom hd
            · simp [hd] at hst
          · simp at hrun'
        · simp at hrun'
        · simp at hrun'
    have heff1 := ByteRegionEffect.of_storeByte (Rl := [(base.toNat, len)]) h1
      (fun addr ha hdom => by
        rw [hdst] at ha
        injection ha with e1; injection e1 with e2; injection e2 with e3; subst e3
        have hnat := bv_add_off_nat base off hbase_lt (by omega)
        exact ⟨(base.toNat, len), List.mem_singleton.2 rfl, by rw [hnat]; omega, by rw [hnat]; omega⟩)
    exact heff1.1.trans (hcont s1 hbase_lt heff1.1.code heff1.1.memaddrs heff1.2)

/-! ### 3. `st_be32` and `st_be64` -/

private theorem st_be32_body_eff {F : Type} (s : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (hma : s.memaddrs = ordinaryDomain)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p))) :
    ByteRegionEffect s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_be32)).2 [(p.toNat, 4)] ∧
    ((evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_be32)).2.memory = s.memory ∨ p.toNat < heapEnd) ∧
    (∀ rv, (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_be32)).1 = some (.returned rv) →
      p.toNat < heapEnd) := by
  have hb : sourceFnBody Guest.Software.guestFn_st_be32 =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_st_be32).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_st_be32,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural]
  have hp_ev0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString "p")) = some (.val (.word p)) := hp
  have hmem_or_lt :
      ((evaluateHOLFiniteState s
        (.seq (.storeByte (.var .local (ofString "p")) (.shift .lsr (.var .local (ofString "v")) (.const 24#64)))
          (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 1#64]) (.shift .lsr (.var .local (ofString "v")) (.const 16#64)))
            (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 2#64]) (.shift .lsr (.var .local (ofString "v")) (.const 8#64)))
              (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 3#64]) (.var .local (ofString "v")))
                (.return (.const 0#64))))))).2.memory = s.memory ∧
       ∀ rv, (evaluateHOLFiniteState s
        (.seq (.storeByte (.var .local (ofString "p")) (.shift .lsr (.var .local (ofString "v")) (.const 24#64)))
          (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 1#64]) (.shift .lsr (.var .local (ofString "v")) (.const 16#64)))
            (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 2#64]) (.shift .lsr (.var .local (ofString "v")) (.const 8#64)))
              (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 3#64]) (.var .local (ofString "v")))
                (.return (.const 0#64))))))).1 ≠ some (.returned rv)) ∨ p.toNat < heapEnd := by
    rw [evaluateHOLFiniteState_seq_line780]
    rcases h1 : evaluateHOLFiniteState s
        (.storeByte (.var .local (ofString "p")) (.shift .lsr (.var .local (ofString "v")) (.const 24#64))) with ⟨r1, s1⟩
    rw [evaluateHOLFiniteState_storeByte, hp_ev0] at h1
    rcases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.shift .lsr (.var .local (ofString "v")) (.const 24#64)) with _ | vv
    · rw [hv] at h1; dsimp only at h1; injection h1 with hr1 hs1; subst hr1 hs1
      exact Or.inl ⟨rfl, by simp⟩
    · rw [hv] at h1
      rcases vv with ⟨⟨vw⟩⟩ | _ | _
      · dsimp only at h1
        split at h1
        · rename_i m' hst
          unfold panMemStoreByteWord8HOL at hst
          rcases hm : s.memory (panByteAlignHOL p) with ⟨cell⟩
          have hm' : (s.6 (panByteAlignHOL p)).1 = cell := by rw [hm]
          dsimp only at hst; rw [hm'] at hst
          by_cases hd : s.memaddrs (panByteAlignHOL p)
          · exact Or.inr (byteAlign_lt_heapEnd hma p hd)
          · simp [hd] at hst
        · injection h1 with hr1 hs1; subst hr1 hs1; exact Or.inl ⟨rfl, by simp⟩
      · dsimp only at h1; injection h1 with hr1 hs1; subst hr1 hs1; exact Or.inl ⟨rfl, by simp⟩
      · dsimp only at h1; injection h1 with hr1 hs1; subst hr1 hs1; exact Or.inl ⟨rfl, by simp⟩
  refine ⟨?_, ?_, ?_⟩
  · refine seq_storeByte_eff (base := p) (off := 0) (len := 4) hma (by omega) (by omega) (fun h => by omega)
      (eval_var_local_zero s "p" p hp) fun s1 hp_lt _ hm1 hl1 => ?_
    have hp1 : s1.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hl1]; exact hp
    refine seq_storeByte_eff (s := s1) (base := p) (off := 1) (len := 4) (hm1.trans hma) (by omega) (by omega)
      (fun _ => hp_lt) (eval_add_local_const s1 "p" p 1 hp1) fun s2 _ _ hm2 hl2 => ?_
    have hp2 : s2.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hl2]; exact hp1
    refine seq_storeByte_eff (s := s2) (base := p) (off := 2) (len := 4) (hm2.trans (hm1.trans hma)) (by omega) (by omega)
      (fun _ => hp_lt) (eval_add_local_const s2 "p" p 2 hp2) fun s3 _ _ hm3 hl3 => ?_
    have hp3 : s3.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hl3]; exact hp2
    refine seq_storeByte_eff (s := s3) (base := p) (off := 3) (len := 4) (hm3.trans (hm2.trans (hm1.trans hma))) (by omega) (by omega)
      (fun _ => hp_lt) (eval_add_local_const s3 "p" p 3 hp3) fun s4 _ _ _ _ => return_eff s4 _ _
  · rcases hmem_or_lt with ⟨hm_eq, _⟩ | hp_lt
    · exact Or.inl hm_eq
    · exact Or.inr hp_lt
  · intro rv hret
    rcases hmem_or_lt with ⟨_, hne⟩ | hp_lt
    · exact absurd hret (hne rv)
    · exact hp_lt

private theorem lookup_two_words_reject_nonword {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (fname p1 p2 : MlS) (body : ProgHOL width) (w1 : BitVec width) (v2 : ValueHOL width)
    (hlook : code fname = some ([(p1, .one), (p2, .one)], body, .one))
    (hnot : ∀ w2 : BitVec width, v2 ≠ .val (.word w2)) :
    lookupCodeHOLFinite code fname [.val (.word w1), v2] = none := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rfl
  · rename_i eb el es hraw
    unfold lookupCodeHOLExact at hraw
    rw [hlook] at hraw
    rcases v2 with ⟨⟨w2⟩⟩ | _ | _
    · exact absurd rfl (hnot w2)
    · simp [shapeOfHOLExact, shapeEqHOL] at hraw
    · simp [shapeOfHOLExact, shapeEqHOL] at hraw

private theorem seq_call_st_be32_eff {F : Type} {s : PanSemStateFiniteExact 64 F}
    {pExp vExp : ExpHOL 64} {base : BitVec 64} {off len : Nat} {cont : ProgHOL 64}
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hlen : len ≤ 32)
    (hoff : off + 4 ≤ len)
    (hprev : off > 0 → base.toNat < heapEnd)
    (hp_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pExp =
      some (.val (.word (base + BitVec.ofNat 64 off))))
    (hcont : ∀ s1 : PanSemStateFiniteExact 64 F,
      base.toNat < heapEnd →
      s1.code = originalRuntimeCode →
      s1.memaddrs = ordinaryDomain →
      s1.locals = s.locals →
      ByteRegionEffect s1 (evaluateHOLFiniteState s1 cont).2 [(base.toNat, len)]) :
    ByteRegionEffect s
      (evaluateHOLFiniteState s (.seq (.call (some (none, none)) (ofString "st_be32") [pExp, vExp]) cont)).2
      [(base.toNat, len)] := by
  let pArg := base + BitVec.ofNat 64 off
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
        (sourceFnBody Guest.Software.guestFn_st_be32) pArg vW (by decide) (by rw [hcode]; exact lookup_st_be32)
      rw [hl] at hc; dsimp only at hc
      split at hc
      · injection hc with hr hsc; subst hr hsc; exact (ByteRegionEffect.refl s _).with_locals_clock _ _
      · let entry := callEntryStateHOLFinite s
          ((HolFiniteMapExact.empty.update (ofString "p", .val (.word pArg))).update (ofString "v", .val (.word vW)))
        have hp_in : entry.locals.lookup (ofString "p") = some (.val (.word pArg)) := by
          simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "v" ≠ ofString "p" by decide]
        obtain ⟨heff_b, hlt_or_eq, hlt_b⟩ := st_be32_body_eff entry pArg hma hp_in
        rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_st_be32) with ⟨rb, sb⟩
        have hb_entry : evaluateHOLFiniteState
            (callEntryStateHOLFinite s
              ((HolFiniteMapExact.empty.update (ofString "p", .val (.word pArg))).update (ofString "v", .val (.word vW))))
            (sourceFnBody Guest.Software.guestFn_st_be32) = (rb, sb) := hb
        rw [hb_entry] at hc
        rw [hb] at heff_b hlt_or_eq
        dsimp only at heff_b hlt_or_eq
        have heff_entry : ByteRegionEffect s entry [(base.toNat, len)] :=
          (ByteRegionEffect.refl s _).with_locals_clock _ _
        have heff_sb : ByteRegionEffect s sb [(base.toNat, len)] := by
          rcases hlt_or_eq with hmem_eq | hpArg_lt
          · exact ByteRegionEffect.of_mem_globals_eq [(base.toNat, len)]
              heff_b.globals hmem_eq heff_b.code heff_b.memaddrs heff_b.shMemaddrs heff_b.baseAddr heff_b.be
          · have hbase_lt : base.toNat < heapEnd := by
              by_cases hz_off : off = 0
              · subst hz_off; have h0 : pArg = base := by simp [pArg]
                rwa [h0] at hpArg_lt
              · exact hprev (by omega)
            have hpArg_nat : pArg.toNat = base.toNat + off := bv_add_off_nat base off hbase_lt (by omega)
            exact heff_entry.trans (heff_b.mono fun i hi => by
              simp only [List.mem_singleton] at hi; subst hi
              exact ⟨(base.toNat, len), List.mem_singleton.2 rfl, by rw [hpArg_nat]; omega, by rw [hpArg_nat]; omega⟩)
        cases rb with
        | none => injection hc with hr hsc; subst hr hsc; exact heff_sb
        | some r =>
          cases r with
          | returned rv =>
            dsimp only at hc
            split at hc
            · injection hc with hr hsc; subst hr hsc
              dsimp only
              have hpArg_lt := hlt_b rv (by rw [hb])
              have hbase_lt : base.toNat < heapEnd := by
                by_cases hz_off : off = 0
                · subst hz_off; have h0 : pArg = base := by simp [pArg]
                  rwa [h0] at hpArg_lt
                · exact hprev (by omega)
              let s1 : PanSemStateFiniteExact 64 F := { sb with locals := s.locals }
              have heff_s1 : ByteRegionEffect s s1 [(base.toNat, len)] := heff_sb.with_locals_clock _ _
              exact heff_s1.trans (hcont s1 hbase_lt (heff_s1.code.trans hcode) (heff_s1.memaddrs.trans hma) rfl)
            · injection hc with hr hsc; subst hr hsc; exact heff_sb
          | timeOut | error | exception _ _ | finalFfi _ =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb.with_locals_clock _ _
          | «break» | «continue» =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb
    · have hln := lookup_two_words_reject_nonword s.code.lookup (ofString "st_be32") (ofString "p") (ofString "v")
        _ pArg vv (by rw [hcode]; exact lookup_st_be32) (fun w hw => hvw ⟨w, hw⟩)
      rw [hln] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s _

private theorem st_be64_body_eff {F : Type} (s : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p))) :
    ByteRegionEffect s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_be64)).2 [(p.toNat, 8)] ∧
    ((evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_be64)).2.memory = s.memory ∨ p.toNat < heapEnd) ∧
    (∀ rv, (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_be64)).1 = some (.returned rv) →
      p.toNat < heapEnd) := by
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
  have hcond := eval_align8_eq0 s "p" p hp
  by_cases hal : (p &&& 7#64) = 0#64
  · let yesProg : ProgHOL 64 :=
      .decCall (ofString "w") .one (ofString "bswap64") [.var .local (ofString "v")]
        (.seq (.store (.var .local (ofString "p")) (.var .local (ofString "w")))
          (.return (.const 0#64)))
    have hyes_info :
        (evaluateHOLFiniteState s yesProg).1 ≠ none ∧
        (((evaluateHOLFiniteState s yesProg).2.memory = s.memory ∧
          ∀ rv, (evaluateHOLFiniteState s yesProg).1 ≠ some (.returned rv)) ∨ p.toNat < heapEnd) := by
      dsimp only [yesProg]
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
      rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.var .local (ofString "v")] with _ | vals
      · exact ⟨by simp, Or.inl ⟨rfl, by simp⟩⟩
      · dsimp only
        rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "bswap64") vals with _ | ⟨b', cal', rs'⟩
        · exact ⟨by simp, Or.inl ⟨rfl, by simp⟩⟩
        · dsimp only
          have hinst := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "bswap64")
            _ _ b' _ rs' vals cal' (by rw [hcode]; exact lookup_bswap64) hl
          subst hinst
          have hrs_eq : rs' = .one := by
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
            split at hl
            · cases hl
            · rename_i eb el es hraw
              have hinj := Option.some.inj hl
              rcases Prod.mk.inj hinj with ⟨_, hr2⟩; rcases Prod.mk.inj hr2 with ⟨_, rfl⟩
              unfold lookupCodeHOLExact at hraw; rw [hcode, lookup_bswap64] at hraw; dsimp only at hraw
              split at hraw <;> [ (injection hraw with h'; exact (Prod.mk.inj (Prod.mk.inj h').2).2.symm); cases hraw ]
          subst hrs_eq
          split
          · exact ⟨by simp, Or.inl ⟨rfl, by simp⟩⟩
          · have hro0 := bswap64_body_ro (callEntryStateHOLFinite s cal') []
            have hmem0 := bswap64_body_mem_eq (callEntryStateHOLFinite s cal')
            rcases hb_run : evaluateHOLFiniteState (callEntryStateHOLFinite s cal')
                (sourceFnBody Guest.Software.guestFn_bswap64) with ⟨rb, sb⟩
            rw [hb_run] at hro0 hmem0
            dsimp only at hro0 hmem0 ⊢
            have hsb_ma : sb.memaddrs = ordinaryDomain := hro0.memaddrs.trans hma
            cases rb with
            | none => exact ⟨by simp, Or.inl ⟨hmem0, by simp⟩⟩
            | some r =>
              cases r with
              | returned v =>
                dsimp only
                split
                · rename_i hsh_v
                  have hvw : ∃ wv : BitVec 64, v = .val (.word wv) := by
                    rcases v with ⟨⟨wv⟩⟩ | _ | _
                    · exact ⟨wv, rfl⟩
                    · simp [shapeOfHOLExact, shapeEqHOL] at hsh_v
                    · simp [shapeOfHOLExact, shapeEqHOL] at hsh_v
                  obtain ⟨wv, rfl⟩ := hvw
                  let mid := setVarHOLFinite (ofString "w") (.val (.word wv)) { sb with locals := s.locals }
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
                  rw [evaluateHOLFiniteState_store, hp_mid, hw_mid] at hst_pair
                  dsimp only at hst_pair
                  split at hst_pair
                  · rename_i m' hst_p
                    injection hst_pair with hrst hsst; subst hrst hsst
                    unfold flattenHOL panMemStoresHOL panMemStoreHOL at hst_p
                    by_cases hd : sb.memaddrs p
                    · dsimp only
                      rw [(return_const0_step _).1]
                      exact ⟨by simp, Or.inr (by have := word_dom_lt_heapEnd hsb_ma p hd; omega)⟩
                    · have hdm : ¬ mid.memaddrs p := hd
                      simp [hdm] at hst_p
                  · injection hst_pair with hrst hsst; subst hrst hsst
                    exact ⟨by simp, Or.inl ⟨hmem0, by simp⟩⟩
                · exact ⟨by simp, Or.inl ⟨hmem0, by simp⟩⟩
              | timeOut | error | exception _ _ | finalFfi _ | «break» | «continue» =>
                exact ⟨by simp, Or.inl ⟨hmem0, by simp⟩⟩
    have hnn := hyes_info.1
    have hml := hyes_info.2
    have hgoal_ite : evaluateHOLFiniteState s
        (.seq (.ite (.cmp .equal (.op .and [.var .local (ofString "p"), .const 7#64]) (.const 0#64)) yesProg .skip)
          (.seq (.call (some (none, none)) (ofString "st_be32")
              [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32#64)])
            (.seq (.call (some (none, none)) (ofString "st_be32")
                [.op .add [.var .local (ofString "p"), .const 4#64], .var .local (ofString "v")])
              (.return (.const 0#64))))) = evaluateHOLFiniteState s yesProg := by
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcond]
      simp only [hal, ↓reduceIte]
      have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
      rw [if_neg h10]
      rcases hy : evaluateHOLFiniteState s yesProg with ⟨ry, sy⟩
      rw [hy] at hnn
      cases ry with
      | none => exact absurd rfl hnn
      | some _ => rfl
    rw [hgoal_ite]
    have heff_yes : ByteRegionEffect s (evaluateHOLFiniteState s yesProg).2 [(p.toNat, 8)] :=
      decCall_bswap64_eff (s := s) (argExp := .var .local (ofString "v"))
        (Rl := [(p.toNat, 8)]) hcode fun mid _ hm_mid _ hp_mid _ ⟨wv, hw_mid⟩ => by
          have hp_m : mid.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hp_mid]; exact hp
          exact seq_store_word_eff (s := mid) (base := p) (w := wv) (off := 0) (len := 8)
            (hm_mid.trans hma) (by omega) (by omega) (fun h => by omega)
            (eval_var_local_zero mid "p" p hp_m)
            (eval_var_local mid "w" wv hw_mid) fun s1 _ _ _ _ => return_eff s1 _ _
    refine ⟨heff_yes, ?_, ?_⟩
    · rcases hml with ⟨hm_eq, _⟩ | hp_lt
      · exact Or.inl hm_eq
      · exact Or.inr hp_lt
    · intro rv hret
      rcases hml with ⟨_, hne⟩ | hp_lt
      · exact absurd hret (hne rv)
      · exact hp_lt
  · -- Unaligned path of `st_be64`:
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcond]
    simp only [hal, ↓reduceIte, evaluateHOLFiniteState_skip]
    have hp_ev0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.var .local (ofString "p")) = some (.val (.word p)) := hp
    have hfirst_call :
        ((evaluateHOLFiniteState s
          (.seq (.call (some (none, none)) (ofString "st_be32")
              [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32#64)])
            (.seq (.call (some (none, none)) (ofString "st_be32")
                [.op .add [.var .local (ofString "p"), .const 4#64], .var .local (ofString "v")])
              (.return (.const 0#64))))).2.memory = s.memory ∧
         ∀ rv, (evaluateHOLFiniteState s
          (.seq (.call (some (none, none)) (ofString "st_be32")
              [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32#64)])
            (.seq (.call (some (none, none)) (ofString "st_be32")
                [.op .add [.var .local (ofString "p"), .const 4#64], .var .local (ofString "v")])
              (.return (.const 0#64))))).1 ≠ some (.returned rv)) ∨ p.toNat < heapEnd := by
      rw [evaluateHOLFiniteState_seq_line780]
      rcases hc1 : evaluateHOLFiniteState s
          (.call (some (none, none)) (ofString "st_be32")
            [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32#64)]) with ⟨rc1, sc1⟩
      rw [evaluateHOLFiniteState_call] at hc1
      rcases hv_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.shift .lsr (.var .local (ofString "v")) (.const 32#64)) with _ | vv
      · have hnone : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
            [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32#64)] = none := by
          simp [evalListHOLFinite, evalListHOLExact, hp_ev0, hv_ev]
        rw [hnone] at hc1; injection hc1 with hr hsc1; subst hr hsc1; exact Or.inl ⟨rfl, by simp⟩
      · have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
            [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32#64)] =
            some [.val (.word p), vv] := by
          simp [evalListHOLFinite, evalListHOLExact, hp_ev0, hv_ev]
        rw [hargs] at hc1; dsimp only at hc1
        by_cases hvw : ∃ vW : BitVec 64, vv = .val (.word vW)
        · obtain ⟨vW, rfl⟩ := hvw
          have hl := pan_two_word_lookup s.code.lookup (ofString "st_be32") (ofString "p") (ofString "v")
            (sourceFnBody Guest.Software.guestFn_st_be32) p vW (by decide) (by rw [hcode]; exact lookup_st_be32)
          rw [hl] at hc1; dsimp only at hc1
          split at hc1
          · injection hc1 with hr hsc1; subst hr hsc1; exact Or.inl ⟨rfl, by simp⟩
          · let entry := callEntryStateHOLFinite s
              ((HolFiniteMapExact.empty.update (ofString "p", .val (.word p))).update (ofString "v", .val (.word vW)))
            have hp_in : entry.locals.lookup (ofString "p") = some (.val (.word p)) := by
              simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "v" ≠ ofString "p" by decide]
            obtain ⟨_, hlt_or_eq, hlt_b⟩ := st_be32_body_eff entry p hma hp_in
            rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_st_be32) with ⟨rb, sb⟩
            have hb_entry : evaluateHOLFiniteState
                (callEntryStateHOLFinite s
                  ((HolFiniteMapExact.empty.update (ofString "p", .val (.word p))).update (ofString "v", .val (.word vW))))
                (sourceFnBody Guest.Software.guestFn_st_be32) = (rb, sb) := hb
            rw [hb_entry] at hc1
            rw [hb] at hlt_or_eq
            dsimp only at hlt_or_eq
            rcases hlt_or_eq with hmem_eq | hp_lt
            · cases rb with
              | none => injection hc1 with hr hsc1; subst hr hsc1; exact Or.inl ⟨hmem_eq, by simp⟩
              | some r =>
                cases r with
                | returned rv' => exact Or.inr (hlt_b rv' (by rw [hb]))
                | timeOut | error | exception _ _ | finalFfi _ | «break» | «continue» =>
                  injection hc1 with hr hsc1; subst hr hsc1; exact Or.inl ⟨hmem_eq, by simp⟩
            · exact Or.inr hp_lt
        · have hln := lookup_two_words_reject_nonword s.code.lookup (ofString "st_be32") (ofString "p") (ofString "v")
            _ p vv (by rw [hcode]; exact lookup_st_be32) (fun w hw => hvw ⟨w, hw⟩)
          rw [hln] at hc1; injection hc1 with hr hsc1; subst hr hsc1; exact Or.inl ⟨rfl, by simp⟩
    refine ⟨?_, ?_, ?_⟩
    · refine seq_call_st_be32_eff (base := p) (off := 0) (len := 8) hcode hma (by omega) (by omega)
        (fun h => by omega)
        (eval_var_local_zero s "p" p hp)
        fun s1 hp_lt hc1 hm1 hl1 => ?_
      have hp1 : s1.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hl1]; exact hp
      refine seq_call_st_be32_eff (s := s1) (base := p) (off := 4) (len := 8) hc1 hm1 (by omega) (by omega)
        (fun _ => hp_lt) (eval_add_local_const s1 "p" p 4 hp1)
        fun s2 _ _ _ _ => return_eff s2 _ _
    · rcases hfirst_call with ⟨hm_eq, _⟩ | hp_lt
      · exact Or.inl hm_eq
      · exact Or.inr hp_lt
    · intro rv hret
      rcases hfirst_call with ⟨_, hne⟩ | hp_lt
      · exact absurd hret (hne rv)
      · exact hp_lt

private theorem seq_call_st_be64_eff {F : Type} {s : PanSemStateFiniteExact 64 F}
    {pExp vExp : ExpHOL 64} {base : BitVec 64} {off : Nat} {cont : ProgHOL 64}
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hoff : off + 8 ≤ 32)
    (hprev : off > 0 → base.toNat < heapEnd)
    (hp_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pExp =
      some (.val (.word (base + BitVec.ofNat 64 off))))
    (hcont : ∀ s1 : PanSemStateFiniteExact 64 F,
      base.toNat < heapEnd →
      s1.code = originalRuntimeCode →
      s1.memaddrs = ordinaryDomain →
      s1.locals = s.locals →
      ByteRegionEffect s1 (evaluateHOLFiniteState s1 cont).2 [(base.toNat, 32)]) :
    ByteRegionEffect s
      (evaluateHOLFiniteState s (.seq (.call (some (none, none)) (ofString "st_be64") [pExp, vExp]) cont)).2
      [(base.toNat, 32)] := by
  let pArg := base + BitVec.ofNat 64 off
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
        (sourceFnBody Guest.Software.guestFn_st_be64) pArg vW (by decide) (by rw [hcode]; exact lookup_st_be64)
      rw [hl] at hc; dsimp only at hc
      split at hc
      · injection hc with hr hsc; subst hr hsc; exact (ByteRegionEffect.refl s _).with_locals_clock _ _
      · let entry := callEntryStateHOLFinite s
          ((HolFiniteMapExact.empty.update (ofString "p", .val (.word pArg))).update (ofString "v", .val (.word vW)))
        have hp_in : entry.locals.lookup (ofString "p") = some (.val (.word pArg)) := by
          simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "v" ≠ ofString "p" by decide]
        obtain ⟨heff_b, hlt_or_eq, hlt_b⟩ := st_be64_body_eff entry pArg hcode hma hp_in
        rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_st_be64) with ⟨rb, sb⟩
        have hb_entry : evaluateHOLFiniteState
            (callEntryStateHOLFinite s
              ((HolFiniteMapExact.empty.update (ofString "p", .val (.word pArg))).update (ofString "v", .val (.word vW))))
            (sourceFnBody Guest.Software.guestFn_st_be64) = (rb, sb) := hb
        rw [hb_entry] at hc
        rw [hb] at heff_b hlt_or_eq
        dsimp only at heff_b hlt_or_eq
        have heff_entry : ByteRegionEffect s entry [(base.toNat, 32)] :=
          (ByteRegionEffect.refl s _).with_locals_clock _ _
        have heff_sb : ByteRegionEffect s sb [(base.toNat, 32)] := by
          rcases hlt_or_eq with hmem_eq | hpArg_lt
          · exact ByteRegionEffect.of_mem_globals_eq [(base.toNat, 32)]
              heff_b.globals hmem_eq heff_b.code heff_b.memaddrs heff_b.shMemaddrs heff_b.baseAddr heff_b.be
          · have hbase_lt : base.toNat < heapEnd := by
              by_cases hz_off : off = 0
              · subst hz_off; have h0 : pArg = base := by simp [pArg]
                rwa [h0] at hpArg_lt
              · exact hprev (by omega)
            have hpArg_nat : pArg.toNat = base.toNat + off := bv_add_off_nat base off hbase_lt (by omega)
            exact heff_entry.trans (heff_b.mono fun i hi => by
              simp only [List.mem_singleton] at hi; subst hi
              exact ⟨(base.toNat, 32), List.mem_singleton.2 rfl, by rw [hpArg_nat]; omega, by rw [hpArg_nat]; omega⟩)
        cases rb with
        | none => injection hc with hr hsc; subst hr hsc; exact heff_sb
        | some r =>
          cases r with
          | returned rv =>
            dsimp only at hc
            split at hc
            · injection hc with hr hsc; subst hr hsc
              dsimp only
              have hpArg_lt := hlt_b rv (by rw [hb])
              have hbase_lt : base.toNat < heapEnd := by
                by_cases hz_off : off = 0
                · subst hz_off; have h0 : pArg = base := by simp [pArg]
                  rwa [h0] at hpArg_lt
                · exact hprev (by omega)
              let s1 : PanSemStateFiniteExact 64 F := { sb with locals := s.locals }
              have heff_s1 : ByteRegionEffect s s1 [(base.toNat, 32)] := heff_sb.with_locals_clock _ _
              exact heff_s1.trans (hcont s1 hbase_lt (heff_s1.code.trans hcode) (heff_s1.memaddrs.trans hma) rfl)
            · injection hc with hr hsc; subst hr hsc; exact heff_sb
          | timeOut | error | exception _ _ | finalFfi _ =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb.with_locals_clock _ _
          | «break» | «continue» =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb
    · have hln := lookup_two_words_reject_nonword s.code.lookup (ofString "st_be64") (ofString "p") (ofString "v")
        _ pArg vv (by rw [hcode]; exact lookup_st_be64) (fun w hw => hvw ⟨w, hw⟩)
      rw [hln] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s _

/-! ### 4. Main theorem: `ek_u256_to_be32` -/

/-- `u256_to_be32` (AST line 2265): EVM step: `EvmInv`, `ev`/`cur_cont` and the frame chain kept. -/
theorem «ek_u256_to_be32» :
    EvmKeeps (EvmAvoids (fun s => [(locN s "out", 32)]))
    [] (ofString "u256_to_be32") := by
  refine ⟨_, _, _, lookup_u256_to_be32, ?_⟩
  intro F s hcode hAv _hlookup _hnt hres
  have hma : s.memaddrs = ordinaryDomain := hAv.1.1.memaddrs
  suffices heff : ByteRegionEffect s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_to_be32)).2
      [(locN s "out", 32)] by
    exact ByteRegionEffect.to_evmStep_avoids hAv heff
  have hb : sourceFnBody Guest.Software.guestFn_u256_to_be32 =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_u256_to_be32).body := rfl
  rw [hb] at hres ⊢
  dsimp only [extractFn, Guest.Software.guestFn_u256_to_be32,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    List.map, Option.map] at hres ⊢
  rcases hout_lu : s.locals.lookup (ofString "out") with _ | vout
  · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres
    simp [evalHOLExact, evalListHOLExact, hout_lu] at hres
    exact absurd hres not_resumes_error
  · rcases vout with ⟨⟨out⟩⟩ | _ | _
    · have hloc_out : locN s "out" = out.toNat := by simp [locN, hout_lu]
      rw [hloc_out]
      have hcond := eval_align8_eq0 s "out" out hout_lu
      have hout_ev0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.var .local (ofString "out")) = some (.val (.word out)) := hout_lu
      by_cases hal : (out &&& 7#64) = 0#64
      · -- Aligned fast path:
        have hdc_ne_none : ∀ (st : PanSemStateFiniteExact 64 F) (nm : MlS) (sh : ShapeHOL)
            (fn : MlS) (args : List (ExpHOL 64)) (c : ProgHOL 64),
            (∀ (m : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState m c).1 ≠ none) →
            (evaluateHOLFiniteState st (.decCall nm sh fn args c)).1 ≠ none := by
          intro st nm sh fn args c hc_nn
          rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
          rcases evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a)) args with _ | _
          · simp
          · dsimp only
            rcases lookupCodeHOLFinite st.code.lookup fn _ with _ | ⟨b', cal', rs'⟩
            · simp
            · dsimp only; split
              · simp
              · rcases evaluateHOLFiniteState (callEntryStateHOLFinite st cal') b' with ⟨rb, sb⟩
                cases rb with
                | none => simp
                | some r =>
                  cases r with
                  | returned _ => dsimp only; split <;> [ exact hc_nn _; simp ]
                  | _ => simp
        have hseq_ne_none : ∀ {p1 p2 : ProgHOL 64},
            (∀ (m : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState m p2).1 ≠ none) →
            ∀ (m : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState m (.seq p1 p2)).1 ≠ none := by
          intro p1 p2 hp2 m
          rw [evaluateHOLFiniteState_seq_line780]
          rcases evaluateHOLFiniteState m p1 with ⟨r1, m1⟩
          cases r1 with
          | none => exact hp2 m1
          | some _ => simp
        have hret_ne_none : ∀ (m : PanSemStateFiniteExact 64 F),
            (evaluateHOLFiniteState m (.return (.const 0#64))).1 ≠ none := by
          intro m; rw [(return_const0_step m).1]; simp
        let yesProg256 : ProgHOL 64 :=
          .decCall (ofString "w") .one (ofString "bswap64") [.rfield 3 (.var .local (ofString "a"))]
            (.seq (.store (.var .local (ofString "out")) (.var .local (ofString "w")))
              (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [.rfield 2 (.var .local (ofString "a"))])
                (.seq (.store (.op .add [.var .local (ofString "out"), .const 8#64]) (.var .local (ofString "w")))
                  (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [.rfield 1 (.var .local (ofString "a"))])
                    (.seq (.store (.op .add [.var .local (ofString "out"), .const 16#64]) (.var .local (ofString "w")))
                      (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [.rfield 0 (.var .local (ofString "a"))])
                        (.seq (.store (.op .add [.var .local (ofString "out"), .const 24#64]) (.var .local (ofString "w")))
                          (.return (.const 0#64)))))))))
        have hyes256_nn : (evaluateHOLFiniteState s yesProg256).1 ≠ none :=
          hdc_ne_none s _ _ _ _ _
            (hseq_ne_none (hseq_ne_none (hseq_ne_none (hseq_ne_none
              (hseq_ne_none (hseq_ne_none (hseq_ne_none hret_ne_none)))))))
        have hgoal_yes256 : evaluateHOLFiniteState s
            (.seq (.ite (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7#64]) (.const 0#64)) yesProg256 .skip)
              (.seq (.call (some (none, none)) (ofString "st_be64") [.var .local (ofString "out"), .rfield 3 (.var .local (ofString "a"))])
                (.seq (.call (some (none, none)) (ofString "st_be64") [.op .add [.var .local (ofString "out"), .const 8#64], .rfield 2 (.var .local (ofString "a"))])
                  (.seq (.call (some (none, none)) (ofString "st_be64") [.op .add [.var .local (ofString "out"), .const 16#64], .rfield 1 (.var .local (ofString "a"))])
                    (.seq (.call (some (none, none)) (ofString "st_be64") [.op .add [.var .local (ofString "out"), .const 24#64], .rfield 0 (.var .local (ofString "a"))])
                      (.return (.const 0#64))))))) = evaluateHOLFiniteState s yesProg256 := by
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcond]
          simp only [hal, ↓reduceIte]
          have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
          rw [if_neg h10]
          rcases hy : evaluateHOLFiniteState s yesProg256 with ⟨ry, sy⟩
          rw [hy] at hyes256_nn
          cases ry with
          | none => exact absurd rfl hyes256_nn
          | some _ => rfl
        rw [hgoal_yes256]
        exact decCall_bswap64_eff (s := s) (Rl := [(out.toNat, 32)]) hcode
          fun mid0 hc_m0 hm_m0 hout_m0 _ _ ⟨wv0, hw_m0⟩ => by
            have ho0 : mid0.locals.lookup (ofString "out") = some (.val (.word out)) := by
              rw [hout_m0]; exact hout_lu
            refine seq_store_word_eff (s := mid0) (base := out) (w := wv0) (off := 0) (len := 32)
              (hm_m0.trans hma) (by omega) (by omega) (fun h => by omega)
              (eval_var_local_zero mid0 "out" out ho0)
              (eval_var_local mid0 "w" wv0 hw_m0) fun s1 hout_lt hc_s1 hm_s1 hl_s1 => ?_
            refine seq_call_bswap64_eff (s := s1) (Rl := [(out.toNat, 32)])
              (hc_s1.trans hc_m0) fun mid1 hc_m1 hm_m1 hout_m1 _ ⟨wv1, hw_m1⟩ => ?_
            have ho1 : mid1.locals.lookup (ofString "out") = some (.val (.word out)) := by
              rw [hout_m1, hl_s1]; exact ho0
            refine seq_store_word_eff (s := mid1) (base := out) (w := wv1) (off := 8) (len := 32)
              (hm_m1.trans (hm_s1.trans (hm_m0.trans hma))) (by omega) (by omega) (fun _ => hout_lt)
              (eval_add_local_const mid1 "out" out 8 ho1)
              (eval_var_local mid1 "w" wv1 hw_m1) fun s2 _ hc_s2 hm_s2 hl_s2 => ?_
            refine seq_call_bswap64_eff (s := s2) (Rl := [(out.toNat, 32)])
              (hc_s2.trans hc_m1) fun mid2 hc_m2 hm_m2 hout_m2 _ ⟨wv2, hw_m2⟩ => ?_
            have ho2 : mid2.locals.lookup (ofString "out") = some (.val (.word out)) := by
              rw [hout_m2, hl_s2]; exact ho1
            refine seq_store_word_eff (s := mid2) (base := out) (w := wv2) (off := 16) (len := 32)
              (hm_m2.trans (hm_s2.trans (hm_m1.trans (hm_s1.trans (hm_m0.trans hma))))) (by omega) (by omega)
              (fun _ => hout_lt)
              (eval_add_local_const mid2 "out" out 16 ho2)
              (eval_var_local mid2 "w" wv2 hw_m2) fun s3 _ hc_s3 hm_s3 hl_s3 => ?_
            refine seq_call_bswap64_eff (s := s3) (Rl := [(out.toNat, 32)])
              (hc_s3.trans hc_m2) fun mid3 _ hm_m3 hout_m3 _ ⟨wv3, hw_m3⟩ => ?_
            have ho3 : mid3.locals.lookup (ofString "out") = some (.val (.word out)) := by
              rw [hout_m3, hl_s3]; exact ho2
            refine seq_store_word_eff (s := mid3) (base := out) (w := wv3) (off := 24) (len := 32)
              (hm_m3.trans (hm_s3.trans (hm_m2.trans (hm_s2.trans (hm_m1.trans (hm_s1.trans (hm_m0.trans hma)))))))
              (by omega) (by omega) (fun _ => hout_lt)
              (eval_add_local_const mid3 "out" out 24 ho3)
              (eval_var_local mid3 "w" wv3 hw_m3) fun s4 _ _ _ _ => return_eff s4 _ _
      · -- Unaligned path:
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcond]
        simp only [hal, ↓reduceIte, evaluateHOLFiniteState_skip]
        refine seq_call_st_be64_eff (base := out) (off := 0) hcode hma (by omega) (fun h => by omega)
          (eval_var_local_zero s "out" out hout_lu)
          fun s1 hout_lt hc1 hm1 hl1 => ?_
        have hout1 : s1.locals.lookup (ofString "out") = some (.val (.word out)) := by rw [hl1]; exact hout_lu
        refine seq_call_st_be64_eff (s := s1) (base := out) (off := 8) hc1 hm1 (by omega) (fun _ => hout_lt)
          (eval_add_local_const s1 "out" out 8 hout1)
          fun s2 _ hc2 hm2 hl2 => ?_
        have hout2 : s2.locals.lookup (ofString "out") = some (.val (.word out)) := by rw [hl2]; exact hout1
        refine seq_call_st_be64_eff (s := s2) (base := out) (off := 16) hc2 hm2 (by omega) (fun _ => hout_lt)
          (eval_add_local_const s2 "out" out 16 hout2)
          fun s3 _ hc3 hm3 hl3 => ?_
        have hout3 : s3.locals.lookup (ofString "out") = some (.val (.word out)) := by rw [hl3]; exact hout2
        refine seq_call_st_be64_eff (s := s3) (base := out) (off := 24) hc3 hm3 (by omega) (fun _ => hout_lt)
          (eval_add_local_const s3 "out" out 24 hout3)
          fun s4 _ _ _ _ => return_eff s4 _ _
    · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres
      simp [evalHOLExact, evalListHOLExact, hout_lu, valueIsWord] at hres
      exact absurd hres not_resumes_error
    · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres
      simp [evalHOLExact, evalListHOLExact, hout_lu, valueIsWord] at hres
      exact absurd hres not_resumes_error

end InitECandidate.Solver.Wave8Contracts.M23
