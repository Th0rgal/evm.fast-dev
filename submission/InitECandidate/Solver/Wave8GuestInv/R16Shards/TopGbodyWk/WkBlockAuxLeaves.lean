import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkAcctWsBase
import InitECandidate.Solver.Wave8GuestInv.R16Shards.ProcessWithdrawals
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.Common
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalRemove
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_htab_has
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_htab_item
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.RlpHelpers

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

theorem ro_bal_sort_gt : ReadOnlyFn (ofString "bal_sort_gt") :=
  InitECandidate.Solver.Wave8Contracts.M15.readOnlyFn_of_guestAst 429 (by rw [guestAst_len]; decide) Guest.Software.guestFn_bal_sort_gt rfl
    (fun _ => false) (fun _ h => by cases h) rfl

theorem wkSc_bal_sort_gt :
    WorldKeepsSc WorldOK (bufRegions []) [] stdKeep NoExtra (ofString "bal_sort_gt") :=
  worldKeepsSc_of_readOnly ro_bal_sort_gt

theorem wkSc_htab_has :
    WorldKeepsSc WorldOK (bufRegions []) [] stdKeep NoExtra (ofString "htab_has") :=
  worldKeepsSc_of_readOnly InitECandidate.Solver.Wave8Contracts.M15.«ro_htab_has»

theorem wkSc_htab_item :
    WorldKeepsSc WorldOK (bufRegions []) [] stdKeep NoExtra (ofString "htab_item") :=
  worldKeepsSc_of_readOnly InitECandidate.Solver.Wave8Contracts.M15.«ro_htab_item»

private def u256FromBeGood (f : MlS) : Bool :=
  f == ofString "bswap64"

theorem ro_u256_from_be : ReadOnlyFn (ofString "u256_from_be") := by
  change InitECandidate.Solver.Wave8Contracts.M18.ReadOnlyFn (ofString "u256_from_be")
  refine InitECandidate.Solver.Wave8Contracts.M18.readOnlyFn_of_guestAst 86
    (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_from_be rfl u256FromBeGood ?_ (by decide)
  intro function hfn values body callee rs hfound
  simp only [u256FromBeGood, beq_iff_eq] at hfn
  subst hfn
  exact InitECandidate.Solver.Wave8Contracts.M18.installed_body_readOnly 23
    (by rw [guestAst_len]; decide) Guest.Software.guestFn_bswap64 rfl u256FromBeGood (by decide) hfound

theorem wkSc_u256_from_be :
    WorldKeepsSc WorldOK (bufRegions []) [] stdKeep NoExtra (ofString "u256_from_be") :=
  worldKeepsSc_of_readOnly ro_u256_from_be

theorem heapByteEff_to_worldStepSc {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {gw : List String}
    (hgw_ok : ∀ g ∈ gw, g = "heap_ptr" ∨ g = "scratch_ptr")
    (hW : WorldOK s)
    (heff : WkBlockTxEnc.HeapByteEff s post (bufRegions [] s) gw) :
    WorldStepSc (bufRegions []) gw stdKeep NoExtra s r post := by
  refine ⟨WkBlockTxEnc.HeapByteEff.to_worldStep (R := bufRegions []) (Q := NoExtra)
    [] (fun _ h => by simp at h) hgw_ok hW ?_ (fun _ _ _ _ _ => trivial), heff.sp_le⟩
  simpa [bufRegions] using heff

theorem bal_list_payload_worldStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {l esz : Nat} (hW : WorldOK s) (hl_nz : l ≠ 0)
    (hesz : esz = 16 ∨ esz = 24 ∨ esz = 40)
    (hslice_all : ∀ S Nd, WorldTypedWith s S Nd →
      LstOK s l ∧ WkBal.BalListSlice s l esz)
    (heff : M11.ByteRegionEffect s post [(memW s l, esz * memW s (l + 16))]) :
    WorldStep (fun _ => []) [] stdKeep NoExtra s r post := by
  obtain ⟨S, hWT⟩ := hW.2
  obtain ⟨Nd, hWT⟩ := (WkBal.worldTyped_iff_with s S).1 hWT
  obtain ⟨hlst, hslice⟩ := hslice_all S Nd hWT
  obtain ⟨hl_fix, _, hdj, _⟩ :=
    WkBal.bal_list_slice_props hWT.2.2.1 hl_nz hesz hlst hslice
  rcases hWT.2.2.1.1 _ hl_fix with hzero | ⟨hal, _⟩
  · simp at hzero
  have hesz_pos : 0 < esz := by rcases hesz with rfl | rfl | rfl <;> decide
  have hpos_arr : esz * memW s (l + 16) ≠ 0 :=
    ne_of_gt (Nat.mul_pos hesz_pos (by have := hlst.1; omega))
  have hbound := M13.allocated_le_2pow64 hW.1.2 hal
  have hlt : l + 8 < 2 ^ 64 := by dsimp only at hbound; omega
  have hlen : memW post (l + 8) = memW s (l + 8) := by
    unfold memW
    rw [heff.cell_frame (BitVec.ofNat 64 (l + 8)) (by
      intro i hi hhit
      have hi' := List.mem_singleton.mp hi
      subst i
      obtain ⟨ha, hb⟩ := hhit
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ha hb
      rcases hdj with h | h | h | h
      · simp at h
      · exact absurd h hpos_arr
      · dsimp only at *; omega
      · dsimp only at *; omega)]
  refine WkBal.bal_list_store_len_and_arr_worldStep (r := r) hW hl_nz hesz hslice_all ?_ hlst.2 hlen
  apply heff.mono
  intro i hi
  have hi' := List.mem_singleton.mp hi
  subst i
  exact ⟨_, by simp, le_rfl, le_rfl⟩

theorem bal_list_payload_worldStepSc {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {l esz : Nat} (hW : WorldOK s) (hl_nz : l ≠ 0)
    (hesz : esz = 16 ∨ esz = 24 ∨ esz = 40)
    (hslice_all : ∀ S Nd, WorldTypedWith s S Nd →
      LstOK s l ∧ WkBal.BalListSlice s l esz)
    (heff : M11.ByteRegionEffect s post [(memW s l, esz * memW s (l + 16))]) :
    WorldStepSc (fun _ => []) [] stdKeep NoExtra s r post := by
  refine ⟨bal_list_payload_worldStep hW hl_nz hesz hslice_all heff, ?_⟩
  have hsp : globN post "scratch_ptr" = globN s "scratch_ptr" := by
    unfold globN
    rw [heff.globals]
  exact hsp.le

theorem eval_call_memcpy_bal_list {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dstExp srcExp nExp : ExpHOL 64)
    (dst0 src0 n0 : BitVec 64) (l esz : Nat)
    (hcode : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hl_nz : l ≠ 0) (hesz : esz = 16 ∨ esz = 24 ∨ esz = 40)
    (hslice_all : ∀ S Nd, WorldTypedWith s S Nd →
      LstOK s l ∧ WkBal.BalListSlice s l esz)
    (hdst : evalAt s dstExp = some (.val (.word dst0)))
    (hsrc : evalAt s srcExp = some (.val (.word src0)))
    (hn : evalAt s nExp = some (.val (.word n0)))
    (hsub : 0 < n0.toNat → memW s l ≤ dst0.toNat ∧
      dst0.toNat + n0.toNat ≤ memW s l + esz * memW s (l + 16))
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])
    (out.1 = none → WorldStepSc (fun _ => []) [] stdKeep NoExtra s out.1 out.2 ∧
      out.2.locals = s.locals) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  obtain ⟨hframe, hstop⟩ := M11.eval_call_memcpy_bre s dstExp srcExp nExp dst0 src0 n0
    [(memW s l, esz * memW s (l + 16))] hcode hW.1.1.memaddrs hdst hsrc hn
    (fun hpos => ⟨(memW s l, esz * memW s (l + 16)), by simp,
      (hsub hpos).1, (hsub hpos).2⟩) hnt
  refine ⟨fun hnone => ?_, hstop⟩
  obtain ⟨heff, hlocals⟩ := hframe hnone
  exact ⟨bal_list_payload_worldStepSc hW hl_nz hesz hslice_all heff, hlocals⟩

theorem indexed_element_bounds (p n esz k : BitVec 64)
    (hbound : p.toNat + n.toNat * esz.toNat < 2 ^ 64)
    (hk : k.toNat < n.toNat) :
    (p + k * esz).toNat = p.toNat + k.toNat * esz.toNat ∧
    p.toNat ≤ (p + k * esz).toNat ∧
    (p + k * esz).toNat + esz.toNat ≤ p.toNat + n.toNat * esz.toNat := by
  have hmul : (k.toNat + 1) * esz.toNat ≤ n.toNat * esz.toNat :=
    Nat.mul_le_mul_right esz.toNat (by omega)
  have hstep : k.toNat * esz.toNat + esz.toNat ≤ n.toNat * esz.toNat := by
    simpa [Nat.add_mul] using hmul
  have hkm : k.toNat * esz.toNat < 2 ^ 64 := by omega
  have hkn : (k * esz).toNat = k.toNat * esz.toNat := by
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hkm]
  have haddr : (p + k * esz).toNat = p.toNat + k.toNat * esz.toNat := by
    rw [BitVec.toNat_add, hkn, Nat.mod_eq_of_lt (by omega)]
  exact ⟨haddr, by omega, by omega⟩

theorem eval_call_memcpy_indexed_heap {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dstExp srcExp nExp : ExpHOL 64)
    (p n esz k src : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hdst : evalAt s dstExp = some (.val (.word (p + k * esz))))
    (hsrc : evalAt s srcExp = some (.val (.word src)))
    (hn : evalAt s nExp = some (.val (.word esz)))
    (hbound : p.toNat + n.toNat * esz.toNat < 2 ^ 64)
    (hk : k.toNat < n.toNat)
    (hregion : ∃ ivl ∈ Rl, ivl.1 ≤ p.toNat ∧
      p.toNat + n.toNat * esz.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])
    (out.1 = none → WkBlockTxEnc.HeapByteEff s out.2 Rl gw ∧
      out.2.locals = s.locals ∧ out.2.globals = s.globals) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  apply WkBlockTxEnc.eval_call_memcpy_heap s dstExp srcExp nExp
    (p + k * esz) src esz Rl gw hcode hAR hdst hsrc hn ?_ hnt
  intro _
  obtain ⟨ivl, hivl, hlo, hhi⟩ := hregion
  obtain ⟨_, hstart, hend⟩ := indexed_element_bounds p n esz k hbound hk
  exact ⟨ivl, hivl, le_trans hlo hstart, le_trans hend hhi⟩

theorem eval_call_memcpy_indexed_bal_list {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dstExp srcExp nExp : ExpHOL 64)
    (p n esz k src : BitVec 64) (l : Nat)
    (hcode : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hl_nz : l ≠ 0) (hesz : esz.toNat = 16 ∨ esz.toNat = 24 ∨ esz.toNat = 40)
    (hslice_all : ∀ S Nd, WorldTypedWith s S Nd →
      LstOK s l ∧ WkBal.BalListSlice s l esz.toNat)
    (hdst : evalAt s dstExp = some (.val (.word (p + k * esz))))
    (hsrc : evalAt s srcExp = some (.val (.word src)))
    (hn : evalAt s nExp = some (.val (.word esz)))
    (hp : p.toNat = memW s l)
    (hcap : n.toNat ≤ memW s (l + 16))
    (hbound : p.toNat + n.toNat * esz.toNat < 2 ^ 64)
    (hk : k.toNat < n.toNat)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])
    (out.1 = none → WorldStepSc (fun _ => []) [] stdKeep NoExtra s out.1 out.2 ∧
      out.2.locals = s.locals) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  apply eval_call_memcpy_bal_list s dstExp srcExp nExp (p + k * esz) src esz
    l esz.toNat hcode hW hl_nz hesz hslice_all hdst hsrc hn ?_ hnt
  intro _
  obtain ⟨_, hlo, hhi⟩ := indexed_element_bounds p n esz k hbound hk
  have hmul : n.toNat * esz.toNat ≤ esz.toNat * memW s (l + 16) := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right esz.toNat hcap
  exact ⟨by omega, by omega⟩

theorem sort_alloc_size_no_wrap (n esz : BitVec 64)
    (hsize : n.toNat * esz.toNat < 2 ^ 64) :
    (n * esz).toNat = n.toNat * esz.toNat := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hsize]

theorem sort_width_double_bounds (width n esz : BitVec 64)
    (hwidth : width.toNat < n.toNat)
    (hesz : 4 ≤ esz.toNat)
    (hsize : n.toNat * esz.toNat < 2 ^ 64) :
    (width * 2#64).toNat = width.toNat * 2 ∧
      (width * 2#64).toNat < 2 ^ 63 ∧
      (0 < width.toNat → width.toNat < (width * 2#64).toNat) := by
  have hfour : n.toNat * 4 ≤ n.toNat * esz.toNat :=
    Nat.mul_le_mul_left n.toNat hesz
  have hdouble : width.toNat * 2 < 2 ^ 63 := by omega
  have heq : (width * 2#64).toNat = width.toNat * 2 := by
    rw [BitVec.toNat_mul]
    change (width.toNat * 2) % 2 ^ 64 = width.toNat * 2
    exact Nat.mod_eq_of_lt (by omega)
  exact ⟨heq, by rw [heq]; exact hdouble, by rw [heq]; omega⟩

theorem htab_keys_alloc_size_no_wrap (n stride : BitVec 64)
    (hsize : n.toNat * stride.toNat + 8 < 2 ^ 64) :
    (n * stride + 8).toNat = n.toNat * stride.toNat + 8 := by
  have hmul := sort_alloc_size_no_wrap n stride (by omega)
  rw [BitVec.toNat_add, hmul]
  change (n.toNat * stride.toNat + 8) % 2 ^ 64 = _
  exact Nat.mod_eq_of_lt hsize

theorem sort_clamped_add_bounds (x width n : BitVec 64)
    (hx : x.toNat ≤ n.toNat) (hw : width.toNat ≤ n.toNat)
    (hn : n.toNat < 2 ^ 63) :
    let y := if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower n (x + width)
      then n else x + width
    y.toNat = min n.toNat (x.toNat + width.toNat) ∧
      x.toNat ≤ y.toNat ∧ y.toNat ≤ n.toNat := by
  have hsum : (x + width).toNat = x.toNat + width.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  dsimp only
  by_cases hcmp : n.toNat < (x + width).toNat
  · have hc : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower n (x + width) = true := by
      simpa [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def] using hcmp
    rw [hc]
    simp only [↓reduceIte]
    exact ⟨by rw [Nat.min_eq_left (by omega)], hx, le_rfl⟩
  · have hnot : ¬ (n < x + width) := by
      simpa [BitVec.lt_def] using hcmp
    have hc : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower n (x + width) = false := by
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnot]
    rw [hc]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨by rw [hsum, Nat.min_eq_right (by omega)], by rw [hsum]; omega, by rw [hsum]; omega⟩

theorem merge_cursor_bounds (left mid right i j k : Nat)
    (hli : left ≤ i) (him : i ≤ mid) (hmj : mid ≤ j) (hjr : j ≤ right)
    (hk : k + mid = i + j) :
    left ≤ k ∧ k ≤ right ∧
      (i < mid ∨ j < right → k < right) := by
  omega

theorem merge_cursor_step_left (mid i j k : Nat)
    (hk : k + mid = i + j) :
    (k + 1) + mid = (i + 1) + j := by
  omega

theorem merge_cursor_step_right (mid i j k : Nat)
    (hk : k + mid = i + j) :
    (k + 1) + mid = i + (j + 1) := by
  omega

theorem bre_decCall_bal_sort_gt {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (args : List (ExpHOL 64))
    (cont : ProgHOL 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode)
    (hcont : ∀ (v : ValueHOL 64) (resumed : PanSemStateFiniteExact 64 F),
      resumed.code = originalRuntimeCode →
      resumed.clock < s.clock →
      M11.ByteRegionEffect s resumed Rl →
      resumed.locals = s.locals.update (ofString lname, v) →
      M11.ByteRegionEffect resumed (evaluateHOLFiniteState resumed cont).2 Rl) :
    M11.ByteRegionEffect s
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "bal_sort_gt") args cont)).2 Rl := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · exact M11.ByteRegionEffect.refl s Rl
  · dsimp only
    rcases hlk : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup (ofString "bal_sort_gt") values with
      _ | ⟨body, callee, rs⟩
    · exact M11.ByteRegionEffect.refl s Rl
    · dsimp only
      split
      · exact (M11.ByteRegionEffect.refl s Rl).with_locals_clock _ _
      · rename_i hcz
        have hlk_orig : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
            (ofString "bal_sort_gt") values = some (body, callee, rs) := by
          rwa [← hcode]
        obtain ⟨params, rs', hinst⟩ :=
          InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hlk_orig
        have hl_gt := lookup_of_guestAst_getElem 429 (by rw [guestAst_len]; decide)
          (extractFn Guest.Software.guestFn_bal_sort_gt) rfl
        change originalRuntimeCode.lookup (ofString "bal_sort_gt") = _ at hl_gt
        rw [hl_gt] at hinst
        have hbody_eq := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
        have hbody_ro : InitECandidate.Solver.Wave8Contracts.M15.readOnlyProg (fun _ => false) body = true := by
          rw [← hbody_eq]; rfl
        have hlf := InitECandidate.Solver.Wave8Contracts.M15.evaluate_readOnlyProg
          (fun _ => false) (fun _ h => by cases h) body hbody_ro
          (callEntryStateHOLFinite s callee) hcode
        have hcl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, st⟩
        rw [hrun] at hlf hcl
        dsimp only at hlf hcl ⊢
        change st.clock ≤ s.clock - 1 at hcl
        have hsmall : st.clock < s.clock := by omega
        have heff_st : M11.ByteRegionEffect s st Rl := by
          unfold InitECandidate.Solver.Wave8Contracts.M15.LocFrame at hlf
          rw [hlf]
          exact (M11.ByteRegionEffect.refl s Rl).with_locals_clock st.locals st.clock
        cases res with
        | none => exact heff_st
        | some r =>
          cases r with
          | returned v =>
            dsimp only
            split
            · set resumed := setVarHOLFinite (ofString lname) v { st with locals := s.locals }
              have heff_res : M11.ByteRegionEffect s resumed Rl :=
                heff_st.with_locals_clock resumed.locals resumed.clock
              have hcode_res : resumed.code = originalRuntimeCode := heff_res.code.trans hcode
              have heff_c := hcont v resumed hcode_res hsmall heff_res rfl
              exact (heff_res.trans heff_c).with_locals_clock _ _
            · exact heff_st
          | «break» => exact heff_st
          | «continue» => exact heff_st
          | timeOut => exact heff_st.with_locals_clock _ _
          | error => exact heff_st.with_locals_clock _ _
          | exception _ _ => exact heff_st.with_locals_clock _ _
          | finalFfi _ => exact heff_st.with_locals_clock _ _

private def sortW1BodyP : ProgHOL 64 :=
  .dec (ofString "a") .one
    (.op .add [.var .local (ofString "src"),
      .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]])
    (.dec (ofString "b") .one
      (.op .add [.var .local (ofString "src"),
        .panop .mul [.var .local (ofString "j"), .var .local (ofString "esz")]])
      (.decCall (ofString "gt") .one (ofString "bal_sort_gt")
        [.var .local (ofString "a"), .var .local (ofString "b"), .var .local (ofString "kind")]
        (.seq
          (.ite (.cmp .equal (.var .local (ofString "gt")) (.const 0))
            (.seq
              (.call (some (none, none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "dst"),
                  .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]],
                 .var .local (ofString "a"),
                 .var .local (ofString "esz")])
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
            (.seq
              (.call (some (none, none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "dst"),
                  .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]],
                 .var .local (ofString "b"),
                 .var .local (ofString "esz")])
              (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1]))))
          (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1])))))

private def sortW2BodyP : ProgHOL 64 :=
  .seq
    (.call (some (none, none)) (ofString "memcpy")
      [.op .add [.var .local (ofString "dst"),
        .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]],
       .op .add [.var .local (ofString "src"),
        .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]],
       .var .local (ofString "esz")])
    (.seq
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))
      (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1])))

private def sortW3BodyP : ProgHOL 64 :=
  .seq
    (.call (some (none, none)) (ofString "memcpy")
      [.op .add [.var .local (ofString "dst"),
        .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]],
       .op .add [.var .local (ofString "src"),
        .panop .mul [.var .local (ofString "j"), .var .local (ofString "esz")]],
       .var .local (ofString "esz")])
    (.seq
      (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1]))
      (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1])))

private def sortMergePassBodyP : ProgHOL 64 :=
  .dec (ofString "mid") .one (.op .add [.var .local (ofString "left"), .var .local (ofString "width")])
    (.seq
      (.ite (.cmp .lower (.var .local (ofString "n")) (.var .local (ofString "mid")))
        (.assign .local (ofString "mid") (.var .local (ofString "n"))) .skip)
      (.dec (ofString "right") .one (.op .add [.var .local (ofString "mid"), .var .local (ofString "width")])
        (.seq
          (.ite (.cmp .lower (.var .local (ofString "n")) (.var .local (ofString "right")))
            (.assign .local (ofString "right") (.var .local (ofString "n"))) .skip)
          (.dec (ofString "i") .one (.var .local (ofString "left"))
            (.dec (ofString "j") .one (.var .local (ofString "mid"))
              (.dec (ofString "k") .one (.var .local (ofString "left"))
                (.seq
                  (.while (.op .and [
                    .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
                    .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))])
                    sortW1BodyP)
                  (.seq
                    (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) sortW2BodyP)
                    (.seq
                      (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) sortW3BodyP)
                      (.assign .local (ofString "left") (.var .local (ofString "right"))))))))))))

private def sortOuterLoopBodyP : ProgHOL 64 :=
  .dec (ofString "left") .one (.const 0)
    (.seq
      (.while (.cmp .less (.var .local (ofString "left")) (.var .local (ofString "n"))) sortMergePassBodyP)
      (.dec (ofString "swap") .one (.var .local (ofString "src"))
        (.seq
          (.assign .local (ofString "src") (.var .local (ofString "dst")))
          (.seq
            (.assign .local (ofString "dst") (.var .local (ofString "swap")))
            (.assign .local (ofString "width")
              (.panop .mul [.var .local (ofString "width"), .const 2#64]))))))

private def sortElemsNcrCallees (f : MlS) : Bool :=
  f == ofString "bal_sort_gt" || f == ofString "memcpy"

private theorem sortElemsNcrCallees_good :
    ∀ f, sortElemsNcrCallees f = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      noCatchableRaise sortElemsNcrCallees body = true := by
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ :=
    InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
  simp only [sortElemsNcrCallees, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with rfl | rfl
  · have hl := lookup_of_guestAst_getElem 429 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_bal_sort_gt) rfl
    change originalRuntimeCode.lookup (ofString "bal_sort_gt") = _ at hl
    rw [hl] at hinst
    have hbody := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
    rw [← hbody]; rfl
  · have hl := M11.lookup_memcpy
    rw [hl] at hinst
    have hbody := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
    rw [← hbody]; rfl

private theorem sortElemsBody_eq :
    sourceFnBody Guest.Software.guestFn_sort_elems =
      .seq
        (.ite (.cmp .lower (.var .local (ofString "n")) (.const 2#64))
          (.return (.const 0#64)) .skip)
        (.decCall (ofString "mark") .one (ofString "heap_mark") []
          (.decCall (ofString "aux") .one (ofString "alloc")
            [.panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]
            (.dec (ofString "src") .one (.var .local (ofString "p"))
              (.dec (ofString "dst") .one (.var .local (ofString "aux"))
                (.dec (ofString "width") .one (.const 1#64)
                  (.seq
                    (.while (.cmp .less (.var .local (ofString "width")) (.var .local (ofString "n")))
                      sortOuterLoopBodyP)
                    (.seq
                      (.ite (.cmp .notEqual (.var .local (ofString "src")) (.var .local (ofString "p")))
                        (.call (some (none, none)) (ofString "memcpy")
                          [.var .local (ofString "p"), .var .local (ofString "src"),
                           .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]])
                        .skip)
                      (.seq
                        (.call (some (none, none)) (ofString "heap_release")
                          [.var .local (ofString "mark")])
                        (.return (.const 0#64)))))))))) := rfl

private theorem eval_add_mul_exp {F : Type}
    (s : PanSemStateFiniteExact 64 F) (baseN idxN eszN : String)
    (base0 idx0 esz0 : BitVec 64)
    (hbase : s.locals.lookup (ofString baseN) = some (.val (.word base0)))
    (hidx : s.locals.lookup (ofString idxN) = some (.val (.word idx0)))
    (hesz : s.locals.lookup (ofString eszN) = some (.val (.word esz0))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString baseN),
        .panop .mul [.var .local (ofString idxN), .var .local (ofString eszN)]]) =
      some (.val (.word (base0 + idx0 * esz0))) := by
  simp [evalHOLExact, evalListHOLExact, hbase, hidx, hesz,
    panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord,
    List.all, List.map, Option.map, List.foldr]

private theorem eval_assign_inc1_bre {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vN : String) (v0 : BitVec 64) (Rl : List Ivl)
    (hv : s.locals.lookup (ofString vN) = some (.val (.word v0))) :
    evaluateHOLFiniteState s
      (.assign .local (ofString vN) (.op .add [.var .local (ofString vN), .const 1])) =
      (none, setVarHOLFinite (ofString vN) (.val (.word (v0 + 1))) s) ∧
    M11.ByteRegionEffect s (setVarHOLFinite (ofString vN) (.val (.word (v0 + 1))) s) Rl := by
  have hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString vN), .const 1]) =
      some (.val (.word (v0 + 1))) := by
    simp [evalHOLExact, evalListHOLExact, hv, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, List.foldr]
  have hvld : isValidValueHOLFinite s .local (ofString vN) (.val (.word (v0 + 1))) = true := by
    simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hv, shapeOfHOLExact, shapeEqHOL]
  refine ⟨?_, (M11.ByteRegionEffect.refl s Rl).with_locals_clock _ _⟩
  rw [evaluateHOLFiniteState_assign, hev]
  dsimp only
  rw [if_pos hvld]
  rfl

private theorem eval_signed_less_nonneg {F : Type}
    (s : PanSemStateFiniteExact 64 F) (xN yN : String) (x0 y0 : BitVec 64)
    (hx : s.locals.lookup (ofString xN) = some (.val (.word x0)))
    (hy : s.locals.lookup (ofString yN) = some (.val (.word y0)))
    (hx_lt : x0.toNat < 2 ^ 63) (hy_lt : y0.toNat < 2 ^ 63) :
    @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .less (.var .local (ofString xN)) (.var .local (ofString yN))) =
      some (.val (.word (if x0.toNat < y0.toNat then 1 else 0))) := by
  have hcmp : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .less x0 y0 = decide (x0.toNat < y0.toNat) := by
    have h1 := x0.isLt
    have h2 := y0.isLt
    simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, Flapjack.Compiler.Encoders.Asm.holAsmSignedLess]
    split_ifs <;> simp_all <;> omega
  simp [evalHOLFinite, evalHOLExact, hx, hy, hcmp]

private theorem eval_w1_cond_nonneg {F : Type}
    (s : PanSemStateFiniteExact 64 F) (i0 mid0 j0 right0 : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i0)))
    (hm : s.locals.lookup (ofString "mid") = some (.val (.word mid0)))
    (hj : s.locals.lookup (ofString "j") = some (.val (.word j0)))
    (hr : s.locals.lookup (ofString "right") = some (.val (.word right0)))
    (hi_lt : i0.toNat < 2 ^ 63) (hm_lt : mid0.toNat < 2 ^ 63)
    (hj_lt : j0.toNat < 2 ^ 63) (hr_lt : right0.toNat < 2 ^ 63) :
    @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .and [
        .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
        .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))]) =
      some (.val (.word (if i0.toNat < mid0.toNat ∧ j0.toNat < right0.toNat then 1 else 0))) := by
  have hcmp1 : Flapjack.Compiler.Encoders.Asm.holAsmSignedLess i0 mid0 = decide (i0.toNat < mid0.toNat) := by
    have h1 := i0.isLt; have h2 := mid0.isLt
    simp only [Flapjack.Compiler.Encoders.Asm.holAsmSignedLess]
    split_ifs <;> simp_all <;> omega
  have hcmp2 : Flapjack.Compiler.Encoders.Asm.holAsmSignedLess j0 right0 = decide (j0.toNat < right0.toNat) := by
    have h1 := j0.isLt; have h2 := right0.isLt
    simp only [Flapjack.Compiler.Encoders.Asm.holAsmSignedLess]
    split_ifs <;> simp_all <;> omega
  by_cases hc1 : i0.toNat < mid0.toNat <;> by_cases hc2 : j0.toNat < right0.toNat <;>
    simp [evalHOLFinite, evalHOLExact, evalListHOLExact, hi, hm, hj, hr, hcmp1, hcmp2, hc1, hc2,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, List.foldr]

private def SortMergeCursorInv {F : Type}
    (p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 : BitVec 64)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.code = originalRuntimeCode ∧
  s.memaddrs = ordinaryDomain ∧
  s.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
  s.locals.lookup (ofString "src") = some (.val (.word src0)) ∧
  s.locals.lookup (ofString "esz") = some (.val (.word esz0)) ∧
  s.locals.lookup (ofString "mid") = some (.val (.word mid0)) ∧
  s.locals.lookup (ofString "right") = some (.val (.word right0)) ∧
  (∃ kindVal, s.locals.lookup (ofString "kind") = some (.val (.word kindVal))) ∧
  (dst0 = p0 ∨ dst0 = aux0) ∧
  n0.toNat < 2 ^ 63 ∧
  p0.toNat + n0.toNat * esz0.toNat < 2 ^ 64 ∧
  aux0.toNat + n0.toNat * esz0.toNat < 2 ^ 64 ∧
  left0.toNat ≤ mid0.toNat ∧ mid0.toNat ≤ right0.toNat ∧ right0.toNat ≤ n0.toNat ∧
  ∃ i0 j0 k0 : BitVec 64,
    s.locals.lookup (ofString "i") = some (.val (.word i0)) ∧
    s.locals.lookup (ofString "j") = some (.val (.word j0)) ∧
    s.locals.lookup (ofString "k") = some (.val (.word k0)) ∧
    left0.toNat ≤ i0.toNat ∧ i0.toNat ≤ mid0.toNat ∧
    mid0.toNat ≤ j0.toNat ∧ j0.toNat ≤ right0.toNat ∧
    k0.toNat + mid0.toNat = i0.toNat + j0.toNat

private theorem sortMergeCursorInv_decClock {F : Type}
    {p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F)
    (h : SortMergeCursorInv p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 s) :
    SortMergeCursorInv p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 (decClockHOLFinite s) :=
  h

private theorem sort_dst_elem_in_regions
    (p0 aux0 n0 esz0 dst0 k0 : BitVec 64)
    (hdst_choice : dst0 = p0 ∨ dst0 = aux0)
    (hk : k0.toNat < n0.toNat)
    (hp_nw : p0.toNat + n0.toNat * esz0.toNat < 2 ^ 64)
    (haux_nw : aux0.toNat + n0.toNat * esz0.toNat < 2 ^ 64)
    (_hpos : 0 < esz0.toNat) :
    ∃ ivl ∈ ([(p0.toNat, n0.toNat * esz0.toNat), (aux0.toNat, n0.toNat * esz0.toNat)] : List Ivl),
      ivl.1 ≤ (dst0 + k0 * esz0).toNat ∧
      (dst0 + k0 * esz0).toNat + esz0.toNat ≤ ivl.1 + ivl.2 := by
  rcases hdst_choice with h | h <;> subst h
  · obtain ⟨_, hlo, hhi⟩ := indexed_element_bounds dst0 n0 esz0 k0 hp_nw hk
    exact ⟨(dst0.toNat, n0.toNat * esz0.toNat), List.Mem.head _, hlo, hhi⟩
  · obtain ⟨_, hlo, hhi⟩ := indexed_element_bounds dst0 n0 esz0 k0 haux_nw hk
    exact ⟨(dst0.toNat, n0.toNat * esz0.toNat), List.Mem.tail _ (List.Mem.head _), hlo, hhi⟩

private theorem eval_sort_merge_copy_bre {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (p0 aux0 n0 esz0 dst0 src0 k0 q0 : BitVec 64) (qN : String)
    (hcode : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hsrc : s.locals.lookup (ofString "src") = some (.val (.word src0)))
    (hk : s.locals.lookup (ofString "k") = some (.val (.word k0)))
    (hq : s.locals.lookup (ofString qN) = some (.val (.word q0)))
    (hesz : s.locals.lookup (ofString "esz") = some (.val (.word esz0)))
    (hchoice : dst0 = p0 ∨ dst0 = aux0)
    (hkn : k0.toNat < n0.toNat)
    (hp_nw : p0.toNat + n0.toNat * esz0.toNat < 2 ^ 64)
    (haux_nw : aux0.toNat + n0.toNat * esz0.toNat < 2 ^ 64)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "dst"),
          .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]],
         .op .add [.var .local (ofString "src"),
          .panop .mul [.var .local (ofString qN), .var .local (ofString "esz")]],
         .var .local (ofString "esz")])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "dst"),
          .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]],
         .op .add [.var .local (ofString "src"),
          .panop .mul [.var .local (ofString qN), .var .local (ofString "esz")]],
         .var .local (ofString "esz")])
    (out.1 = none →
      M11.ByteRegionEffect s out.2
        [(p0.toNat, n0.toNat * esz0.toNat), (aux0.toNat, n0.toNat * esz0.toNat)] ∧
      out.2.locals = s.locals) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  apply M11.eval_call_memcpy_bre s _ _ _ (dst0 + k0 * esz0) (src0 + q0 * esz0) esz0
    _ hcode hma
    (eval_add_mul_exp s "dst" "k" "esz" dst0 k0 esz0 hdst hk hesz)
    (eval_add_mul_exp s "src" qN "esz" src0 q0 esz0 hsrc hq hesz)
    (by simpa [evalHOLExact] using hesz) ?_ hnt
  intro hpos
  exact sort_dst_elem_in_regions p0 aux0 n0 esz0 dst0 k0 hchoice hkn hp_nw haux_nw hpos

private theorem eval_sort_merge_copy_var_bre {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (p0 aux0 n0 esz0 dst0 srcVal k0 : BitVec 64) (srcVarN : String)
    (hcode : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hsrcVar : s.locals.lookup (ofString srcVarN) = some (.val (.word srcVal)))
    (hk : s.locals.lookup (ofString "k") = some (.val (.word k0)))
    (hesz : s.locals.lookup (ofString "esz") = some (.val (.word esz0)))
    (hchoice : dst0 = p0 ∨ dst0 = aux0)
    (hkn : k0.toNat < n0.toNat)
    (hp_nw : p0.toNat + n0.toNat * esz0.toNat < 2 ^ 64)
    (haux_nw : aux0.toNat + n0.toNat * esz0.toNat < 2 ^ 64)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "dst"),
          .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]],
         .var .local (ofString srcVarN),
         .var .local (ofString "esz")])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "dst"),
          .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]],
         .var .local (ofString srcVarN),
         .var .local (ofString "esz")])
    (out.1 = none →
      M11.ByteRegionEffect s out.2
        [(p0.toNat, n0.toNat * esz0.toNat), (aux0.toNat, n0.toNat * esz0.toNat)] ∧
      out.2.locals = s.locals) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  apply M11.eval_call_memcpy_bre s _ _ _ (dst0 + k0 * esz0) srcVal esz0
    _ hcode hma
    (eval_add_mul_exp s "dst" "k" "esz" dst0 k0 esz0 hdst hk hesz)
    (by simpa [evalHOLExact] using hsrcVar)
    (by simpa [evalHOLExact] using hesz) ?_ hnt
  intro hpos
  exact sort_dst_elem_in_regions p0 aux0 n0 esz0 dst0 k0 hchoice hkn hp_nw haux_nw hpos

private theorem eval_sortW2_while_bre {F : Type}
    (s0 : PanSemStateFiniteExact 64 F)
    (p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 : BitVec 64)
    (hinv0 : SortMergeCursorInv p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 s0)
    (hnt0 : (evaluateHOLFiniteState s0
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) sortW2BodyP)).1 ≠
        some .timeOut) :
    let out := evaluateHOLFiniteState s0
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) sortW2BodyP)
    (out.1 = none →
      SortMergeCursorInv p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 out.2 ∧
      M11.ByteRegionEffect s0 out.2
        [(p0.toNat, n0.toNat * esz0.toNat), (aux0.toNat, n0.toNat * esz0.toNat)]) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  let Rl : List Ivl := [(p0.toNat, n0.toNat * esz0.toNat), (aux0.toNat, n0.toNat * esz0.toNat)]
  let loopP : ProgHOL 64 := .while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) sortW2BodyP
  suffices hmain : ∀ (clk : Nat) (s : PanSemStateFiniteExact 64 F), s.clock = clk →
      SortMergeCursorInv p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 s →
      (evaluateHOLFiniteState s loopP).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState s loopP).1 = none →
        SortMergeCursorInv p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 (evaluateHOLFiniteState s loopP).2 ∧
        M11.ByteRegionEffect s (evaluateHOLFiniteState s loopP).2 Rl) ∧
      ((evaluateHOLFiniteState s loopP).1 ≠ none → ¬ Resumes (evaluateHOLFiniteState s loopP).1) by
    exact hmain s0.clock s0 rfl hinv0 hnt0
  intro clk
  induction clk using Nat.strong_induction_on with
  | h clk ih =>
    intro s hclk hPs hnt
    obtain ⟨hcode, hma, hdst, hsrc, hesz, hmid, hright, hkind, hchoice, hn_lt,
      hp_nw, haux_nw, hl_m, hm_r, hr_n, i0, j0, k0, hi, hj, hk, hl_i, hi_m, hm_j, hj_r, hk_eq⟩ := hPs
    have hc := eval_signed_less_nonneg s "i" "mid" i0 mid0 hi hmid (by omega) (by omega)
    dsimp only [loopP] at hnt ⊢
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    simp only [hc] at hnt ⊢
    by_cases hlt : i0.toNat < mid0.toNat
    · simp only [hlt, ↓reduceIte] at hnt ⊢
      have h1nz : (1 : BitVec 64) ≠ 0 := by decide
      rw [if_pos h1nz] at hnt ⊢
      by_cases hclk0 : s.clock = 0
      · simp [hclk0] at hnt
      · rw [if_neg hclk0] at hnt ⊢
        set d0 := decClockHOLFinite s
        have heff_dec : M11.ByteRegionEffect s d0 Rl :=
          (M11.ByteRegionEffect.refl s Rl).with_locals_clock d0.locals d0.clock
        have hd_clk : d0.clock < clk := by simp [d0, decClockHOLFinite, hclk]; omega
        have hb_clk := Flapjack.evaluateHOLFiniteState_clock_le d0 sortW2BodyP
        have hk_bounds := merge_cursor_bounds left0.toNat mid0.toNat right0.toNat
          i0.toNat j0.toNat k0.toNat hl_i hi_m hm_j hj_r hk_eq
        have hk_lt_n : k0.toNat < n0.toNat := by omega
        dsimp only [sortW2BodyP] at hnt hb_clk ⊢
        rw [evaluateHOLFiniteState_seq_line780] at hnt hb_clk ⊢
        rcases hmc : evaluateHOLFiniteState d0
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "dst"),
              .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]],
             .op .add [.var .local (ofString "src"),
              .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]],
             .var .local (ofString "esz")]) with ⟨rmc, s1⟩
        simp only [hmc] at hnt hb_clk ⊢
        have hnt_mc : rmc ≠ some .timeOut := by rintro rfl; exact hnt rfl
        have hspec_mc := eval_sort_merge_copy_bre d0 p0 aux0 n0 esz0 dst0 src0 k0 i0 "i"
          hcode hma hdst hsrc hk hi hesz hchoice hk_lt_n hp_nw haux_nw (by rw [hmc]; exact hnt_mc)
        rw [hmc] at hspec_mc
        cases rmc with
        | some r =>
          dsimp only at hspec_mc hnt ⊢
          have hnr : ¬ Resumes (some r) := hspec_mc.2 (by simp)
          cases r with
          | «continue» =>
            exfalso
            have hnc : (evaluateHOLFiniteState d0
              (.call (some (none, none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "dst"),
                  .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]],
                 .op .add [.var .local (ofString "src"),
                  .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]],
                 .var .local (ofString "esz")])).1 ≠ some .continue :=
              evaluate_noTopContinue _ rfl d0
            exact hnc (by rw [hmc])
          | «break» =>
            exfalso
            have hnb : (evaluateHOLFiniteState d0
              (.call (some (none, none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "dst"),
                  .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]],
                 .op .add [.var .local (ofString "src"),
                  .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]],
                 .var .local (ofString "esz")])).1 ≠ some .break :=
              InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak _ rfl d0
            exact hnb (by rw [hmc])
          | returned v => exact ⟨fun h => by simp at h, fun _ => hnr⟩
          | exception e v => exact ⟨fun h => by simp at h, fun _ => hnr⟩
          | timeOut => exact absurd rfl hnt_mc
          | error => exact ⟨fun h => by simp at h, fun _ => hnr⟩
          | finalFfi f => exact ⟨fun h => by simp at h, fun _ => hnr⟩
        | none =>
          dsimp only at hspec_mc hnt hb_clk ⊢
          obtain ⟨heff_mc, hloc1⟩ := hspec_mc.1 rfl
          rw [evaluateHOLFiniteState_seq_line780] at hnt hb_clk ⊢
          obtain ⟨hinc_i, heff_i⟩ := eval_assign_inc1_bre s1 "i" i0 Rl (by rw [hloc1]; exact hi)
          rw [hinc_i] at hnt hb_clk ⊢
          dsimp only at hnt hb_clk ⊢
          set s2 := setVarHOLFinite (ofString "i") (.val (.word (i0 + 1))) s1
          have hloc2_k : s2.locals.lookup (ofString "k") = some (.val (.word k0)) := by
            have hd0k : d0.locals.lookup (ofString "k") = some (.val (.word k0)) := hk
            simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "k" by decide, hloc1, hd0k]
          obtain ⟨hinc_k, heff_k⟩ := eval_assign_inc1_bre s2 "k" k0 Rl hloc2_k
          rw [hinc_k] at hnt hb_clk ⊢
          dsimp only at hnt hb_clk ⊢
          set s3 := setVarHOLFinite (ofString "k") (.val (.word (k0 + 1))) s2
          have heff_body : M11.ByteRegionEffect d0 s3 Rl :=
            (heff_mc.trans heff_i).trans heff_k
          have hi1_nat : (i0 + 1).toNat = i0.toNat + 1 := by
            rw [BitVec.toNat_add]; change (i0.toNat + 1) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
          have hk1_nat : (k0 + 1).toNat = k0.toNat + 1 := by
            rw [BitVec.toNat_add]; change (k0.toNat + 1) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
          have hstep_eq := merge_cursor_step_left mid0.toNat i0.toNat j0.toNat k0.toNat hk_eq
          have hloc3_other : ∀ x, x ≠ ofString "k" → x ≠ ofString "i" →
              s3.locals.lookup x = s.locals.lookup x := by
            intro x hxk hxi
            change (setVarHOLFinite _ _ _).locals.lookup x = d0.locals.lookup x
            simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              Ne.symm hxk, Ne.symm hxi, hloc1]
          have hPs3 : SortMergeCursorInv p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 s3 := by
            obtain ⟨kindVal, hkv⟩ := hkind
            refine ⟨heff_body.code.trans hcode, heff_body.memaddrs.trans hma,
              (hloc3_other _ (by decide) (by decide)).trans hdst,
              (hloc3_other _ (by decide) (by decide)).trans hsrc,
              (hloc3_other _ (by decide) (by decide)).trans hesz,
              (hloc3_other _ (by decide) (by decide)).trans hmid,
              (hloc3_other _ (by decide) (by decide)).trans hright,
              ⟨kindVal, (hloc3_other _ (by decide) (by decide)).trans hkv⟩,
              hchoice, hn_lt, hp_nw, haux_nw, hl_m, hm_r, hr_n,
              i0 + 1, j0, k0 + 1, ?_, ?_, ?_, ?_, ?_, hm_j, hj_r, ?_⟩
            · simp [s3, s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "k" ≠ ofString "i" by decide]
            · exact (hloc3_other _ (by decide) (by decide)).trans hj
            · simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            · rw [hi1_nat]; omega
            · rw [hi1_nat]; omega
            · rw [hk1_nat, hi1_nat]; exact hstep_eq
          have jih := ih s3.clock (lt_of_le_of_lt hb_clk hd_clk) s3 rfl hPs3 hnt
          exact ⟨fun hn => ⟨(jih.1 hn).1, (heff_dec.trans heff_body).trans (jih.1 hn).2⟩, jih.2⟩
    · rw [if_neg hlt] at hnt ⊢
      have h0nz : ¬ ((0 : BitVec 64) ≠ 0) := by decide
      rw [if_neg h0nz]
      exact ⟨fun _ => ⟨⟨hcode, hma, hdst, hsrc, hesz, hmid, hright, hkind, hchoice, hn_lt,
        hp_nw, haux_nw, hl_m, hm_r, hr_n, i0, j0, k0, hi, hj, hk, hl_i, hi_m, hm_j, hj_r, hk_eq⟩,
        M11.ByteRegionEffect.refl s Rl⟩, fun h => False.elim (h rfl)⟩

private theorem eval_sortW3_while_bre {F : Type}
    (s0 : PanSemStateFiniteExact 64 F)
    (p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 : BitVec 64)
    (hinv0 : SortMergeCursorInv p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 s0)
    (hnt0 : (evaluateHOLFiniteState s0
      (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) sortW3BodyP)).1 ≠
        some .timeOut) :
    let out := evaluateHOLFiniteState s0
      (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) sortW3BodyP)
    (out.1 = none →
      SortMergeCursorInv p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 out.2 ∧
      M11.ByteRegionEffect s0 out.2
        [(p0.toNat, n0.toNat * esz0.toNat), (aux0.toNat, n0.toNat * esz0.toNat)]) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  let Rl : List Ivl := [(p0.toNat, n0.toNat * esz0.toNat), (aux0.toNat, n0.toNat * esz0.toNat)]
  let loopP : ProgHOL 64 := .while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) sortW3BodyP
  suffices hmain : ∀ (clk : Nat) (s : PanSemStateFiniteExact 64 F), s.clock = clk →
      SortMergeCursorInv p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 s →
      (evaluateHOLFiniteState s loopP).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState s loopP).1 = none →
        SortMergeCursorInv p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 (evaluateHOLFiniteState s loopP).2 ∧
        M11.ByteRegionEffect s (evaluateHOLFiniteState s loopP).2 Rl) ∧
      ((evaluateHOLFiniteState s loopP).1 ≠ none → ¬ Resumes (evaluateHOLFiniteState s loopP).1) by
    exact hmain s0.clock s0 rfl hinv0 hnt0
  intro clk
  induction clk using Nat.strong_induction_on with
  | h clk ih =>
    intro s hclk hPs hnt
    obtain ⟨hcode, hma, hdst, hsrc, hesz, hmid, hright, hkind, hchoice, hn_lt,
      hp_nw, haux_nw, hl_m, hm_r, hr_n, i0, j0, k0, hi, hj, hk, hl_i, hi_m, hm_j, hj_r, hk_eq⟩ := hPs
    have hc := eval_signed_less_nonneg s "j" "right" j0 right0 hj hright (by omega) (by omega)
    dsimp only [loopP] at hnt ⊢
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    simp only [hc] at hnt ⊢
    by_cases hlt : j0.toNat < right0.toNat
    · simp only [hlt, ↓reduceIte] at hnt ⊢
      have h1nz : (1 : BitVec 64) ≠ 0 := by decide
      rw [if_pos h1nz] at hnt ⊢
      by_cases hclk0 : s.clock = 0
      · simp [hclk0] at hnt
      · rw [if_neg hclk0] at hnt ⊢
        set d0 := decClockHOLFinite s
        have heff_dec : M11.ByteRegionEffect s d0 Rl :=
          (M11.ByteRegionEffect.refl s Rl).with_locals_clock d0.locals d0.clock
        have hd_clk : d0.clock < clk := by simp [d0, decClockHOLFinite, hclk]; omega
        have hb_clk := Flapjack.evaluateHOLFiniteState_clock_le d0 sortW3BodyP
        have hk_bounds := merge_cursor_bounds left0.toNat mid0.toNat right0.toNat
          i0.toNat j0.toNat k0.toNat hl_i hi_m hm_j hj_r hk_eq
        have hk_lt_n : k0.toNat < n0.toNat := by omega
        dsimp only [sortW3BodyP] at hnt hb_clk ⊢
        rw [evaluateHOLFiniteState_seq_line780] at hnt hb_clk ⊢
        rcases hmc : evaluateHOLFiniteState d0
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "dst"),
              .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]],
             .op .add [.var .local (ofString "src"),
              .panop .mul [.var .local (ofString "j"), .var .local (ofString "esz")]],
             .var .local (ofString "esz")]) with ⟨rmc, s1⟩
        simp only [hmc] at hnt hb_clk ⊢
        have hnt_mc : rmc ≠ some .timeOut := by rintro rfl; exact hnt rfl
        have hspec_mc := eval_sort_merge_copy_bre d0 p0 aux0 n0 esz0 dst0 src0 k0 j0 "j"
          hcode hma hdst hsrc hk hj hesz hchoice hk_lt_n hp_nw haux_nw (by rw [hmc]; exact hnt_mc)
        rw [hmc] at hspec_mc
        cases rmc with
        | some r =>
          dsimp only at hspec_mc hnt ⊢
          have hnr : ¬ Resumes (some r) := hspec_mc.2 (by simp)
          cases r with
          | «continue» =>
            exfalso
            have hnc : (evaluateHOLFiniteState d0
              (.call (some (none, none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "dst"),
                  .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]],
                 .op .add [.var .local (ofString "src"),
                  .panop .mul [.var .local (ofString "j"), .var .local (ofString "esz")]],
                 .var .local (ofString "esz")])).1 ≠ some .continue :=
              evaluate_noTopContinue _ rfl d0
            exact hnc (by rw [hmc])
          | «break» =>
            exfalso
            have hnb : (evaluateHOLFiniteState d0
              (.call (some (none, none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "dst"),
                  .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]],
                 .op .add [.var .local (ofString "src"),
                  .panop .mul [.var .local (ofString "j"), .var .local (ofString "esz")]],
                 .var .local (ofString "esz")])).1 ≠ some .break :=
              InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak _ rfl d0
            exact hnb (by rw [hmc])
          | returned v => exact ⟨fun h => by simp at h, fun _ => hnr⟩
          | exception e v => exact ⟨fun h => by simp at h, fun _ => hnr⟩
          | timeOut => exact absurd rfl hnt_mc
          | error => exact ⟨fun h => by simp at h, fun _ => hnr⟩
          | finalFfi f => exact ⟨fun h => by simp at h, fun _ => hnr⟩
        | none =>
          dsimp only at hspec_mc hnt hb_clk ⊢
          obtain ⟨heff_mc, hloc1⟩ := hspec_mc.1 rfl
          rw [evaluateHOLFiniteState_seq_line780] at hnt hb_clk ⊢
          obtain ⟨hinc_j, heff_j⟩ := eval_assign_inc1_bre s1 "j" j0 Rl (by rw [hloc1]; exact hj)
          rw [hinc_j] at hnt hb_clk ⊢
          dsimp only at hnt hb_clk ⊢
          set s2 := setVarHOLFinite (ofString "j") (.val (.word (j0 + 1))) s1
          have hloc2_k : s2.locals.lookup (ofString "k") = some (.val (.word k0)) := by
            have hd0k : d0.locals.lookup (ofString "k") = some (.val (.word k0)) := hk
            simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "j" ≠ ofString "k" by decide, hloc1, hd0k]
          obtain ⟨hinc_k, heff_k⟩ := eval_assign_inc1_bre s2 "k" k0 Rl hloc2_k
          rw [hinc_k] at hnt hb_clk ⊢
          dsimp only at hnt hb_clk ⊢
          set s3 := setVarHOLFinite (ofString "k") (.val (.word (k0 + 1))) s2
          have heff_body : M11.ByteRegionEffect d0 s3 Rl :=
            (heff_mc.trans heff_j).trans heff_k
          have hj1_nat : (j0 + 1).toNat = j0.toNat + 1 := by
            rw [BitVec.toNat_add]; change (j0.toNat + 1) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
          have hk1_nat : (k0 + 1).toNat = k0.toNat + 1 := by
            rw [BitVec.toNat_add]; change (k0.toNat + 1) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
          have hstep_eq := merge_cursor_step_right mid0.toNat i0.toNat j0.toNat k0.toNat hk_eq
          have hloc3_other : ∀ x, x ≠ ofString "k" → x ≠ ofString "j" →
              s3.locals.lookup x = s.locals.lookup x := by
            intro x hxk hxj
            change (setVarHOLFinite _ _ _).locals.lookup x = d0.locals.lookup x
            simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              Ne.symm hxk, Ne.symm hxj, hloc1]
          have hPs3 : SortMergeCursorInv p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 s3 := by
            obtain ⟨kindVal, hkv⟩ := hkind
            refine ⟨heff_body.code.trans hcode, heff_body.memaddrs.trans hma,
              (hloc3_other _ (by decide) (by decide)).trans hdst,
              (hloc3_other _ (by decide) (by decide)).trans hsrc,
              (hloc3_other _ (by decide) (by decide)).trans hesz,
              (hloc3_other _ (by decide) (by decide)).trans hmid,
              (hloc3_other _ (by decide) (by decide)).trans hright,
              ⟨kindVal, (hloc3_other _ (by decide) (by decide)).trans hkv⟩,
              hchoice, hn_lt, hp_nw, haux_nw, hl_m, hm_r, hr_n,
              i0, j0 + 1, k0 + 1, ?_, ?_, ?_, hl_i, hi_m, ?_, ?_, ?_⟩
            · exact (hloc3_other _ (by decide) (by decide)).trans hi
            · simp [s3, s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "k" ≠ ofString "j" by decide]
            · simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            · rw [hj1_nat]; omega
            · rw [hj1_nat]; omega
            · rw [hk1_nat, hj1_nat]; exact hstep_eq
          have jih := ih s3.clock (lt_of_le_of_lt hb_clk hd_clk) s3 rfl hPs3 hnt
          exact ⟨fun hn => ⟨(jih.1 hn).1, (heff_dec.trans heff_body).trans (jih.1 hn).2⟩, jih.2⟩
    · rw [if_neg hlt] at hnt ⊢
      have h0nz : ¬ ((0 : BitVec 64) ≠ 0) := by decide
      rw [if_neg h0nz]
      exact ⟨fun _ => ⟨⟨hcode, hma, hdst, hsrc, hesz, hmid, hright, hkind, hchoice, hn_lt,
        hp_nw, haux_nw, hl_m, hm_r, hr_n, i0, j0, k0, hi, hj, hk, hl_i, hi_m, hm_j, hj_r, hk_eq⟩,
        M11.ByteRegionEffect.refl s Rl⟩, fun h => False.elim (h rfl)⟩

private theorem eval_decCall_bal_sort_gt_bre {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String)
    (aExp bExp kindExp : ExpHOL 64) (a0 b0 kind0 : BitVec 64)
    (cont : ProgHOL 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode)
    (ha : evalAt s aExp = some (.val (.word a0)))
    (hb : evalAt s bExp = some (.val (.word b0)))
    (hkind : evalAt s kindExp = some (.val (.word kind0)))
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "bal_sort_gt") [aExp, bExp, kindExp] cont)).1 ≠
        some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "bal_sort_gt") [aExp, bExp, kindExp] cont)
    (∃ (gtw : BitVec 64) (resumed : PanSemStateFiniteExact 64 F),
      M11.ByteRegionEffect s resumed Rl ∧
      resumed.clock < s.clock ∧
      resumed.locals = s.locals.update (ofString lname, .val (.word gtw)) ∧
      (evaluateHOLFiniteState resumed cont).1 ≠ some .timeOut ∧
      out = ((evaluateHOLFiniteState resumed cont).1,
        { (evaluateHOLFiniteState resumed cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState resumed cont).2.locals
            (ofString lname, s.locals.lookup (ofString lname)) })) ∨
    (out.1 ≠ none ∧ out.1 ≠ some .continue ∧ out.1 ≠ some .break ∧ ¬ Resumes out.1) := by
  have hncr_call : ∀ eid ev, eid ≠ ofString "TrapErr" →
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "bal_sort_gt") [aExp, bExp, kindExp] .skip)).1 ≠
          some (.exception eid ev) :=
    evaluate_noCatchableRaise sortElemsNcrCallees sortElemsNcrCallees_good _ rfl s hcode
  dsimp only
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hncr_call ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [aExp, bExp, kindExp] =
      some [.val (.word a0), .val (.word b0), .val (.word kind0)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalAt, ha, hb, hkind]
  rw [hargs] at hnt hncr_call ⊢
  dsimp only at hnt hncr_call ⊢
  rcases hlk : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup (ofString "bal_sort_gt")
      [.val (.word a0), .val (.word b0), .val (.word kind0)] with _ | ⟨body, callee, rs⟩
  · rw [hlk] at hnt hncr_call
    right; exact ⟨by simp, by simp, by simp, not_resumes_error⟩
  · rw [hlk] at hnt hncr_call
    dsimp only at hnt hncr_call ⊢
    by_cases hcz : s.clock = 0
    · simp [hcz] at hnt
    · rw [if_neg hcz] at hnt hncr_call ⊢
      have hinst := lookup_of_guestAst_getElem 429 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_bal_sort_gt) rfl
      change originalRuntimeCode.lookup (ofString "bal_sort_gt") = _ at hinst
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "bal_sort_gt")
        _ (sourceFnBody Guest.Software.guestFn_bal_sort_gt) body .one rs
        [.val (.word a0), .val (.word b0), .val (.word kind0)] callee
        (by rw [hcode]; exact hinst) hlk
      have hrs_eq : rs = .one :=
        lookupCodeHOLFinite_installed_return s (ofString "bal_sort_gt")
          _ (sourceFnBody Guest.Software.guestFn_bal_sort_gt) body .one rs
          [.val (.word a0), .val (.word b0), .val (.word kind0)] callee
          (by rw [hcode]; exact hinst) hlk
      subst hsame; subst hrs_eq
      let ent := callEntryStateHOLFinite s callee
      have hlf : InitECandidate.Solver.Wave8Contracts.M15.LocFrame ent
          (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_bal_sort_gt)).2 :=
        InitECandidate.Solver.Wave8Contracts.M15.evaluate_readOnlyProg
          (fun _ => false) (fun _ h => by cases h)
          (sourceFnBody Guest.Software.guestFn_bal_sort_gt) rfl ent hcode
      have hcl := Flapjack.evaluateHOLFiniteState_clock_le ent (sourceFnBody Guest.Software.guestFn_bal_sort_gt)
      rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_bal_sort_gt) with ⟨res, st⟩
      dsimp only [ent] at hrun
      simp only [hrun] at hnt hncr_call ⊢
      rw [show evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_bal_sort_gt) = (res, st) from hrun] at hlf hcl
      dsimp only at hlf hcl hnt hncr_call ⊢
      change st.clock ≤ s.clock - 1 at hcl
      have hsmall : st.clock < s.clock := by omega
      have heff_st : M11.ByteRegionEffect s st Rl := by
        unfold InitECandidate.Solver.Wave8Contracts.M15.LocFrame at hlf
        rw [hlf]
        exact (M11.ByteRegionEffect.refl s Rl).with_locals_clock st.locals st.clock
      cases res with
      | none => right; exact ⟨by simp, by simp, by simp, not_resumes_error⟩
      | some r =>
        cases r with
        | returned rv =>
          dsimp only at hnt ⊢
          rcases rv with ⟨⟨gtw⟩⟩ | fields | ⟨nm, fields⟩
          · have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word gtw) : ValueHOL 64)) .one &&
                shapeEqHOL (shapeOfHOLExact (.val (.word gtw) : ValueHOL 64)) .one) = true := by
              simp [shapeOfHOLExact, shapeEqHOL]
            rw [if_pos hsh] at hnt ⊢
            left
            let resumed := setVarHOLFinite (ofString lname) (.val (.word gtw)) { st with locals := s.locals }
            exact ⟨gtw, resumed, heff_st.with_locals_clock resumed.locals resumed.clock,
              hsmall, rfl, hnt, rfl⟩
          · have hsh : ¬ ((shapeEqHOL (shapeOfHOLExact (.rStruct fields : ValueHOL 64)) .one &&
                shapeEqHOL (shapeOfHOLExact (.rStruct fields : ValueHOL 64)) .one) = true) := by
              cases fields <;> simp [shapeOfHOLExact, shapeEqHOL]
            rw [if_neg hsh]
            right; exact ⟨by simp, by simp, by simp, not_resumes_error⟩
          · have hsh : ¬ ((shapeEqHOL (shapeOfHOLExact (.nStruct nm fields : ValueHOL 64)) .one &&
                shapeEqHOL (shapeOfHOLExact (.nStruct nm fields : ValueHOL 64)) .one) = true) := by
              cases fields <;> simp [shapeOfHOLExact, shapeEqHOL]
            rw [if_neg hsh]
            right; exact ⟨by simp, by simp, by simp, not_resumes_error⟩
        | «break» => right; exact ⟨by simp, by simp, by simp, not_resumes_error⟩
        | «continue» => right; exact ⟨by simp, by simp, by simp, not_resumes_error⟩
        | timeOut => exact absurd rfl hnt
        | error => right; exact ⟨by simp, by simp, by simp, not_resumes_error⟩
        | finalFfi f =>
          right; refine ⟨by simp, by simp, by simp, ?_⟩
          rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        | exception eid ev =>
          right; refine ⟨by simp, by simp, by simp, ?_⟩
          by_cases heid : eid = ofString "TrapErr"
          · subst eid
            rintro (⟨_, h⟩ | ⟨_, _, h, hne⟩)
            · simp at h
            · injection h with h'; injection h' with he1 _; exact hne he1.symm
          · exact False.elim (hncr_call eid ev heid rfl)

private theorem eval_sortW1_while_bre {F : Type}
    (s0 : PanSemStateFiniteExact 64 F)
    (p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 : BitVec 64)
    (_hsrc_choice : src0 = p0 ∨ src0 = aux0)
    (hinv0 : SortMergeCursorInv p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 s0)
    (hnt0 : (evaluateHOLFiniteState s0
      (.while (.op .and [
        .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
        .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))])
        sortW1BodyP)).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s0
      (.while (.op .and [
        .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
        .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))])
        sortW1BodyP)
    (out.1 = none →
      SortMergeCursorInv p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 out.2 ∧
      M11.ByteRegionEffect s0 out.2
        [(p0.toNat, n0.toNat * esz0.toNat), (aux0.toNat, n0.toNat * esz0.toNat)]) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  let Rl : List Ivl := [(p0.toNat, n0.toNat * esz0.toNat), (aux0.toNat, n0.toNat * esz0.toNat)]
  let condE : ExpHOL 64 := .op .and [
    .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
    .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))]
  let loopP : ProgHOL 64 := .while condE sortW1BodyP
  suffices hmain : ∀ (clk : Nat) (s : PanSemStateFiniteExact 64 F), s.clock = clk →
      SortMergeCursorInv p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 s →
      (evaluateHOLFiniteState s loopP).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState s loopP).1 = none →
        SortMergeCursorInv p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 (evaluateHOLFiniteState s loopP).2 ∧
        M11.ByteRegionEffect s (evaluateHOLFiniteState s loopP).2 Rl) ∧
      ((evaluateHOLFiniteState s loopP).1 ≠ none → ¬ Resumes (evaluateHOLFiniteState s loopP).1) by
    exact hmain s0.clock s0 rfl hinv0 hnt0
  intro clk
  induction clk using Nat.strong_induction_on with
  | h clk ih =>
    intro s hclk hPs hnt
    obtain ⟨hcode, hma, hdst, hsrc, hesz, hmid, hright, hkind, hchoice, hn_lt,
      hp_nw, haux_nw, hl_m, hm_r, hr_n, i0, j0, k0, hi, hj, hk, hl_i, hi_m, hm_j, hj_r, hk_eq⟩ := hPs
    obtain ⟨kind0, hkv⟩ := hkind
    have hc := eval_w1_cond_nonneg s i0 mid0 j0 right0 hi hmid hj hright
      (by omega) (by omega) (by omega) (by omega)
    dsimp only [loopP] at hnt ⊢
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    dsimp only [condE] at hnt ⊢
    simp only [hc] at hnt ⊢
    by_cases hlt : i0.toNat < mid0.toNat ∧ j0.toNat < right0.toNat
    · rw [if_pos hlt] at hnt ⊢
      have h1nz : (1 : BitVec 64) ≠ 0 := by decide
      rw [if_pos h1nz] at hnt ⊢
      by_cases hclk0 : s.clock = 0
      · simp [hclk0] at hnt
      · rw [if_neg hclk0] at hnt ⊢
        set d0 := decClockHOLFinite s
        have heff_dec : M11.ByteRegionEffect s d0 Rl :=
          (M11.ByteRegionEffect.refl s Rl).with_locals_clock d0.locals d0.clock
        have hd_clk : d0.clock < clk := by simp [d0, decClockHOLFinite, hclk]; omega
        have hb_clk := Flapjack.evaluateHOLFiniteState_clock_le d0 sortW1BodyP
        have hk_bounds := merge_cursor_bounds left0.toNat mid0.toNat right0.toNat
          i0.toNat j0.toNat k0.toNat hl_i hi_m hm_j hj_r hk_eq
        have hk_lt_n : k0.toNat < n0.toNat := by omega
        dsimp only [sortW1BodyP] at hnt hb_clk ⊢
        rw [evaluateHOLFiniteState_dec_total] at hnt hb_clk ⊢
        have hea : @evalHOLExact 64 F _ d0.toExact (fun a => Classical.propDecidable (d0.memaddrs a))
            (.op .add [.var .local (ofString "src"),
              .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]) =
            some (.val (.word (src0 + i0 * esz0))) :=
          eval_add_mul_exp d0 "src" "i" "esz" src0 i0 esz0 hsrc hi hesz
        have hsh_w : ∀ w : BitVec 64, shapeEqHOL .one (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) = true :=
          fun _ => by simp [shapeOfHOLExact, shapeEqHOL]
        dsimp only at hnt hb_clk ⊢
        rw [hea] at hnt hb_clk ⊢
        dsimp only at hnt hb_clk ⊢
        rw [if_pos (hsh_w _)] at hnt hb_clk ⊢
        set d1 := setVarHOLFinite (ofString "a") (.val (.word (src0 + i0 * esz0))) d0
        have hd1_src : d1.locals.lookup (ofString "src") = some (.val (.word src0)) := by
          simp [d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "a" ≠ ofString "src" by decide]; exact hsrc
        have hd1_j : d1.locals.lookup (ofString "j") = some (.val (.word j0)) := by
          simp [d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "a" ≠ ofString "j" by decide]; exact hj
        have hd1_esz : d1.locals.lookup (ofString "esz") = some (.val (.word esz0)) := by
          simp [d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "a" ≠ ofString "esz" by decide]; exact hesz
        rw [evaluateHOLFiniteState_dec_total] at hnt hb_clk ⊢
        dsimp only at hnt hb_clk ⊢
        have heb : @evalHOLExact 64 F _ d1.toExact (fun a => Classical.propDecidable (d1.memaddrs a))
            (.op .add [.var .local (ofString "src"),
              .panop .mul [.var .local (ofString "j"), .var .local (ofString "esz")]]) =
            some (.val (.word (src0 + j0 * esz0))) :=
          eval_add_mul_exp d1 "src" "j" "esz" src0 j0 esz0 hd1_src hd1_j hd1_esz
        rw [heb] at hnt hb_clk ⊢
        dsimp only at hnt hb_clk ⊢
        rw [if_pos (hsh_w _)] at hnt hb_clk ⊢
        set d2 := setVarHOLFinite (ofString "b") (.val (.word (src0 + j0 * esz0))) d1
        have hd2_a : evalAt d2 (.var .local (ofString "a")) = some (.val (.word (src0 + i0 * esz0))) := by
          simp [evalAt, evalHOLExact, d2, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "b" ≠ ofString "a" by decide]
        have hd2_b : evalAt d2 (.var .local (ofString "b")) = some (.val (.word (src0 + j0 * esz0))) := by
          simp [evalAt, evalHOLExact, d2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hd2_kind : evalAt d2 (.var .local (ofString "kind")) = some (.val (.word kind0)) := by
          simp [evalAt, evalHOLExact, d2, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "b" ≠ ofString "kind" by decide,
            show ofString "a" ≠ ofString "kind" by decide]; exact hkv
        let gtCont : ProgHOL 64 :=
          .seq
            (.ite (.cmp .equal (.var .local (ofString "gt")) (.const 0))
              (.seq
                (.call (some (none, none)) (ofString "memcpy")
                  [.op .add [.var .local (ofString "dst"),
                    .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]],
                   .var .local (ofString "a"),
                   .var .local (ofString "esz")])
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
              (.seq
                (.call (some (none, none)) (ofString "memcpy")
                  [.op .add [.var .local (ofString "dst"),
                    .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]],
                   .var .local (ofString "b"),
                   .var .local (ofString "esz")])
                (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1]))))
            (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
        have hnt_d2 : (evaluateHOLFiniteState d2
            (.decCall (ofString "gt") .one (ofString "bal_sort_gt")
              [.var .local (ofString "a"), .var .local (ofString "b"), .var .local (ofString "kind")]
              gtCont)).1 ≠ some .timeOut := by
          intro heq
          rw [heq] at hnt; exact hnt rfl
        have hgt_spec := eval_decCall_bal_sort_gt_bre d2 "gt"
          (.var .local (ofString "a")) (.var .local (ofString "b")) (.var .local (ofString "kind"))
          (src0 + i0 * esz0) (src0 + j0 * esz0) kind0 gtCont Rl hcode hd2_a hd2_b hd2_kind hnt_d2
        dsimp only at hgt_spec
        rcases hgt_spec with ⟨gtw, s_gt, heff_gt, hgt_clk, hs_gt_loc, hnt_cont, hgt_eq⟩ |
            ⟨hgt_ne, hgt_nc, hgt_nb, hgt_nr⟩
        · rw [hgt_eq] at hnt hb_clk ⊢
          dsimp only [gtCont] at hnt_cont hnt hb_clk ⊢
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt_cont hnt hb_clk ⊢
          have hs_gt_gt : s_gt.locals.lookup (ofString "gt") = some (.val (.word gtw)) := by
            rw [hs_gt_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
          have hs_gt_other : ∀ x, x ≠ ofString "gt" → x ≠ ofString "b" → x ≠ ofString "a" →
              s_gt.locals.lookup x = s.locals.lookup x := by
            intro x hxg hxb hxa
            rw [hs_gt_loc]
            simp [d2, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              Ne.symm hxg, Ne.symm hxb, Ne.symm hxa]
            rfl
          have hev_gt0 : @evalHOLExact 64 F _ s_gt.toExact (fun a => Classical.propDecidable (s_gt.memaddrs a))
              (.cmp .equal (.var .local (ofString "gt")) (.const 0)) =
              some (.val (.word (if gtw = 0 then 1 else 0))) := by
            by_cases hgt0 : gtw = 0 <;>
              simp [evalHOLExact, hs_gt_gt, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hgt0]
          rw [hev_gt0] at hnt_cont hnt hb_clk ⊢
          dsimp only at hnt_cont hnt hb_clk ⊢
          by_cases hgt0 : gtw = 0
          · simp only [hgt0, ↓reduceIte] at hnt_cont hnt hb_clk ⊢
            rw [if_neg (by decide : ¬ ((1 : BitVec 64) = 0))] at hnt_cont hnt hb_clk ⊢
            rw [evaluateHOLFiniteState_seq_line780] at hnt_cont hnt hb_clk ⊢
            have hnt_mc : (evaluateHOLFiniteState s_gt
                (.call (some (none, none)) (ofString "memcpy")
                  [.op .add [.var .local (ofString "dst"),
                    .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]],
                   .var .local (ofString "a"),
                   .var .local (ofString "esz")])).1 ≠ some .timeOut := by
              intro heq
              rcases hmc : evaluateHOLFiniteState s_gt _ with ⟨rmc, smc⟩
              rw [hmc] at heq hnt_cont; dsimp only at heq; subst rmc; exact hnt_cont rfl
            have hs_gt_a : s_gt.locals.lookup (ofString "a") = some (.val (.word (src0 + i0 * esz0))) := by
              rw [hs_gt_loc]
              simp [d2, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "gt" ≠ ofString "a" by decide,
                show ofString "b" ≠ ofString "a" by decide]
            have hspec_mc := eval_sort_merge_copy_var_bre s_gt p0 aux0 n0 esz0 dst0 (src0 + i0 * esz0) k0 "a"
              (heff_gt.code.trans hcode) (heff_gt.memaddrs.trans hma)
              ((hs_gt_other _ (by decide) (by decide) (by decide)).trans hdst)
              hs_gt_a
              ((hs_gt_other _ (by decide) (by decide) (by decide)).trans hk)
              ((hs_gt_other _ (by decide) (by decide) (by decide)).trans hesz)
              hchoice hk_lt_n hp_nw haux_nw hnt_mc
            dsimp only at hspec_mc
            rcases hmc : evaluateHOLFiniteState s_gt
                (.call (some (none, none)) (ofString "memcpy")
                  [.op .add [.var .local (ofString "dst"),
                    .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]],
                   .var .local (ofString "a"),
                   .var .local (ofString "esz")]) with ⟨rmc, s1⟩
            rw [hmc] at hspec_mc hnt_mc
            simp only [hmc] at hnt_cont hnt hb_clk ⊢
            cases rmc with
            | some r =>
              dsimp only at hspec_mc hnt_cont hnt ⊢
              have hnr : ¬ Resumes (some r) := hspec_mc.2 (by simp)
              cases r with
              | «continue» =>
                exfalso
                have hnc := evaluate_noTopContinue
                  (.call (some (none, none)) (ofString "memcpy")
                    [.op .add [.var .local (ofString "dst"),
                      .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]],
                     .var .local (ofString "a"),
                     .var .local (ofString "esz")]) rfl s_gt
                exact hnc (by rw [hmc])
              | «break» =>
                exfalso
                have hnb := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak
                  (.call (some (none, none)) (ofString "memcpy")
                    [.op .add [.var .local (ofString "dst"),
                      .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]],
                     .var .local (ofString "a"),
                     .var .local (ofString "esz")]) rfl s_gt
                exact hnb (by rw [hmc])
              | returned v => exact ⟨fun h => by simp at h, fun _ => hnr⟩
              | exception e v => exact ⟨fun h => by simp at h, fun _ => hnr⟩
              | timeOut => exact False.elim (hnt_mc (by simp only [hmc]))
              | error => exact ⟨fun h => by simp at h, fun _ => hnr⟩
              | finalFfi f => exact ⟨fun h => by simp at h, fun _ => hnr⟩
            | none =>
              dsimp only at hspec_mc hnt_cont hnt hb_clk ⊢
              obtain ⟨heff_mc, hloc1⟩ := hspec_mc.1 rfl
              have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word i0)) := by
                rw [hloc1]; exact (hs_gt_other _ (by decide) (by decide) (by decide)).trans hi
              obtain ⟨hinc_i, heff_i⟩ := eval_assign_inc1_bre s1 "i" i0 Rl hs1_i
              rw [hinc_i] at hnt_cont hnt hb_clk ⊢
              dsimp only at hnt_cont hnt hb_clk ⊢
              set s2 := setVarHOLFinite (ofString "i") (.val (.word (i0 + 1))) s1
              have hs2_k : s2.locals.lookup (ofString "k") = some (.val (.word k0)) := by
                simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "i" ≠ ofString "k" by decide, hloc1]
                exact (hs_gt_other _ (by decide) (by decide) (by decide)).trans hk
              obtain ⟨hinc_k, heff_k⟩ := eval_assign_inc1_bre s2 "k" k0 Rl hs2_k
              rw [hinc_k] at hnt_cont hnt hb_clk ⊢
              dsimp only at hnt_cont hnt hb_clk ⊢
              set s3 := setVarHOLFinite (ofString "k") (.val (.word (k0 + 1))) s2
              set s_end_locals := HolFiniteMapExact.resVarEq
                (HolFiniteMapExact.resVarEq
                  (HolFiniteMapExact.resVarEq s3.locals
                    (ofString "gt", d2.locals.lookup (ofString "gt")))
                  (ofString "b", d1.locals.lookup (ofString "b")))
                (ofString "a", d0.locals.lookup (ofString "a"))
              set s_end : PanSemStateFiniteExact 64 F := { s3 with locals := s_end_locals }
              have heff_d0_d2 : M11.ByteRegionEffect d0 d2 Rl :=
                (M11.ByteRegionEffect.refl d0 Rl).with_locals_clock d2.locals d2.clock
              have heff_body : M11.ByteRegionEffect d0 s_end Rl :=
                ((((heff_d0_d2.trans heff_gt).trans heff_mc).trans heff_i).trans heff_k).with_locals_clock _ _
              have hi1_nat : (i0 + 1).toNat = i0.toNat + 1 := by
                rw [BitVec.toNat_add]; change (i0.toNat + 1) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
              have hk1_nat : (k0 + 1).toNat = k0.toNat + 1 := by
                rw [BitVec.toNat_add]; change (k0.toNat + 1) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
              have hstep_eq := merge_cursor_step_left mid0.toNat i0.toNat j0.toNat k0.toNat hk_eq
              have hres_ne : ∀ (m : HolFiniteMapExact MlS (ValueHOL 64)) (v : MlS)
                  (old : Option (ValueHOL 64)) (x : MlS), x ≠ v →
                  (HolFiniteMapExact.resVarEq m (v, old)).lookup x = m.lookup x := by
                intro m v old x hxv
                cases old <;>
                  simp [HolFiniteMapExact.resVarEq, FDOMSUB_HOL, FUPDATE_HOL, hxv, Ne.symm hxv]
              have hloc_end : ∀ x, x ≠ ofString "a" → x ≠ ofString "b" → x ≠ ofString "gt" →
                  s_end.locals.lookup x = s3.locals.lookup x := by
                intro x hxa hxb hxg
                dsimp only [s_end]
                rw [hres_ne _ _ _ _ hxa, hres_ne _ _ _ _ hxb, hres_ne _ _ _ _ hxg]
              have hs3_other : ∀ x, x ≠ ofString "k" → x ≠ ofString "i" →
                  x ≠ ofString "gt" → x ≠ ofString "b" → x ≠ ofString "a" →
                  s_end.locals.lookup x = s.locals.lookup x := by
                intro x hxk hxi hxg hxb hxa
                rw [hloc_end x hxa hxb hxg]
                simp [s3, s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  Ne.symm hxk, Ne.symm hxi, hloc1]
                exact hs_gt_other x hxg hxb hxa
              have hPs_end : SortMergeCursorInv p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 s_end := by
                refine ⟨heff_body.code.trans hcode, heff_body.memaddrs.trans hma,
                  (hs3_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hdst,
                  (hs3_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsrc,
                  (hs3_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hesz,
                  (hs3_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hmid,
                  (hs3_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hright,
                  ⟨kind0, (hs3_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hkv⟩,
                  hchoice, hn_lt, hp_nw, haux_nw, hl_m, hm_r, hr_n,
                  i0 + 1, j0, k0 + 1, ?_, ?_, ?_, ?_, ?_, hm_j, hj_r, ?_⟩
                · rw [hloc_end _ (by decide) (by decide) (by decide)]
                  simp [s3, s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "k" ≠ ofString "i" by decide]
                · exact (hs3_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hj
                · rw [hloc_end _ (by decide) (by decide) (by decide)]
                  simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                · rw [hi1_nat]; omega
                · rw [hi1_nat]; omega
                · rw [hk1_nat, hi1_nat]; exact hstep_eq
              have hclk_end : s_end.clock < clk := by
                have hle_cont := Flapjack.evaluateHOLFiniteState_clock_le s_gt gtCont
                dsimp only [gtCont] at hle_cont
                rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hev_gt0] at hle_cont
                simp only [hgt0, ↓reduceIte] at hle_cont
                rw [if_neg (by decide : ¬ ((1 : BitVec 64) = 0)), evaluateHOLFiniteState_seq_line780, hmc] at hle_cont
                dsimp only at hle_cont
                rw [hinc_i] at hle_cont; dsimp only at hle_cont
                rw [hinc_k] at hle_cont; dsimp only at hle_cont
                have hd2_clk : d2.clock = d0.clock := rfl
                change s3.clock ≤ s_gt.clock at hle_cont
                change s3.clock < clk
                omega
              have jih := ih s_end.clock hclk_end s_end rfl hPs_end hnt
              exact ⟨fun hn => ⟨(jih.1 hn).1, (heff_dec.trans heff_body).trans (jih.1 hn).2⟩, jih.2⟩
          · simp only [hgt0, ↓reduceIte] at hnt_cont hnt hb_clk ⊢
            rw [evaluateHOLFiniteState_seq_line780] at hnt_cont hnt hb_clk ⊢
            have hnt_mc : (evaluateHOLFiniteState s_gt
                (.call (some (none, none)) (ofString "memcpy")
                  [.op .add [.var .local (ofString "dst"),
                    .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]],
                   .var .local (ofString "b"),
                   .var .local (ofString "esz")])).1 ≠ some .timeOut := by
              intro heq
              rcases hmc : evaluateHOLFiniteState s_gt _ with ⟨rmc, smc⟩
              rw [hmc] at heq hnt_cont; dsimp only at heq; subst rmc; exact hnt_cont rfl
            have hs_gt_b : s_gt.locals.lookup (ofString "b") = some (.val (.word (src0 + j0 * esz0))) := by
              rw [hs_gt_loc]
              simp [d2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "gt" ≠ ofString "b" by decide]
            have hspec_mc := eval_sort_merge_copy_var_bre s_gt p0 aux0 n0 esz0 dst0 (src0 + j0 * esz0) k0 "b"
              (heff_gt.code.trans hcode) (heff_gt.memaddrs.trans hma)
              ((hs_gt_other _ (by decide) (by decide) (by decide)).trans hdst)
              hs_gt_b
              ((hs_gt_other _ (by decide) (by decide) (by decide)).trans hk)
              ((hs_gt_other _ (by decide) (by decide) (by decide)).trans hesz)
              hchoice hk_lt_n hp_nw haux_nw hnt_mc
            dsimp only at hspec_mc
            rcases hmc : evaluateHOLFiniteState s_gt
                (.call (some (none, none)) (ofString "memcpy")
                  [.op .add [.var .local (ofString "dst"),
                    .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]],
                   .var .local (ofString "b"),
                   .var .local (ofString "esz")]) with ⟨rmc, s1⟩
            rw [hmc] at hspec_mc hnt_cont hnt hb_clk
            cases rmc with
            | some r =>
              dsimp only at hspec_mc hnt_cont hnt ⊢
              have hnr : ¬ Resumes (some r) := hspec_mc.2 (by simp)
              cases r with
              | «continue» =>
                exfalso
                have hnc := evaluate_noTopContinue
                  (.call (some (none, none)) (ofString "memcpy")
                    [.op .add [.var .local (ofString "dst"),
                      .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]],
                     .var .local (ofString "b"),
                     .var .local (ofString "esz")]) rfl s_gt
                exact hnc (by rw [hmc])
              | «break» =>
                exfalso
                have hnb := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak
                  (.call (some (none, none)) (ofString "memcpy")
                    [.op .add [.var .local (ofString "dst"),
                      .panop .mul [.var .local (ofString "k"), .var .local (ofString "esz")]],
                     .var .local (ofString "b"),
                     .var .local (ofString "esz")]) rfl s_gt
                exact hnb (by rw [hmc])
              | returned v => exact ⟨fun h => by simp at h, fun _ => hnr⟩
              | exception e v => exact ⟨fun h => by simp at h, fun _ => hnr⟩
              | timeOut => exact False.elim (hnt_mc (by simp only [hmc]))
              | error => exact ⟨fun h => by simp at h, fun _ => hnr⟩
              | finalFfi f => exact ⟨fun h => by simp at h, fun _ => hnr⟩
            | none =>
              dsimp only at hspec_mc hnt_cont hnt hb_clk ⊢
              obtain ⟨heff_mc, hloc1⟩ := hspec_mc.1 rfl
              have hs1_j : s1.locals.lookup (ofString "j") = some (.val (.word j0)) := by
                rw [hloc1]; exact (hs_gt_other _ (by decide) (by decide) (by decide)).trans hj
              obtain ⟨hinc_j, heff_j⟩ := eval_assign_inc1_bre s1 "j" j0 Rl hs1_j
              rw [hinc_j] at hnt_cont hnt hb_clk ⊢
              dsimp only at hnt_cont hnt hb_clk ⊢
              set s2 := setVarHOLFinite (ofString "j") (.val (.word (j0 + 1))) s1
              have hs2_k : s2.locals.lookup (ofString "k") = some (.val (.word k0)) := by
                simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "j" ≠ ofString "k" by decide, hloc1]
                exact (hs_gt_other _ (by decide) (by decide) (by decide)).trans hk
              obtain ⟨hinc_k, heff_k⟩ := eval_assign_inc1_bre s2 "k" k0 Rl hs2_k
              rw [hinc_k] at hnt_cont hnt hb_clk ⊢
              dsimp only at hnt_cont hnt hb_clk ⊢
              set s3 := setVarHOLFinite (ofString "k") (.val (.word (k0 + 1))) s2
              set s_end_locals := HolFiniteMapExact.resVarEq
                (HolFiniteMapExact.resVarEq
                  (HolFiniteMapExact.resVarEq s3.locals
                    (ofString "gt", d2.locals.lookup (ofString "gt")))
                  (ofString "b", d1.locals.lookup (ofString "b")))
                (ofString "a", d0.locals.lookup (ofString "a"))
              set s_end : PanSemStateFiniteExact 64 F := { s3 with locals := s_end_locals }
              have heff_d0_d2 : M11.ByteRegionEffect d0 d2 Rl :=
                (M11.ByteRegionEffect.refl d0 Rl).with_locals_clock d2.locals d2.clock
              have heff_body : M11.ByteRegionEffect d0 s_end Rl :=
                ((((heff_d0_d2.trans heff_gt).trans heff_mc).trans heff_j).trans heff_k).with_locals_clock _ _
              have hj1_nat : (j0 + 1).toNat = j0.toNat + 1 := by
                rw [BitVec.toNat_add]; change (j0.toNat + 1) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
              have hk1_nat : (k0 + 1).toNat = k0.toNat + 1 := by
                rw [BitVec.toNat_add]; change (k0.toNat + 1) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
              have hstep_eq := merge_cursor_step_right mid0.toNat i0.toNat j0.toNat k0.toNat hk_eq
              have hres_ne : ∀ (m : HolFiniteMapExact MlS (ValueHOL 64)) (v : MlS)
                  (old : Option (ValueHOL 64)) (x : MlS), x ≠ v →
                  (HolFiniteMapExact.resVarEq m (v, old)).lookup x = m.lookup x := by
                intro m v old x hxv
                cases old <;>
                  simp [HolFiniteMapExact.resVarEq, FDOMSUB_HOL, FUPDATE_HOL, hxv, Ne.symm hxv]
              have hloc_end : ∀ x, x ≠ ofString "a" → x ≠ ofString "b" → x ≠ ofString "gt" →
                  s_end.locals.lookup x = s3.locals.lookup x := by
                intro x hxa hxb hxg
                dsimp only [s_end]
                rw [hres_ne _ _ _ _ hxa, hres_ne _ _ _ _ hxb, hres_ne _ _ _ _ hxg]
              have hs3_other : ∀ x, x ≠ ofString "k" → x ≠ ofString "j" →
                  x ≠ ofString "gt" → x ≠ ofString "b" → x ≠ ofString "a" →
                  s_end.locals.lookup x = s.locals.lookup x := by
                intro x hxk hxj hxg hxb hxa
                rw [hloc_end x hxa hxb hxg]
                simp [s3, s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  Ne.symm hxk, Ne.symm hxj, hloc1]
                exact hs_gt_other x hxg hxb hxa
              have hPs_end : SortMergeCursorInv p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 s_end := by
                refine ⟨heff_body.code.trans hcode, heff_body.memaddrs.trans hma,
                  (hs3_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hdst,
                  (hs3_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsrc,
                  (hs3_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hesz,
                  (hs3_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hmid,
                  (hs3_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hright,
                  ⟨kind0, (hs3_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hkv⟩,
                  hchoice, hn_lt, hp_nw, haux_nw, hl_m, hm_r, hr_n,
                  i0, j0 + 1, k0 + 1, ?_, ?_, ?_, hl_i, hi_m, ?_, ?_, ?_⟩
                · exact (hs3_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hi
                · rw [hloc_end _ (by decide) (by decide) (by decide)]
                  simp [s3, s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "k" ≠ ofString "j" by decide]
                · rw [hloc_end _ (by decide) (by decide) (by decide)]
                  simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                · rw [hj1_nat]; omega
                · rw [hj1_nat]; omega
                · rw [hk1_nat, hj1_nat]; exact hstep_eq
              have hclk_end : s_end.clock < clk := by
                have hle_cont := Flapjack.evaluateHOLFiniteState_clock_le s_gt gtCont
                dsimp only [gtCont] at hle_cont
                rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hev_gt0] at hle_cont
                simp only [hgt0, ↓reduceIte] at hle_cont
                rw [evaluateHOLFiniteState_seq_line780, hmc] at hle_cont
                dsimp only at hle_cont
                rw [hinc_j] at hle_cont; dsimp only at hle_cont
                rw [hinc_k] at hle_cont; dsimp only at hle_cont
                have hd2_clk : d2.clock = d0.clock := rfl
                change s3.clock ≤ s_gt.clock at hle_cont
                change s3.clock < clk
                omega
              have jih := ih s_end.clock hclk_end s_end rfl hPs_end hnt
              exact ⟨fun hn => ⟨(jih.1 hn).1, (heff_dec.trans heff_body).trans (jih.1 hn).2⟩, jih.2⟩
        · rcases hgt_out : evaluateHOLFiniteState d2
            (.decCall (ofString "gt") .one (ofString "bal_sort_gt")
              [.var .local (ofString "a"), .var .local (ofString "b"), .var .local (ofString "kind")]
              gtCont) with ⟨rg, sg⟩
          rw [hgt_out] at hgt_ne hgt_nc hgt_nb hgt_nr hnt_d2
          simp only [show evaluateHOLFiniteState d2
            (.decCall (ofString "gt") .one (ofString "bal_sort_gt")
              [.var .local (ofString "a"), .var .local (ofString "b"), .var .local (ofString "kind")]
              gtCont) = (rg, sg) from hgt_out] at hnt ⊢
          dsimp only at hgt_ne hgt_nc hgt_nb hgt_nr hnt_d2 hnt ⊢
          cases rg with
          | none => exact absurd rfl hgt_ne
          | some r =>
            cases r with
            | «continue» => exact absurd rfl hgt_nc
            | «break» => exact absurd rfl hgt_nb
            | timeOut => exact absurd rfl hnt_d2
            | returned v => exact ⟨fun h => by simp at h, fun _ => hgt_nr⟩
            | exception e v => exact ⟨fun h => by simp at h, fun _ => hgt_nr⟩
            | error => exact ⟨fun h => by simp at h, fun _ => hgt_nr⟩
            | finalFfi f => exact ⟨fun h => by simp at h, fun _ => hgt_nr⟩
    · rw [if_neg hlt] at hnt ⊢
      have h0nz : ¬ ((0 : BitVec 64) ≠ 0) := by decide
      rw [if_neg h0nz]
      exact ⟨fun _ => ⟨⟨hcode, hma, hdst, hsrc, hesz, hmid, hright, ⟨kind0, hkv⟩, hchoice, hn_lt,
        hp_nw, haux_nw, hl_m, hm_r, hr_n, i0, j0, k0, hi, hj, hk, hl_i, hi_m, hm_j, hj_r, hk_eq⟩,
        M11.ByteRegionEffect.refl s Rl⟩, fun h => False.elim (h rfl)⟩

private theorem eval_sort_tail_loops_bre {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 : BitVec 64)
    (hinv : SortMergeCursorInv p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 s)
    (hnt : (evaluateHOLFiniteState s
      (.seq
        (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) sortW2BodyP)
        (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) sortW3BodyP))).1 ≠
          some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.seq
        (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) sortW2BodyP)
        (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) sortW3BodyP))
    (out.1 = none →
      SortMergeCursorInv p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 out.2 ∧
      M11.ByteRegionEffect s out.2
        [(p0.toNat, n0.toNat * esz0.toNat), (aux0.toNat, n0.toNat * esz0.toNat)]) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  have hnt_first : (evaluateHOLFiniteState s
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) sortW2BodyP)).1 ≠
        some .timeOut := by
    intro heq
    rcases hf : evaluateHOLFiniteState s
        (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) sortW2BodyP) with ⟨r, mid⟩
    rw [hf] at heq hnt; dsimp only at heq; subst r; exact hnt rfl
  have hfirst_spec := eval_sortW2_while_bre s p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 hinv hnt_first
  dsimp only at hfirst_spec
  rcases hfirst : evaluateHOLFiniteState s
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) sortW2BodyP) with ⟨r, mid⟩
  rw [hfirst] at hfirst_spec
  cases r with
  | some r =>
    dsimp only at hnt hfirst_spec ⊢
    exact ⟨fun h => by simp at h, hfirst_spec.2⟩
  | none =>
    dsimp only at hnt hfirst_spec ⊢
    rw [hfirst] at hnt
    dsimp only at hnt
    obtain ⟨hinv_mid, heff_mid⟩ := hfirst_spec.1 rfl
    have hlast := eval_sortW3_while_bre mid p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 hinv_mid hnt
    exact ⟨fun hn => ⟨(hlast.1 hn).1, heff_mid.trans (hlast.1 hn).2⟩, hlast.2⟩

theorem lookup_sort_elems :
    originalRuntimeCode.lookup (ofString "sort_elems") =
      some ([(ofString "p", .one), (ofString "n", .one), (ofString "esz", .one),
             (ofString "kind", .one), (ofString "tmp", .one)],
        sourceFnBody Guest.Software.guestFn_sort_elems, .one) :=
  lookup_of_guestAst_getElem 430 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_sort_elems) rfl

theorem eval_call_sort_elems_lt2 {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (pExp nExp eszExp kindExp tmpExp : ExpHOL 64)
    (p0 n0 esz0 kind0 tmp0 : BitVec 64)
    (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hp : evalAt s pExp = some (.val (.word p0)))
    (hn : evalAt s nExp = some (.val (.word n0)))
    (hesz : evalAt s eszExp = some (.val (.word esz0)))
    (hkind : evalAt s kindExp = some (.val (.word kind0)))
    (htmp : evalAt s tmpExp = some (.val (.word tmp0)))
    (hlt2 : n0.toNat < 2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "sort_elems")
        [pExp, nExp, eszExp, kindExp, tmpExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "sort_elems")
        [pExp, nExp, eszExp, kindExp, tmpExp])
    out.1 = none ∧ out.2.locals = s.locals ∧ out.2.globals = s.globals ∧
    out.2.memory = s.memory ∧ WkBlockTxEnc.HeapByteEff s out.2 Rl gw := by
  intro out; dsimp only [out]
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [pExp, nExp, eszExp, kindExp, tmpExp] =
      some [.val (.word p0), .val (.word n0), .val (.word esz0), .val (.word kind0), .val (.word tmp0)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalAt, hp, hn, hesz, hkind, htmp]
  let cmap := ((((HolFiniteMapExact.empty.update (ofString "p", ValueHOL.val (.word p0))).update
    (ofString "n", ValueHOL.val (.word n0))).update
    (ofString "esz", ValueHOL.val (.word esz0))).update
    (ofString "kind", ValueHOL.val (.word kind0))).update
    (ofString "tmp", ValueHOL.val (.word tmp0))
  have hlk : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup (ofString "sort_elems")
      [.val (.word p0), .val (.word n0), .val (.word esz0), .val (.word kind0), .val (.word tmp0)] =
      some (sourceFnBody Guest.Software.guestFn_sort_elems, cmap, .one) := by
    have h12 : ofString "p" ≠ ofString "n" := by decide
    have h13 : ofString "p" ≠ ofString "esz" := by decide
    have h14 : ofString "p" ≠ ofString "kind" := by decide
    have h15 : ofString "p" ≠ ofString "tmp" := by decide
    have h23 : ofString "n" ≠ ofString "esz" := by decide
    have h24 : ofString "n" ≠ ofString "kind" := by decide
    have h25 : ofString "n" ≠ ofString "tmp" := by decide
    have h34 : ofString "esz" ≠ ofString "kind" := by decide
    have h35 : ofString "esz" ≠ ofString "tmp" := by decide
    have h45 : ofString "kind" ≠ ofString "tmp" := by decide
    have hraw : lookupCodeHOLExact s.code.lookup (ofString "sort_elems")
        [.val (.word p0), .val (.word n0), .val (.word esz0), .val (.word kind0), .val (.word tmp0)] =
        some (sourceFnBody Guest.Software.guestFn_sort_elems, (fun key => if key = ofString "tmp" then some (.val (.word tmp0))
          else if key = ofString "kind" then some (.val (.word kind0))
          else if key = ofString "esz" then some (.val (.word esz0))
          else if key = ofString "n" then some (.val (.word n0))
          else if key = ofString "p" then some (.val (.word p0)) else none), .one) := by
      rw [hcode]
      simp [lookupCodeHOLExact, lookup_sort_elems, shapeOfHOLExact, shapeEqHOL,
        h12, h13, h14, h15, h23, h24, h25, h34, h35, h45]
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite
    split
    · rename_i hm; rw [hraw] at hm; cases hm
    · rename_i b l r hf
      have hinj := Option.some.inj (hf.symm.trans hraw)
      obtain ⟨rfl, hr⟩ := Prod.mk.inj hinj
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
      apply congrArg (fun locals => some (sourceFnBody Guest.Software.guestFn_sort_elems, locals, ShapeHOL.one))
      apply HolFiniteMapExact.ext
      funext key
      by_cases k5 : key = ofString "tmp"
      · subst key; simp [cmap, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
      · by_cases k4 : key = ofString "kind"
        · subst key; simp [cmap, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, h45, Ne.symm h45]
        · by_cases k3 : key = ofString "esz"
          · subst key; simp [cmap, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, h34, Ne.symm h34, h35, Ne.symm h35]
          · by_cases k2 : key = ofString "n"
            · subst key; simp [cmap, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, h23, Ne.symm h23, h24, Ne.symm h24, h25, Ne.symm h25]
            · by_cases k1 : key = ofString "p"
              · subst key; simp [cmap, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, h12, Ne.symm h12, h13, Ne.symm h13, h14, Ne.symm h14, h15, Ne.symm h15]
              · simp [cmap, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY,
                  k1, k2, k3, k4, k5, Ne.symm k1, Ne.symm k2, Ne.symm k3, Ne.symm k4, Ne.symm k5]
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set ent := callEntryStateHOLFinite s cmap
    have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "tmp" ≠ ofString "n" by decide,
        show ofString "kind" ≠ ofString "n" by decide,
        show ofString "esz" ≠ ofString "n" by decide]
    have hbody_step : ∃ tailProg,
        sourceFnBody Guest.Software.guestFn_sort_elems =
          .seq (.ite (.cmp .lower (.var .local (ofString "n")) (.const 2#64))
            (.return (.const 0#64)) .skip) tailProg := ⟨_, rfl⟩
    obtain ⟨tailProg, hbeq⟩ := hbody_step
    rw [hbeq, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
    have hcnd : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
        (.cmp .lower (.var .local (ofString "n")) (.const 2#64)) =
        some (.val (.word 1#64)) := by
      have hbv : n0 < 2#64 := BitVec.lt_def.2 hlt2
      simp [evalHOLExact, hent_n, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hbv]
    rw [hcnd]; dsimp only
    have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
    rw [if_neg h10, evaluateHOLFiniteState_return]
    have hc0 : @evalHOLExact 64 F _ ent.toExact
        (fun a => Classical.propDecidable (ent.memaddrs a)) (.const 0#64) =
        some (.val (.word 0#64)) := rfl
    rw [hc0]
    have hsz : sizeOfShapeWithContextHOL ent.structs ShapeHOL.one ≤ 32 := by
      simp [sizeOfShapeWithContextHOL]
    have hsh1 : shapeEqHOL ShapeHOL.one ShapeHOL.one = true := by simp [shapeEqHOL]
    simp only [shapeOfHOLExact, hsz, ↓reduceIte]
    rw [if_pos hsh1]
    have hlf : M13.LocFrame s { ent.emptyLocalsHOLFinite with locals := s.locals } := by
      cases s; rfl
    exact ⟨rfl, rfl, rfl, rfl, WkBlockTxEnc.HeapByteEff.of_locFrame hAR hlf Rl gw⟩

private theorem globalsKept_journal_n_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (gw : List String) (hjn : "journal_n" ∈ gw) :
    GlobalsKept gw s (setGlobalHOLFinite (ofString "journal_n") (.val (.word 0#64)) s) := by
  intro k hk
  have hne : k ≠ ofString "journal_n" := by
    intro he
    apply hk
    exact List.mem_map.mpr ⟨"journal_n", hjn, he.symm⟩
  simp [setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]

private theorem recordsKept_journal_n_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl)
    (keep : List (String × List Nat)) :
    RecordsKept R keep s (setGlobalHOLFinite (ofString "journal_n") (.val (.word 0#64)) s) := by
  intro _ _ _ _ _ _
  rfl

private theorem worldTypedWith_set_journal_n_zero {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hAs : ArenaReady s) (hWTW : WorldTypedWith s S Nd) :
    let s' := setGlobalHOLFinite (ofString "journal_n") (.val (.word 0#64)) s
    WorldTypedWith s' S Nd ∧ worldOwned s' S Nd = worldOwned s S Nd := by
  intro s'
  obtain ⟨hT, hJ, hF, hTr⟩ := hWTW
  have hAs' : ArenaReady s' :=
    arenaReady_setGlobal_word_ne hAs (ofString "journal_n") 0#64
      (by decide) (by decide) (by decide)
  have hmemW : memW s' = memW s := rfl
  have hhdr : hdr s' = hdr s := rfl
  have hnodeF : nodeF s' = nodeF s := rfl
  have hfp : htabFootprint s' = htabFootprint s := rfl
  have hhWF : ∀ t, HtabWF s t → HtabWF s' t := fun t h =>
    R13Shards.htabWF_congr_unhit hAs.1 hAs'.1 h (fun _ _ _ _ _ => rfl)
  have hlstOK : ∀ l, LstOK s' l ↔ LstOK s l := fun _ => Iff.rfl
  have hhVals : htabValues s' = htabValues s := rfl
  have hwordsOK : ∀ i, WordsOK s' i ↔ WordsOK s i := fun _ => Iff.rfl
  have halloc : ∀ i, Allocated s' i ↔ Allocated s i := by
    intro i
    simp only [Allocated, s',
      globN_setGlobal_ne s (ofString "journal_n") _ "heap_ptr" (by decide),
      globN_setGlobal_ne s (ofString "journal_n") _ "scratch_ptr" (by decide)]
  have hbo_eq : globN s' "bo" = globN s "bo" :=
    globN_setGlobal_ne s (ofString "journal_n") _ "bo" (by decide)
  have hws_eq : globN s' "ws" = globN s "ws" :=
    globN_setGlobal_ne s (ofString "journal_n") _ "ws" (by decide)
  have hbs_eq : globN s' "bs" = globN s "bs" :=
    globN_setGlobal_ne s (ofString "journal_n") _ "bs" (by decide)
  have hts_eq : globN s' "ts" = globN s "ts" :=
    globN_setGlobal_ne s (ofString "journal_n") _ "ts" (by decide)
  have hba_eq : globN s' "bal_accounts" = globN s "bal_accounts" :=
    globN_setGlobal_ne s (ofString "journal_n") _ "bal_accounts" (by decide)
  have hbia_eq : globN s' "bal_idx_accts" = globN s "bal_idx_accts" :=
    globN_setGlobal_ne s (ofString "journal_n") _ "bal_idx_accts" (by decide)
  have hbis_eq : globN s' "bal_idx_stor" = globN s "bal_idx_stor" :=
    globN_setGlobal_ne s (ofString "journal_n") _ "bal_idx_stor" (by decide)
  have hjc_eq : globN s' "journal_cap" = globN s "journal_cap" :=
    globN_setGlobal_ne s (ofString "journal_n") _ "journal_cap" (by decide)
  have hjr_eq : globN s' "journal" = globN s "journal" :=
    globN_setGlobal_ne s (ofString "journal_n") _ "journal" (by decide)
  have hjn_zero : globN s' "journal_n" = 0 := by
    simpa [s'] using globN_setGlobal_same s "journal_n" 0#64
  have hbalRecs : balRecords s' = balRecords s := by
    simp only [balRecords, hba_eq, hhdr, hnodeF, hmemW]
  have hbalObjs : balObjects s' = balObjects s := by
    simp only [balObjects, hbalRecs, lstObjects, hhVals, hmemW]
  have hboObjs : blockOutObjects s' = blockOutObjects s := by
    simp only [blockOutObjects, hbo_eq, hmemW]
  have hgb_ne : ∀ gn ∈ globalBuffers, ofString gn.1 ≠ ofString "journal_n" := by decide
  have hgb_map :
      (globalBuffers.map fun gn => (globN s' gn.1, if globN s' gn.1 = 0 then 0 else gn.2)) =
      (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) := by
    apply List.map_congr_left
    intro gn hgn
    have hge : globN s' gn.1 = globN s gn.1 :=
      globN_setGlobal_ne s (ofString "journal_n") _ gn.1 (hgb_ne gn hgn)
    rw [hge]
  have hfixObjs : fixedObjects s' = fixedObjects s := by
    simp only [fixedObjects, hgb_map, hjc_eq, hjr_eq, hboObjs, hbalObjs]
  have hnodeHeap : NodeHeap s' Nd ↔ NodeHeap s Nd := by
    simp only [NodeHeap, hmemW, halloc, hwordsOK, nodeIvl, KeyIn, NibblesOK]; exact Iff.rfl
  have hnodeExt : nodeExtents s' Nd = nodeExtents s Nd := rfl
  have hrecR_ws : ∀ ks, recRoles s' "ws" ks = recRoles s "ws" ks := fun _ => by
    simp only [recRoles, hws_eq, hmemW]
  have hrecR_bs : ∀ ks, recRoles s' "bs" ks = recRoles s "bs" ks := fun _ => by
    simp only [recRoles, hbs_eq, hmemW]
  have hrecR_ts : ∀ ks, recRoles s' "ts" ks = recRoles s "ts" ks := fun _ => by
    simp only [recRoles, hts_eq, hmemW]
  have hnest_bs : nestRoles s' "bs" "bs.inner" = nestRoles s "bs" "bs.inner" := by
    simp only [nestRoles, hbs_eq, hmemW, hhVals]
  have hnest_ts : nestRoles s' "ts" "ts.inner" = nestRoles s "ts" "ts.inner" := by
    simp only [nestRoles, hts_eq, hmemW, hhVals]
  have hwrs : worldRoleSlots s' = worldRoleSlots s := by
    simp only [worldRoleSlots, hrecR_ws, hrecR_bs, hrecR_ts, hba_eq, hbia_eq, hbis_eq,
      hnest_bs, hnest_ts, hbalRecs, hmemW]
  have hjrs : journalRoleSlots s' = [] := by
    simp [journalRoleSlots, hjn_zero]
  have hwo : worldOwned s' S Nd = worldOwned s S Nd := by
    simp only [worldOwned, hfp, hfixObjs, hnodeExt]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hwo⟩
  · obtain ⟨hnd, htf, htp, hws_s, hbs_s, hts_s, hgt_s, hb_in, ht_in, hbal_t, hbo_t, hrol⟩ := hT
    refine ⟨hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      refine ⟨hhWF t (htf t ht).1, fun i hi => ?_⟩
      rw [hfp] at hi
      rw [hfixObjs]
      exact ⟨(halloc i).2 ((htf t ht).2 i hi).1, ((htf t ht).2 i hi).2⟩
    · simpa only [hfp] using htp
    · simpa only [hws_eq, hmemW] using hws_s
    · simpa only [hbs_eq, hmemW] using hbs_s
    · simpa only [hts_eq, hmemW] using hts_s
    · intro g hg
      have hg_ne : ofString g ≠ ofString "journal_n" := by
        simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl <;> decide
      rw [globN_setGlobal_ne s (ofString "journal_n") _ g hg_ne]
      exact hgt_s g hg
    · simpa only [hbs_eq, hmemW, HtabValuesIn, hhdr, hnodeF] using hb_in
    · simpa only [hts_eq, hmemW, HtabValuesIn, hhdr, hnodeF] using ht_in
    · simpa only [hbalRecs, hmemW, hlstOK, hhVals] using hbal_t
    · simpa only [hbo_eq, hmemW, hlstOK] using hbo_t
    · rw [hwrs, hjrs]
      refine ⟨fun a ha => ?_, hrol.2.1, fun _ ha => by simp at ha⟩
      rw [List.append_nil] at ha
      exact hrol.1 a (List.mem_append_left _ ha)
  · refine ⟨by rw [hjn_zero]; exact Nat.zero_le _, ?_, ?_, ?_⟩
    · rw [hjc_eq]; exact hJ.2.1
    · rw [hjc_eq, hjr_eq]
      rcases hJ.2.2.1 with h0 | ⟨ha, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨(halloc _).2 ha, (hwordsOK _).2 hw⟩
    · intro i hi; rw [hjn_zero] at hi; omega
  · unfold FixedTyped; rw [hfixObjs]
    exact ⟨fun i hi => (hF.1 i hi).elim Or.inl (fun h => Or.inr ⟨(halloc i).2 h.1, (hwordsOK i).2 h.2⟩), hF.2⟩
  · unfold TriesTypedWith
    refine ⟨hnodeHeap.2 hTr.1, ?_, ?_⟩
    · rw [hnodeExt, hfixObjs]; simpa only [hfp] using hTr.2.1
    · simpa only [hws_eq, hmemW, hfp, hhdr, hnodeF] using hTr.2.2

theorem worldStepSc_set_journal_n_zero {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    (s : PanSemStateFiniteExact 64 F) (r : Option (PanSemResultExact 64))
    (hAs : ArenaReady s) (hjn : "journal_n" ∈ gw) :
    WorldStepSc R gw keep NoExtra s r
      (setGlobalHOLFinite (ofString "journal_n") (.val (.word 0#64)) s) := by
  set s' := setGlobalHOLFinite (ofString "journal_n") (.val (.word 0#64)) s
  have hAs' : ArenaReady s' :=
    arenaReady_setGlobal_word_ne hAs (ofString "journal_n") 0#64
      (by decide) (by decide) (by decide)
  have hhp : globN s "heap_ptr" ≤ globN s' "heap_ptr" := by
    rw [globN_setGlobal_ne s (ofString "journal_n") _ "heap_ptr" (by decide)]
  have hsc : globN s' "scratch_ptr" ≤ globN s "scratch_ptr" := by
    rw [globN_setGlobal_ne s (ofString "journal_n") _ "scratch_ptr" (by decide)]
  refine ⟨⟨hAs', hhp, globalsKept_journal_n_zero s gw hjn,
    recordsKept_journal_n_zero s R keep, ?_⟩, hsc⟩
  intro S Nd hWTW _
  obtain ⟨hWTW', hwo⟩ := worldTypedWith_set_journal_n_zero hAs hWTW
  refine ⟨S, Nd, fun _ h => h, hWTW', ?_, fun _ _ _ => rfl, trivial⟩
  rw [hwo]
  exact fun o ho => Or.inr (Or.inl ⟨o, ho, le_rfl, le_rfl⟩)

theorem progWStep_assign_journal_n_zero (B : BufList) (gw : List String)
    (hjn : "journal_n" ∈ gw) :
    ProgWStep B gw (.assign .global (ofString "journal_n") (.const 0#64)) := by
  intro F s _ hW _ hfr
  rw [evaluateHOLFiniteState_assign] at hfr ⊢
  have hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.const 0#64) = some (.val (.word 0#64)) := rfl
  simp only [hev] at hfr ⊢
  by_cases hv : s.isValidValueHOLFinite .global (ofString "journal_n") (.val (.word 0#64)) = true
  · rw [if_pos hv]
    exact worldStepSc_set_journal_n_zero s none hW.1 hjn
  · rw [if_neg hv] at hfr
    exact absurd hfr not_flowingOrResumes_error

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
