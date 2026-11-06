import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkAcctWsBase
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkMarkAccountCreated
import InitECandidate.Solver.Wave8GuestInv.R16Shards.HtabUnionIntoSpec
import InitECandidate.Solver.Wave8GuestInv.R16Shards.ProcessWithdrawals
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.Common
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalRemove
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalInitFresh
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalStateInit.SetLstNew
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_htab_has
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_htab_item
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.RlpHelpers
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.Batch1
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.wk_u256_to_be_min
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.rv_u256_to_be_min
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_u256_mul
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.AccountWk
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkSysTxLeaves
import InitECandidate.Solver.Wave8GuestInv.R16Shards.PayloadWorldHelpers

set_option autoImplicit false
set_option Elab.async false
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
    WorldStep (bufRegions []) [] stdKeep NoExtra s r post := by
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
    WorldStepSc (bufRegions []) [] stdKeep NoExtra s r post := by
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
    (out.1 = none → WorldStepSc (bufRegions []) [] stdKeep NoExtra s out.1 out.2 ∧
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
    (out.1 = none → WorldStepSc (bufRegions []) [] stdKeep NoExtra s out.1 out.2 ∧
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

private theorem eval_sort_merge_loops_bre {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 : BitVec 64)
    (hsrc : src0 = p0 ∨ src0 = aux0)
    (hinv : SortMergeCursorInv p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 s)
    (hnt : (evaluateHOLFiniteState s
      (.seq
        (.while (.op .and [
          .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
          .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))])
          sortW1BodyP)
        (.seq
          (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) sortW2BodyP)
          (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) sortW3BodyP)))).1 ≠
        some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.seq
        (.while (.op .and [
          .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
          .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))])
          sortW1BodyP)
        (.seq
          (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) sortW2BodyP)
          (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) sortW3BodyP)))
    (out.1 = none →
      SortMergeCursorInv p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 out.2 ∧
      M11.ByteRegionEffect s out.2
        [(p0.toNat, n0.toNat * esz0.toNat), (aux0.toNat, n0.toNat * esz0.toNat)]) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  let firstP : ProgHOL 64 :=
    .while (.op .and [
      .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
      .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))])
      sortW1BodyP
  have hnt_first : (evaluateHOLFiniteState s firstP).1 ≠ some .timeOut := by
    intro heq
    rcases hf : evaluateHOLFiniteState s firstP with ⟨r, mid⟩
    change evaluateHOLFiniteState s _ = (r, mid) at hf
    rw [hf] at heq hnt
    dsimp only at heq
    subst r
    exact hnt rfl
  have hfirst_spec := eval_sortW1_while_bre s p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0
    hsrc hinv hnt_first
  dsimp only at hfirst_spec
  rcases hfirst : evaluateHOLFiniteState s
      (.while (.op .and [
        .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
        .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))])
        sortW1BodyP) with ⟨r, mid⟩
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
    have hlast := eval_sort_tail_loops_bre mid p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 hinv_mid hnt
    exact ⟨fun hn => ⟨(hlast.1 hn).1, heff_mid.trans (hlast.1 hn).2⟩, hlast.2⟩

private theorem eval_assign_var_bre {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dstN srcN : String) (dstOld srcVal : BitVec 64)
    (Rl : List Ivl)
    (hdst : s.locals.lookup (ofString dstN) = some (.val (.word dstOld)))
    (hsrc : s.locals.lookup (ofString srcN) = some (.val (.word srcVal))) :
    evaluateHOLFiniteState s
      (.assign .local (ofString dstN) (.var .local (ofString srcN))) =
      (none, setVarHOLFinite (ofString dstN) (.val (.word srcVal)) s) ∧
    M11.ByteRegionEffect s (setVarHOLFinite (ofString dstN) (.val (.word srcVal)) s) Rl := by
  have hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString srcN)) =
      some (.val (.word srcVal)) := hsrc
  have hvld : isValidValueHOLFinite s .local (ofString dstN) (.val (.word srcVal)) = true := by
    simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hdst, shapeOfHOLExact, shapeEqHOL]
  refine ⟨?_, (M11.ByteRegionEffect.refl s Rl).with_locals_clock _ _⟩
  rw [evaluateHOLFiniteState_assign, hev]
  dsimp only
  rw [if_pos hvld]
  rfl

private theorem eval_clamp_ite_bre {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vN nN : String) (v0 n0 : BitVec 64)
    (Rl : List Ivl)
    (hv : s.locals.lookup (ofString vN) = some (.val (.word v0)))
    (hn : s.locals.lookup (ofString nN) = some (.val (.word n0))) :
    let v' := if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower n0 v0 then n0 else v0
    ∃ s',
      evaluateHOLFiniteState s
        (.ite (.cmp .lower (.var .local (ofString nN)) (.var .local (ofString vN)))
          (.assign .local (ofString vN) (.var .local (ofString nN))) .skip) = (none, s') ∧
      M11.ByteRegionEffect s s' Rl ∧
      s'.clock = s.clock ∧
      s'.locals.lookup (ofString vN) = some (.val (.word v')) ∧
      ∀ x, x ≠ ofString vN → s'.locals.lookup x = s.locals.lookup x := by
  dsimp only
  rw [evaluateHOLFiniteState_ite]
  have hcnd : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local (ofString nN)) (.var .local (ofString vN))) =
      some (.val (.word (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower n0 v0 then 1 else 0))) := by
    by_cases hc : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower n0 v0 <;>
      simp [evalHOLExact, hv, hn, hc]
  rw [hcnd]
  dsimp only
  by_cases hc : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower n0 v0
  · simp only [hc, ↓reduceIte]
    rw [if_neg (by decide : ¬ ((1 : BitVec 64) = 0))]
    obtain ⟨hass, heff⟩ := eval_assign_var_bre s vN nN v0 n0 Rl hv hn
    refine ⟨setVarHOLFinite (ofString vN) (.val (.word n0)) s, hass, heff, rfl, ?_, ?_⟩
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · intro x hx
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hx]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    rw [evaluateHOLFiniteState_skip]
    exact ⟨s, rfl, M11.ByteRegionEffect.refl s Rl, rfl, hv, fun _ _ => rfl⟩

private def SortMergePassInv {F : Type}
    (p0 aux0 n0 esz0 width0 dst0 src0 : BitVec 64)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.code = originalRuntimeCode ∧
  s.memaddrs = ordinaryDomain ∧
  s.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
  s.locals.lookup (ofString "src") = some (.val (.word src0)) ∧
  s.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
  s.locals.lookup (ofString "esz") = some (.val (.word esz0)) ∧
  s.locals.lookup (ofString "width") = some (.val (.word width0)) ∧
  (∃ kindVal, s.locals.lookup (ofString "kind") = some (.val (.word kindVal))) ∧
  (dst0 = p0 ∨ dst0 = aux0) ∧
  (src0 = p0 ∨ src0 = aux0) ∧
  width0.toNat ≤ n0.toNat ∧
  n0.toNat < 2 ^ 63 ∧
  p0.toNat + n0.toNat * esz0.toNat < 2 ^ 64 ∧
  aux0.toNat + n0.toNat * esz0.toNat < 2 ^ 64 ∧
  ∃ left0 : BitVec 64,
    s.locals.lookup (ofString "left") = some (.val (.word left0)) ∧
    left0.toNat ≤ n0.toNat

private theorem sortMergeLoans_avoids (key : MlS)
    (hki : key ≠ ofString "i") (hkj : key ≠ ofString "j") (hkk : key ≠ ofString "k") :
    avoidsLocal key
      (.seq
        (.while (.op .and [
          .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
          .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))])
          sortW1BodyP)
        (.seq
          (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) sortW2BodyP)
          (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) sortW3BodyP))) = true := by
  have hi : (ofString "i" == key) = false := beq_false_of_ne (Ne.symm hki)
  have hj : (ofString "j" == key) = false := beq_false_of_ne (Ne.symm hkj)
  have hk : (ofString "k" == key) = false := beq_false_of_ne (Ne.symm hkk)
  simp [avoidsLocal, sortW1BodyP, sortW2BodyP, sortW3BodyP, hi, hj, hk]

private theorem sortMergePassLoop_avoids (key : MlS)
    (hkl : key ≠ ofString "left") :
    avoidsLocal key
      (.while (.cmp .less (.var .local (ofString "left")) (.var .local (ofString "n")))
        sortMergePassBodyP) = true := by
  have hl : (ofString "left" == key) = false := beq_false_of_ne (Ne.symm hkl)
  by_cases hm : ofString "mid" == key <;>
  by_cases hr : ofString "right" == key <;>
  by_cases hi : ofString "i" == key <;>
  by_cases hj : ofString "j" == key <;>
  by_cases hk : ofString "k" == key <;>
    simp [avoidsLocal, sortMergePassBodyP, sortW1BodyP, sortW2BodyP, sortW3BodyP,
      hl, hm, hr, hi, hj, hk]

private theorem sortOuterLoop_avoids (key : MlS)
    (hks : key ≠ ofString "src") (hkd : key ≠ ofString "dst") (hkw : key ≠ ofString "width") :
    avoidsLocal key
      (.while (.cmp .less (.var .local (ofString "width")) (.var .local (ofString "n")))
        sortOuterLoopBodyP) = true := by
  have hs : (ofString "src" == key) = false := beq_false_of_ne (Ne.symm hks)
  have hd : (ofString "dst" == key) = false := beq_false_of_ne (Ne.symm hkd)
  have hw : (ofString "width" == key) = false := beq_false_of_ne (Ne.symm hkw)
  by_cases hl : ofString "left" == key <;>
  by_cases hsw : ofString "swap" == key <;>
  by_cases hm : ofString "mid" == key <;>
  by_cases hr : ofString "right" == key <;>
  by_cases hi : ofString "i" == key <;>
  by_cases hj : ofString "j" == key <;>
  by_cases hk : ofString "k" == key <;>
    simp [avoidsLocal, sortOuterLoopBodyP, sortMergePassBodyP, sortW1BodyP, sortW2BodyP, sortW3BodyP,
      hs, hd, hw, hl, hsw, hm, hr, hi, hj, hk]

private theorem eval_sortMergePass_while_bre {F : Type}
    (s0 : PanSemStateFiniteExact 64 F)
    (p0 aux0 n0 esz0 width0 dst0 src0 : BitVec 64)
    (hinv0 : SortMergePassInv p0 aux0 n0 esz0 width0 dst0 src0 s0)
    (hnt0 : (evaluateHOLFiniteState s0
      (.while (.cmp .less (.var .local (ofString "left")) (.var .local (ofString "n")))
        sortMergePassBodyP)).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s0
      (.while (.cmp .less (.var .local (ofString "left")) (.var .local (ofString "n")))
        sortMergePassBodyP)
    (out.1 = none →
      SortMergePassInv p0 aux0 n0 esz0 width0 dst0 src0 out.2 ∧
      (∀ x, x ≠ ofString "left" → out.2.locals.lookup x = s0.locals.lookup x) ∧
      M11.ByteRegionEffect s0 out.2
        [(p0.toNat, n0.toNat * esz0.toNat), (aux0.toNat, n0.toNat * esz0.toNat)]) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  let Rl : List Ivl := [(p0.toNat, n0.toNat * esz0.toNat), (aux0.toNat, n0.toNat * esz0.toNat)]
  let loopP : ProgHOL 64 :=
    .while (.cmp .less (.var .local (ofString "left")) (.var .local (ofString "n"))) sortMergePassBodyP
  suffices hmain : ∀ (clk : Nat) (s : PanSemStateFiniteExact 64 F), s.clock = clk →
      SortMergePassInv p0 aux0 n0 esz0 width0 dst0 src0 s →
      (evaluateHOLFiniteState s loopP).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState s loopP).1 = none →
        SortMergePassInv p0 aux0 n0 esz0 width0 dst0 src0 (evaluateHOLFiniteState s loopP).2 ∧
        M11.ByteRegionEffect s (evaluateHOLFiniteState s loopP).2 Rl) ∧
      ((evaluateHOLFiniteState s loopP).1 ≠ none → ¬ Resumes (evaluateHOLFiniteState s loopP).1) by
    have hm := hmain s0.clock s0 rfl hinv0 hnt0
    refine ⟨fun hn => ⟨(hm.1 hn).1, ?_, (hm.1 hn).2⟩, hm.2⟩
    intro x hxl
    exact evaluate_avoidsLocal_flowing x loopP (sortMergePassLoop_avoids x hxl) s0 (Or.inl hn)
  intro clk
  induction clk using Nat.strong_induction_on with
  | h clk ih =>
    intro s hclk hPs hnt
    obtain ⟨hcode, hma, hdst, hsrc, hn, hesz, hwidth, hkind, hdst_c, hsrc_c,
      hw_n, hn_lt, hp_nw, haux_nw, left0, hleft, hl_n⟩ := hPs
    obtain ⟨kind0, hkv⟩ := hkind
    have hc := eval_signed_less_nonneg s "left" "n" left0 n0 hleft hn (by omega) hn_lt
    dsimp only [loopP] at hnt ⊢
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    simp only [hc] at hnt ⊢
    by_cases hlt : left0.toNat < n0.toNat
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
        have hb_clk := Flapjack.evaluateHOLFiniteState_clock_le d0 sortMergePassBodyP
        have hsh_w : ∀ w : BitVec 64, shapeEqHOL .one (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) = true :=
          fun _ => by simp [shapeOfHOLExact, shapeEqHOL]
        have hres_ne : ∀ (m : HolFiniteMapExact MlS (ValueHOL 64)) (v : MlS)
            (old : Option (ValueHOL 64)) (x : MlS), x ≠ v →
            (HolFiniteMapExact.resVarEq m (v, old)).lookup x = m.lookup x := by
          intro m v old x hxv
          cases old <;>
            simp [HolFiniteMapExact.resVarEq, FDOMSUB_HOL, FUPDATE_HOL, hxv, Ne.symm hxv]
        dsimp only [sortMergePassBodyP] at hnt hb_clk ⊢
        rw [evaluateHOLFiniteState_dec_total] at hnt hb_clk ⊢
        dsimp only at hnt hb_clk ⊢
        have he_mid0 : @evalHOLExact 64 F _ d0.toExact (fun a => Classical.propDecidable (d0.memaddrs a))
            (.op .add [.var .local (ofString "left"), .var .local (ofString "width")]) =
            some (.val (.word (left0 + width0))) := by
          have hleft_d : d0.locals.lookup (ofString "left") = some (.val (.word left0)) := hleft
          have hwidth_d : d0.locals.lookup (ofString "width") = some (.val (.word width0)) := hwidth
          simp [evalHOLExact, evalListHOLExact, hleft_d, hwidth_d, wordOpHOL, wordOp,
            valueIsWord, valueWord, List.all, List.map, Option.map, List.foldr]
        rw [he_mid0] at hnt hb_clk ⊢
        dsimp only at hnt hb_clk ⊢
        rw [if_pos (hsh_w _)] at hnt hb_clk ⊢
        set d1 := setVarHOLFinite (ofString "mid") (.val (.word (left0 + width0))) d0
        rw [evaluateHOLFiniteState_seq_line780] at hnt hb_clk ⊢
        have hd1_mid : d1.locals.lookup (ofString "mid") = some (.val (.word (left0 + width0))) := by
          simp [d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hd1_n : d1.locals.lookup (ofString "n") = some (.val (.word n0)) := by
          simp [d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "mid" ≠ ofString "n" by decide]; exact hn
        obtain ⟨d2, hd2_ev, heff_d12, hd2_clk, hd2_mid, hd2_other⟩ :=
          eval_clamp_ite_bre d1 "mid" "n" (left0 + width0) n0 Rl hd1_mid hd1_n
        set mid0 := if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower n0 (left0 + width0) then n0 else left0 + width0
        have hmid_b := sort_clamped_add_bounds left0 width0 n0 hl_n hw_n hn_lt
        dsimp only at hmid_b
        obtain ⟨_, hl_m, hm_n⟩ := hmid_b
        rw [hd2_ev] at hnt hb_clk ⊢
        dsimp only at hnt hb_clk ⊢
        rw [evaluateHOLFiniteState_dec_total] at hnt hb_clk ⊢
        dsimp only at hnt hb_clk ⊢
        have hd2_width : d2.locals.lookup (ofString "width") = some (.val (.word width0)) := by
          rw [hd2_other _ (by decide)]
          simp [d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "mid" ≠ ofString "width" by decide]; exact hwidth
        have he_right0 : @evalHOLExact 64 F _ d2.toExact (fun a => Classical.propDecidable (d2.memaddrs a))
            (.op .add [.var .local (ofString "mid"), .var .local (ofString "width")]) =
            some (.val (.word (mid0 + width0))) := by
          simp [evalHOLExact, evalListHOLExact, hd2_mid, hd2_width, wordOpHOL, wordOp,
            valueIsWord, valueWord, List.all, List.map, Option.map, List.foldr]
        rw [he_right0] at hnt hb_clk ⊢
        dsimp only at hnt hb_clk ⊢
        rw [if_pos (hsh_w _)] at hnt hb_clk ⊢
        set d3 := setVarHOLFinite (ofString "right") (.val (.word (mid0 + width0))) d2
        rw [evaluateHOLFiniteState_seq_line780] at hnt hb_clk ⊢
        have hd3_right : d3.locals.lookup (ofString "right") = some (.val (.word (mid0 + width0))) := by
          simp [d3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hd3_n : d3.locals.lookup (ofString "n") = some (.val (.word n0)) := by
          simp [d3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "right" ≠ ofString "n" by decide]
          rw [hd2_other _ (by decide)]; exact hd1_n
        obtain ⟨d4, hd4_ev, heff_d34, hd4_clk, hd4_right, hd4_other⟩ :=
          eval_clamp_ite_bre d3 "right" "n" (mid0 + width0) n0 Rl hd3_right hd3_n
        set right0 := if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower n0 (mid0 + width0) then n0 else mid0 + width0
        have hright_b := sort_clamped_add_bounds mid0 width0 n0 hm_n hw_n hn_lt
        dsimp only at hright_b
        obtain ⟨_, hm_r, hr_n⟩ := hright_b
        rw [hd4_ev] at hnt hb_clk ⊢
        dsimp only at hnt hb_clk ⊢
        have hd4_preserve : ∀ x, x ≠ ofString "right" → x ≠ ofString "mid" →
            d4.locals.lookup x = s.locals.lookup x := by
          intro x hxr hxm
          rw [hd4_other x hxr]
          simp [d3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxr]
          rw [hd2_other x hxm]
          simp [d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxm]
          rfl
        have hd4_mid : d4.locals.lookup (ofString "mid") = some (.val (.word mid0)) := by
          rw [hd4_other _ (by decide)]
          simp [d3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "right" ≠ ofString "mid" by decide]; exact hd2_mid
        have hd4_left : d4.locals.lookup (ofString "left") = some (.val (.word left0)) :=
          (hd4_preserve _ (by decide) (by decide)).trans hleft
        rw [evaluateHOLFiniteState_dec_total] at hnt hb_clk ⊢
        dsimp only at hnt hb_clk ⊢
        have he_i : @evalHOLExact 64 F _ d4.toExact (fun a => Classical.propDecidable (d4.memaddrs a))
            (.var .local (ofString "left")) = some (.val (.word left0)) := hd4_left
        rw [he_i] at hnt hb_clk ⊢
        dsimp only at hnt hb_clk ⊢
        rw [if_pos (hsh_w _)] at hnt hb_clk ⊢
        set d5 := setVarHOLFinite (ofString "i") (.val (.word left0)) d4
        rw [evaluateHOLFiniteState_dec_total] at hnt hb_clk ⊢
        dsimp only at hnt hb_clk ⊢
        have hd5_mid : d5.locals.lookup (ofString "mid") = some (.val (.word mid0)) := by
          simp [d5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "mid" by decide]; exact hd4_mid
        have he_j : @evalHOLExact 64 F _ d5.toExact (fun a => Classical.propDecidable (d5.memaddrs a))
            (.var .local (ofString "mid")) = some (.val (.word mid0)) := hd5_mid
        rw [he_j] at hnt hb_clk ⊢
        dsimp only at hnt hb_clk ⊢
        rw [if_pos (hsh_w _)] at hnt hb_clk ⊢
        set d6 := setVarHOLFinite (ofString "j") (.val (.word mid0)) d5
        rw [evaluateHOLFiniteState_dec_total] at hnt hb_clk ⊢
        dsimp only at hnt hb_clk ⊢
        have hd6_left : d6.locals.lookup (ofString "left") = some (.val (.word left0)) := by
          simp [d6, d5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "j" ≠ ofString "left" by decide,
            show ofString "i" ≠ ofString "left" by decide]; exact hd4_left
        have he_k : @evalHOLExact 64 F _ d6.toExact (fun a => Classical.propDecidable (d6.memaddrs a))
            (.var .local (ofString "left")) = some (.val (.word left0)) := hd6_left
        rw [he_k] at hnt hb_clk ⊢
        dsimp only at hnt hb_clk ⊢
        rw [if_pos (hsh_w _)] at hnt hb_clk ⊢
        set d7 := setVarHOLFinite (ofString "k") (.val (.word left0)) d6
        have hd7_preserve : ∀ x, x ≠ ofString "k" → x ≠ ofString "j" → x ≠ ofString "i" →
            x ≠ ofString "right" → x ≠ ofString "mid" →
            d7.locals.lookup x = s.locals.lookup x := by
          intro x hxk hxj hxi hxr hxm
          simp [d7, d6, d5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            Ne.symm hxk, Ne.symm hxj, Ne.symm hxi]
          exact hd4_preserve x hxr hxm
        have heff_d07 : M11.ByteRegionEffect d0 d7 Rl := by
          have h01 : M11.ByteRegionEffect d0 d1 Rl :=
            (M11.ByteRegionEffect.refl d0 Rl).with_locals_clock d1.locals d1.clock
          have h23 : M11.ByteRegionEffect d2 d3 Rl :=
            (M11.ByteRegionEffect.refl d2 Rl).with_locals_clock d3.locals d3.clock
          exact (((h01.trans heff_d12).trans h23).trans heff_d34).with_locals_clock d7.locals d7.clock
        have hinv_d7 : SortMergeCursorInv p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0 d7 := by
          refine ⟨heff_d07.code.trans hcode, heff_d07.memaddrs.trans hma,
            (hd7_preserve _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hdst,
            (hd7_preserve _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsrc,
            (hd7_preserve _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hesz,
            ?_, ?_,
            ⟨kind0, (hd7_preserve _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hkv⟩,
            hdst_c, hn_lt, hp_nw, haux_nw, hl_m, hm_r, hr_n,
            left0, mid0, left0, ?_, ?_, ?_, le_rfl, hl_m, le_rfl, hm_r, by omega⟩
          · simp [d7, d6, d5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "k" ≠ ofString "mid" by decide,
              show ofString "j" ≠ ofString "mid" by decide,
              show ofString "i" ≠ ofString "mid" by decide]; exact hd4_mid
          · simp [d7, d6, d5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "k" ≠ ofString "right" by decide,
              show ofString "j" ≠ ofString "right" by decide,
              show ofString "i" ≠ ofString "right" by decide]; exact hd4_right
          · simp [d7, d6, d5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "k" ≠ ofString "i" by decide,
              show ofString "j" ≠ ofString "i" by decide]
          · simp [d7, d6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "k" ≠ ofString "j" by decide]
          · simp [d7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        let mlP : ProgHOL 64 :=
          .seq
            (.while (.op .and [
              .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
              .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))])
              sortW1BodyP)
            (.seq
              (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) sortW2BodyP)
              (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) sortW3BodyP))
        let assignLeftP : ProgHOL 64 :=
          .assign .local (ofString "left") (.var .local (ofString "right"))
        have hseq_reassoc : evaluateHOLFiniteState d7
            (.seq
              (.while (.op .and [
                .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
                .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))])
                sortW1BodyP)
              (.seq
                (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) sortW2BodyP)
                (.seq
                  (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) sortW3BodyP)
                  assignLeftP))) =
            evaluateHOLFiniteState d7 (.seq mlP assignLeftP) := by
          simp only [mlP, evaluateHOLFiniteState_seq_line780]
          rcases evaluateHOLFiniteState d7 _ with ⟨r1, t1⟩
          cases r1 with
          | some _ => rfl
          | none =>
            dsimp only
            rcases evaluateHOLFiniteState t1 _ with ⟨r2, t2⟩
            cases r2 <;> rfl
        rw [hseq_reassoc, evaluateHOLFiniteState_seq_line780] at hnt hb_clk ⊢
        have hnt_ml : (evaluateHOLFiniteState d7 mlP).1 ≠ some .timeOut := by
          intro heq
          rcases hml : evaluateHOLFiniteState d7 mlP with ⟨rml, sml⟩
          rw [hml] at heq hnt; dsimp only at heq; subst rml; exact hnt rfl
        have hml_spec := eval_sort_merge_loops_bre d7 p0 aux0 n0 esz0 left0 mid0 right0 dst0 src0
          hsrc_c hinv_d7 hnt_ml
        dsimp only at hml_spec
        rcases hml : evaluateHOLFiniteState d7 mlP with ⟨rml, sml⟩
        have hml_raw : evaluateHOLFiniteState d7
            (.seq
              (.while (.op .and [
                .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))),
                .cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right")))])
                sortW1BodyP)
              (.seq
                (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "mid"))) sortW2BodyP)
                (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "right"))) sortW3BodyP))) =
            (rml, sml) := hml
        rw [hml_raw] at hml_spec
        cases rml with
        | some r =>
          dsimp only at hml_spec ⊢
          have hnr : ¬ Resumes (some r) := hml_spec.2 (by simp)
          cases r with
          | «continue» =>
            exfalso
            have hnc : (evaluateHOLFiniteState d7 mlP).1 ≠ some .continue :=
              evaluate_noTopContinue mlP rfl d7
            exact hnc (by rw [hml])
          | «break» =>
            exfalso
            have hnb : (evaluateHOLFiniteState d7 mlP).1 ≠ some .break :=
              InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak mlP rfl d7
            exact hnb (by rw [hml])
          | timeOut =>
            exfalso
            exact hnt_ml (by rw [hml])
          | returned _ => exact ⟨fun h => by simp at h, fun _ => hnr⟩
          | exception _ _ => exact ⟨fun h => by simp at h, fun _ => hnr⟩
          | error => exact ⟨fun h => by simp at h, fun _ => hnr⟩
          | finalFfi _ => exact ⟨fun h => by simp at h, fun _ => hnr⟩
        | none =>
          have hsml_av : ∀ x, x ≠ ofString "i" → x ≠ ofString "j" → x ≠ ofString "k" →
              sml.locals.lookup x = d7.locals.lookup x := by
            intro x hxi hxj hxk
            have hav := evaluate_avoidsLocal_flowing x mlP (sortMergeLoans_avoids x hxi hxj hxk)
              d7 (by rw [hml]; exact Or.inl rfl)
            rwa [hml] at hav
          rw [hml] at hnt hb_clk
          dsimp only at hml_spec hnt hb_clk ⊢
          obtain ⟨hinv_sml, heff_ml⟩ := hml_spec.1 rfl
          have hsml_left : sml.locals.lookup (ofString "left") = some (.val (.word left0)) := by
            rw [hsml_av _ (by decide) (by decide) (by decide)]
            exact (hd7_preserve _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hleft
          have hsml_right : sml.locals.lookup (ofString "right") = some (.val (.word right0)) := hinv_sml.2.2.2.2.2.2.1
          obtain ⟨hass_l, heff_ass⟩ := eval_assign_var_bre sml "left" "right" left0 right0 Rl hsml_left hsml_right
          dsimp only [assignLeftP] at hnt hb_clk ⊢
          rw [hass_l] at hnt hb_clk ⊢
          dsimp only at hnt hb_clk ⊢
          set s_step := setVarHOLFinite (ofString "left") (.val (.word right0)) sml
          set end_locals := HolFiniteMapExact.resVarEq
            (HolFiniteMapExact.resVarEq
              (HolFiniteMapExact.resVarEq
                (HolFiniteMapExact.resVarEq
                  (HolFiniteMapExact.resVarEq s_step.locals
                    (ofString "k", d6.locals.lookup (ofString "k")))
                  (ofString "j", d5.locals.lookup (ofString "j")))
                (ofString "i", d4.locals.lookup (ofString "i")))
              (ofString "right", d2.locals.lookup (ofString "right")))
            (ofString "mid", d0.locals.lookup (ofString "mid"))
          set s_end : PanSemStateFiniteExact 64 F := { s_step with locals := end_locals }
          have heff_body : M11.ByteRegionEffect d0 s_end Rl :=
            ((heff_d07.trans heff_ml).trans heff_ass).with_locals_clock _ _
          have hloc_end : ∀ x, x ≠ ofString "mid" → x ≠ ofString "right" →
              x ≠ ofString "i" → x ≠ ofString "j" → x ≠ ofString "k" →
              s_end.locals.lookup x = s_step.locals.lookup x := by
            intro x hxm hxr hxi hxj hxk
            dsimp only [s_end, end_locals]
            rw [hres_ne _ _ _ _ hxm, hres_ne _ _ _ _ hxr, hres_ne _ _ _ _ hxi,
              hres_ne _ _ _ _ hxj, hres_ne _ _ _ _ hxk]
          have hloc_other : ∀ x, x ≠ ofString "left" → x ≠ ofString "mid" → x ≠ ofString "right" →
              x ≠ ofString "i" → x ≠ ofString "j" → x ≠ ofString "k" →
              s_end.locals.lookup x = s.locals.lookup x := by
            intro x hxl hxm hxr hxi hxj hxk
            rw [hloc_end x hxm hxr hxi hxj hxk]
            simp [s_step, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxl]
            rw [hsml_av x hxi hxj hxk]
            exact hd7_preserve x hxk hxj hxi hxr hxm
          have hPs_end : SortMergePassInv p0 aux0 n0 esz0 width0 dst0 src0 s_end := by
            refine ⟨heff_body.code.trans hcode, heff_body.memaddrs.trans hma,
              (hloc_other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hdst,
              (hloc_other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsrc,
              (hloc_other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hn,
              (hloc_other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hesz,
              (hloc_other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hwidth,
              ⟨kind0, (hloc_other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hkv⟩,
              hdst_c, hsrc_c, hw_n, hn_lt, hp_nw, haux_nw,
              right0, ?_, hr_n⟩
            rw [hloc_end _ (by decide) (by decide) (by decide) (by decide) (by decide)]
            simp [s_step, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have jih := ih s_end.clock (lt_of_le_of_lt hb_clk hd_clk) s_end rfl hPs_end hnt
          exact ⟨fun hn_out => ⟨(jih.1 hn_out).1, (heff_dec.trans heff_body).trans (jih.1 hn_out).2⟩, jih.2⟩
    · rw [if_neg hlt] at hnt ⊢
      have h0nz : ¬ ((0 : BitVec 64) ≠ 0) := by decide
      rw [if_neg h0nz]
      exact ⟨fun _ => ⟨⟨hcode, hma, hdst, hsrc, hn, hesz, hwidth, ⟨kind0, hkv⟩,
        hdst_c, hsrc_c, hw_n, hn_lt, hp_nw, haux_nw, left0, hleft, hl_n⟩,
        M11.ByteRegionEffect.refl s Rl⟩, fun h => False.elim (h rfl)⟩

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

private theorem eval_assign_mul2_bre {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vN : String) (v0 : BitVec 64) (Rl : List Ivl)
    (hv : s.locals.lookup (ofString vN) = some (.val (.word v0))) :
    evaluateHOLFiniteState s
      (.assign .local (ofString vN) (.panop .mul [.var .local (ofString vN), .const 2#64])) =
      (none, setVarHOLFinite (ofString vN) (.val (.word (v0 * 2#64))) s) ∧
    M11.ByteRegionEffect s (setVarHOLFinite (ofString vN) (.val (.word (v0 * 2#64))) s) Rl := by
  have hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.panop .mul [.var .local (ofString vN), .const 2#64]) =
      some (.val (.word (v0 * 2#64))) := by
    simp [evalHOLExact, evalListHOLExact, hv, panOpHOL, valueIsWord, valueWord,
      List.all, List.map, Option.map]
  have hvld : isValidValueHOLFinite s .local (ofString vN) (.val (.word (v0 * 2#64))) = true := by
    simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hv, shapeOfHOLExact, shapeEqHOL]
  refine ⟨?_, (M11.ByteRegionEffect.refl s Rl).with_locals_clock _ _⟩
  rw [evaluateHOLFiniteState_assign, hev]
  dsimp only
  rw [if_pos hvld]
  rfl

private def SortOuterInv {F : Type}
    (p0 aux0 n0 esz0 : BitVec 64)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.code = originalRuntimeCode ∧
  s.memaddrs = ordinaryDomain ∧
  s.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
  s.locals.lookup (ofString "esz") = some (.val (.word esz0)) ∧
  (∃ kindVal, s.locals.lookup (ofString "kind") = some (.val (.word kindVal))) ∧
  4 ≤ esz0.toNat ∧
  n0.toNat < 2 ^ 63 ∧
  p0.toNat + n0.toNat * esz0.toNat < 2 ^ 64 ∧
  aux0.toNat + n0.toNat * esz0.toNat < 2 ^ 64 ∧
  ∃ dst0 src0 width0 : BitVec 64,
    s.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
    s.locals.lookup (ofString "src") = some (.val (.word src0)) ∧
    s.locals.lookup (ofString "width") = some (.val (.word width0)) ∧
    (dst0 = p0 ∨ dst0 = aux0) ∧
    (src0 = p0 ∨ src0 = aux0) ∧
    width0.toNat < 2 ^ 63

private theorem eval_sortOuterLoop_while_bre {F : Type}
    (s0 : PanSemStateFiniteExact 64 F)
    (p0 aux0 n0 esz0 : BitVec 64)
    (hinv0 : SortOuterInv p0 aux0 n0 esz0 s0)
    (hnt0 : (evaluateHOLFiniteState s0
      (.while (.cmp .less (.var .local (ofString "width")) (.var .local (ofString "n")))
        sortOuterLoopBodyP)).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s0
      (.while (.cmp .less (.var .local (ofString "width")) (.var .local (ofString "n")))
        sortOuterLoopBodyP)
    (out.1 = none →
      SortOuterInv p0 aux0 n0 esz0 out.2 ∧
      (∀ x, x ≠ ofString "src" → x ≠ ofString "dst" → x ≠ ofString "width" →
        out.2.locals.lookup x = s0.locals.lookup x) ∧
      M11.ByteRegionEffect s0 out.2
        [(p0.toNat, n0.toNat * esz0.toNat), (aux0.toNat, n0.toNat * esz0.toNat)]) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  let Rl : List Ivl := [(p0.toNat, n0.toNat * esz0.toNat), (aux0.toNat, n0.toNat * esz0.toNat)]
  let loopP : ProgHOL 64 :=
    .while (.cmp .less (.var .local (ofString "width")) (.var .local (ofString "n"))) sortOuterLoopBodyP
  suffices hmain : ∀ (clk : Nat) (s : PanSemStateFiniteExact 64 F), s.clock = clk →
      SortOuterInv p0 aux0 n0 esz0 s →
      (evaluateHOLFiniteState s loopP).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState s loopP).1 = none →
        SortOuterInv p0 aux0 n0 esz0 (evaluateHOLFiniteState s loopP).2 ∧
        M11.ByteRegionEffect s (evaluateHOLFiniteState s loopP).2 Rl) ∧
      ((evaluateHOLFiniteState s loopP).1 ≠ none → ¬ Resumes (evaluateHOLFiniteState s loopP).1) by
    have hm := hmain s0.clock s0 rfl hinv0 hnt0
    refine ⟨fun hn => ⟨(hm.1 hn).1, ?_, (hm.1 hn).2⟩, hm.2⟩
    intro x hxs hxd hxw
    exact evaluate_avoidsLocal_flowing x loopP (sortOuterLoop_avoids x hxs hxd hxw) s0 (Or.inl hn)
  intro clk
  induction clk using Nat.strong_induction_on with
  | h clk ih =>
    intro s hclk hPs hnt
    obtain ⟨hcode, hma, hn, hesz, hkind, hesz4, hn_lt, hp_nw, haux_nw,
      dst0, src0, width0, hdst, hsrc, hwidth, hdst_c, hsrc_c, hw_lt⟩ := hPs
    obtain ⟨kind0, hkv⟩ := hkind
    have hc := eval_signed_less_nonneg s "width" "n" width0 n0 hwidth hn hw_lt hn_lt
    dsimp only [loopP] at hnt ⊢
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    simp only [hc] at hnt ⊢
    by_cases hlt : width0.toNat < n0.toNat
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
        have hb_clk := Flapjack.evaluateHOLFiniteState_clock_le d0 sortOuterLoopBodyP
        have hsh_w : ∀ w : BitVec 64, shapeEqHOL .one (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) = true :=
          fun _ => by simp [shapeOfHOLExact, shapeEqHOL]
        have hres_ne : ∀ (m : HolFiniteMapExact MlS (ValueHOL 64)) (v : MlS)
            (old : Option (ValueHOL 64)) (x : MlS), x ≠ v →
            (HolFiniteMapExact.resVarEq m (v, old)).lookup x = m.lookup x := by
          intro m v old x hxv
          cases old <;>
            simp [HolFiniteMapExact.resVarEq, FDOMSUB_HOL, FUPDATE_HOL, hxv, Ne.symm hxv]
        dsimp only [sortOuterLoopBodyP] at hnt hb_clk ⊢
        rw [evaluateHOLFiniteState_dec_total] at hnt hb_clk ⊢
        dsimp only at hnt hb_clk ⊢
        have he_z : @evalHOLExact 64 F _ d0.toExact (fun a => Classical.propDecidable (d0.memaddrs a))
            (.const 0) = some (.val (.word 0#64)) := rfl
        rw [he_z] at hnt hb_clk ⊢
        dsimp only at hnt hb_clk ⊢
        rw [if_pos (hsh_w _)] at hnt hb_clk ⊢
        set d1 := setVarHOLFinite (ofString "left") (.val (.word 0#64)) d0
        have heff_d01 : M11.ByteRegionEffect d0 d1 Rl :=
          (M11.ByteRegionEffect.refl d0 Rl).with_locals_clock d1.locals d1.clock
        have hd1_preserve : ∀ x, x ≠ ofString "left" → d1.locals.lookup x = s.locals.lookup x := by
          intro x hxl
          simp [d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxl]
          rfl
        have hinv_d1 : SortMergePassInv p0 aux0 n0 esz0 width0 dst0 src0 d1 := by
          refine ⟨hcode, hma,
            (hd1_preserve _ (by decide)).trans hdst,
            (hd1_preserve _ (by decide)).trans hsrc,
            (hd1_preserve _ (by decide)).trans hn,
            (hd1_preserve _ (by decide)).trans hesz,
            (hd1_preserve _ (by decide)).trans hwidth,
            ⟨kind0, (hd1_preserve _ (by decide)).trans hkv⟩,
            hdst_c, hsrc_c, by omega, hn_lt, hp_nw, haux_nw,
            0#64, ?_, Nat.zero_le _⟩
          simp [d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        rw [evaluateHOLFiniteState_seq_line780] at hnt hb_clk ⊢
        let mpP : ProgHOL 64 :=
          .while (.cmp .less (.var .local (ofString "left")) (.var .local (ofString "n")))
            sortMergePassBodyP
        have hnt_mp : (evaluateHOLFiniteState d1 mpP).1 ≠ some .timeOut := by
          intro heq
          rcases hmp : evaluateHOLFiniteState d1 mpP with ⟨rmp, smp⟩
          change evaluateHOLFiniteState d1 _ = (rmp, smp) at hmp
          rw [hmp] at heq hnt; dsimp only at heq; subst rmp; exact hnt rfl
        have hmp_spec := eval_sortMergePass_while_bre d1 p0 aux0 n0 esz0 width0 dst0 src0 hinv_d1 hnt_mp
        dsimp only at hmp_spec
        rcases hmp : evaluateHOLFiniteState d1
            (.while (.cmp .less (.var .local (ofString "left")) (.var .local (ofString "n")))
              sortMergePassBodyP) with ⟨rmp, smp⟩
        rw [hmp] at hmp_spec
        cases rmp with
        | some r =>
          dsimp only at hmp_spec ⊢
          have hnr : ¬ Resumes (some r) := hmp_spec.2 (by simp)
          cases r with
          | «continue» =>
            exfalso
            have hnc : (evaluateHOLFiniteState d1 mpP).1 ≠ some .continue :=
              evaluate_noTopContinue mpP rfl d1
            exact hnc (by simpa [mpP] using congrArg Prod.fst hmp)
          | «break» =>
            exfalso
            have hnb : (evaluateHOLFiniteState d1 mpP).1 ≠ some .break :=
              InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak mpP rfl d1
            exact hnb (by simpa [mpP] using congrArg Prod.fst hmp)
          | timeOut =>
            exfalso
            exact hnt_mp (by simpa [mpP] using congrArg Prod.fst hmp)
          | returned _ => exact ⟨fun h => by simp at h, fun _ => hnr⟩
          | exception _ _ => exact ⟨fun h => by simp at h, fun _ => hnr⟩
          | error => exact ⟨fun h => by simp at h, fun _ => hnr⟩
          | finalFfi _ => exact ⟨fun h => by simp at h, fun _ => hnr⟩
        | none =>
          rw [hmp] at hnt hb_clk
          dsimp only at hmp_spec hnt hb_clk ⊢
          obtain ⟨hinv_smp, hsmp_loc, heff_mp⟩ := hmp_spec.1 rfl
          have hsmp_preserve : ∀ x, x ≠ ofString "left" → smp.locals.lookup x = s.locals.lookup x := by
            intro x hxl; exact (hsmp_loc x hxl).trans (hd1_preserve x hxl)
          rw [evaluateHOLFiniteState_dec_total] at hnt hb_clk ⊢
          dsimp only at hnt hb_clk ⊢
          have hsmp_src : smp.locals.lookup (ofString "src") = some (.val (.word src0)) :=
            (hsmp_preserve _ (by decide)).trans hsrc
          have he_sw : @evalHOLExact 64 F _ smp.toExact (fun a => Classical.propDecidable (smp.memaddrs a))
              (.var .local (ofString "src")) = some (.val (.word src0)) := hsmp_src
          rw [he_sw] at hnt hb_clk ⊢
          dsimp only at hnt hb_clk ⊢
          rw [if_pos (hsh_w _)] at hnt hb_clk ⊢
          set d2 := setVarHOLFinite (ofString "swap") (.val (.word src0)) smp
          have heff_smp2 : M11.ByteRegionEffect smp d2 Rl :=
            (M11.ByteRegionEffect.refl smp Rl).with_locals_clock d2.locals d2.clock
          rw [evaluateHOLFiniteState_seq_line780] at hnt hb_clk ⊢
          have hd2_src : d2.locals.lookup (ofString "src") = some (.val (.word src0)) := by
            simp [d2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "swap" ≠ ofString "src" by decide]; exact hsmp_src
          have hd2_dst : d2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
            simp [d2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "swap" ≠ ofString "dst" by decide]
            exact (hsmp_preserve _ (by decide)).trans hdst
          obtain ⟨hass_src, heff_src⟩ := eval_assign_var_bre d2 "src" "dst" src0 dst0 Rl hd2_src hd2_dst
          rw [hass_src] at hnt hb_clk ⊢
          dsimp only at hnt hb_clk ⊢
          set d3 := setVarHOLFinite (ofString "src") (.val (.word dst0)) d2
          rw [evaluateHOLFiniteState_seq_line780] at hnt hb_clk ⊢
          have hd3_dst : d3.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
            simp [d3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "src" ≠ ofString "dst" by decide]; exact hd2_dst
          have hd3_swap : d3.locals.lookup (ofString "swap") = some (.val (.word src0)) := by
            simp [d3, d2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "src" ≠ ofString "swap" by decide]
          obtain ⟨hass_dst, heff_dst⟩ := eval_assign_var_bre d3 "dst" "swap" dst0 src0 Rl hd3_dst hd3_swap
          rw [hass_dst] at hnt hb_clk ⊢
          dsimp only at hnt hb_clk ⊢
          set d4 := setVarHOLFinite (ofString "dst") (.val (.word src0)) d3
          have hd4_width : d4.locals.lookup (ofString "width") = some (.val (.word width0)) := by
            simp [d4, d3, d2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "dst" ≠ ofString "width" by decide,
              show ofString "src" ≠ ofString "width" by decide,
              show ofString "swap" ≠ ofString "width" by decide]
            exact (hsmp_preserve _ (by decide)).trans hwidth
          obtain ⟨hass_w, heff_w⟩ := eval_assign_mul2_bre d4 "width" width0 Rl hd4_width
          rw [hass_w] at hnt hb_clk ⊢
          dsimp only at hnt hb_clk ⊢
          set d5 := setVarHOLFinite (ofString "width") (.val (.word (width0 * 2#64))) d4
          set end_locals := HolFiniteMapExact.resVarEq
            (HolFiniteMapExact.resVarEq d5.locals (ofString "swap", smp.locals.lookup (ofString "swap")))
            (ofString "left", d0.locals.lookup (ofString "left"))
          set s_end : PanSemStateFiniteExact 64 F := { d5 with locals := end_locals }
          have heff_body : M11.ByteRegionEffect d0 s_end Rl :=
            (((((heff_d01.trans heff_mp).trans heff_smp2).trans heff_src).trans heff_dst).trans heff_w).with_locals_clock _ _
          have hloc_end : ∀ x, x ≠ ofString "left" → x ≠ ofString "swap" →
              s_end.locals.lookup x = d5.locals.lookup x := by
            intro x hxl hxsw
            dsimp only [s_end, end_locals]
            rw [hres_ne _ _ _ _ hxl, hres_ne _ _ _ _ hxsw]
          have hloc_other : ∀ x, x ≠ ofString "left" → x ≠ ofString "swap" →
              x ≠ ofString "width" → x ≠ ofString "dst" → x ≠ ofString "src" →
              s_end.locals.lookup x = s.locals.lookup x := by
            intro x hxl hxsw hxw hxd hxs
            rw [hloc_end x hxl hxsw]
            simp [d5, d4, d3, d2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              Ne.symm hxw, Ne.symm hxd, Ne.symm hxs, Ne.symm hxsw]
            exact hsmp_preserve x hxl
          have hw2_bounds := sort_width_double_bounds width0 n0 esz0 hlt hesz4 (by omega)
          have hPs_end : SortOuterInv p0 aux0 n0 esz0 s_end := by
            refine ⟨heff_body.code.trans hcode, heff_body.memaddrs.trans hma,
              (hloc_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hn,
              (hloc_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hesz,
              ⟨kind0, (hloc_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hkv⟩,
              hesz4, hn_lt, hp_nw, haux_nw,
              src0, dst0, width0 * 2#64, ?_, ?_, ?_, hsrc_c, hdst_c, hw2_bounds.2.1⟩
            · rw [hloc_end _ (by decide) (by decide)]
              simp [d5, d4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "width" ≠ ofString "dst" by decide]
            · rw [hloc_end _ (by decide) (by decide)]
              simp [d5, d4, d3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "width" ≠ ofString "src" by decide,
                show ofString "dst" ≠ ofString "src" by decide]
            · rw [hloc_end _ (by decide) (by decide)]
              simp [d5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have jih := ih s_end.clock (lt_of_le_of_lt hb_clk hd_clk) s_end rfl hPs_end hnt
          exact ⟨fun hn_out => ⟨(jih.1 hn_out).1, (heff_dec.trans heff_body).trans (jih.1 hn_out).2⟩, jih.2⟩
    · rw [if_neg hlt] at hnt ⊢
      have h0nz : ¬ ((0 : BitVec 64) ≠ 0) := by decide
      rw [if_neg h0nz]
      exact ⟨fun _ => ⟨⟨hcode, hma, hn, hesz, ⟨kind0, hkv⟩, hesz4, hn_lt, hp_nw, haux_nw,
        dst0, src0, width0, hdst, hsrc, hwidth, hdst_c, hsrc_c, hw_lt⟩,
        M11.ByteRegionEffect.refl s Rl⟩, fun h => False.elim (h rfl)⟩

private theorem heapByteEff_of_bre {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {gw : List String}
    (hAR : ArenaReady s) (heff : M11.ByteRegionEffect s post Rl) :
    WkBlockTxEnc.HeapByteEff s post Rl gw :=
  WkBlockTxEnc.HeapByteEff.of_m11_bre hAR heff

theorem eval_call_sort_elems_heap {F : Type}
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
    (hesz4 : 4 ≤ esz0.toNat)
    (hbound : p0.toNat + n0.toNat * esz0.toNat < 2 ^ 64)
    (hregion : 2 ≤ n0.toNat → ∃ ivl ∈ Rl, ivl.1 ≤ p0.toNat ∧
      p0.toNat + n0.toNat * esz0.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "sort_elems")
        [pExp, nExp, eszExp, kindExp, tmpExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "sort_elems")
        [pExp, nExp, eszExp, kindExp, tmpExp])
    (out.1 = none →
      WkBlockTxEnc.HeapByteEff s out.2 Rl gw ∧
      out.2.locals = s.locals ∧
      out.2.globals = s.globals) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  by_cases hlt2 : n0.toNat < 2
  · have h := eval_call_sort_elems_lt2 s pExp nExp eszExp kindExp tmpExp
      p0 n0 esz0 kind0 tmp0 Rl gw hcode hAR hp hn hesz hkind htmp hlt2 hnt
    dsimp only at h ⊢
    exact ⟨fun _ => ⟨h.2.2.2.2, h.2.1, h.2.2.1⟩, fun hne => False.elim (hne h.1)⟩
  · have hge2 : 2 ≤ n0.toNat := by omega
    obtain ⟨ivl_p, hivl_p, hp_lo, hp_hi⟩ := hregion hge2
    have hn_lt63 : n0.toNat < 2 ^ 63 := by
      have h4 : n0.toNat * 4 ≤ n0.toNat * esz0.toNat := Nat.mul_le_mul_left _ hesz4
      omega
    have hmul_nw := sort_alloc_size_no_wrap n0 esz0 (by omega)
    dsimp only
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
      have hent_code : ent.code = originalRuntimeCode := hcode
      have hent_AR : ArenaReady ent := localsFree_arenaReady s cmap (s.clock - 1) hAR
      have hent_p : ent.locals.lookup (ofString "p") = some (.val (.word p0)) := by
        simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "tmp" ≠ ofString "p" by decide,
          show ofString "kind" ≠ ofString "p" by decide,
          show ofString "esz" ≠ ofString "p" by decide,
          show ofString "n" ≠ ofString "p" by decide]
      have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word n0)) := by
        simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "tmp" ≠ ofString "n" by decide,
          show ofString "kind" ≠ ofString "n" by decide,
          show ofString "esz" ≠ ofString "n" by decide]
      have hent_esz : ent.locals.lookup (ofString "esz") = some (.val (.word esz0)) := by
        simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "tmp" ≠ ofString "esz" by decide,
          show ofString "kind" ≠ ofString "esz" by decide]
      have hent_kind : ent.locals.lookup (ofString "kind") = some (.val (.word kind0)) := by
        simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "tmp" ≠ ofString "kind" by decide]
      have hnt_ent : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_sort_elems)).1 ≠
          some .timeOut := by
        intro heq
        rcases hr : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_sort_elems) with ⟨r, st⟩
        rw [hr] at heq hnt; dsimp only at heq; subst r; exact hnt rfl
      by_cases hres_ent : Resumes (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_sort_elems)).1
      · rw [sortElemsBody_eq, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt_ent hres_ent ⊢
        have hcnd : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
            (.cmp .lower (.var .local (ofString "n")) (.const 2#64)) =
            some (.val (.word 0#64)) := by
          have hnbv : ¬ (n0 < 2#64) := by simpa [BitVec.lt_def] using hlt2
          simp [evalHOLExact, hent_n, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnbv]
        rw [hcnd] at hnt_ent hres_ent ⊢
        dsimp only at hnt_ent hres_ent ⊢
        have h0eq : ((0#64 : BitVec 64) = 0) := rfl
        rw [if_pos h0eq, evaluateHOLFiniteState_skip] at hnt_ent hres_ent ⊢
        dsimp only at hnt_ent hres_ent ⊢
        let Rl1 : List Ivl :=
          [(p0.toNat, n0.toNat * esz0.toNat), (globN s "heap_ptr", n0.toNat * esz0.toNat)]
        let gw_int : List String := ["heap_ptr"]
        have hgw_int : "heap_ptr" ∈ gw_int := List.Mem.head _
        have hent_hp_gn : globN ent "heap_ptr" = globN s "heap_ptr" := rfl
        obtain ⟨hp_w, m1, hhp_g, hhp_nat, hm1_g, hm1_m, hm1_l, heff_m1, hnt_m1, hm1_eq⟩ :=
          WkBlockTxEnc.eval_decCall_heap_mark ent "mark" _ Rl1 gw_int hent_code hent_AR hnt_ent
        rw [hm1_eq] at hres_ent ⊢
        dsimp only at hres_ent ⊢
        have hm1_code : m1.code = originalRuntimeCode :=
          heff_m1.arena.1.code
        obtain ⟨hp_a, alloc_n, q_w, m2, halloc_ev, hhp_a_nat, _, hq_nat, hpq_le, hq_hi, _,
          _, hm2_g, hm2_m, hm2_l, heff_m2, hnt_m2, hres_m2, hm2_eq⟩ :=
          WkBlockTxEnc.eval_decCall_alloc_resumes m1 "aux" _ _ Rl1 gw_int hm1_code heff_m1.arena
            hgw_int hnt_m1 hres_ent
        rw [hm2_eq]
        dsimp only
        have hm1_n : m1.locals.lookup (ofString "n") = some (.val (.word n0)) := by
          rw [hm1_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "mark" ≠ ofString "n" by decide]; exact hent_n
        have hm1_esz : m1.locals.lookup (ofString "esz") = some (.val (.word esz0)) := by
          rw [hm1_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "mark" ≠ ofString "esz" by decide]; exact hent_esz
        have halloc_eq : alloc_n = n0 * esz0 := by
          have hev_ne : @evalHOLExact 64 F _ m1.toExact (fun a => Classical.propDecidable (m1.memaddrs a))
              (.panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]) =
              some (.val (.word (n0 * esz0))) := by
            simp [evalHOLExact, evalListHOLExact, hm1_n, hm1_esz, panOpHOL, valueIsWord, valueWord,
              List.all, List.map, Option.map]
          have hinj := Option.some.inj (halloc_ev.symm.trans hev_ne)
          cases hinj; rfl
        subst halloc_eq
        have hhp_a_eq : hp_w = hp_a := by
          apply BitVec.eq_of_toNat_eq
          rw [hhp_nat, show globN ent "heap_ptr" = globN m1 "heap_ptr" by simp [globN, hm1_g], hhp_a_nat]
        subst hhp_a_eq
        have haux_hi : hp_w.toNat + n0.toNat * esz0.toNat ≤ heapLimit := by
          rw [hmul_nw] at hpq_le; omega
        have haux_nw : hp_w.toNat + n0.toNat * esz0.toNat < 2 ^ 64 := by
          have : heapLimit < 2 ^ 64 := by decide
          omega
        have hRl1_eq : Rl1 = [(p0.toNat, n0.toNat * esz0.toNat), (hp_w.toNat, n0.toNat * esz0.toNat)] := by
          dsimp only [Rl1]; rw [hhp_nat, hent_hp_gn]
        have hsh_w : ∀ w : BitVec 64, shapeEqHOL .one (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) = true :=
          fun _ => by simp [shapeOfHOLExact, shapeEqHOL]
        have hm2_preserve : ∀ x, x ≠ ofString "aux" → x ≠ ofString "mark" →
            m2.locals.lookup x = ent.locals.lookup x := by
          intro x hxa hxm
          rw [hm2_l]
          simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxa]
          rw [hm1_l]
          simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxm]
        have hm2_mark : m2.locals.lookup (ofString "mark") = some (.val (.word hp_w)) := by
          rw [hm2_l]
          simp [HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "aux" ≠ ofString "mark" by decide]
          rw [hm1_l]
          simp [HolFiniteMapExact.lookup_update, FUPDATE]
        have hm2_aux : m2.locals.lookup (ofString "aux") = some (.val (.word hp_w)) := by
          rw [hm2_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        have hm2_p : m2.locals.lookup (ofString "p") = some (.val (.word p0)) :=
          (hm2_preserve _ (by decide) (by decide)).trans hent_p
        rw [evaluateHOLFiniteState_dec_total] at hnt_m2 hres_m2 ⊢
        dsimp only at hnt_m2 hres_m2 ⊢
        have he_src : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a))
            (.var .local (ofString "p")) = some (.val (.word p0)) := hm2_p
        rw [he_src] at hnt_m2 hres_m2 ⊢
        dsimp only at hnt_m2 hres_m2 ⊢
        rw [if_pos (hsh_w _)] at hnt_m2 hres_m2 ⊢
        set d1 := setVarHOLFinite (ofString "src") (.val (.word p0)) m2
        rw [evaluateHOLFiniteState_dec_total] at hnt_m2 hres_m2 ⊢
        dsimp only at hnt_m2 hres_m2 ⊢
        have hd1_aux : d1.locals.lookup (ofString "aux") = some (.val (.word hp_w)) := by
          simp [d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "src" ≠ ofString "aux" by decide]; exact hm2_aux
        have he_dst : @evalHOLExact 64 F _ d1.toExact (fun a => Classical.propDecidable (d1.memaddrs a))
            (.var .local (ofString "aux")) = some (.val (.word hp_w)) := hd1_aux
        rw [he_dst] at hnt_m2 hres_m2 ⊢
        dsimp only at hnt_m2 hres_m2 ⊢
        rw [if_pos (hsh_w _)] at hnt_m2 hres_m2 ⊢
        set d2 := setVarHOLFinite (ofString "dst") (.val (.word hp_w)) d1
        rw [evaluateHOLFiniteState_dec_total] at hnt_m2 hres_m2 ⊢
        dsimp only at hnt_m2 hres_m2 ⊢
        have he_w1 : @evalHOLExact 64 F _ d2.toExact (fun a => Classical.propDecidable (d2.memaddrs a))
            (.const 1#64) = some (.val (.word 1#64)) := rfl
        rw [he_w1] at hnt_m2 hres_m2 ⊢
        dsimp only at hnt_m2 hres_m2 ⊢
        rw [if_pos (hsh_w _)] at hnt_m2 hres_m2 ⊢
        set d3 := setVarHOLFinite (ofString "width") (.val (.word 1#64)) d2
        have hd3_AR : ArenaReady d3 :=
          localsFree_arenaReady m2 d3.locals d3.clock heff_m2.arena
        have heff_m2_d3 : WkBlockTxEnc.HeapByteEff m2 d3 Rl1 gw_int :=
          (WkBlockTxEnc.HeapByteEff.refl heff_m2.arena Rl1 gw_int).locals_clock d3.locals d3.clock
        have hd3_preserve : ∀ x, x ≠ ofString "width" → x ≠ ofString "dst" → x ≠ ofString "src" →
            d3.locals.lookup x = m2.locals.lookup x := by
          intro x hxw hxd hxs
          simp [d3, d2, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            Ne.symm hxw, Ne.symm hxd, Ne.symm hxs]
        have hinv_d3 : SortOuterInv p0 hp_w n0 esz0 d3 := by
          refine ⟨hd3_AR.1.code, hd3_AR.1.memaddrs,
            (hd3_preserve _ (by decide) (by decide) (by decide)).trans
              ((hm2_preserve _ (by decide) (by decide)).trans hent_n),
            (hd3_preserve _ (by decide) (by decide) (by decide)).trans
              ((hm2_preserve _ (by decide) (by decide)).trans hent_esz),
            ⟨kind0, (hd3_preserve _ (by decide) (by decide) (by decide)).trans
              ((hm2_preserve _ (by decide) (by decide)).trans hent_kind)⟩,
            hesz4, hn_lt63, hbound, haux_nw,
            hp_w, p0, 1#64, ?_, ?_, ?_, Or.inr rfl, Or.inl rfl, by decide⟩
          · simp [d3, d2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "width" ≠ ofString "dst" by decide]
          · simp [d3, d2, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "width" ≠ ofString "src" by decide,
              show ofString "dst" ≠ ofString "src" by decide]
          · simp [d3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        rw [evaluateHOLFiniteState_seq_line780] at hnt_m2 hres_m2 ⊢
        let outerP : ProgHOL 64 :=
          .while (.cmp .less (.var .local (ofString "width")) (.var .local (ofString "n")))
            sortOuterLoopBodyP
        have hnt_out : (evaluateHOLFiniteState d3 outerP).1 ≠ some .timeOut := by
          intro heq
          rcases hout : evaluateHOLFiniteState d3 outerP with ⟨ro, so⟩
          change evaluateHOLFiniteState d3 _ = (ro, so) at hout
          rw [hout] at heq hnt_m2; dsimp only at heq; subst ro; exact hnt_m2 rfl
        have hout_spec := eval_sortOuterLoop_while_bre d3 p0 hp_w n0 esz0 hinv_d3 hnt_out
        dsimp only at hout_spec
        rcases hout : evaluateHOLFiniteState d3
            (.while (.cmp .less (.var .local (ofString "width")) (.var .local (ofString "n")))
              sortOuterLoopBodyP) with ⟨ro, so⟩
        rw [hout] at hout_spec
        cases ro with
        | some r =>
          exfalso
          have hnr : ¬ Resumes (some r) := hout_spec.2 (by simp)
          cases r with
          | «continue» =>
            have hnc : (evaluateHOLFiniteState d3 outerP).1 ≠ some .continue :=
              evaluate_noTopContinue outerP rfl d3
            exact hnc (by simpa [outerP] using congrArg Prod.fst hout)
          | «break» =>
            have hnb : (evaluateHOLFiniteState d3 outerP).1 ≠ some .break :=
              InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak outerP rfl d3
            exact hnb (by simpa [outerP] using congrArg Prod.fst hout)
          | timeOut => exact hnt_out (by simpa [outerP] using congrArg Prod.fst hout)
          | returned _ =>
            rw [hout] at hres_m2; dsimp only at hres_m2; exact hnr hres_m2
          | exception _ _ =>
            rw [hout] at hres_m2; dsimp only at hres_m2; exact hnr hres_m2
          | error =>
            rw [hout] at hres_m2; dsimp only at hres_m2; exact hnr hres_m2
          | finalFfi _ =>
            rw [hout] at hres_m2; dsimp only at hres_m2; exact hnr hres_m2
        | none =>
          rw [hout] at hnt_m2 hres_m2
          dsimp only at hout_spec hnt_m2 hres_m2 ⊢
          obtain ⟨hinv_so, hso_loc, heff_so_bre⟩ := hout_spec.1 rfl
          rw [← hRl1_eq] at heff_so_bre
          have heff_so : WkBlockTxEnc.HeapByteEff d3 so Rl1 gw_int :=
            heapByteEff_of_bre hd3_AR heff_so_bre
          obtain ⟨_, _, hso_n, hso_esz, _, _, _, _, _,
            dst_f, src_f, width_f, _, hso_src, _, _, _, _⟩ := hinv_so
          have hso_p : so.locals.lookup (ofString "p") = some (.val (.word p0)) :=
            (hso_loc _ (by decide) (by decide) (by decide)).trans
              ((hd3_preserve _ (by decide) (by decide) (by decide)).trans hm2_p)
          have hso_mark : so.locals.lookup (ofString "mark") = some (.val (.word hp_w)) :=
            (hso_loc _ (by decide) (by decide) (by decide)).trans
              ((hd3_preserve _ (by decide) (by decide) (by decide)).trans hm2_mark)
          rw [evaluateHOLFiniteState_seq_line780] at hnt_m2 hres_m2 ⊢
          have hstep_copy : ∃ s_cp : PanSemStateFiniteExact 64 F,
              evaluateHOLFiniteState so
                (.ite (.cmp .notEqual (.var .local (ofString "src")) (.var .local (ofString "p")))
                  (.call (some (none, none)) (ofString "memcpy")
                    [.var .local (ofString "p"), .var .local (ofString "src"),
                     .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]])
                  .skip) = (none, s_cp) ∧
              WkBlockTxEnc.HeapByteEff so s_cp Rl1 gw_int ∧
              s_cp.locals = so.locals := by
            have hc_neq : @evalHOLExact 64 F _ so.toExact (fun a => Classical.propDecidable (so.memaddrs a))
                (.cmp .notEqual (.var .local (ofString "src")) (.var .local (ofString "p"))) =
                some (.val (.word (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .notEqual src_f p0 then 1 else 0))) := by
              by_cases hc : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .notEqual src_f p0 <;>
                simp [evalHOLExact, hso_src, hso_p, hc]
            by_cases hc : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .notEqual src_f p0
            · have hnt_cp : (evaluateHOLFiniteState so
                  (.call (some (none, none)) (ofString "memcpy")
                    [.var .local (ofString "p"), .var .local (ofString "src"),
                     .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]])).1 ≠
                  some .timeOut := by
                intro heq
                rw [evaluateHOLFiniteState_ite, hc_neq] at hnt_m2
                dsimp only at hnt_m2
                simp only [hc, ↓reduceIte] at hnt_m2
                rw [if_neg (by decide : ¬ ((1 : BitVec 64) = 0))] at hnt_m2
                rcases hcp : evaluateHOLFiniteState so _ with ⟨rcp, scp⟩
                rw [hcp] at heq hnt_m2; dsimp only at heq; subst rcp; exact hnt_m2 rfl
              have hmul_ev : evalAt so (.panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]) =
                  some (.val (.word (n0 * esz0))) := by
                simp [evalAt, evalHOLExact, evalListHOLExact, hso_n, hso_esz, panOpHOL,
                  valueIsWord, valueWord, List.all, List.map, Option.map]
              have hcp_spec := WkBlockTxEnc.eval_call_memcpy_heap so
                (.var .local (ofString "p")) (.var .local (ofString "src"))
                (.panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")])
                p0 src_f (n0 * esz0) Rl1 gw_int heff_so.arena.1.code heff_so.arena
                hso_p hso_src hmul_ev
                (fun _ => ⟨(p0.toNat, n0.toNat * esz0.toNat), List.Mem.head _, le_rfl, by rw [hmul_nw]⟩)
                hnt_cp
              dsimp only at hcp_spec
              rcases hcp : evaluateHOLFiniteState so
                  (.call (some (none, none)) (ofString "memcpy")
                    [.var .local (ofString "p"), .var .local (ofString "src"),
                     .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]) with ⟨rcp, scp⟩
              rw [hcp] at hcp_spec
              cases rcp with
              | some r =>
                exfalso
                have hnr : ¬ Resumes (some r) := hcp_spec.2 (by simp)
                rw [evaluateHOLFiniteState_ite, hc_neq] at hres_m2
                dsimp only at hres_m2
                simp only [hc, ↓reduceIte] at hres_m2
                rw [if_neg (by decide : ¬ ((1 : BitVec 64) = 0)), hcp] at hres_m2
                dsimp only at hres_m2
                exact hnr hres_m2
              | none =>
                obtain ⟨heff_cp, hloc_cp, _⟩ := hcp_spec.1 rfl
                refine ⟨scp, ?_, heff_cp, hloc_cp⟩
                rw [evaluateHOLFiniteState_ite, hc_neq]
                dsimp only
                simp only [hc, ↓reduceIte]
                rw [if_neg (by decide : ¬ ((1 : BitVec 64) = 0)), hcp]
            · refine ⟨so, ?_, WkBlockTxEnc.HeapByteEff.refl heff_so.arena Rl1 gw_int, rfl⟩
              rw [evaluateHOLFiniteState_ite, hc_neq]
              dsimp only
              simp only [hc, Bool.false_eq_true, ↓reduceIte, evaluateHOLFiniteState_skip]
          obtain ⟨s_cp, hcp_ev, heff_cp, hcp_loc⟩ := hstep_copy
          rw [hcp_ev] at hnt_m2 hres_m2 ⊢
          dsimp only at hnt_m2 hres_m2 ⊢
          rw [evaluateHOLFiniteState_seq_line780] at hnt_m2 hres_m2 ⊢
          have heff_ent_scp : WkBlockTxEnc.HeapByteEff ent s_cp Rl1 gw_int :=
            (((heff_m1.trans heff_m2).trans heff_m2_d3).trans heff_so).trans heff_cp
          have hnt_rel : (evaluateHOLFiniteState s_cp
              (.call (some (none, none)) (ofString "heap_release")
                [.var .local (ofString "mark")])).1 ≠ some .timeOut := by
            intro heq
            rcases hrel : evaluateHOLFiniteState s_cp _ with ⟨rrel, srel⟩
            rw [hrel] at heq hnt_m2; dsimp only at heq; subst rrel; exact hnt_m2 rfl
          have hscp_mark : @evalHOLExact 64 F _ s_cp.toExact (fun a => Classical.propDecidable (s_cp.memaddrs a))
              (.var .local (ofString "mark")) = some (.val (.word hp_w)) := by
            change s_cp.locals.lookup (ofString "mark") = _
            rw [hcp_loc]; exact hso_mark
          have hrel_spec := WkBlockTxEnc.eval_call_heap_release s_cp
            (.var .local (ofString "mark")) hp_w Rl1 gw_int
            heff_ent_scp.arena.1.code heff_ent_scp hgw_int hscp_mark
            (by rw [hhp_nat])
            (by rw [hhp_nat, hent_hp_gn]; exact hAR.2.1)
            (by rw [hhp_nat, hent_hp_gn]; exact hAR.2.2.1)
            (by rw [hhp_nat, hent_hp_gn]; exact hAR.2.2.2.2.2.2.1)
            hnt_rel
          dsimp only at hrel_spec
          rcases hrel : evaluateHOLFiniteState s_cp
              (.call (some (none, none)) (ofString "heap_release")
                [.var .local (ofString "mark")]) with ⟨rrel, srel⟩
          rw [hrel] at hrel_spec
          obtain ⟨rfl, _, hsrel_g, _, heff_ent_srel⟩ := hrel_spec
          dsimp only
          rw [evaluateHOLFiniteState_return]
          have hc0 : @evalHOLExact 64 F _ srel.toExact
              (fun a => Classical.propDecidable (srel.memaddrs a)) (.const 0#64) =
              some (.val (.word 0#64)) := rfl
          rw [hc0]
          have hsz : sizeOfShapeWithContextHOL srel.structs ShapeHOL.one ≤ 32 := by
            simp [sizeOfShapeWithContextHOL]
          have hsh1 : shapeEqHOL ShapeHOL.one ShapeHOL.one = true := by simp [shapeEqHOL]
          simp only [shapeOfHOLExact, hsz, ↓reduceIte]
          rw [if_pos hsh1]
          dsimp only [emptyLocalsHOLFinite]
          have hsrel_globals_eq : srel.globals = s.globals := by
            apply HolFiniteMapExact.ext
            funext k
            by_cases hk : k = ofString "heap_ptr"
            · subst hk
              have hlk1 : srel.globals.lookup (ofString "heap_ptr") = some (.val (.word hp_w)) := by
                rw [hsrel_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
              exact hlk1.trans hhp_g.symm
            · exact (heff_ent_srel.globals k (by simp [gw_int, hk])).symm
          have heff_s_srel : WkBlockTxEnc.HeapByteEff s { srel with locals := s.locals } Rl gw := by
            have heff_base : WkBlockTxEnc.HeapByteEff s { srel with locals := s.locals } Rl1 gw :=
              ⟨localsFree_arenaReady srel s.locals srel.clock heff_ent_srel.arena,
               heff_ent_srel.memaddrs, heff_ent_srel.hp_le, heff_ent_srel.fp_eq, heff_ent_srel.sp_le,
               heff_ent_srel.be, fun _ _ => by simp [hsrel_globals_eq],
               heff_ent_srel.out_dom, heff_ent_srel.cell_frame, heff_ent_srel.byte_frame⟩
            refine WkBlockTxEnc.HeapByteEff.mono heff_base ?_ (fun _ h => h)
            intro ivl hivl _
            simp only [Rl1, List.mem_cons, List.not_mem_nil, or_false] at hivl
            rcases hivl with rfl | rfl
            · exact Or.inl ⟨ivl_p, hivl_p, hp_lo, hp_hi⟩
            · exact Or.inr (Or.inr ⟨le_rfl, by rw [← hent_hp_gn, ← hhp_nat]; exact haux_hi⟩)
          exact ⟨fun _ => ⟨heff_s_srel, rfl, hsrel_globals_eq⟩, fun hne => False.elim (hne rfl)⟩
      · rcases hrun : ent.evaluateHOLFiniteState (sourceFnBody Guest.Software.guestFn_sort_elems) with ⟨res, st⟩
        cases res with
        | none => exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
        | some r =>
          cases r with
          | returned rv => exact False.elim (hres_ent (Or.inl ⟨rv, by rw [hrun]⟩))
          | «break» => exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
          | «continue» => exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
          | timeOut => exact False.elim (hnt_ent (by rw [hrun]))
          | error => exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
          | exception eid ev =>
            exact ⟨fun h => by simp at h, fun _ hres => hres_ent (by rw [hrun]; exact hres)⟩
          | finalFfi _ =>
            exact ⟨fun h => by simp at h, fun _ hres => by rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

private theorem bal_list_heapByteEff_worldStepSc {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {l esz : Nat} (hW : WorldOK s) (hl_nz : l ≠ 0)
    (hesz : esz = 16 ∨ esz = 24 ∨ esz = 40)
    (hslice_all : ∀ S Nd, WorldTypedWith s S Nd →
      LstOK s l ∧ WkBal.BalListSlice s l esz)
    (heff : WkBlockTxEnc.HeapByteEff s post [(memW s l, esz * memW s (l + 16))] []) :
    WorldStepSc (bufRegions []) [] stdKeep NoExtra s r post := by
  let I : Ivl := (memW s l, esz * memW s (l + 16))
  obtain ⟨S0, hWT0_raw⟩ := hW.2
  obtain ⟨Nd0, hWT0⟩ := (WkBal.worldTyped_iff_with s S0).1 hWT0_raw
  obtain ⟨hlst0, hslice0⟩ := hslice_all S0 Nd0 hWT0
  obtain ⟨_, hp_fix, _, _⟩ := WkBal.bal_list_slice_props hWT0.2.2.1 hl_nz hesz hlst0 hslice0
  have hesz_pos : 0 < esz := by rcases hesz with rfl | rfl | rfl <;> decide
  have hpos_arr : esz * memW s (l + 16) ≠ 0 :=
    ne_of_gt (Nat.mul_pos hesz_pos (by have := hlst0.1; omega))
  rcases hWT0.2.2.1.1 I hp_fix with hzero | ⟨_, hws_I⟩
  · exact False.elim (hpos_arr hzero)
  have hI_mod : I.1 % 8 = 0 ∧ I.2 % 8 = 0 := ⟨hws_I.1, hws_I.2.1⟩
  let hitB : Nat → Bool := fun x => decide (I.1 < x + 8 ∧ x < I.1 + I.2)
  have hhitB_iff : ∀ x, hitB x = true ↔ CellHits x I := by
    intro x; simp [hitB, CellHits]
  let mid : PanSemStateFiniteExact 64 F :=
    { s with memory := fun a => if hitB a.toNat then post.memory a else s.memory a }
  have halign_iff : ∀ b : Nat, b < 2 ^ 64 →
      (CellHits (panByteAlignHOL (BitVec.ofNat 64 b)).toNat I ↔ InIvl b I) := by
    intro b hb
    rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
    obtain ⟨h1, h2⟩ := hI_mod
    dsimp only [CellHits, InIvl]
    omega
  have hmid_bre : M11.ByteRegionEffect s mid [I] := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · intro a hna
      change (if hitB a.toNat = true then post.memory a else s.memory a) = s.memory a
      by_cases hh : hitB a.toNat = true
      · rw [if_pos hh]
        by_contra hne
        exact hna (heff.out_dom a hne)
      · rw [if_neg hh]
    · intro a hno
      have hnI : ¬ CellHits a.toNat I := hno I (List.Mem.head _)
      have hnh : ¬ (hitB a.toNat = true) := fun h => hnI ((hhitB_iff a.toNat).mp h)
      change (if hitB a.toNat = true then post.memory a else s.memory a) = s.memory a
      rw [if_neg hnh]
    · intro b hb hno
      have hnI : ¬ InIvl b I := hno I (List.Mem.head _)
      have hnc : ¬ CellHits (panByteAlignHOL (BitVec.ofNat 64 b)).toNat I :=
        fun hc => hnI ((halign_iff b hb).mp hc)
      have hnh : hitB (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = false :=
        Bool.eq_false_iff.mpr fun h => hnc ((hhitB_iff _).mp h)
      simp [memB, mid, hnh]
  have hws1 : WorldStepSc (bufRegions []) [] stdKeep NoExtra s r mid :=
    bal_list_payload_worldStepSc hW hl_nz hesz hslice_all hmid_bre
  have hW_mid : WorldOK mid :=
    hws1.worldOK_bufs (fun _ h => by simp at h) hW
  have hmid_post : WkBlockTxEnc.HeapByteEff mid post (bufRegions [] mid) [] := by
    refine ⟨heff.arena, heff.memaddrs, heff.hp_le, heff.fp_eq, heff.sp_le, heff.be,
      heff.globals, ?_, ?_, ?_⟩
    · intro a hne
      change post.memory a ≠ (if hitB a.toNat = true then post.memory a else s.memory a) at hne
      by_cases hh : hitB a.toNat = true
      · rw [if_pos hh] at hne; exact False.elim (hne rfl)
      · rw [if_neg hh] at hne; exact heff.out_dom a hne
    · intro a hne
      change post.memory a ≠ (if hitB a.toNat = true then post.memory a else s.memory a) at hne
      by_cases hh : hitB a.toNat = true
      · rw [if_pos hh] at hne; exact False.elim (hne rfl)
      · rw [if_neg hh] at hne
        rcases heff.cell_frame a hne with ⟨i, hi, _, hhit⟩ | hfg | hhf
        · rw [List.mem_singleton.mp hi] at hhit
          exact False.elim (hh ((hhitB_iff a.toNat).mpr hhit))
        · exact Or.inr (Or.inl hfg)
        · exact Or.inr (Or.inr hhf)
    · intro b hb hne
      by_cases hin : InIvl b I
      · exfalso
        have hc : CellHits (panByteAlignHOL (BitVec.ofNat 64 b)).toNat I :=
          (halign_iff b hb).mpr hin
        have hh : hitB (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = true :=
          (hhitB_iff _).mpr hc
        have hm_eq : memB mid b = memB post b := by
          simp [memB, mid, hh, heff.be]
        exact hne hm_eq.symm
      · have hnc : ¬ CellHits (panByteAlignHOL (BitVec.ofNat 64 b)).toNat I :=
          fun hc => hin ((halign_iff b hb).mp hc)
        have hh : hitB (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = false :=
          Bool.eq_false_iff.mpr fun h => hnc ((hhitB_iff _).mp h)
        have hm_eq : memB mid b = memB s b := by
          simp [memB, mid, hh]
        rw [hm_eq] at hne
        rcases heff.byte_frame b hb hne with ⟨i, hi, hbi⟩ | hfg | hhf
        · rw [List.mem_singleton.mp hi] at hbi
          exact False.elim (hin hbi)
        · exact Or.inr (Or.inl hfg)
        · exact Or.inr (Or.inr hhf)
  have hws2 : WorldStepSc (bufRegions []) [] stdKeep NoExtra mid r post :=
    heapByteEff_to_worldStepSc (r := r) (fun _ h => by simp at h) hW_mid hmid_post
  exact hws1.trans (fun _ h => by simp at h) (fun _ h => by simp at h) hws2

theorem eval_call_sort_elems_bal_list {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (pExp nExp eszExp kindExp tmpExp : ExpHOL 64)
    (p0 n0 esz0 kind0 tmp0 : BitVec 64) (l : Nat)
    (hcode : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hl_nz : l ≠ 0) (hesz : esz0.toNat = 16 ∨ esz0.toNat = 24 ∨ esz0.toNat = 40)
    (hslice_all : ∀ S Nd, WorldTypedWith s S Nd →
      LstOK s l ∧ WkBal.BalListSlice s l esz0.toNat)
    (hp : evalAt s pExp = some (.val (.word p0)))
    (hn : evalAt s nExp = some (.val (.word n0)))
    (hesz_ev : evalAt s eszExp = some (.val (.word esz0)))
    (hkind : evalAt s kindExp = some (.val (.word kind0)))
    (htmp : evalAt s tmpExp = some (.val (.word tmp0)))
    (hp_arr : p0.toNat = memW s l)
    (hn_cap : n0.toNat ≤ memW s (l + 16))
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "sort_elems")
        [pExp, nExp, eszExp, kindExp, tmpExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "sort_elems")
        [pExp, nExp, eszExp, kindExp, tmpExp])
    (out.1 = none →
      WorldStepSc (bufRegions []) [] stdKeep NoExtra s out.1 out.2 ∧
      out.2.locals = s.locals ∧
      out.2.globals = s.globals) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  obtain ⟨S0, hWT0_raw⟩ := hW.2
  obtain ⟨Nd0, hWT0⟩ := (WkBal.worldTyped_iff_with s S0).1 hWT0_raw
  obtain ⟨hlst0, hslice0⟩ := hslice_all S0 Nd0 hWT0
  obtain ⟨_, hp_fix, _, _⟩ := WkBal.bal_list_slice_props hWT0.2.2.1 hl_nz hesz hlst0 hslice0
  have hesz4 : 4 ≤ esz0.toNat := by rcases hesz with h | h | h <;> omega
  have hesz_pos : 0 < esz0.toNat := by omega
  have hpos_arr : esz0.toNat * memW s (l + 16) ≠ 0 :=
    ne_of_gt (Nat.mul_pos hesz_pos (by have := hlst0.1; omega))
  rcases hWT0.2.2.1.1 _ hp_fix with hzero | ⟨hal_arr, _⟩
  · exact False.elim (hpos_arr hzero)
  have halloc_hi : memW s l + esz0.toNat * memW s (l + 16) < 2 ^ 64 := by
    rcases hal_arr with ⟨_, hhi⟩ | ⟨_, hhi⟩
    · have hhl : globN s "heap_ptr" ≤ heapLimit := hW.1.2.2.1
      have : heapLimit < 2 ^ 64 := by decide
      dsimp only at hhi; omega
    · have : scratchEnd < 2 ^ 64 := by decide
      dsimp only at hhi; omega
  have hmul_le : n0.toNat * esz0.toNat ≤ esz0.toNat * memW s (l + 16) := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right esz0.toNat hn_cap
  have hbound : p0.toNat + n0.toNat * esz0.toNat < 2 ^ 64 := by omega
  have hspec := eval_call_sort_elems_heap s pExp nExp eszExp kindExp tmpExp
    p0 n0 esz0 kind0 tmp0 [(memW s l, esz0.toNat * memW s (l + 16))] []
    hcode hW.1 hp hn hesz_ev hkind htmp hesz4 hbound
    (fun _ => ⟨(memW s l, esz0.toNat * memW s (l + 16)), List.Mem.head _,
      by omega, by omega⟩)
    hnt
  dsimp only at hspec ⊢
  refine ⟨fun hnone => ?_, hspec.2⟩
  obtain ⟨heff, hloc, hglob⟩ := hspec.1 hnone
  exact ⟨bal_list_heapByteEff_worldStepSc hW hl_nz hesz hslice_all heff, hloc, hglob⟩

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

/-! ## BAL helper chain: `htab_item`, `bal_reads_slot_distinct`, `bal_ensure_account`, `add_storage_read`, `add_touched_account` -/

theorem lookup_htab_item_bal :
    originalRuntimeCode.lookup (ofString "htab_item") =
      some ([(ofString "t", .one), (ofString "ordinal", .one)],
        sourceFnBody Guest.Software.guestFn_htab_item, .comb [.one, .one, .one]) :=
  lookup_of_guestAst_getElem 143 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_item) rfl

theorem htab_item_no_catchable_exn {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (e : MlS) (v : ValueHOL 64)
    (hne : e ≠ ofString "TrapErr") :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_item)).1 ≠
      some (.exception e v) :=
  WkBal.evaluate_noCatchableRaise (fun _ => false) (fun _ h => by cases h)
    (sourceFnBody Guest.Software.guestFn_htab_item) rfl s hcode e v hne

theorem htab_item_t_nonzero {F : Type}
    (s : PanSemStateFiniteExact 64 F) (tw ordw : BitVec 64)
    (hG : GuestInv s)
    (ht : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (ho : s.locals.lookup (ofString "ordinal") = some (.val (.word ordw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_item)).1 = some (.returned v)) :
    tw ≠ 0 := by
  rintro rfl
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_htab_item,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map] at hret
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  have hnot24 : ¬ s.memaddrs 24#64 := by
    rw [hG.memaddrs, M13.ordinaryDomain_iff]
    simp
  have hev0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "ordinal"))
        (.load .one (.op .add [.var .local (ofString "t"), .const 24#64]))) = none := by
    simp [evalHOLExact, evalListHOLExact, ht, ho, valueIsWord, valueWord, wordOpHOL, wordOp,
      memLoadHOLExact, hnot24]
  rw [hev0] at hret
  simp at hret

theorem htab_item_ret_spec {F : Type}
    (s : PanSemStateFiniteExact 64 F) (tw ordw : BitVec 64)
    (ht : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (ho : s.locals.lookup (ofString "ordinal") = some (.val (.word ordw)))
    (hW : HtabWF s tw.toNat)
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_item)).1 = some (.returned v)) :
    ∃ f0 f1 f2 : BitVec 64,
      v = .rStruct [.val (.word f0), .val (.word f1), .val (.word f2)] ∧
      (f0 ≠ 0 →
        Inside (f1.toNat, hdr s tw.toNat 1) (hdr s tw.toNat 4)
          (hdr s tw.toNat 4 + (hdr s tw.toNat 10 + 1) * hdr s tw.toNat 1) ∧
        Inside (f1.toNat, hdr s tw.toNat 0) (hdr s tw.toNat 4)
          (hdr s tw.toNat 4 + (hdr s tw.toNat 10 + 1) * hdr s tw.toNat 1) ∧
        f2.toNat ∈ htabValues s tw.toNat) := by
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  obtain ⟨hB, _, hklen_pos, hklen_max, hstride_eq, hncap_ge, hnext_pos, hnext_le,
    L0, I0, Fr0, hL_len, hnodup, hmem_iff, _, hL_spec, _⟩ := hW
  have hfp_hdr : (tw.toNat, 88) ∈ htabFootprint s tw.toNat := by simp [htabFootprint]
  have hfp_keys : (hdr s tw.toNat 4, (hdr s tw.toNat 10 + 1) * hdr s tw.toNat 1) ∈ htabFootprint s tw.toNat := by
    simp [htabFootprint]
  have hfp_nodes : (hdr s tw.toNat 5, (hdr s tw.toNat 10 + 1) * 32) ∈ htabFootprint s tw.toNat := by
    simp [htabFootprint]
  have hfp_ord : (hdr s tw.toNat 6, (hdr s tw.toNat 10 + 1) * 8) ∈ htabFootprint s tw.toNat := by
    simp [htabFootprint]
  have htw_hi : tw.toNat + 88 ≤ heapEnd := (hB _ hfp_hdr).1.2
  have hkeys_hi : hdr s tw.toNat 4 + (hdr s tw.toNat 10 + 1) * hdr s tw.toNat 1 ≤ heapEnd := (hB _ hfp_keys).1.2
  have hnodes_hi : hdr s tw.toNat 5 + (hdr s tw.toNat 10 + 1) * 32 ≤ heapEnd := (hB _ hfp_nodes).1.2
  have hord_hi : hdr s tw.toNat 6 + (hdr s tw.toNat 10 + 1) * 8 ≤ heapEnd := (hB _ hfp_ord).1.2
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_htab_item,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map] at hret
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  rcases hcv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "ordinal"))
        (.load .one (.op .add [.var .local (ofString "t"), .const 24#64]))) with _ | cv
  · rw [hcv] at hret; simp at hret
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _
    rotate_left
    · rw [hcv] at hret; simp at hret
    · rw [hcv] at hret; simp at hret
    · rw [hcv] at hret; dsimp only at hret
      by_cases hcw : cw = 0
      · subst hcw
        rw [if_pos rfl, evaluateHOLFiniteState_skip] at hret
        dsimp only at hret
        -- Extract `ordw.toNat < hdr s tw.toNat 3` from `hcv`:
        have hord_lt_cnt : ordw.toNat < hdr s tw.toNat 3 := by
          simp only [evalHOLExact, evalListHOLExact, ht, ho, valueIsWord, valueWord,
            wordOpHOL, wordOp, memLoadHOLExact, isWfShapeExactHOL, List.all, List.map, Option.map,
            Bool.and_self, List.foldr, BitVec.add_zero, ↓reduceIte] at hcv
          by_cases hd24 : s.memaddrs (tw + (24#64 + 0))
          · rw [if_pos hd24] at hcv
            rcases hm24 : s.memory (tw + (24#64 + 0)) with ⟨cntw⟩
            rw [hm24] at hcv
            have hcnt_eq : hdr s tw.toNat 3 = cntw.toNat := by
              unfold hdr memW
              have had : BitVec.ofNat 64 (tw.toNat + 8 * 3) = tw + (24#64 + 0) := by
                apply BitVec.eq_of_toNat_eq
                simp only [BitVec.add_zero, BitVec.toNat_ofNat, BitVec.toNat_add]
                rfl
              rw [had, hm24]
            rw [hcnt_eq]
            by_cases hlt : ordw < cntw
            · exact BitVec.lt_def.1 hlt
            · exfalso
              have hcmp : Flapjack.Compiler.Encoders.Asm.wordCmpHOL Cmp.notLower ordw cntw = true := by
                simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt]
              simp [hcmp] at hcv
          · rw [if_neg hd24] at hcv; simp at hcv
        have hidx_L : ordw.toNat < L0.length := by omega
        have hleaf_mem_L : L0[ordw.toNat] ∈ L0 := List.getElem_mem hidx_L
        have hleaf_rng : 1 ≤ L0[ordw.toNat] ∧ L0[ordw.toNat] < hdr s tw.toNat 8 :=
          (hmem_iff _).1 (List.mem_append_left _ (List.mem_append_left _ hleaf_mem_L))
        have hleaf_le_ncap : L0[ordw.toNat] ≤ hdr s tw.toNat 10 := by omega
        have hord_le_ncap : ordw.toNat ≤ hdr s tw.toNat 10 := by
          have hnd_L : L0.Nodup := (List.nodup_append.1 (List.nodup_append.1 hnodup).1).1
          have hsub : ∀ {M : List Nat}, M.Nodup → (∀ x ∈ M, x ∈ List.range' 1 (hdr s tw.toNat 8 - 1)) →
              M.length ≤ (List.range' 1 (hdr s tw.toNat 8 - 1)).length := by
            intro M hnd hinc
            have hfl : (M.filter (· ∈ List.range' 1 (hdr s tw.toNat 8 - 1))).length = M.length := by
              rw [List.filter_eq_self.2 (fun x hx => decide_eq_true (hinc x hx))]
            have hnd2 : (List.range' 1 (hdr s tw.toNat 8 - 1)).Nodup := List.nodup_range'
            have hperm : List.Subperm M (List.range' 1 (hdr s tw.toNat 8 - 1)) := by
              rw [List.subperm_ext_iff]
              intro y hy
              by_cases hym : y ∈ M
              · have hcM : M.count y ≤ 1 := by
                  clear hfl hinc hy hym
                  induction M with
                  | nil => simp
                  | cons a as ih =>
                    obtain ⟨hna, hnd_as⟩ := List.nodup_cons.1 hnd
                    by_cases hay : a = y
                    · subst hay
                      rw [List.count_cons_self, List.count_eq_zero.2 hna]
                    · rw [List.count_cons_of_ne hay]
                      exact ih hnd_as
                have hcR : 1 ≤ (List.range' 1 (hdr s tw.toNat 8 - 1)).count y :=
                  List.count_pos_iff.2 (hinc y hym)
                omega
              · rw [List.count_eq_zero.2 hym]
                omega
            exact hperm.length_le
          have hle := hsub hnd_L (fun x hx => by
            have hxr := (hmem_iff x).1 (List.mem_append_left _ (List.mem_append_left _ hx))
            exact List.mem_range'.2 ⟨x - 1, by omega, by omega⟩)
          rw [List.length_range'] at hle
          omega
        -- Step through `dec "leaf"`, `dec "stride"`, `dec "keyp"`, `dec "val"`, `return`:
        rw [evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
        split at hret
        · simp at hret
        · rename_i v_leaf hv_leaf
          split at hret
          · rename_i hsh_leaf
            rcases v_leaf with ⟨⟨leafw⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hsh_leaf; done)
            rw [evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
            split at hret
            · simp at hret
            · rename_i v_stride hv_stride
              split at hret
              · rename_i hsh_stride
                rcases v_stride with ⟨⟨stridew⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hsh_stride; done)
                rw [evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
                split at hret
                · simp at hret
                · rename_i v_keyp hv_keyp
                  split at hret
                  · rename_i hsh_keyp
                    rcases v_keyp with ⟨⟨keypw⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hsh_keyp; done)
                    rw [evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
                    split at hret
                    · simp at hret
                    · rename_i v_val hv_val
                      split at hret
                      · rename_i hsh_val
                        rcases v_val with ⟨⟨valw⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hsh_val; done)
                        rw [evaluateHOLFiniteState_return] at hret
                        have hk_eq : (ofString "val" == ofString "keyp") = false := by decide
                        have hk_self : (ofString "keyp" == ofString "keyp") = true := by decide
                        have hv_self : (ofString "val" == ofString "val") = true := by decide
                        simp only [evalHOLExact, evalListHOLExact, setVarHOLFinite,
                          HolFiniteMapExact.lookup_update, FUPDATE,
                          hk_eq, hk_self, hv_self, Option.map] at hret
                        simp only [Bool.false_eq_true, ↓reduceIte,
                          shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL,
                          List.map, List.foldr, Nat.reduceAdd, Nat.reduceLeDiff,
                          Option.some.injEq, PanSemResultExact.returned.injEq] at hret
                        subst hret
                        -- Compute `leafw.toNat = L0[ordw.toNat]`:
                        have hleaf_eq : leafw.toNat = L0[ordw.toNat] := by
                          have hmul_no : ordw.toNat * 8 < 2 ^ 64 := by omega
                          simp only [evalHOLExact, evalListHOLExact, ht, ho, valueIsWord, valueWord,
                            wordOpHOL, wordOp, panOpHOL, memLoadHOLExact, isWfShapeExactHOL,
                            List.all, List.map, Option.map, Bool.and_self, List.foldr,
                            BitVec.add_zero, ↓reduceIte] at hv_leaf
                          by_cases hd48 : s.memaddrs (tw + (48#64 + 0))
                          · rw [if_pos hd48] at hv_leaf
                            rcases hm48 : s.memory (tw + (48#64 + 0)) with ⟨ordbase⟩
                            rw [hm48] at hv_leaf
                            simp only [List.all, List.map, Option.map, valueIsWord, valueWord,
                              Bool.and_self, List.foldr, BitVec.add_zero, ↓reduceIte] at hv_leaf
                            have hhdr6 : hdr s tw.toNat 6 = ordbase.toNat := by
                              unfold hdr memW
                              have had : BitVec.ofNat 64 (tw.toNat + 8 * 6) = tw + (48#64 + 0) := by
                                apply BitVec.eq_of_toNat_eq
                                simp only [BitVec.add_zero, BitVec.toNat_ofNat, BitVec.toNat_add]; rfl
                              rw [had, hm48]
                            by_cases hd_el : s.memaddrs (ordbase + (ordw * 8#64 + 0))
                            · rw [if_pos hd_el] at hv_leaf
                              rcases hm_el : s.memory (ordbase + (ordw * 8#64 + 0)) with ⟨lfw⟩
                              rw [hm_el] at hv_leaf
                              simp only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hv_leaf
                              subst hv_leaf
                              have h_ord_memW : memW s (hdr s tw.toNat 6 + 8 * ordw.toNat) = lfw.toNat := by
                                rw [hhdr6]; unfold memW
                                have had : BitVec.ofNat 64 (ordbase.toNat + 8 * ordw.toNat) =
                                    ordbase + (ordw * 8#64 + 0) := by
                                  apply BitVec.eq_of_toNat_eq
                                  have hfit : ordbase.toNat + 8 * ordw.toNat < 2 ^ 64 := by rw [← hhdr6]; omega
                                  have hz : ordw * 8#64 + (0 : BitVec 64) = ordw * 8#64 := BitVec.add_zero _
                                  rw [hz, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit,
                                    BitVec.toNat_add, BitVec.toNat_mul]
                                  change ordbase.toNat + 8 * ordw.toNat =
                                    (ordbase.toNat + (ordw.toNat * 8) % 2 ^ 64) % 2 ^ 64
                                  rw [Nat.mod_eq_of_lt hmul_no, Nat.mul_comm ordw.toNat 8, Nat.mod_eq_of_lt hfit]
                                rw [had, hm_el]
                              exact h_ord_memW.symm.trans (hL_spec ordw.toNat hidx_L).1
                            · rw [if_neg hd_el] at hv_leaf; simp at hv_leaf
                          · rw [if_neg hd48] at hv_leaf; simp at hv_leaf
                        have hml_word : ∀ (ad : BitVec 64) (dom : BitVec 64 → Prop) (dec : DecidablePred dom)
                            (vt : ValueHOL 64),
                            dom = s.memaddrs →
                            @memLoadHOLExact 64 _ .one ad dom dec s.memory s.structs = some vt →
                            ∃ w : BitVec 64, s.memory ad = .word w ∧ vt = .val (.word w) := by
                          intro ad dom dec vt hdom hml
                          unfold memLoadHOLExact at hml
                          by_cases hd : dom ad
                          · rw [if_pos hd] at hml
                            rcases hm : s.memory ad with ⟨w⟩
                            rw [hm] at hml
                            exact ⟨w, rfl, (Option.some.inj hml).symm⟩
                          · rw [if_neg hd] at hml; cases hml
                        -- Compute `stridew.toNat = hdr s tw.toNat 1`:
                        have hstridew_eq : stridew.toNat = hdr s tw.toNat 1 := by
                          have hne_lt : (ofString "leaf" == ofString "t") = false := by decide
                          simp only [evalHOLExact, evalListHOLExact, PanSemStateFiniteExact.toExact,
                            setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                            hne_lt, Bool.false_eq_true, ht, valueIsWord, valueWord, wordOpHOL, wordOp,
                            isWfShapeExactHOL, List.all, List.map, Option.map, Bool.and_self,
                            List.foldr, BitVec.add_zero, ↓reduceIte] at hv_stride
                          obtain ⟨stw, hm8, hv_eq⟩ := hml_word (tw + (8#64 + 0)) _ _ _ rfl hv_stride
                          simp only [ValueHOL.val.injEq, HolWordLab.word.injEq] at hv_eq
                          subst hv_eq
                          unfold hdr memW
                          have had : BitVec.ofNat 64 (tw.toNat + 8 * 1) = tw + (8#64 + 0) := by
                            apply BitVec.eq_of_toNat_eq
                            simp only [BitVec.add_zero, BitVec.toNat_ofNat, BitVec.toNat_add]; rfl
                          rw [had, hm8]
                        -- Compute `keypw.toNat = hdr s tw.toNat 4 + leafw.toNat * stridew.toNat`:
                        have hkeyp_eq : keypw.toNat = hdr s tw.toNat 4 + leafw.toNat * stridew.toNat := by
                          have hmul_no : leafw.toNat * stridew.toNat < 2 ^ 64 := by
                            rw [hleaf_eq, hstridew_eq]
                            have hst_pos : 1 ≤ hdr s tw.toNat 1 := by omega
                            have hle : L0[ordw.toNat] * hdr s tw.toNat 1 < (hdr s tw.toNat 10 + 1) * hdr s tw.toNat 1 :=
                              Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
                            omega
                          have hne_st : (ofString "stride" == ofString "t") = false := by decide
                          have hne_lt : (ofString "leaf" == ofString "t") = false := by decide
                          have hne_sl : (ofString "stride" == ofString "leaf") = false := by decide
                          have hll : (ofString "leaf" == ofString "leaf") = true := by decide
                          have hss : (ofString "stride" == ofString "stride") = true := by decide
                          let s_ls := setVarHOLFinite (ofString "stride") (ValueHOL.val (HolWordLab.word stridew))
                            (setVarHOLFinite (ofString "leaf") (ValueHOL.val (HolWordLab.word leafw)) s)
                          have hkp_ev : @evalHOLExact 64 F _ s_ls.toExact (fun a => Classical.propDecidable (s_ls.memaddrs a))
                              (.op .add
                                [.load .one (.op .add [.var .local (ofString "t"), .const 32#64]),
                                 .panop .mul [.const leafw, .const stridew]]) =
                              some (.val (.word keypw)) := by
                            simpa only [s_ls, evalHOLExact, evalListHOLExact, PanSemStateFiniteExact.toExact,
                              setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                              hne_st, hne_lt, hne_sl, hll, hss, Bool.false_eq_true, ↓reduceIte] using hv_keyp
                          have ht_ls : s_ls.locals.lookup (ofString "t") = some (.val (.word tw)) := by
                            simp only [s_ls, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                              hne_st, hne_lt, Bool.false_eq_true, ↓reduceIte, ht]
                          simp only [evalHOLExact, evalListHOLExact, ht_ls, valueIsWord, valueWord,
                            wordOpHOL, wordOp, panOpHOL, memLoadHOLExact, isWfShapeExactHOL,
                            List.all, List.map, Option.map, Bool.and_self, List.foldr,
                            BitVec.add_zero, ↓reduceIte] at hkp_ev
                          by_cases hd32 : s_ls.memaddrs (tw + (32#64 + 0))
                          · rw [if_pos hd32] at hkp_ev
                            rcases hm32 : s_ls.memory (tw + (32#64 + 0)) with ⟨kbase⟩
                            rw [hm32] at hkp_ev
                            simp only [List.all, List.map, Option.map, valueIsWord, valueWord,
                              Bool.and_self, List.foldr, ↓reduceIte,
                              Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hkp_ev
                            have hhdr4 : hdr s tw.toNat 4 = kbase.toNat := by
                              unfold hdr memW
                              have had : BitVec.ofNat 64 (tw.toNat + 8 * 4) = tw + (32#64 + 0) := by
                                apply BitVec.eq_of_toNat_eq
                                simp only [BitVec.add_zero, BitVec.toNat_ofNat, BitVec.toNat_add]; rfl
                              have hm32' : s.memory (tw + (32#64 + 0)) = .word kbase := hm32
                              rw [had, hm32']
                            subst hkp_ev
                            have hz : leafw * stridew + (0 : BitVec 64) = leafw * stridew := BitVec.add_zero _
                            rw [hz, hhdr4, BitVec.toNat_add, BitVec.toNat_mul,
                              Nat.mod_eq_of_lt hmul_no]
                            have hfit : kbase.toNat + leafw.toNat * stridew.toNat < 2 ^ 64 := by
                              rw [← hhdr4, hleaf_eq, hstridew_eq]
                              have hlt : L0[ordw.toNat] * hdr s tw.toNat 1 < (hdr s tw.toNat 10 + 1) * hdr s tw.toNat 1 :=
                                Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
                              omega
                            exact Nat.mod_eq_of_lt hfit
                          · rw [if_neg hd32] at hkp_ev; simp at hkp_ev
                        -- Compute `valw.toNat = nodeF s (hdr s tw.toNat 5) leafw.toNat 8`:
                        have hval_eq : valw.toNat = nodeF s (hdr s tw.toNat 5) leafw.toNat 8 := by
                          have hmul_no : leafw.toNat * 32 < 2 ^ 64 := by rw [hleaf_eq]; omega
                          have hne_kt : (ofString "keyp" == ofString "t") = false := by decide
                          have hne_st : (ofString "stride" == ofString "t") = false := by decide
                          have hne_lt : (ofString "leaf" == ofString "t") = false := by decide
                          have hne_kl : (ofString "keyp" == ofString "leaf") = false := by decide
                          have hne_sl : (ofString "stride" == ofString "leaf") = false := by decide
                          have hll : (ofString "leaf" == ofString "leaf") = true := by decide
                          let s_lsk := setVarHOLFinite (ofString "keyp") (ValueHOL.val (HolWordLab.word keypw))
                            (setVarHOLFinite (ofString "stride") (ValueHOL.val (HolWordLab.word stridew))
                              (setVarHOLFinite (ofString "leaf") (ValueHOL.val (HolWordLab.word leafw)) s))
                          have hv_ev : @evalHOLExact 64 F _ s_lsk.toExact (fun a => Classical.propDecidable (s_lsk.memaddrs a))
                              (.load .one (.op .add
                                [.load .one (.op .add [.var .local (ofString "t"), .const 40#64]),
                                 .panop .mul [.const leafw, .const 32#64],
                                 .const 8#64])) =
                              some (.val (.word valw)) := by
                            simpa only [s_lsk, evalHOLExact, evalListHOLExact, PanSemStateFiniteExact.toExact,
                              setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                              hne_kt, hne_st, hne_lt, hne_kl, hne_sl, hll, Bool.false_eq_true, ↓reduceIte] using hv_val
                          have ht_lsk : s_lsk.locals.lookup (ofString "t") = some (.val (.word tw)) := by
                            simp only [s_lsk, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                              hne_kt, hne_st, hne_lt, Bool.false_eq_true, ↓reduceIte, ht]
                          simp only [evalHOLExact, evalListHOLExact, ht_lsk, valueIsWord, valueWord,
                            wordOpHOL, wordOp, panOpHOL, memLoadHOLExact, isWfShapeExactHOL,
                            List.all, List.map, Option.map, Bool.and_self, List.foldr,
                            BitVec.add_zero, ↓reduceIte] at hv_ev
                          by_cases hd40 : s_lsk.memaddrs (tw + (40#64 + 0))
                          · rw [if_pos hd40] at hv_ev
                            rcases hm40 : s_lsk.memory (tw + (40#64 + 0)) with ⟨ndbase⟩
                            rw [hm40] at hv_ev
                            simp only [List.all, List.map, Option.map, valueIsWord, valueWord,
                              Bool.and_self, List.foldr, ↓reduceIte] at hv_ev
                            have hhdr5 : hdr s tw.toNat 5 = ndbase.toNat := by
                              unfold hdr memW
                              have had : BitVec.ofNat 64 (tw.toNat + 8 * 5) = tw + (40#64 + 0) := by
                                apply BitVec.eq_of_toNat_eq
                                simp only [BitVec.add_zero, BitVec.toNat_ofNat, BitVec.toNat_add]; rfl
                              have hm40' : s.memory (tw + (40#64 + 0)) = .word ndbase := hm40
                              rw [had, hm40']
                            by_cases hd_v : s_lsk.memaddrs (ndbase + (leafw * 32#64 + (8#64 + 0)))
                            · rw [if_pos hd_v] at hv_ev
                              rcases hm_v : s_lsk.memory (ndbase + (leafw * 32#64 + (8#64 + 0))) with ⟨vw⟩
                              rw [hm_v] at hv_ev
                              simp only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hv_ev
                              subst hv_ev
                              rw [hhdr5]; unfold nodeF memW
                              have had : BitVec.ofNat 64 (ndbase.toNat + 32 * leafw.toNat + 8) =
                                  ndbase + (leafw * 32#64 + (8#64 + 0)) := by
                                apply BitVec.eq_of_toNat_eq
                                have hfit : ndbase.toNat + 32 * leafw.toNat + 8 < 2 ^ 64 := by
                                  rw [← hhdr5, hleaf_eq]; omega
                                have hz : (8#64 : BitVec 64) + 0 = 8#64 := BitVec.add_zero _
                                rw [hz, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit, BitVec.toNat_add,
                                  BitVec.toNat_add, BitVec.toNat_mul]
                                change ndbase.toNat + 32 * leafw.toNat + 8 =
                                  (ndbase.toNat + ((leafw.toNat * 32) % 2 ^ 64 + 8) % 2 ^ 64) % 2 ^ 64
                                rw [Nat.mod_eq_of_lt hmul_no, Nat.mul_comm leafw.toNat 32,
                                  Nat.mod_eq_of_lt (by omega)]
                                omega
                              have hm_v' : s.memory (ndbase + (leafw * 32#64 + (8#64 + 0))) = .word vw := hm_v
                              rw [had, hm_v']
                            · rw [if_neg hd_v] at hv_ev; simp at hv_ev
                          · rw [if_neg hd40] at hv_ev; simp at hv_ev
                        refine ⟨1#64, keypw, valw, rfl, fun _ => ⟨?_, ?_, ?_⟩⟩
                        · rw [hkeyp_eq, hleaf_eq, hstridew_eq]
                          have hle : (L0[ordw.toNat] + 1) * hdr s tw.toNat 1 ≤ (hdr s tw.toNat 10 + 1) * hdr s tw.toNat 1 :=
                            Nat.mul_le_mul_right _ (by omega)
                          have heq : L0[ordw.toNat] * hdr s tw.toNat 1 + hdr s tw.toNat 1 =
                              (L0[ordw.toNat] + 1) * hdr s tw.toNat 1 := by ring
                          dsimp [Inside]
                          exact ⟨by omega, by omega⟩
                        · rw [hkeyp_eq, hleaf_eq, hstridew_eq]
                          have hle : (L0[ordw.toNat] + 1) * hdr s tw.toNat 1 ≤ (hdr s tw.toNat 10 + 1) * hdr s tw.toNat 1 :=
                            Nat.mul_le_mul_right _ (by omega)
                          have hk_le_st : hdr s tw.toNat 0 ≤ hdr s tw.toNat 1 := by omega
                          have heq : L0[ordw.toNat] * hdr s tw.toNat 1 + hdr s tw.toNat 1 =
                              (L0[ordw.toNat] + 1) * hdr s tw.toNat 1 := by ring
                          dsimp [Inside]
                          exact ⟨by omega, by omega⟩
                        · unfold htabValues
                          refine List.mem_map.2 ⟨ordw.toNat, List.mem_range.2 hord_lt_cnt, ?_⟩
                          rw [(hL_spec ordw.toNat hidx_L).1, ← hleaf_eq, ← hval_eq]
                      · simp at hret
                  · simp at hret
              · simp at hret
          · simp at hret
      · rw [if_neg hcw, evaluateHOLFiniteState_return] at hret
        simp [evalHOLExact, evalListHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hret
        exact ⟨0, 0, 0, hret.symm, fun h => absurd rfl h⟩

theorem decCall_htab_item_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (x : MlS) (tExp ordExp : ExpHOL 64) (cont : ProgHOL 64)
    (hG : GuestInv s)
    (hnt : (evaluateHOLFiniteState s
      (.decCall x (.comb [.one, .one, .one]) (ofString "htab_item") [tExp, ordExp] cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall x (.comb [.one, .one, .one]) (ofString "htab_item") [tExp, ordExp] cont)).1) :
    ∃ (tw ordw f0 f1 f2 : BitVec 64) (ck : Nat),
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) tExp =
        some (.val (.word tw)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) ordExp =
        some (.val (.word ordw)) ∧
      tw ≠ 0 ∧
      (HtabWF s tw.toNat → f0 ≠ 0 →
        Inside (f1.toNat, hdr s tw.toNat 1) (hdr s tw.toNat 4)
          (hdr s tw.toNat 4 + (hdr s tw.toNat 10 + 1) * hdr s tw.toNat 1) ∧
        Inside (f1.toNat, hdr s tw.toNat 0) (hdr s tw.toNat 4)
          (hdr s tw.toNat 4 + (hdr s tw.toNat 10 + 1) * hdr s tw.toNat 1) ∧
        f2.toNat ∈ htabValues s tw.toNat) ∧
      let s_cont := setVarHOLFinite x (.rStruct [.val (.word f0), .val (.word f1), .val (.word f2)])
        { s with clock := ck }
      (evaluateHOLFiniteState s_cont cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState s_cont cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x (.comb [.one, .one, .one]) (ofString "htab_item") [tExp, ordExp] cont)).1 =
        (evaluateHOLFiniteState s_cont cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x (.comb [.one, .one, .one]) (ofString "htab_item") [tExp, ordExp] cont)).2 =
        { (evaluateHOLFiniteState s_cont cont).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState s_cont cont).2.locals (x, s.locals.lookup x) } := by
  dsimp only
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [tExp, ordExp] with _ | vals
  · rw [hargs] at hres; exact absurd hres WkBal.not_resumes_error
  · rw [hargs] at hnt hres; dsimp only at hnt hres
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_item") vals with _ | ⟨body, callee, rs⟩
    · rw [hl] at hres; exact absurd hres WkBal.not_resumes_error
    · rw [hl] at hnt hres; dsimp only at hnt hres
      by_cases hcz : s.clock = 0
      · rw [if_pos hcz] at hnt; exact absurd rfl hnt
      · rw [if_neg hcz] at hnt hres
        have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "htab_item") vals =
            some (body, callee, rs) := by rwa [← hG.code]
        have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "htab_item") vals body callee rs hl'
        simp only [lookupCodeHOLExact, lookup_htab_item_bal] at hx
        rcases vals with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
        · simp at hx
        · simp at hx
        · rcases v1 with ⟨⟨tw⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨ordw⟩⟩ | _ | _ <;>
            simp [shapeOfHOLExact, shapeEqHOL] at hx
          obtain ⟨_, rfl, hc_eq, rfl⟩ := hx
          have hev_pair : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
              [tExp, ordExp] = some [.val (.word tw), .val (.word ordw)] := hargs
          have hev_t : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) tExp =
              some (.val (.word tw)) := by
            rcases he1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) tExp with _ | x1
            · simp [evalListHOLExact, he1] at hev_pair
            · rcases he2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) ordExp with _ | x2
              · simp [evalListHOLExact, he1, he2] at hev_pair
              · simp [evalListHOLExact, he1, he2] at hev_pair
                exact congrArg some hev_pair.1
          have hev_o : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) ordExp =
              some (.val (.word ordw)) := by
            rcases he2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) ordExp with _ | x2
            · simp [evalListHOLExact, hev_t, he2] at hev_pair
            · simp [evalListHOLExact, hev_t, he2] at hev_pair
              exact congrArg some hev_pair
          have hc_t : (callEntryStateHOLFinite s callee).locals.lookup (ofString "t") =
              some (.val (.word tw)) := by
            change callee.lookup (ofString "t") = some (.val (.word tw))
            rw [← hc_eq]
            simp [show ofString "t" ≠ ofString "ordinal" by decide]
          have hc_o : (callEntryStateHOLFinite s callee).locals.lookup (ofString "ordinal") =
              some (.val (.word ordw)) := by
            change callee.lookup (ofString "ordinal") = some (.val (.word ordw))
            rw [← hc_eq]
            simp
          have hlf : M13.LocFrame (callEntryStateHOLFinite s callee)
              (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
                (sourceFnBody Guest.Software.guestFn_htab_item)).2 :=
            Wave8Contracts.M15.evaluate_readOnlyProg (fun _ => false) (fun _ h => by cases h)
              (sourceFnBody Guest.Software.guestFn_htab_item) rfl _ hG.code
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
              (sourceFnBody Guest.Software.guestFn_htab_item) with ⟨rg, sg⟩
          have hrun2 : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
              (sourceFnBody Guest.Software.guestFn_htab_item)).2 = sg := congrArg Prod.snd hrun
          rw [hrun] at hnt hres; rw [hrun2] at hlf
          cases rg with
          | none => exact absurd hres WkBal.not_resumes_error
          | some rg' =>
            cases rg' with
            | timeOut => exact absurd rfl hnt
            | exception e ev =>
              exfalso
              rcases hres with ⟨_, hh⟩ | ⟨e', ev', hh, hne⟩
              · simp at hh
              · dsimp only at hh
                injection hh with hh'; injection hh' with he1 he2
                subst he1 he2
                exact htab_item_no_catchable_exn (callEntryStateHOLFinite s callee) hG.code e ev hne
                  (congrArg Prod.fst hrun)
            | returned vg =>
              dsimp only at hnt hres
              split at hnt
              · rename_i hsh
                rw [if_pos hsh] at hres
                have htw_nz : tw ≠ 0 :=
                  htab_item_t_nonzero (callEntryStateHOLFinite s callee) tw ordw
                    (guestInv_callEntry s callee hG) hc_t hc_o vg (congrArg Prod.fst hrun)
                have hvg_shape : ∃ f0 f1 f2 : BitVec 64,
                    vg = .rStruct [.val (.word f0), .val (.word f1), .val (.word f2)] := by
                  rcases vg with _ | vs_g | _
                  · simp [shapeOfHOLExact, shapeEqHOL] at hsh
                  · rcases vs_g with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | _⟩⟩⟩
                    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
                    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
                    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
                    · rcases x0 with ⟨⟨f0⟩⟩ | _ | _ <;> rcases x1 with ⟨⟨f1⟩⟩ | _ | _ <;>
                        rcases x2 with ⟨⟨f2⟩⟩ | _ | _ <;>
                        simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
                      exact ⟨f0, f1, f2, rfl⟩
                    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
                  · simp [shapeOfHOLExact, shapeEqHOL] at hsh
                obtain ⟨f0, f1, f2, rfl⟩ := hvg_shape
                have hsg_eq : { sg with locals := s.locals } = { s with clock := sg.clock } := by
                  unfold M13.LocFrame at hlf
                  rw [hlf]; rfl
                rw [hsg_eq] at hnt hres
                let s_cont := setVarHOLFinite x (.rStruct [.val (.word f0), .val (.word f1), .val (.word f2)])
                  { s with clock := sg.clock }
                let co := evaluateHOLFiniteState s_cont cont
                have heval_eq : evaluateHOLFiniteState s
                    (.decCall x (.comb [.one, .one, .one]) (ofString "htab_item") [tExp, ordExp] cont) =
                    (co.1, { co.2 with locals := HolFiniteMapExact.resVarEq co.2.locals (x, s.locals.lookup x) }) := by
                  rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs]
                  dsimp only
                  rw [hl]; dsimp only
                  rw [if_neg hcz, hrun]; dsimp only
                  rw [if_pos hsh, hsg_eq]
                refine ⟨tw, ordw, f0, f1, f2, sg.clock, hev_t, hev_o, htw_nz, fun hW hf0 => ?_,
                  by intro hto; rw [hto] at hnt; exact hnt rfl,
                  hres, by rw [heval_eq], by rw [heval_eq]⟩
                have hent_W : HtabWF (callEntryStateHOLFinite s callee) tw.toNat :=
                  (WkBal.htabWF_with_locals s callee (s.clock - 1) tw.toNat).2 hW
                obtain ⟨f0', f1', f2', hveq, hin_spec⟩ :=
                  htab_item_ret_spec (callEntryStateHOLFinite s callee) tw ordw hc_t hc_o hent_W
                    (.rStruct [.val (.word f0), .val (.word f1), .val (.word f2)]) (congrArg Prod.fst hrun)
                simp only [ValueHOL.rStruct.injEq, List.cons.injEq, ValueHOL.val.injEq,
                  HolWordLab.word.injEq, and_true] at hveq
                obtain ⟨rfl, rfl, rfl⟩ := hveq
                exact hin_spec hf0
              · rename_i hsh
                rw [if_neg hsh] at hres
                exact absurd hres WkBal.not_resumes_error
            | «break» | «continue» | error =>
              exact absurd hres WkBal.not_resumes_error
            | finalFfi _ =>
              exfalso
              rcases hres with ⟨_, hh⟩ | ⟨_, _, hh, _⟩ <;> simp at hh
        · simp at hx

theorem bal_reads_slot_distinct {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hT : TablesTyped s S) {ad0 : Nat} (had0 : ad0 ∈ balRecords s) :
    let t0 := memW s (ad0 + 8)
    t0 ∈ S ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∧
    globN s "bal_accounts" ≠ t0 ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) := by
  dsimp only
  have ht0_S : memW s (ad0 + 8) ∈ S := (hT.2.2.2.2.2.2.2.2.2.1 ad0 had0).2.1
  have ht0_nz : memW s (ad0 + 8) ≠ 0 := WkBal.htab_nonzero_of_wf (hT.2.1 _ ht0_S).1
  have ht0_wrs : (memW s (ad0 + 8), "bal.reads") ∈ worldRoleSlots s := by
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [ht0_nz]⟩
    apply List.mem_append.2; right
    exact List.mem_flatMap.2 ⟨ad0, had0, by simp⟩
  have hslot_ne : ∀ u r, (u, r) ∈ worldRoleSlots s → r ≠ "bal.reads" → u ≠ memW s (ad0 + 8) := by
    intro u r hur hner heq
    subst heq
    obtain ⟨i1, hi1, heq1⟩ := List.mem_iff_getElem.1 hur
    obtain ⟨i2, hi2, heq2⟩ := List.mem_iff_getElem.1 ht0_wrs
    have hroles := hT.2.2.2.2.2.2.2.2.2.2.2
    rcases Nat.lt_trichotomy i1 i2 with hlt | rfl | hgt
    · have hp := List.pairwise_iff_getElem.1 hroles.2.1 i1 i2 hi1 hi2 hlt
      rw [heq1, heq2] at hp
      exact hner (hp rfl).1
    · rw [heq1] at heq2; exact hner (Prod.mk.inj heq2).2
    · have hp := List.pairwise_iff_getElem.1 hroles.2.1 i2 i1 hi2 hi1 hgt
      rw [heq1, heq2] at hp
      exact hner (hp rfl).1.symm
  refine ⟨ht0_S, ?_, ?_, ?_, ?_, ?_⟩
  · intro hbs h32
    apply hslot_ne (memW s (globN s "bs" + 32)) "bs+32" _ (by decide) h32
    have h32_nz : memW s (globN s "bs" + 32) ≠ 0 := by rw [h32]; exact ht0_nz
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [h32_nz]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    simp [recRoles, hbs]
  · intro hts h32
    apply hslot_ne (memW s (globN s "ts" + 32)) "ts+32" _ (by decide) h32
    have h32_nz : memW s (globN s "ts" + 32) ≠ 0 := by rw [h32]; exact ht0_nz
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [h32_nz]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_right
    simp [recRoles, hts]
  · intro hba
    apply hslot_ne (globN s "bal_accounts") "bal_accounts" _ (by decide) hba
    have hba_nz : globN s "bal_accounts" ≠ 0 := by rw [hba]; exact ht0_nz
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [hba_nz]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_right; simp
  · intro ad had h0
    apply hslot_ne (memW s ad) "bal.stor" _ (by decide) h0
    have h0_nz : memW s ad ≠ 0 := by rw [h0]; exact ht0_nz
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [h0_nz]⟩
    apply List.mem_append_right
    exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
  · intro hws h32
    apply hslot_ne (memW s (globN s "ws" + 32)) "ws+32" _ (by decide) h32
    have h32_nz : memW s (globN s "ws" + 32) ≠ 0 := by rw [h32]; exact ht0_nz
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [h32_nz]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    simp [recRoles, hws]

theorem bal_accounts_slot_distinct {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hT : TablesTyped s S) (hba_nz : globN s "bal_accounts" ≠ 0) :
    let ba := globN s "bal_accounts"
    ba ∈ S ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ ba) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ ba) ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ ba ∧ memW s (ad + 8) ≠ ba) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ ba) := by
  dsimp only
  have hba_S : globN s "bal_accounts" ∈ S := by
    rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by decide) with h0 | hS
    · exact absurd h0 hba_nz
    · exact hS
  have hba_wrs : (globN s "bal_accounts", "bal_accounts") ∈ worldRoleSlots s := by
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [hba_nz]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_right; simp
  have hslot_ne : ∀ u r, (u, r) ∈ worldRoleSlots s → r ≠ "bal_accounts" → u ≠ globN s "bal_accounts" := by
    intro u r hur hner heq
    subst heq
    obtain ⟨i1, hi1, heq1⟩ := List.mem_iff_getElem.1 hur
    obtain ⟨i2, hi2, heq2⟩ := List.mem_iff_getElem.1 hba_wrs
    have hroles := hT.2.2.2.2.2.2.2.2.2.2.2
    rcases Nat.lt_trichotomy i1 i2 with hlt | rfl | hgt
    · have hp := List.pairwise_iff_getElem.1 hroles.2.1 i1 i2 hi1 hi2 hlt
      rw [heq1, heq2] at hp
      exact hner (hp rfl).1
    · rw [heq1] at heq2; exact hner (Prod.mk.inj heq2).2
    · have hp := List.pairwise_iff_getElem.1 hroles.2.1 i2 i1 hi2 hi1 hgt
      rw [heq1, heq2] at hp
      exact hner (hp rfl).1.symm
  refine ⟨hba_S, ?_, ?_, ?_, ?_⟩
  · intro hbs h32
    apply hslot_ne (memW s (globN s "bs" + 32)) "bs+32" _ (by decide) h32
    have h32_nz : memW s (globN s "bs" + 32) ≠ 0 := by rw [h32]; exact hba_nz
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [h32_nz]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    simp [recRoles, hbs]
  · intro hts h32
    apply hslot_ne (memW s (globN s "ts" + 32)) "ts+32" _ (by decide) h32
    have h32_nz : memW s (globN s "ts" + 32) ≠ 0 := by rw [h32]; exact hba_nz
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [h32_nz]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_right
    simp [recRoles, hts]
  · intro ad had
    refine ⟨fun h0 => ?_, fun h8 => ?_⟩
    · apply hslot_ne (memW s ad) "bal.stor" _ (by decide) h0
      have h0_nz : memW s ad ≠ 0 := by rw [h0]; exact hba_nz
      unfold worldRoleSlots
      refine List.mem_filter.2 ⟨?_, by simp [h0_nz]⟩
      apply List.mem_append_right
      exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
    · apply hslot_ne (memW s (ad + 8)) "bal.reads" _ (by decide) h8
      have h8_nz : memW s (ad + 8) ≠ 0 := by rw [h8]; exact hba_nz
      unfold worldRoleSlots
      refine List.mem_filter.2 ⟨?_, by simp [h8_nz]⟩
      apply List.mem_append_right
      exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
  · intro hws h32
    apply hslot_ne (memW s (globN s "ws" + 32)) "ws+32" _ (by decide) h32
    have h32_nz : memW s (globN s "ws" + 32) ≠ 0 := by rw [h32]; exact hba_nz
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [h32_nz]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    simp [recRoles, hws]

theorem seq_store_word_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (eaddr eval_ : ExpHOL 64) (cont : ProgHOL 64)
    (aw vw : BitVec 64)
    (ha : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) eaddr =
      some (.val (.word aw)))
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) eval_ =
      some (.val (.word vw)))
    (hnt : (evaluateHOLFiniteState s (.seq (.store eaddr eval_) cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (.seq (.store eaddr eval_) cont)).1) :
    s.memaddrs aw ∧
    let mid : PanSemStateFiniteExact 64 F := { s with memory := Wave8Contracts.M26.updW s.memory aw vw }
    (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
    Resumes (evaluateHOLFiniteState mid cont).1 ∧
    evaluateHOLFiniteState s (.seq (.store eaddr eval_) cont) = evaluateHOLFiniteState mid cont := by
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store, ha, hv] at hnt hres ⊢
  simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hnt hres ⊢
  by_cases hd : s.memaddrs aw
  · refine ⟨hd, ?_⟩
    simp only [hd, ↓reduceIte] at hnt hres ⊢
    exact ⟨hnt, hres, rfl⟩
  · simp only [hd, ↓reduceIte] at hres
    exact absurd hres WkBal.not_resumes_error

theorem lookup_bal_ensure_account :
    originalRuntimeCode.lookup (ofString "bal_ensure_account") =
      some ([(ofString "addr", .one)], sourceFnBody Guest.Software.guestFn_bal_ensure_account, .one) :=
  lookup_of_guestAst_getElem 412 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bal_ensure_account) rfl

theorem lookup_add_storage_read :
    originalRuntimeCode.lookup (ofString "add_storage_read") =
      some ([(ofString "addr", .one), (ofString "slot", .one)],
        sourceFnBody Guest.Software.guestFn_add_storage_read, .one) :=
  lookup_of_guestAst_getElem 415 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_add_storage_read) rfl

theorem lookup_add_touched_account :
    originalRuntimeCode.lookup (ofString "add_touched_account") =
      some ([(ofString "addr", .one)], sourceFnBody Guest.Software.guestFn_add_touched_account, .one) :=
  lookup_of_guestAst_getElem 419 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_add_touched_account) rfl

theorem seq_store_ad_slot_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (adw off vw : BitVec 64) (vname : MlS) (cont : ProgHOL 64)
    (hAR : ArenaReady s)
    (had_lk : s.locals.lookup (ofString "ad") = some (.val (.word adw)))
    (hv_lk : s.locals.lookup vname = some (.val (.word vw)))
    (had_lo : sourceBase ≤ adw.toNat)
    (had_hi : adw.toNat + 40 ≤ heapLimit)
    (had8 : adw.toNat % 8 = 0)
    (hoff8 : off.toNat % 8 = 0)
    (hoff_hi : off.toNat + 8 ≤ 40)
    (hnt : (evaluateHOLFiniteState s
      (.seq (.store (.op .add [.var .local (ofString "ad"), .const off]) (.var .local vname)) cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq (.store (.op .add [.var .local (ofString "ad"), .const off]) (.var .local vname)) cont)).1) :
    let mid : PanSemStateFiniteExact 64 F := { s with memory := Wave8Contracts.M26.updW s.memory (adw + off) vw }
    ArenaReady mid ∧
    mid.globals = s.globals ∧
    mid.locals = s.locals ∧
    mid.be = s.be ∧
    (adw + off).toNat = adw.toNat + off.toNat ∧
    memW mid (adw.toNat + off.toNat) = vw.toNat ∧
    (∀ k : Nat, k ≠ adw.toNat + off.toNat → k < 2 ^ 64 → memW mid k = memW s k) ∧
    FrameOutside s mid [] (adw.toNat, 40) ∧
    (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
    Resumes (evaluateHOLFiniteState mid cont).1 ∧
    evaluateHOLFiniteState s
      (.seq (.store (.op .add [.var .local (ofString "ad"), .const off]) (.var .local vname)) cont) =
      evaluateHOLFiniteState mid cont := by
  dsimp only
  have h264 : heapLimit < 2 ^ 64 ∧ heapLimit ≤ heapEnd := ⟨by decide, by decide⟩
  have haddr_nat : (adw + off).toNat = adw.toNat + off.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hz_off : off + (0 : BitVec 64) = off := BitVec.add_zero _
  have ha_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "ad"), .const off]) = some (.val (.word (adw + off))) := by
    simp only [evalHOLExact, evalListHOLExact, had_lk, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_off, ↓reduceIte]
  have hv_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local vname) = some (.val (.word vw)) := by
    simp [evalHOLExact, hv_lk]
  obtain ⟨_, hnt', hres', heq⟩ := seq_store_word_resumes s _ _ cont (adw + off) vw ha_ev hv_ev hnt hres
  set mid : PanSemStateFiniteExact 64 F := { s with memory := Wave8Contracts.M26.updW s.memory (adw + off) vw }
  have hAR_mid : ArenaReady mid := ⟨guestInv_congr (s := s) rfl rfl rfl rfl hAR.1, hAR.2⟩
  have hmw_eq : memW mid (adw.toNat + off.toNat) = vw.toNat := by
    unfold memW
    have hb_eq : BitVec.ofNat 64 (adw.toNat + off.toNat) = adw + off := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), haddr_nat]
    simp [mid, Wave8Contracts.M26.updW, hb_eq]
  have hmw_ne : ∀ k : Nat, k ≠ adw.toNat + off.toNat → k < 2 ^ 64 → memW mid k = memW s k := by
    intro k hne hk64
    unfold memW
    have hb_ne : BitVec.ofNat 64 k ≠ adw + off := by
      intro heq_b
      have := congrArg BitVec.toNat heq_b
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64, haddr_nat] at this
      exact hne this
    simp [mid, Wave8Contracts.M26.updW, hb_ne]
  have hfr : FrameOutside s mid [] (adw.toNat, 40) := by
    intro a _ hno
    have hne : a ≠ adw + off := by
      rintro rfl
      exact hno ⟨by dsimp only; omega, by dsimp only; omega⟩
    simp [mid, Wave8Contracts.M26.updW, hne]
  exact ⟨hAR_mid, rfl, rfl, rfl, haddr_nat, hmw_eq, hmw_ne, hfr, hnt', hres', heq⟩

theorem frameOutside_ad_store {F : Type} {s a b : PanSemStateFiniteExact 64 F}
    {keep : List Ivl} {ad : Nat}
    (had_lo : globN s "heap_ptr" ≤ ad)
    (had_hi : ad + 40 ≤ globN a "heap_ptr")
    (hba : globN b "heap_ptr" = globN a "heap_ptr")
    (h1 : FrameOutside s a keep (globN s "heap_ptr", globN a "heap_ptr" - globN s "heap_ptr"))
    (h2 : FrameOutside a b [] (ad, 40)) :
    FrameOutside s b keep (globN s "heap_ptr", globN b "heap_ptr" - globN s "heap_ptr") := by
  rw [hba]
  intro x hno hnhf
  have hno_ad : ¬ CellHits x.toNat (ad, 40) := by
    intro ⟨c1, c2⟩; dsimp only at c1 c2
    exact hnhf ⟨by dsimp only; omega, by dsimp only; omega⟩
  exact (h2 x (fun _ h => by cases h) hno_ad).trans (h1 x hno hnhf)

theorem flatMap_set_decomp {α β : Type} (f : α → List β) :
    ∀ (xs : List α) (i : Nat) (hi : i < xs.length) (x : α),
      (xs.set i x).flatMap f =
        (xs.take i).flatMap f ++ f x ++ (xs.drop (i + 1)).flatMap f ∧
      xs.flatMap f =
        (xs.take i).flatMap f ++ f (xs[i]) ++ (xs.drop (i + 1)).flatMap f
  | [], _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | _ :: xs, 0, _, x => by
    simp [List.set, List.take, List.drop, List.flatMap_cons]
  | y :: xs, i + 1, hi, x => by
    have hi' : i < xs.length := Nat.lt_of_succ_lt_succ hi
    obtain ⟨h1, h2⟩ := flatMap_set_decomp f xs i hi' x
    simp only [List.set, List.take, List.drop, List.flatMap_cons, List.getElem_cons_succ,
      h1, h2, List.append_assoc]
    exact ⟨trivial, trivial⟩

theorem bal_ensure_account_miss_worldStepSc {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    {r : Option (PanSemResultExact 64)}
    (adw t1w t2w l1w l2w l3w : BitVec 64)
    (hp2 hp3 hp4 hp5 hp6 : Nat)
    (hW0 : WorldOK s)
    (hARp : ArenaReady post)
    (hbe : post.be = s.be)
    (hba_nz : globN s "bal_accounts" ≠ 0)
    (hg_nonHeap : ∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = post.globals.lookup k)
    (had_eq : adw.toNat = globN s "heap_ptr")
    (had8 : adw.toNat % 8 = 0)
    (hhp_order : adw.toNat + 40 ≤ hp2 ∧ hp2 ≤ hp3 ∧ hp3 ≤ hp4 ∧ hp4 ≤ hp5 ∧ hp5 ≤ hp6 ∧
      hp6 ≤ globN post "heap_ptr")
    (hnew_t1 : HtabWF post t1w.toNat ∧ hdr post t1w.toNat 0 = 32 ∧ hdr post t1w.toNat 3 = 0 ∧
      ∀ i ∈ htabFootprint post t1w.toNat, Allocated post i ∧ Inside i (adw.toNat + 40) hp2)
    (hnew_t2 : HtabWF post t2w.toNat ∧ hdr post t2w.toNat 0 = 32 ∧ hdr post t2w.toNat 3 = 0 ∧
      ∀ i ∈ htabFootprint post t2w.toNat, Allocated post i ∧ Inside i hp2 hp3)
    (ht12_ne : t1w.toNat ≠ t2w.toNat)
    (hl1 : l1w.toNat ≠ 0 ∧ LstOK post l1w.toNat ∧
      lstObjects post l1w.toNat 40 = [(l1w.toNat, 24), (l1w.toNat + 24, 160)] ∧
      Disj (l1w.toNat, 24) (l1w.toNat + 24, 160) ∧
      ∀ i ∈ lstObjects post l1w.toNat 40, Allocated post i ∧ WordsOK post i ∧ Inside i hp3 hp4)
    (hl2 : l2w.toNat ≠ 0 ∧ LstOK post l2w.toNat ∧
      lstObjects post l2w.toNat 16 = [(l2w.toNat, 24), (l2w.toNat + 24, 64)] ∧
      Disj (l2w.toNat, 24) (l2w.toNat + 24, 64) ∧
      ∀ i ∈ lstObjects post l2w.toNat 16, Allocated post i ∧ WordsOK post i ∧ Inside i hp4 hp5)
    (hl3 : l3w.toNat ≠ 0 ∧ LstOK post l3w.toNat ∧
      lstObjects post l3w.toNat 24 = [(l3w.toNat, 24), (l3w.toNat + 24, 48)] ∧
      Disj (l3w.toNat, 24) (l3w.toNat + 24, 48) ∧
      ∀ i ∈ lstObjects post l3w.toNat 24, Allocated post i ∧ WordsOK post i ∧ Inside i hp5 hp6)
    (had_words : memW post adw.toNat = t1w.toNat ∧
      memW post (adw.toNat + 8) = t2w.toNat ∧
      memW post (adw.toNat + 16) = l1w.toNat ∧
      memW post (adw.toNat + 24) = l2w.toNat ∧
      memW post (adw.toNat + 32) = l3w.toNat)
    (hba_wf : HtabWF post (globN s "bal_accounts"))
    (hba_hdr0 : hdr post (globN s "bal_accounts") 0 = hdr s (globN s "bal_accounts") 0)
    (hba_fp : ∀ i ∈ htabFootprint post (globN s "bal_accounts"), Allocated post i ∧
      ((∃ j ∈ htabFootprint s (globN s "bal_accounts"), Inside i j.1 (j.1 + j.2)) ∨
        Inside i hp6 (globN post "heap_ptr")))
    (hba_vals : htabValues post (globN s "bal_accounts") =
        htabValues s (globN s "bal_accounts") ++ [adw.toNat] ∨
      ∃ i0 < (htabValues s (globN s "bal_accounts")).length,
        htabValues post (globN s "bal_accounts") =
          (htabValues s (globN s "bal_accounts")).set i0 adw.toNat)
    (hfr : FrameOutside s post
      ((globN s "scratch_ptr", 0) :: htabFootprint s (globN s "bal_accounts"))
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")) :
    WorldStepSc (bufRegions []) ["heap_ptr"] stdKeep NoExtra s r post ∧
    adw.toNat ∈ balRecords post := by
  set ba := globN s "bal_accounts"
  have hAs := hW0.1
  have hhp : globN s "heap_ptr" ≤ globN post "heap_ptr" := by omega
  have hsp_eq : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    globN_eq_of_lookup (hg_nonHeap (ofString "scratch_ptr") (by decide))
  have hag : AllocatorGrows s post := ⟨hhp, by rw [hsp_eq]⟩
  have hgk : GlobalsKept ["heap_ptr"] s post := fun k hk =>
    hg_nonHeap k (fun h => hk (List.mem_singleton.2 h))
  have hcore : ∀ g ∈ coreWorldGlobals, globN post g = globN s g := fun g hg => by
    have hne : ofString g ≠ ofString "heap_ptr" := by revert g hg; decide
    exact globN_eq_of_lookup (hg_nonHeap (ofString g) hne)
  have hba_g : globN post "bal_accounts" = ba := hcore "bal_accounts" (by decide)
  have hba_nz_p : globN post "bal_accounts" ≠ 0 := by rw [hba_g]; exact hba_nz
  have hrecs_s : balRecords s = htabValues s ba := by
    unfold balRecords htabValues; simp [ba, hba_nz]
  have hrecs_p : balRecords post = htabValues post ba := by
    unfold balRecords htabValues; simp [hba_g, ba, hba_nz]
  have had_in_recs_p : adw.toNat ∈ balRecords post := by
    rw [hrecs_p]
    rcases hba_vals with happ | ⟨i0, hi0, hset⟩
    · rw [happ]; simp
    · rw [hset]; exact List.mem_iff_getElem.2 ⟨i0, by simp [hi0], by simp⟩
  have hf_al : (globN s "heap_ptr") % 8 = 0 ∧ (globN post "heap_ptr" - globN s "heap_ptr") % 8 = 0 := by
    have h1 := hAs.2.2.2.2.2.2.1; have h2 := hARp.2.2.2.2.2.2.1; omega
  have hsp8_s : globN s "scratch_ptr" % 8 = 0 := hAs.2.2.2.2.2.2.2.2.1
  obtain ⟨S0, hWT0_ex⟩ := hW0.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
  have hba_S0 : ba ∈ S0 := (bal_accounts_slot_distinct hWT0.1 hba_nz).1
  have hk_al0 : ∀ j ∈ (globN s "scratch_ptr", 0) :: htabFootprint s ba, j.1 % 8 = 0 ∧ j.2 % 8 = 0 := by
    intro j hj
    rcases List.mem_cons.1 hj with rfl | hj_fp
    · exact ⟨hsp8_s, rfl⟩
    · have hw := ((hWT0.1.2.1 ba hba_S0).1.1 j hj_fp).2
      exact ⟨hw.1, hw.2.1⟩
  have hrk : RecordsKept (bufRegions []) stdKeep s post := by
    intro rec hrec hgnz k hk _
    have hrec_sz : ∃ sz, (rec.1, sz) ∈ typedRecords ∧ sz ≠ 0 ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
      simp only [stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · refine ⟨40, by simp [typedRecords], by decide, ?_⟩; simp at hk; omega
      · refine ⟨80, by simp [typedRecords], by decide, ?_⟩; simp at hk; omega
      · refine ⟨72, by simp [typedRecords], by decide, ?_⟩; simp at hk; omega
      · refine ⟨88, by simp [typedRecords], by decide, ?_⟩; simp at hk; omega
    obtain ⟨sz, htr, hsz_nz, hk8, hksz⟩ := hrec_sz
    have hmf := typedRecord_mem_fixedObjects s htr
    simp only [hgnz, ↓reduceIte] at hmf
    rcases hWT0.2.2.1.1 _ hmf with h0 | ⟨hal, hwords⟩
    · omega
    · have hhi := (ivl_allocated_bound hAs.2 hal).2
      have hg8 : (globN s rec.1) % 8 = 0 := hwords.1
      have hu_rec : IvlUnhit s post (globN s rec.1, sz) :=
        R10Shards.P26_P28.ivlUnhit_of_frameOutside_aligned hsz_nz hfr hk_al0 hf_al
          (fun j hj => by
            rcases List.mem_cons.1 hj with rfl | hj_fp
            · exact Or.inr (Or.inl rfl)
            · exact (((hWT0.1.2.1 ba hba_S0).2 j hj_fp).2 _ hmf).flip)
          (disj_fresh_of_zero_or_allocated hAs.2 hARp.2 hhp (Or.inr hal))
      exact memW_eq_of_ivlUnhit hu_rec (by omega) hhi ⟨by omega, by omega⟩
  refine ⟨⟨⟨hARp, hhp, hgk, hrk, fun S Nd hWT _ => ?_⟩, by rw [hsp_eq]⟩, had_in_recs_p⟩
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  obtain ⟨hba_S, hno_bs32, hno_ts32, hno_ad, hno_ws32⟩ := bal_accounts_slot_distinct hT hba_nz
  have hk_al : ∀ j ∈ (globN s "scratch_ptr", 0) :: htabFootprint s ba, j.1 % 8 = 0 ∧ j.2 % 8 = 0 := by
    intro j hj
    rcases List.mem_cons.1 hj with rfl | hj_fp
    · exact ⟨hsp8_s, rfl⟩
    · have hw := ((hT.2.1 ba hba_S).1.1 j hj_fp).2
      exact ⟨hw.1, hw.2.1⟩
  have hunhit_disj : ∀ i : Ivl, i.2 ≠ 0 → (∀ j ∈ htabFootprint s ba, Disj i j) →
      Allocated s i → IvlUnhit s post i := fun i hipos hdi hal =>
    R10Shards.P26_P28.ivlUnhit_of_frameOutside_aligned hipos hfr hk_al hf_al
      (fun j hj => by
        rcases List.mem_cons.1 hj with rfl | hj_fp
        · exact Or.inr (Or.inl rfl)
        · exact hdi j hj_fp)
      (disj_fresh_of_zero_or_allocated hAs.2 hARp.2 hhp (Or.inr hal))
  have hu_other : ∀ u ∈ S, u ≠ ba → ∀ i ∈ htabFootprint s u, IvlUnhit s post i := fun u hu hne i hi =>
    hunhit_disj i (htabFootprint_len_pos (hT.2.1 u hu).1 hi)
      (fun j hj => hT.2.2.1 u hu ba hba_S hne i hi j hj)
      (((hT.2.1 u hu).2 i hi).1)
  have hu_fix : ∀ i ∈ fixedObjects s, i.2 ≠ 0 → IvlUnhit s post i := fun i hi hipos =>
    hunhit_disj i hipos (fun j hj => (((hT.2.1 ba hba_S).2 j hj).2 i hi).flip)
      (by rcases hF.1 i hi with h0 | ⟨hal, _⟩; exact absurd h0 hipos; exact hal)
  have hu_nd_rec : ∀ n ∈ Nd, IvlUnhit s post (nodeIvl s n) := fun n hn => by
    have hmem : nodeIvl s n ∈ nodeExtents s Nd := by
      unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
    have hpos : (nodeIvl s n).2 ≠ 0 := by
      dsimp [nodeIvl]; unfold nodeSize; split_ifs <;> decide
    exact hunhit_disj _ hpos (fun j hj => (hTr.2.1 _ hmem).1 ba hba_S j hj)
      ((hTr.1.1 n hn).2.1)
  have hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k) := by
    intro n hn h12 hlen0 k hk
    have h264 : heapLimit ≤ 2 ^ 64 := by decide
    rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_p, hin_p, _⟩
    · exact absurd h0 hlen0
    · have hp_ne : (memW s (n + 32), memW s (n + 40)) ∈ nodeExtents s Nd := by
        unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩
      have ha_lt : memW s (n + 32) + k < 2 ^ 64 := by have := hin_p.2; omega
      let c := panByteAlignHOL (BitVec.ofNat 64 (memW s (n + 32) + k))
      have hc_nat : c.toNat = (memW s (n + 32) + k) / 8 * 8 := by
        rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
      have hmem := hfr c
        (fun j hj hcj => by
          obtain ⟨h1, h2⟩ := hcj
          rw [hc_nat] at h1 h2
          rcases List.mem_cons.1 hj with rfl | hj_fp
          · dsimp only at h1 h2; omega
          · have hj_al := ((hT.2.1 ba hba_S).1.1 j hj_fp).2
            have hj1 := hj_al.1; have hj2 := hj_al.2.1
            have hdj := (hTr.2.1 _ hp_ne).1 ba hba_S j hj_fp
            rcases hdj with d | d | d | d <;> omega)
        (fun hcf => by
          obtain ⟨h1, h2⟩ := hcf
          dsimp at h1 h2
          rw [hc_nat] at h1 h2
          have hp_hp8 : (globN post "heap_ptr") % 8 = 0 := hARp.2.2.2.2.2.2.1
          have hdj := disj_fresh_of_zero_or_allocated hAs.2 hARp.2 hhp (Or.inr hal_p)
          try dsimp at hdj
          rcases hdj with d | d | d | d <;> omega)
      unfold memB
      change (match post.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (memW s (n + 32) + k)) v post.be).toNat) =
             (match s.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (memW s (n + 32) + k)) v s.be).toNat)
      rw [hmem, hbe]
  have hm0 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 :=
    WkBal.mem0_8_16_eq_of_heap_sp_frame hAs.2
      (fun j hj => by
        rcases List.mem_cons.1 hj with rfl | hj_fp
        · dsimp only; have := hAs.2.2.2.1; have := hAs.2.2.2.2.1; rw [M13.sourceBase_val]; rw [M13.scratchStart_val] at *; omega
        · exact ((hT.2.1 ba hba_S).1.1 j hj_fp).1.1)
      hfr
  have hu_ws : globN s "ws" ≠ 0 → IvlUnhit s post (globN s "ws", 40) := fun hnz => by
    have hm := typedRecord_mem_fixedObjects s (r := ("ws", 40)) (by simp [typedRecords])
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by dsimp only; omega)
  have hu_bs : globN s "bs" ≠ 0 → IvlUnhit s post (globN s "bs", 80) := fun hnz => by
    have hm := typedRecord_mem_fixedObjects s (r := ("bs", 80)) (by simp [typedRecords])
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by dsimp only; omega)
  have hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72) := fun hnz => by
    have hm := typedRecord_mem_fixedObjects s (r := ("ts", 72)) (by simp [typedRecords])
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by dsimp only; omega)
  have hu_bo : globN s "bo" ≠ 0 → IvlUnhit s post (globN s "bo", 88) := fun hnz => by
    have hm := typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by simp [typedRecords])
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by dsimp only; omega)
  have hu_jr : globN s "journal_cap" ≠ 0 → IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap") := fun hnz => by
    have hmem_jr : (globN s "journal", 32 * globN s "journal_cap") ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
      simp [hnz]
    exact hu_fix _ hmem_jr (by dsimp only; omega)
  have hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → IvlUnhit s post i := fun i hi h24 =>
    hu_fix i (M13.blockOut_in_fixedObjects hi) (by omega)
  have hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → IvlUnhit s post i := fun i hi hipos =>
    hu_fix i (M13.bal_in_fixedObjects hi) hipos
  have hbo_eq := R10Shards.P26_P28.blockOutObjects_eq_of_bo_unhit hAs.2 hF (hcore "bo" (by decide))
    hT.2.2.2.2.2.2.2.2.2.2.1 hu_bo hu_bo_lst
  obtain ⟨hNH_post, hne_eq⟩ := nodeHeap_congr_bytes
    hAs.1 hARp.1 hag hTr.1 hu_nd_rec hu_nd_byte
  let T_new : List Nat := [t1w.toNat, t2w.toNat]
  let S' : List Nat := S ++ T_new
  have hsub_S : ∀ u ∈ S, u ∈ S' := fun u hu => List.mem_append_left _ hu
  obtain ⟨hjr_eq, hJ_post⟩ := R10Shards.P26_P28.journalRoleSlots_eq_of_unhit
    hAs.1 hARp.1 hAs.2 hag hsub_S hJ hF
    hcore
    hu_ts hu_jr
  -- Old BAL records preserved on `post`:
  let F_bal_s : Nat → List Ivl := fun ad =>
    (ad, 40) :: lstObjects s (memW s (ad + 16)) 40 ++ lstObjects s (memW s (ad + 24)) 16 ++
      lstObjects s (memW s (ad + 32)) 24 ++
      (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40)
  let F_bal_p : Nat → List Ivl := fun ad =>
    (ad, 40) :: lstObjects post (memW post (ad + 16)) 40 ++ lstObjects post (memW post (ad + 24)) 16 ++
      lstObjects post (memW post (ad + 32)) 24 ++
      (htabValues post (memW post ad)).flatMap (fun l => lstObjects post l 40)
  have hold_ad : ∀ ad ∈ balRecords s,
      memW post ad = memW s ad ∧ memW post (ad + 8) = memW s (ad + 8) ∧
      htabValues post (memW post ad) = htabValues s (memW s ad) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat), LstOK post (memW post (ad + k))) ∧
      (∀ l ∈ htabValues post (memW post ad), LstOK post l) ∧
      F_bal_p ad = F_bal_s ad := by
    intro ad had
    have had_bal : (ad, 40) ∈ balObjects s := by
      unfold balObjects; exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
    rcases hF.1 _ (M13.bal_in_fixedObjects had_bal) with h0 | ⟨hal_ad, hw_ad⟩
    · simp at h0
    have hhi_ad := (ivl_allocated_bound hAs.2 hal_ad).2
    have had8_old : ad % 8 = 0 := hw_ad.1
    have hoff_eq : ∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off) := by
      intro off hoff
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl <;>
        exact memW_eq_of_ivlUnhit (hu_bal _ had_bal (by simp)) (by omega) hhi_ad ⟨by omega, by omega⟩
    have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have hvals_ad : htabValues post (memW s ad) = htabValues s (memW s ad) :=
      htabValues_eq_of_unhit (hT.2.1 _ had_T.1).1 (hu_other _ had_T.1 (hno_ad ad had).1)
    have hlst_eq : ∀ l, (l, 24) ∈ balObjects s →
        memW post l = memW s l ∧ memW post (l + 8) = memW s (l + 8) ∧ memW post (l + 16) = memW s (l + 16) := by
      intro l hl_bal
      rcases hF.1 _ (M13.bal_in_fixedObjects hl_bal) with h0 | ⟨hal_l, hw_l⟩
      · simp at h0
      have hhi_l := (ivl_allocated_bound hAs.2 hal_l).2
      have hl8 : l % 8 = 0 := hw_l.1
      have hul := hu_bal _ hl_bal (by simp)
      exact ⟨by simpa using memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩,
             memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩,
             memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩⟩
    have hklst : ∀ k ∈ ([16, 24, 32] : List Nat), memW s (ad + k) ≠ 0 →
        memW post (memW s (ad + k)) = memW s (memW s (ad + k)) ∧
        memW post (memW s (ad + k) + 8) = memW s (memW s (ad + k) + 8) ∧
        memW post (memW s (ad + k) + 16) = memW s (memW s (ad + k) + 16) := by
      intro k hk hnz
      apply hlst_eq
      unfold balObjects; refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> simp [lstObjects, hnz]
    have hllst : ∀ l ∈ htabValues s (memW s ad), l ≠ 0 →
        memW post l = memW s l ∧ memW post (l + 8) = memW s (l + 8) ∧ memW post (l + 16) = memW s (l + 16) := by
      intro l hl hnz
      apply hlst_eq
      unfold balObjects; refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
      apply List.mem_cons_of_mem; apply List.mem_append.2; right
      exact List.mem_flatMap.2 ⟨l, hl, by simp [lstObjects, hnz]⟩
    have h0 := hoff_eq 0 (by simp); simp only [Nat.add_zero] at h0
    have h8 := hoff_eq 8 (by simp)
    have h16 := hoff_eq 16 (by simp)
    have h24 := hoff_eq 24 (by simp)
    have h32 := hoff_eq 32 (by simp)
    have hlst_congr : ∀ k esz, k ∈ ([16, 24, 32] : List Nat) →
        lstObjects post (memW s (ad + k)) esz = lstObjects s (memW s (ad + k)) esz := by
      intro k esz hk
      by_cases hkz : memW s (ad + k) = 0
      · simp [lstObjects, hkz]
      · obtain ⟨hc0, _, hc16⟩ := hklst k hk hkz
        simp [lstObjects, hkz, hc0, hc16]
    have htail : (htabValues post (memW post ad)).flatMap (fun l => lstObjects post l 40) =
        (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40) := by
      rw [h0, hvals_ad]
      apply List.flatMap_congr
      intro l hl
      by_cases hlz : l = 0
      · simp [lstObjects, hlz]
      · obtain ⟨hl0, _, hl16⟩ := hllst l hl hlz
        simp [lstObjects, hlz, hl0, hl16]
    refine ⟨h0, h8, by rw [h0, hvals_ad], ?_, ?_, ?_⟩
    · intro k hk
      have hk_in : k ∈ ([0, 8, 16, 24, 32] : List Nat) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        rcases hk with rfl | rfl | rfl <;> simp
      rw [hoff_eq k hk_in]
      by_cases hkz : memW s (ad + k) = 0
      · unfold LstOK; rw [hkz]; simp [hm0.2.1, hm0.2.2]; simpa [LstOK, hkz] using had_T.2.2.1 k hk
      · obtain ⟨_, hk8, hk16⟩ := hklst k hk hkz
        unfold LstOK; rw [hk8, hk16]; exact had_T.2.2.1 k hk
    · intro l hl
      rw [h0, hvals_ad] at hl
      by_cases hlz : l = 0
      · unfold LstOK; rw [hlz]; simp [hm0.2.1, hm0.2.2]; simpa [LstOK, hlz] using had_T.2.2.2 l hl
      · obtain ⟨_, hl8, hl16⟩ := hllst l hl hlz
        unfold LstOK; rw [hl8, hl16]; exact had_T.2.2.2 l hl
    · dsimp only [F_bal_p, F_bal_s]
      rw [htail, h16, h24, h32, hlst_congr 16 40 (by simp), hlst_congr 24 16 (by simp), hlst_congr 32 24 (by simp)]
  -- New BAL record `adw.toNat` properties on `post`:
  have ht1_vals_nil : htabValues post t1w.toNat = [] := by
    unfold htabValues
    change List.map _ (List.range (hdr post t1w.toNat 3)) = []
    rw [hnew_t1.2.2.1]; rfl
  have had_alloc : Allocated post (adw.toNat, 40) :=
    Or.inl ⟨by rw [had_eq]; exact hAs.2.1, by have := hARp.2.2.1; omega⟩
  have had_wordsOK : WordsOK post (adw.toNat, 40) :=
    M13.wordsOK_of_allocated hARp had_alloc had8 (by dsimp only)
  have hF_bal_adw : F_bal_p adw.toNat =
      [(adw.toNat, 40), (l1w.toNat, 24), (l1w.toNat + 24, 160),
       (l2w.toNat, 24), (l2w.toNat + 24, 64),
       (l3w.toNat, 24), (l3w.toNat + 24, 48)] := by
    dsimp only [F_bal_p]
    rw [had_words.1, had_words.2.2.1, had_words.2.2.2.1, had_words.2.2.2.2,
      hl1.2.2.1, hl2.2.2.1, hl3.2.2.1, ht1_vals_nil]
    rfl
  have hF_bal_adw_props : ∀ i ∈ F_bal_p adw.toNat,
      Allocated post i ∧ WordsOK post i ∧ Inside i (globN s "heap_ptr") hp6 := by
    intro i hi
    rw [hF_bal_adw] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨had_alloc, had_wordsOK, by dsimp [Inside]; omega, by dsimp [Inside]; omega⟩
    · obtain ⟨ha, hw, hin⟩ := hl1.2.2.2.2 (l1w.toNat, 24) (by rw [hl1.2.2.1]; simp)
      exact ⟨ha, hw, by dsimp [Inside] at hin ⊢; omega, by dsimp [Inside] at hin ⊢; omega⟩
    · obtain ⟨ha, hw, hin⟩ := hl1.2.2.2.2 (l1w.toNat + 24, 160) (by rw [hl1.2.2.1]; simp)
      exact ⟨ha, hw, by dsimp [Inside] at hin ⊢; omega, by dsimp [Inside] at hin ⊢; omega⟩
    · obtain ⟨ha, hw, hin⟩ := hl2.2.2.2.2 (l2w.toNat, 24) (by rw [hl2.2.2.1]; simp)
      exact ⟨ha, hw, by dsimp [Inside] at hin ⊢; omega, by dsimp [Inside] at hin ⊢; omega⟩
    · obtain ⟨ha, hw, hin⟩ := hl2.2.2.2.2 (l2w.toNat + 24, 64) (by rw [hl2.2.2.1]; simp)
      exact ⟨ha, hw, by dsimp [Inside] at hin ⊢; omega, by dsimp [Inside] at hin ⊢; omega⟩
    · obtain ⟨ha, hw, hin⟩ := hl3.2.2.2.2 (l3w.toNat, 24) (by rw [hl3.2.2.1]; simp)
      exact ⟨ha, hw, by dsimp [Inside] at hin ⊢; omega, by dsimp [Inside] at hin ⊢; omega⟩
    · obtain ⟨ha, hw, hin⟩ := hl3.2.2.2.2 (l3w.toNat + 24, 48) (by rw [hl3.2.2.1]; simp)
      exact ⟨ha, hw, by dsimp [Inside] at hin ⊢; omega, by dsimp [Inside] at hin ⊢; omega⟩
  have hF_bal_adw_pw : (F_bal_p adw.toNat).Pairwise Disj := by
    rw [hF_bal_adw]
    have i0 : Inside (adw.toNat, 40) (globN s "heap_ptr") (adw.toNat + 40) := ⟨by omega, le_rfl⟩
    have i1a := (hl1.2.2.2.2 (l1w.toNat, 24) (by rw [hl1.2.2.1]; simp)).2.2
    have i1b := (hl1.2.2.2.2 (l1w.toNat + 24, 160) (by rw [hl1.2.2.1]; simp)).2.2
    have i2a := (hl2.2.2.2.2 (l2w.toNat, 24) (by rw [hl2.2.2.1]; simp)).2.2
    have i2b := (hl2.2.2.2.2 (l2w.toNat + 24, 64) (by rw [hl2.2.2.1]; simp)).2.2
    have i3a := (hl3.2.2.2.2 (l3w.toNat, 24) (by rw [hl3.2.2.1]; simp)).2.2
    have i3b := (hl3.2.2.2.2 (l3w.toNat + 24, 48) (by rw [hl3.2.2.1]; simp)).2.2
    refine List.Pairwise.cons (fun y hy => ?_)
      (List.Pairwise.cons (fun y hy => ?_)
      (List.Pairwise.cons (fun y hy => ?_)
      (List.Pairwise.cons (fun y hy => ?_)
      (List.Pairwise.cons (fun y hy => ?_)
      (List.Pairwise.cons (fun y hy => ?_)
      (List.Pairwise.cons (fun _ hy => by cases hy) List.Pairwise.nil))))))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
      · exact WkBal.disj_fresh_sub i0 i1a (by omega)
      · exact WkBal.disj_fresh_sub i0 i1b (by omega)
      · exact WkBal.disj_fresh_sub i0 i2a (by omega)
      · exact WkBal.disj_fresh_sub i0 i2b (by omega)
      · exact WkBal.disj_fresh_sub i0 i3a (by omega)
      · exact WkBal.disj_fresh_sub i0 i3b (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · exact hl1.2.2.2.1
      · exact WkBal.disj_fresh_sub i1a i2a (by omega)
      · exact WkBal.disj_fresh_sub i1a i2b (by omega)
      · exact WkBal.disj_fresh_sub i1a i3a (by omega)
      · exact WkBal.disj_fresh_sub i1a i3b (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact WkBal.disj_fresh_sub i1b i2a (by omega)
      · exact WkBal.disj_fresh_sub i1b i2b (by omega)
      · exact WkBal.disj_fresh_sub i1b i3a (by omega)
      · exact WkBal.disj_fresh_sub i1b i3b (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl
      · exact hl2.2.2.2.1
      · exact WkBal.disj_fresh_sub i2a i3a (by omega)
      · exact WkBal.disj_fresh_sub i2a i3b (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · exact WkBal.disj_fresh_sub i2b i3a (by omega)
      · exact WkBal.disj_fresh_sub i2b i3b (by omega)
    · simp only [List.mem_singleton] at hy; subst hy; exact hl3.2.2.2.1
  -- Decompose `fixedObjects post` as `L1 ++ F_bal_p adw.toNat ++ L2` where `L1 ++ mid ++ L2 = fixedObjects s`:
  let nonBal_s : List Ivl :=
    (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) ++
      [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] ++
      blockOutObjects s
  let nonBal_p : List Ivl :=
    (globalBuffers.map fun gn => (globN post gn.1, if globN post gn.1 = 0 then 0 else gn.2)) ++
      [(if globN post "journal_cap" = 0 then 0 else globN post "journal", 32 * globN post "journal_cap")] ++
      blockOutObjects post
  have hnonBal_eq : nonBal_p = nonBal_s := by
    dsimp only [nonBal_p, nonBal_s]
    rw [hbo_eq.1, hcore "journal" (by decide), hcore "journal_cap" (by decide)]
    congr 2
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "heap_ptr" := by revert gn hgn; decide
    have hg_eq : globN post gn.1 = globN s gn.1 := globN_eq_of_lookup (hg_nonHeap (ofString gn.1) hne)
    simp [hg_eq]
  have hfix_slice : ∃ L1 mid L2 : List Ivl,
      fixedObjects s = L1 ++ mid ++ L2 ∧
      fixedObjects post = L1 ++ F_bal_p adw.toNat ++ L2 := by
    rcases hba_vals with happ | ⟨i0, hi0, hset⟩
    · refine ⟨fixedObjects s, [], [], by simp, ?_⟩
      change nonBal_p ++ (balRecords post).flatMap F_bal_p = fixedObjects s ++ F_bal_p adw.toNat ++ []
      rw [hnonBal_eq, hrecs_p, happ, List.flatMap_append, List.flatMap_singleton, List.append_nil]
      have hcongr : (htabValues s ba).flatMap F_bal_p = balObjects s := by
        unfold balObjects
        rw [hrecs_s]
        exact List.flatMap_congr fun ad had => (hold_ad ad (by rwa [hrecs_s])).2.2.2.2.2
      rw [hcongr, ← List.append_assoc]
      rfl
    · obtain ⟨hd_set, hd_old⟩ := flatMap_set_decomp F_bal_p (htabValues s ba) i0 hi0 adw.toNat
      obtain ⟨_, hd_old_s⟩ := flatMap_set_decomp F_bal_s (htabValues s ba) i0 hi0 adw.toNat
      have htake_eq : ((htabValues s ba).take i0).flatMap F_bal_p =
          ((htabValues s ba).take i0).flatMap F_bal_s :=
        List.flatMap_congr fun ad had =>
          (hold_ad ad (by rw [hrecs_s]; exact List.mem_of_mem_take had)).2.2.2.2.2
      have hdrop_eq : ((htabValues s ba).drop (i0 + 1)).flatMap F_bal_p =
          ((htabValues s ba).drop (i0 + 1)).flatMap F_bal_s :=
        List.flatMap_congr fun ad had =>
          (hold_ad ad (by rw [hrecs_s]; exact List.mem_of_mem_drop had)).2.2.2.2.2
      refine ⟨nonBal_s ++ ((htabValues s ba).take i0).flatMap F_bal_s,
              F_bal_s ((htabValues s ba)[i0]),
              ((htabValues s ba).drop (i0 + 1)).flatMap F_bal_s, ?_, ?_⟩
      · change nonBal_s ++ (balRecords s).flatMap F_bal_s = _
        rw [hrecs_s, hd_old_s]
        simp only [List.append_assoc]
      · change nonBal_p ++ (balRecords post).flatMap F_bal_p = _
        rw [hnonBal_eq, hrecs_p, hset, hd_set, htake_eq, hdrop_eq]
        simp only [List.append_assoc]
  obtain ⟨L1_fix, mid_fix, L2_fix, hfix_s_eq, hfix_p_eq⟩ := hfix_slice
  have hL12_old : ∀ x ∈ L1_fix ++ L2_fix, x ∈ fixedObjects s := by
    intro x hx
    rw [hfix_s_eq]
    rcases List.mem_append.1 hx with hx1 | hx2
    · exact List.mem_append_left _ (List.mem_append_left _ hx1)
    · exact List.mem_append_right _ hx2
  have hdisj_old_fresh : ∀ x ∈ fixedObjects s, ∀ y : Ivl,
      Inside y (globN s "heap_ptr") (globN post "heap_ptr") → Disj x y := by
    intro x hx y hy
    rcases hF.1 x hx with hx0 | ⟨hal_x, _⟩
    · exact Or.inl hx0
    · exact (disj_allocated_fresh_heap hAs.2 hARp.2 hal_x hy).flip
  have hF_post : FixedTyped post := by
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [hfix_p_eq] at hi
      rcases List.mem_append.1 hi with hi1m | hi2
      · rcases List.mem_append.1 hi1m with hi1 | him
        · rcases hF.1 i (hL12_old i (List.mem_append_left _ hi1)) with h0 | ⟨hal, hw⟩
          · exact Or.inl h0
          · exact Or.inr ⟨hag.allocated hal, wordsOK_transfer hAs.1 hARp.1 hw⟩
        · obtain ⟨hal, hw, _⟩ := hF_bal_adw_props i him
          exact Or.inr ⟨hal, hw⟩
      · rcases hF.1 i (hL12_old i (List.mem_append_right _ hi2)) with h0 | ⟨hal, hw⟩
        · exact Or.inl h0
        · exact Or.inr ⟨hag.allocated hal, wordsOK_transfer hAs.1 hARp.1 hw⟩
    · rw [hfix_p_eq]
      exact WkBal.pairwise_disj_replace_slice (by rw [← hfix_s_eq]; exact hF.2) hF_bal_adw_pw
        (fun x hx y hy => hdisj_old_fresh x (hL12_old x (List.mem_append_left _ hx)) y
          (let hi := (hF_bal_adw_props y hy).2.2; ⟨hi.1, by dsimp [Inside] at hi ⊢; omega⟩))
        (fun x hx y hy => (hdisj_old_fresh y (hL12_old y (List.mem_append_right _ hy)) x
          (let hi := (hF_bal_adw_props x hx).2.2; ⟨hi.1, by dsimp [Inside] at hi ⊢; omega⟩)).flip)
  have hfix_p_class : ∀ j ∈ fixedObjects post, j ∈ fixedObjects s ∨ j ∈ F_bal_p adw.toNat := by
    intro j hj
    rw [hfix_p_eq] at hj
    rcases List.mem_append.1 hj with hj1m | hj2
    · rcases List.mem_append.1 hj1m with hj1 | hjm
      · exact Or.inl (hL12_old j (List.mem_append_left _ hj1))
      · exact Or.inr hjm
    · exact Or.inl (hL12_old j (List.mem_append_right _ hj2))
  -- Disjointness of `t1w, t2w` from `F_bal_p adw.toNat`, `fixedObjects post`, `S`, and `nodeExtents`:
  have ht12_disj_Fadw : ∀ t ∈ T_new, ∀ i ∈ htabFootprint post t, ∀ j ∈ F_bal_p adw.toNat, Disj i j := by
    intro t ht i hi j hj
    rw [hF_bal_adw] at hj
    have i0 : Inside (adw.toNat, 40) (globN s "heap_ptr") (adw.toNat + 40) := ⟨by omega, le_rfl⟩
    have i1a := (hl1.2.2.2.2 (l1w.toNat, 24) (by rw [hl1.2.2.1]; simp)).2.2
    have i1b := (hl1.2.2.2.2 (l1w.toNat + 24, 160) (by rw [hl1.2.2.1]; simp)).2.2
    have i2a := (hl2.2.2.2.2 (l2w.toNat, 24) (by rw [hl2.2.2.1]; simp)).2.2
    have i2b := (hl2.2.2.2.2 (l2w.toNat + 24, 64) (by rw [hl2.2.2.1]; simp)).2.2
    have i3a := (hl3.2.2.2.2 (l3w.toNat, 24) (by rw [hl3.2.2.1]; simp)).2.2
    have i3b := (hl3.2.2.2.2 (l3w.toNat + 24, 48) (by rw [hl3.2.2.1]; simp)).2.2
    simp only [T_new, List.mem_cons, List.not_mem_nil, or_false] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases ht with rfl | rfl
    · have hin := (hnew_t1.2.2.2 i hi).2
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (WkBal.disj_fresh_sub i0 hin le_rfl).flip
      · exact WkBal.disj_fresh_sub hin i1a (by omega)
      · exact WkBal.disj_fresh_sub hin i1b (by omega)
      · exact WkBal.disj_fresh_sub hin i2a (by omega)
      · exact WkBal.disj_fresh_sub hin i2b (by omega)
      · exact WkBal.disj_fresh_sub hin i3a (by omega)
      · exact WkBal.disj_fresh_sub hin i3b (by omega)
    · have hin := (hnew_t2.2.2.2 i hi).2
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (WkBal.disj_fresh_sub i0 hin (by omega)).flip
      · exact WkBal.disj_fresh_sub hin i1a (by omega)
      · exact WkBal.disj_fresh_sub hin i1b (by omega)
      · exact WkBal.disj_fresh_sub hin i2a (by omega)
      · exact WkBal.disj_fresh_sub hin i2b (by omega)
      · exact WkBal.disj_fresh_sub hin i3a (by omega)
      · exact WkBal.disj_fresh_sub hin i3b (by omega)
  have ht_new_in_heap : ∀ t ∈ T_new, ∀ i ∈ htabFootprint post t,
      Allocated post i ∧ Inside i (globN s "heap_ptr") hp6 := by
    intro t ht i hi
    simp only [T_new, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · obtain ⟨ha, hin⟩ := hnew_t1.2.2.2 i hi
      exact ⟨ha, by dsimp [Inside] at hin ⊢; omega, by dsimp [Inside] at hin ⊢; omega⟩
    · obtain ⟨ha, hin⟩ := hnew_t2.2.2.2 i hi
      exact ⟨ha, by dsimp [Inside] at hin ⊢; omega, by dsimp [Inside] at hin ⊢; omega⟩
  have hT_disj_S : ∀ t ∈ T_new, t ∉ S := by
    intro t ht htS
    obtain ⟨_, hin⟩ := ht_new_in_heap t ht (t, 88) (by simp [htabFootprint])
    have hal_s := ((hT.2.1 t htS).2 (t, 88) (by simp [htabFootprint])).1
    have hd := disj_allocated_fresh_heap hAs.2 hARp.2 hal_s
      ⟨hin.1, by dsimp [Inside] at hin ⊢; omega⟩
    rcases hd with h | h | h | h <;> dsimp at h <;> omega
  have hother_fp : ∀ u ∈ S, u ≠ ba →
      (∀ k, k < 11 → hdr post u k = hdr s u k) ∧ htabFootprint post u = htabFootprint s u := by
    intro u hu hne
    have h264 : heapEnd ≤ 2 ^ 64 := by decide
    have hfp := (hT.2.1 u hu).1.1
    have ht_fp : (u, 88) ∈ htabFootprint s u := by simp [htabFootprint]
    exact htabFootprint_eq_of_hdr_unhit ((hfp _ ht_fp).2.1)
      (by have := (hfp _ ht_fp).1.2; dsimp at this; omega) (hu_other u hu hne _ ht_fp)
  have hba_disj_post : ∀ i ∈ htabFootprint post ba,
      (∀ u ∈ S, u ≠ ba → ∀ j ∈ htabFootprint s u, Disj i j) ∧
      (∀ t ∈ T_new, ∀ j ∈ htabFootprint post t, Disj i j) ∧
      (∀ j ∈ fixedObjects post, Disj i j) ∧
      (∀ o ∈ nodeExtents s Nd, Disj i o) := by
    intro i hi
    rcases (hba_fp i hi).2 with ⟨k, hk, hin⟩ | hfresh6
    · have hal_k : Allocated s k := ((hT.2.1 ba hba_S).2 k hk).1
      refine ⟨fun u hu hne j hj => disj_of_inside_left hin (hT.2.2.1 ba hba_S u hu hne.symm k hk j hj),
              fun t ht j hj => disj_of_inside_left hin
                (disj_allocated_fresh_heap hAs.2 hARp.2 hal_k
                  (let hj_in := (ht_new_in_heap t ht j hj).2; ⟨hj_in.1, by dsimp [Inside] at hj_in ⊢; omega⟩)).flip,
              fun j hj => ?_,
              fun o ho => disj_of_inside_left hin ((hTr.2.1 o ho).1 ba hba_S k hk).flip⟩
      rcases hfix_p_class j hj with hj_s | hj_new
      · exact disj_of_inside_left hin (((hT.2.1 ba hba_S).2 k hk).2 j hj_s)
      · exact disj_of_inside_left hin
          (disj_allocated_fresh_heap hAs.2 hARp.2 hal_k
            (let hj_in := (hF_bal_adw_props j hj_new).2.2; ⟨hj_in.1, by dsimp [Inside] at hj_in ⊢; omega⟩)).flip
    · have hfresh_full : Inside i (globN s "heap_ptr") (globN post "heap_ptr") :=
        ⟨by dsimp [Inside] at hfresh6 ⊢; omega, hfresh6.2⟩
      refine ⟨fun u hu _ j hj => disj_allocated_fresh_heap hAs.2 hARp.2 ((hT.2.1 u hu).2 j hj).1 hfresh_full,
              fun t ht j hj => (WkBal.disj_fresh_sub (ht_new_in_heap t ht j hj).2 hfresh6 le_rfl).flip,
              fun j hj => ?_,
              fun o ho => ?_⟩
      · rcases hfix_p_class j hj with hj_s | hj_new
        · exact (hdisj_old_fresh j hj_s i hfresh_full).flip
        · exact (WkBal.disj_fresh_sub (hF_bal_adw_props j hj_new).2.2 hfresh6 le_rfl).flip
      · unfold nodeExtents at ho
        obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
        rcases hno with rfl | rfl
        · exact disj_allocated_fresh_heap hAs.2 hARp.2 (hTr.1.1 n hn).2.1 hfresh_full
        · unfold nodePath; split_ifs with hc
          · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hc.1 with h0 | ⟨_, hal, _⟩
            · exact absurd h0 hc.2
            · exact disj_allocated_fresh_heap hAs.2 hARp.2 hal hfresh_full
          · exact Or.inr (Or.inl rfl)
  -- `RolesOK post S' (worldRoleSlots post) (journalRoleSlots post)`:
  have hroles_post : RolesOK post S' (worldRoleSlots post) (journalRoleSlots post) := by
    let nonBalRoles : PanSemStateFiniteExact 64 F → List (Nat × String) := fun st =>
      recRoles st "ws" [(16, "ws+16"), (32, "ws+32")] ++
        recRoles st "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"), (40, "bs+40"),
          (48, "bs+48"), (72, "bs+72")] ++
        recRoles st "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"), (40, "ts+40"),
          (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] ++
        [(globN st "bal_accounts", "bal_accounts"), (globN st "bal_idx_accts", "bal_idx_accts"),
          (globN st "bal_idx_stor", "bal_idx_stor")] ++
        nestRoles st "bs" "bs.inner" ++ nestRoles st "ts" "ts.inner"
    have hnonBalRoles_eq : nonBalRoles post = nonBalRoles s := by
      dsimp only [nonBalRoles]
      have hws_g := hcore "ws" (by decide)
      have hbs_g := hcore "bs" (by decide)
      have hts_g := hcore "ts" (by decide)
      have hbia_g := hcore "bal_idx_accts" (by decide)
      have hbis_g := hcore "bal_idx_stor" (by decide)
      have hrec_ws : recRoles post "ws" [(16, "ws+16"), (32, "ws+32")] =
          recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] := by
        unfold recRoles; rw [hws_g]; split_ifs with h0
        · rfl
        · apply List.map_congr_left; intro ⟨k, r⟩ hkr
          have hk8 : k % 8 = 0 ∧ k + 8 ≤ 40 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
            rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
          have ew := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g h0 (hu_ws h0) hk8.1 hk8.2
          rw [hws_g] at ew; rw [ew]
      have hrec_bs : recRoles post "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"), (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] =
          recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"), (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] := by
        unfold recRoles; rw [hbs_g]; split_ifs with h0
        · rfl
        · apply List.map_congr_left; intro ⟨k, r⟩ hkr
          have hk8 : k % 8 = 0 ∧ k + 8 ≤ 80 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
            rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
          have ew := rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g h0 (hu_bs h0) hk8.1 hk8.2
          rw [hbs_g] at ew; rw [ew]
      have hrec_ts : recRoles post "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"), (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] =
          recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"), (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] := by
        unfold recRoles; rw [hts_g]; split_ifs with h0
        · rfl
        · apply List.map_congr_left; intro ⟨k, r⟩ hkr
          have hk8 : k % 8 = 0 ∧ k + 8 ≤ 72 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
            rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
          have ew := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g h0 (hu_ts h0) hk8.1 hk8.2
          rw [hts_g] at ew; rw [ew]
      have hnest_bs : nestRoles post "bs" "bs.inner" = nestRoles s "bs" "bs.inner" := by
        unfold nestRoles; rw [hbs_g]; by_cases h0 : globN s "bs" = 0
        · simp [h0]
        · simp only [h0, ↓reduceIte]
          have ew := rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g h0 (hu_bs h0) (k := 32) (by omega) (by omega)
          rw [hbs_g] at ew; simp only [ew]
          split_ifs with hm0_bs
          · rfl
          · rcases hT.2.2.2.2.1 32 (by simp [bsTableSlots]) h0 with hz | hmS
            · exact absurd hz hm0_bs
            · rw [htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_other _ hmS (hno_bs32 h0))]
      have hnest_ts : nestRoles post "ts" "ts.inner" = nestRoles s "ts" "ts.inner" := by
        unfold nestRoles; rw [hts_g]; by_cases h0 : globN s "ts" = 0
        · simp [h0]
        · simp only [h0, ↓reduceIte]
          have ew := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g h0 (hu_ts h0) (k := 32) (by omega) (by omega)
          rw [hts_g] at ew; simp only [ew]
          split_ifs with hm0_ts
          · rfl
          · rcases hT.2.2.2.2.2.1 32 (by simp [tsTableSlots]) h0 with hz | hmS
            · exact absurd hz hm0_ts
            · rw [htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_other _ hmS (hno_ts32 h0))]
      rw [hrec_ws, hrec_bs, hrec_ts, hba_g, hbia_g, hbis_g, hnest_bs, hnest_ts]
    let gRole_s : Nat → List (Nat × String) := fun ad =>
      ([(memW s ad, "bal.stor"), (memW s (ad + 8), "bal.reads")]).filter (fun a => a.1 != 0)
    let gRole_p : Nat → List (Nat × String) := fun ad =>
      ([(memW post ad, "bal.stor"), (memW post (ad + 8), "bal.reads")]).filter (fun a => a.1 != 0)
    have hgRole_old : ∀ ad ∈ balRecords s, gRole_p ad = gRole_s ad := by
      intro ad had
      obtain ⟨e0, e8, _⟩ := hold_ad ad had
      dsimp only [gRole_p, gRole_s]; rw [e0, e8]
    have ht1_nz : t1w.toNat ≠ 0 := WkBal.htab_nonzero_of_wf hnew_t1.1
    have ht2_nz : t2w.toNat ≠ 0 := WkBal.htab_nonzero_of_wf hnew_t2.1
    have hgRole_adw : gRole_p adw.toNat = [(t1w.toNat, "bal.stor"), (t2w.toNat, "bal.reads")] := by
      dsimp only [gRole_p]
      rw [had_words.1, had_words.2.1]
      simp [ht1_nz, ht2_nz]
    have hwrs_s_eq : worldRoleSlots s =
        (nonBalRoles s).filter (fun a => a.1 != 0) ++ (balRecords s).flatMap gRole_s := by
      unfold worldRoleSlots
      rw [List.filter_append, List.filter_flatMap]
    have hwrs_p_eq : worldRoleSlots post =
        (nonBalRoles post).filter (fun a => a.1 != 0) ++ (balRecords post).flatMap gRole_p := by
      unfold worldRoleSlots
      rw [List.filter_append, List.filter_flatMap]
    rw [hjr_eq]
    apply WkBal.rolesOK_adjoin_fresh_slots hT.2.2.2.2.2.2.2.2.2.2.2
      (fun t ht => by
        by_cases htb : t = ba
        · subst htb; exact hba_hdr0
        · exact (hother_fp t ht htb).1 0 (by omega))
      _ hT_disj_S
    rcases hba_vals with happ | ⟨i0, hi0, hset⟩
    · refine ⟨worldRoleSlots s, [(t1w.toNat, "bal.stor"), (t2w.toNat, "bal.reads")], [], ?_, ?_, ?_, ?_, ?_⟩
      · rw [hwrs_p_eq, hnonBalRoles_eq, hrecs_p, happ, List.flatMap_append, List.flatMap_singleton,
          hgRole_adw, List.append_nil]
        have hc : (htabValues s ba).flatMap gRole_p = (balRecords s).flatMap gRole_s := by
          rw [hrecs_s]
          exact List.flatMap_congr fun ad had => hgRole_old ad (by rwa [hrecs_s])
        rw [hc, ← List.append_assoc, ← hwrs_s_eq]
      · intro a ha; rw [List.append_nil] at ha; exact ha
      · rw [List.append_nil]; exact hT.2.2.2.2.2.2.2.2.2.2.2.2.1
      · intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · exact ⟨by simp [T_new], hnew_t1.2.1⟩
        · exact ⟨by simp [T_new], hnew_t2.2.1⟩
      · simp [ht12_ne]
    · obtain ⟨hd_set, _⟩ := flatMap_set_decomp gRole_p (htabValues s ba) i0 hi0 adw.toNat
      obtain ⟨_, hd_old_s⟩ := flatMap_set_decomp gRole_s (htabValues s ba) i0 hi0 adw.toNat
      have htake_eq : ((htabValues s ba).take i0).flatMap gRole_p =
          ((htabValues s ba).take i0).flatMap gRole_s :=
        List.flatMap_congr fun ad had => hgRole_old ad (by rw [hrecs_s]; exact List.mem_of_mem_take had)
      have hdrop_eq : ((htabValues s ba).drop (i0 + 1)).flatMap gRole_p =
          ((htabValues s ba).drop (i0 + 1)).flatMap gRole_s :=
        List.flatMap_congr fun ad had => hgRole_old ad (by rw [hrecs_s]; exact List.mem_of_mem_drop had)
      let pre_sl := (nonBalRoles s).filter (fun a => a.1 != 0) ++ ((htabValues s ba).take i0).flatMap gRole_s
      let suf_sl := ((htabValues s ba).drop (i0 + 1)).flatMap gRole_s
      have hwrs_s_split : worldRoleSlots s = pre_sl ++ gRole_s ((htabValues s ba)[i0]) ++ suf_sl := by
        rw [hwrs_s_eq, hrecs_s, hd_old_s]
        simp only [pre_sl, suf_sl, List.append_assoc]
      have hsub_sl : (pre_sl ++ suf_sl).Sublist (worldRoleSlots s) := by
        rw [hwrs_s_split]
        exact (List.Sublist.append_right (List.sublist_append_left _ _) _)
      refine ⟨pre_sl, [(t1w.toNat, "bal.stor"), (t2w.toNat, "bal.reads")], suf_sl, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hwrs_p_eq, hnonBalRoles_eq, hrecs_p, hset, hd_set, hgRole_adw, htake_eq, hdrop_eq]
        simp only [pre_sl, suf_sl, List.append_assoc]
      · intro a ha; exact hsub_sl.subset ha
      · exact hT.2.2.2.2.2.2.2.2.2.2.2.2.1.sublist hsub_sl
      · intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · exact ⟨by simp [T_new], hnew_t1.2.1⟩
        · exact ⟨by simp [T_new], hnew_t2.2.1⟩
      · simp [ht12_ne]
  -- Assemble `TablesTyped post S'`:
  have hroot_S : ∀ {v}, RootIn S v → RootIn S' v := by
    rintro v (rfl | hv); exact Or.inl rfl; exact Or.inr (hsub_S v hv)
  have hT_post : TablesTyped post S' := by
    obtain ⟨hnd, htwf, htpw, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, _, _⟩ := hT
    have ews := hcore "ws" (by decide)
    have ebs := hcore "bs" (by decide)
    have ets := hcore "ts" (by decide)
    refine ⟨List.nodup_append.2 ⟨hnd, by simp [T_new, ht12_ne], fun u hu v hv heq => by subst heq; exact hT_disj_S u hv hu⟩,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_eq.2, hroles_post⟩
    · intro u hu
      rcases List.mem_append.1 hu with huS | huN
      · by_cases hub : u = ba
        · subst hub
          exact ⟨hba_wf, fun i hi => ⟨(hba_fp i hi).1, (hba_disj_post i hi).2.2.1⟩⟩
        · rw [(hother_fp u huS hub).2]
          refine ⟨htabWF_congr_unhit hAs.1 hARp.1 (htwf u huS).1 (hu_other u huS hub),
            fun i hi => ⟨hag.allocated ((htwf u huS).2 i hi).1, fun j hj => ?_⟩⟩
          rcases hfix_p_class j hj with hj_s | hj_new
          · exact ((htwf u huS).2 i hi).2 j hj_s
          · exact (disj_allocated_fresh_heap hAs.2 hARp.2
              ((htwf u huS).2 i hi).1
              (let hj_in := (hF_bal_adw_props j hj_new).2.2; ⟨hj_in.1, by dsimp [Inside] at hj_in ⊢; omega⟩)).flip
      · have hwf_u : HtabWF post u := by
          simp only [T_new, List.mem_cons, List.not_mem_nil, or_false] at huN
          rcases huN with rfl | rfl; exact hnew_t1.1; exact hnew_t2.1
        refine ⟨hwf_u, fun i hi => ⟨(ht_new_in_heap u huN i hi).1, fun j hj => ?_⟩⟩
        rcases hfix_p_class j hj with hj_s | hj_new
        · exact (hdisj_old_fresh j hj_s i
            (let hi_in := (ht_new_in_heap u huN i hi).2; ⟨hi_in.1, by dsimp [Inside] at hi_in ⊢; omega⟩)).flip
        · exact ht12_disj_Fadw u huN i hi j hj_new
    · intro u hu v hv hne i hi j hj
      rcases List.mem_append.1 hu with huS | huN <;> rcases List.mem_append.1 hv with hvS | hvN
      · by_cases hub : u = ba
        · subst hub; rw [(hother_fp v hvS hne.symm).2] at hj
          exact (hba_disj_post i hi).1 v hvS hne.symm j hj
        · by_cases hvb : v = ba
          · subst hvb; rw [(hother_fp u huS hub).2] at hi
            exact ((hba_disj_post j hj).1 u huS hub i hi).flip
          · rw [(hother_fp u huS hub).2] at hi; rw [(hother_fp v hvS hvb).2] at hj
            exact htpw u huS v hvS hne i hi j hj
      · by_cases hub : u = ba
        · subst hub; exact (hba_disj_post i hi).2.1 v hvN j hj
        · rw [(hother_fp u huS hub).2] at hi
          exact (disj_allocated_fresh_heap hAs.2 hARp.2
            ((htwf u huS).2 i hi).1
            (let hj_in := (ht_new_in_heap v hvN j hj).2; ⟨hj_in.1, by dsimp [Inside] at hj_in ⊢; omega⟩)).flip
      · by_cases hvb : v = ba
        · subst hvb; exact ((hba_disj_post j hj).2.1 u huN i hi).flip
        · rw [(hother_fp v hvS hvb).2] at hj
          exact disj_allocated_fresh_heap hAs.2 hARp.2
            ((htwf v hvS).2 j hj).1
            (let hi_in := (ht_new_in_heap u huN i hi).2; ⟨hi_in.1, by dsimp [Inside] at hi_in ⊢; omega⟩)
      · simp only [T_new, List.mem_cons, List.not_mem_nil, or_false] at huN hvN
        rcases huN with rfl | rfl <;> rcases hvN with rfl | rfl
        · exact absurd rfl hne
        · exact WkBal.disj_fresh_sub (hnew_t1.2.2.2 i hi).2 (hnew_t2.2.2.2 j hj).2 le_rfl
        · exact (WkBal.disj_fresh_sub (hnew_t1.2.2.2 j hj).2 (hnew_t2.2.2.2 i hi).2 le_rfl).flip
        · exact absurd rfl hne
    · intro k hk hnz
      rw [ews] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) ews hnz (hu_ws hnz) hk8.1 hk8.2]
      exact hroot_S (hwsR k hk hnz)
    · intro k hk hnz
      rw [ebs] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) ebs hnz (hu_bs hnz) hk8.1 hk8.2]
      exact hroot_S (hbsR k hk hnz)
    · intro k hk hnz
      rw [ets] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) ets hnz (hu_ts hnz) hk8.1 hk8.2]
      exact hroot_S (htsR k hk hnz)
    · intro g hg_mem
      rw [hcore g (by simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg_mem; rcases hg_mem with rfl | rfl | rfl <;> decide)]
      exact hroot_S (hgR g hg_mem)
    · intro hnz hm
      rw [ebs] at hnz
      have ew := rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) ebs hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hm ⊢
      rcases List.mem_append.1 hm with hmS | hmN
      · exact htabValuesIn_congr_unhit
          (htwf _ hmS).1 (hu_other _ hmS (hno_bs32 hnz)) hsub_S (hbsN hnz hmS)
      · rcases hbsR 32 (by simp [bsTableSlots]) hnz with h0 | hmS
        · simp only [T_new, List.mem_cons, List.not_mem_nil, or_false] at hmN
          rcases hmN with h1 | h2
          · exact absurd h1.symm (h0 ▸ WkBal.htab_nonzero_of_wf hnew_t1.1)
          · exact absurd h2.symm (h0 ▸ WkBal.htab_nonzero_of_wf hnew_t2.1)
        · exact absurd hmS (hT_disj_S _ hmN)
    · intro hnz hm
      rw [ets] at hnz
      have ew := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) ets hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hm ⊢
      rcases List.mem_append.1 hm with hmS | hmN
      · exact htabValuesIn_congr_unhit
          (htwf _ hmS).1 (hu_other _ hmS (hno_ts32 hnz)) hsub_S (htsN hnz hmS)
      · rcases htsR 32 (by simp [tsTableSlots]) hnz with h0 | hmS
        · simp only [T_new, List.mem_cons, List.not_mem_nil, or_false] at hmN
          rcases hmN with h1 | h2
          · exact absurd h1.symm (h0 ▸ WkBal.htab_nonzero_of_wf hnew_t1.1)
          · exact absurd h2.symm (h0 ▸ WkBal.htab_nonzero_of_wf hnew_t2.1)
        · exact absurd hmS (hT_disj_S _ hmN)
    · intro ad had
      have had_cases : ad ∈ balRecords s ∨ ad = adw.toNat := by
        rw [hrecs_p] at had; rw [hrecs_s]
        rcases hba_vals with happ | ⟨i0, hi0, hset⟩
        · rw [happ] at had
          rcases List.mem_append.1 had with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (List.mem_singleton.1 h2)
        · rw [hset] at had
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 had
          rw [List.length_set] at hj
          by_cases hji : j = i0
          · subst hji; right; simp
          · left; rw [List.getElem_set_ne (Ne.symm hji)]; exact List.getElem_mem hj
      rcases had_cases with had_s | rfl
      · obtain ⟨e0, e8, _, hkl, hll, _⟩ := hold_ad ad had_s
        exact ⟨e0 ▸ hsub_S _ (hbalT ad had_s).1, e8 ▸ hsub_S _ (hbalT ad had_s).2.1, hkl, hll⟩
      · refine ⟨by rw [had_words.1]; exact List.mem_append_right _ (by simp [T_new]),
                by rw [had_words.2.1]; exact List.mem_append_right _ (by simp [T_new]),
                fun k hk => ?_,
                fun l hl => by rw [had_words.1, ht1_vals_nil] at hl; cases hl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl
        · rw [had_words.2.2.1]; exact hl1.2.1
        · rw [had_words.2.2.2.1]; exact hl2.2.1
        · rw [had_words.2.2.2.2]; exact hl3.2.1
  -- `TriesTypedWith post S' Nd`:
  have hTr_post : TriesTypedWith post S' Nd := by
    have ews := hcore "ws" (by decide)
    refine ⟨hNH_post, ?_, ?_⟩
    · rw [hne_eq]
      intro o ho
      have ho_alloc : o = (0, 0) ∨ Allocated s o := by
        unfold nodeExtents at ho
        obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
        rcases hno with rfl | rfl
        · exact Or.inr (hTr.1.1 n hn).2.1
        · unfold nodePath; split_ifs with hp
          · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hp.1 with h0 | ⟨_, hal, _, _⟩
            · exact absurd h0 hp.2
            · exact Or.inr hal
          · exact Or.inl rfl
      refine ⟨fun u hu i hi => ?_, fun j hj => ?_⟩
      · rcases List.mem_append.1 hu with huS | huN
        · by_cases hub : u = ba
          · subst hub; exact ((hba_disj_post i hi).2.2.2 o ho).flip
          · rw [(hother_fp u huS hub).2] at hi; exact (hTr.2.1 o ho).1 u huS i hi
        · rcases ho_alloc with rfl | hal_o
          · exact Or.inl rfl
          · exact (disj_allocated_fresh_heap hAs.2 hARp.2 hal_o
              (let hi_in := (ht_new_in_heap u huN i hi).2; ⟨hi_in.1, by dsimp [Inside] at hi_in ⊢; omega⟩)).flip
      · rcases hfix_p_class j hj with hj_s | hj_new
        · exact (hTr.2.1 o ho).2 j hj_s
        · rcases ho_alloc with rfl | hal_o
          · exact Or.inl rfl
          · exact (disj_allocated_fresh_heap hAs.2 hARp.2 hal_o
              (let hj_in := (hF_bal_adw_props j hj_new).2.2; ⟨hj_in.1, by dsimp [Inside] at hj_in ⊢; omega⟩)).flip
    · intro hws_nz
      rw [ews] at hws_nz
      have e24 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) ews hws_nz (hu_ws hws_nz) (k := 24) (by omega) (by omega)
      have e32 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) ews hws_nz (hu_ws hws_nz) (k := 32) (by omega) (by omega)
      rw [e24, e32]
      obtain ⟨hr24, hr32⟩ := hTr.2.2 hws_nz
      refine ⟨hr24, fun htS' i hi => ?_⟩
      rcases List.mem_append.1 htS' with htS | htN
      · have hne32 := hno_ws32 hws_nz
        have hu32 := hu_other _ htS hne32
        have hwf32 := (hT.2.1 _ htS).1
        have hvals_eq := htabValues_eq_of_unhit hwf32 hu32
        obtain ⟨hhdr32, _⟩ := hother_fp _ htS hne32
        rw [hhdr32 3 (by omega)] at hi
        have hget : (htabValues post (memW s (globN s "ws" + 32)))[i]? =
            (htabValues s (memW s (globN s "ws" + 32)))[i]? := by rw [hvals_eq]
        simp only [htabValues, List.getElem?_map, List.getElem?_range, hhdr32 3 (by omega), hi,
          Option.map_some, Option.some.injEq] at hget
        rw [hget]; exact hr32 htS i hi
      · rcases hT.2.2.2.1 32 (by simp [wsTableSlots]) hws_nz with h0 | hmS
        · simp only [T_new, List.mem_cons, List.not_mem_nil, or_false] at htN
          rcases htN with h1 | h2
          · exact absurd h1.symm (h0 ▸ WkBal.htab_nonzero_of_wf hnew_t1.1)
          · exact absurd h2.symm (h0 ▸ WkBal.htab_nonzero_of_wf hnew_t2.1)
        · exact absurd hmS (hT_disj_S _ htN)
  refine ⟨S', Nd, hsub_S, ⟨hT_post, hJ_post, hF_post, hTr_post⟩, ?_, ?_, trivial⟩
  · intro o ho
    unfold worldOwned at ho
    rcases List.mem_append.1 ho with ho12 | ho_nd
    · rcases List.mem_append.1 ho12 with ho_tab | ho_fix
      · rw [List.flatMap_append] at ho_tab
        rcases List.mem_append.1 ho_tab with ho_S | ho_N
        · obtain ⟨u, hu, hi⟩ := List.mem_flatMap.1 ho_S
          by_cases hub : u = ba
          · subst hub
            rcases (hba_fp o hi).2 with ⟨j, hj, hin⟩ | hfresh6
            · refine Or.inr (Or.inl ⟨j, ?_, hin⟩)
              unfold worldOwned
              exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨ba, hu, hj⟩))
            · exact Or.inr (Or.inr ⟨by dsimp [Inside] at hfresh6 ⊢; omega, hfresh6.2⟩)
          · rw [(hother_fp u hu hub).2] at hi
            refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
            unfold worldOwned
            exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨u, hu, hi⟩))
        · obtain ⟨t, htN, hi⟩ := List.mem_flatMap.1 ho_N
          have hin := (ht_new_in_heap t htN o hi).2
          exact Or.inr (Or.inr ⟨hin.1, by dsimp [Inside] at hin ⊢; omega⟩)
      · rcases hfix_p_class o ho_fix with ho_s | ho_new
        · refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
          unfold worldOwned
          exact List.mem_append_left _ (List.mem_append_right _ ho_s)
        · have hin := (hF_bal_adw_props o ho_new).2.2
          exact Or.inr (Or.inr ⟨hin.1, by dsimp [Inside] at hin ⊢; omega⟩)
    · rw [hne_eq] at ho_nd
      refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
      unfold worldOwned
      exact List.mem_append_right _ ho_nd
  · intro a hkeep hnot_hf
    apply hfr a
    · intro j hj hcj
      rcases List.mem_cons.1 hj with rfl | hj_fp
      · exact hkeep (freeGap s) (List.mem_append_right _ (List.mem_singleton.2 rfl))
          (WkBal.cellHits_sp0_imp_freeGap hAs.2 hcj)
      · apply hkeep j _ hcj
        apply List.mem_append_left; apply List.mem_append_left
        unfold worldOwned
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨ba, hba_S, hj_fp⟩))
    · intro hcf
      apply hnot_hf
      obtain ⟨h1, h2⟩ := hcf
      unfold heapFree CellHits at *
      dsimp at h1 h2 ⊢
      have := hARp.2.2.1
      omega

/-- A successful BAL enumeration returns an owned account record and a bounded key. -/
theorem decCall_bal_account_item_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (x : MlS) (ordExp : ExpHOL 64) (cont : ProgHOL 64)
    (hW : WorldOK s)
    (hnt : (evaluateHOLFiniteState s
      (.decCall x (.comb [.one, .one, .one]) (ofString "htab_item")
        [.var .global (ofString "bal_accounts"), ordExp] cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall x (.comb [.one, .one, .one]) (ofString "htab_item")
        [.var .global (ofString "bal_accounts"), ordExp] cont)).1) :
    ∃ (f0 f1 f2 : BitVec 64) (ck : Nat),
      (f0 ≠ 0 → f2.toNat ∈ balRecords s ∧
        Inside (f1.toNat, hdr s (globN s "bal_accounts") 0)
          (hdr s (globN s "bal_accounts") 4)
          (hdr s (globN s "bal_accounts") 4 +
            (hdr s (globN s "bal_accounts") 10 + 1) * hdr s (globN s "bal_accounts") 1)) ∧
      let sc := setVarHOLFinite x (.rStruct [.val (.word f0), .val (.word f1), .val (.word f2)])
        { s with clock := ck }
      (evaluateHOLFiniteState sc cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState sc cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x (.comb [.one, .one, .one]) (ofString "htab_item")
          [.var .global (ofString "bal_accounts"), ordExp] cont)).1 =
        (evaluateHOLFiniteState sc cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x (.comb [.one, .one, .one]) (ofString "htab_item")
          [.var .global (ofString "bal_accounts"), ordExp] cont)).2 =
        { (evaluateHOLFiniteState sc cont).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState sc cont).2.locals (x, s.locals.lookup x) } := by
  obtain ⟨tw, ordw, f0, f1, f2, ck, ht, _, htnz, hspec, hcont⟩ :=
    decCall_htab_item_resumes s x (.var .global (ofString "bal_accounts")) ordExp cont
      hW.1.1 hnt hres
  have hlookup : s.globals.lookup (ofString "bal_accounts") = some (.val (.word tw)) := ht
  have htN : globN s "bal_accounts" = tw.toNat := by
    simp [globN, hlookup]
  have hnz : globN s "bal_accounts" ≠ 0 := by
    rw [htN]
    intro hz
    apply htnz
    apply BitVec.eq_of_toNat_eq
    simpa using hz
  obtain ⟨S, htyped⟩ := hW.2
  obtain ⟨Nd, htyped⟩ := (worldTyped_iff_with s S).1 htyped
  have hS := (bal_accounts_slot_distinct htyped.1 hnz).1
  have htab : HtabWF s tw.toNat := by
    rw [← htN]
    exact (htyped.1.2.1 _ hS).1
  refine ⟨f0, f1, f2, ck, ?_, hcont⟩
  intro hf0
  obtain ⟨_, hkey, hval⟩ := hspec htab hf0
  refine ⟨?_, ?_⟩
  · have htn : tw.toNat ≠ 0 := by rwa [htN] at hnz
    simpa [balRecords, htN, htn, htabValues] using hval
  · simpa only [htN] using hkey

/-! ## Withdrawal iteration: multiplication, credit, and journal reset. -/

/-- Pure arithmetic can be composed with the withdrawal world effect. -/
theorem wkSc_u256_mul :
    WorldKeepsSc WorldOK (bufRegions []) [] stdKeep NoExtra (ofString "u256_mul") :=
  worldKeepsSc_of_readOnly InitECandidate.Solver.Wave8Contracts.M18.ro_u256_mul

theorem progWStep_withdrawal_iteration
    (B : BufList) (gw : List String)
    (hB : ValidBufList B) (hgw : SafeStepGlobals gw)
    (hbuf : ∀ p ∈ [("keccak_pad", 136), ("keccak_st", 200),
      ("mpt_nib_scratch", 64), ("sk_buf", 52)], p ∈ B)
    (hglobals : ∀ g ∈ ["heap_ptr", "journal_n", "scratch_ptr"], g ∈ gw)
    (e_w e_amt : ExpHOL 64) (args_mul args_ce : List (ExpHOL 64)) :
    ProgWStep B gw
      (.dec (ofString "w") .one e_w
        (.dec (ofString "amt") (.comb [.one, .one, .one, .one]) e_amt
          (.decCall (ofString "wei") (.comb [.one, .one, .one, .one])
            (ofString "u256_mul") args_mul
            (.seq (.call (some (none, none)) (ofString "create_ether") args_ce)
              (.seq (.assign .global (ofString "journal_n") (.const 0#64))
                (.assign .local (ofString "i")
                  (.op .add [.var .local (ofString "i"), .const 1#64]))))))) := by
  apply progWStep_dec
  apply progWStep_dec
  refine progWStep_decCall hB hgw (by simp) (by simp) wkSc_u256_mul ?_
  refine progWStep_seq hB hgw ?_ ?_
  · exact progWStep_call0 hbuf hglobals EvmEkFk.wkSc_create_ether
  · exact progWStep_seq hB hgw
      (progWStep_assign_journal_n_zero B gw (hglobals _ (by simp)))
      (progWStep_assign_local B gw _ _)

/-- The complete credit loop preserves the world, including every finite number
of iterations and each resumable exceptional exit. -/
theorem progWStep_withdrawal_loop
    (B : BufList) (gw : List String)
    (hB : ValidBufList B) (hgw : SafeStepGlobals gw)
    (hbuf : ∀ p ∈ [("keccak_pad", 136), ("keccak_st", 200),
      ("mpt_nib_scratch", 64), ("sk_buf", 52)], p ∈ B)
    (hglobals : ∀ g ∈ ["heap_ptr", "journal_n", "scratch_ptr"], g ∈ gw)
    (cond e_w e_amt : ExpHOL 64) (args_mul args_ce : List (ExpHOL 64)) :
    ProgWStep B gw
      (.while cond
        (.dec (ofString "w") .one e_w
          (.dec (ofString "amt") (.comb [.one, .one, .one, .one]) e_amt
            (.decCall (ofString "wei") (.comb [.one, .one, .one, .one])
              (ofString "u256_mul") args_mul
              (.seq (.call (some (none, none)) (ofString "create_ether") args_ce)
                (.seq (.assign .global (ofString "journal_n") (.const 0#64))
                  (.assign .local (ofString "i")
                    (.op .add [.var .local (ofString "i"), .const 1#64])))))))) :=
  progWStep_while hB hgw
    (progWStep_withdrawal_iteration B gw hB hgw hbuf hglobals e_w e_amt args_mul args_ce)

/-- Transaction initialization leaves scratch unchanged, so its world contract
also supplies the monotonicity needed by sequential framing. -/
theorem wkSc_state_fresh_tx :
    WorldKeepsSc WorldOK (fun _ => [])
      ["heap_ptr", "journal_n", "ts"]
      [("ws", [0, 8, 16, 24, 32]),
       ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "state_fresh_tx") := by
  obtain ⟨params, body, ret, hlookup, hbody⟩ := WkBal.wk_state_fresh_tx
  refine ⟨params, body, ret, hlookup, ?_⟩
  intro F s hc hW hex hnt hres
  have hs := hbody s hc hW hex hnt hres
  refine ⟨hs, ?_⟩
  have heq := hs.2.2.1 (ofString "scratch_ptr") (by decide)
  have hn := globN_eq_of_lookup heq
  exact Nat.le_of_eq hn

/-- Compose sequential world effects with arbitrary record masks. Only roots with a
nonempty preservation mask need to remain fixed. -/
theorem worldStepSc_trans_mask {F : Type}
    {B : BufList} {gw : List String} {keep : List (String × List Nat)}
    {s1 s2 s3 : PanSemStateFiniteExact 64 F}
    {r1 r2 : Option (PanSemResultExact 64)}
    (hB : ValidBufList B)
    (hbuf : bufRegions B s2 = bufRegions B s1)
    (hframe : globN s2 "frame_mem_ptr" = globN s1 "frame_mem_ptr")
    (hroots : ∀ rec ∈ keep, ∀ k ∈ rec.2, globN s2 rec.1 = globN s1 rec.1)
    (h12 : WorldStepSc (bufRegions B) gw keep NoExtra s1 r1 s2)
    (h23 : WorldStepSc (bufRegions B) gw keep NoExtra s2 r2 s3) :
    WorldStepSc (bufRegions B) gw keep NoExtra s1 r2 s3 := by
  obtain ⟨⟨hA2, hhp12, hG12, hK12, hW12⟩, hsc12⟩ := h12
  obtain ⟨⟨hA3, hhp23, hG23, hK23, hW23⟩, hsc23⟩ := h23
  refine ⟨⟨hA3, le_trans hhp12 hhp23,
    fun k hk => (hG12 k hk).trans (hG23 k hk), ?_, ?_⟩, le_trans hsc23 hsc12⟩
  · intro rec hrec hnz k hk hno
    have hg := hroots rec hrec k hk
    have h2 := hK23 rec hrec (by rw [hg]; exact hnz) k hk
      (by change ∀ i ∈ bufRegions B s2, ¬ CellHits (globN s2 rec.1 + k) i
          rw [hbuf, hg]; exact hno)
    rw [hg] at h2
    exact h2.trans (hK12 rec hrec hnz k hk hno)
  · intro S Nd hWT1 hD1
    obtain ⟨S2, Nd2, hsub12, hWT2, hOG12, hFO12, _⟩ := hW12 S Nd hWT1 hD1
    obtain ⟨S3, Nd3, hsub23, hWT3, hOG23, hFO23, _⟩ :=
      hW23 S2 Nd2 hWT2 (validBufList_disj hB hWT2)
    refine ⟨S3, Nd3, fun t ht => hsub23 t (hsub12 t ht), hWT3, ?_, ?_, trivial⟩
    · intro o ho
      rcases hOG23 o ho with rfl | ⟨j, hj, hin_oj⟩ | hin_o23
      · exact Or.inl rfl
      · rcases hOG12 j hj with rfl | ⟨k, hk, hin_jk⟩ | hin_j12
        · left
          rcases o with ⟨o1, o2⟩
          dsimp only [Inside] at hin_oj
          have ho1 : o1 = 0 := by omega
          have ho2 : o2 = 0 := by omega
          rw [ho1, ho2]
        · exact Or.inr (Or.inl ⟨k, hk, le_trans hin_jk.1 hin_oj.1, le_trans hin_oj.2 hin_jk.2⟩)
        · exact Or.inr (Or.inr ⟨le_trans hin_j12.1 hin_oj.1,
            le_trans hin_oj.2 (le_trans hin_j12.2 hhp23)⟩)
      · exact Or.inr (Or.inr ⟨le_trans hhp12 hin_o23.1, hin_o23.2⟩)
    · intro a ha hhf
      have hm12 : s2.memory a = s1.memory a := hFO12 a ha hhf
      have hm23 : s3.memory a = s2.memory a := by
        apply hFO23 a
        · intro i hi hch
          obtain ⟨hc1, hc2⟩ := hch
          rcases List.mem_append.1 hi with hi1 | hfg2
          · rcases List.mem_append.1 hi1 with hwo2 | hR2
            · rcases hOG12 i hwo2 with rfl | ⟨k, hk, hin_ik⟩ | hin_i12
              · dsimp only at hc2; omega
              · exact ha k (List.mem_append_left _ (List.mem_append_left _ hk))
                  ⟨by dsimp only [Inside] at hin_ik; omega,
                   by dsimp only [Inside] at hin_ik; omega⟩
              · have hp2_lim : globN s2 "heap_ptr" ≤ heapLimit := hA2.2.2.1
                exact hhf ⟨by unfold heapFree; dsimp only [Inside] at hin_i12 ⊢; omega,
                           by unfold heapFree; dsimp only [Inside] at hin_i12 ⊢; omega⟩
            · change i ∈ bufRegions B s2 at hR2
              rw [hbuf] at hR2
              exact ha i (List.mem_append_left _ (List.mem_append_right _ hR2)) ⟨hc1, hc2⟩
          · simp only [List.mem_singleton] at hfg2
            subst hfg2
            exact ha (freeGap s1) (List.mem_append_right _ (List.mem_singleton.2 rfl))
              ⟨by unfold freeGap at hc1 ⊢; dsimp only at hc1 ⊢; omega,
               by unfold freeGap at hc2 ⊢; dsimp only at hc2 ⊢; omega⟩
        · intro ⟨hc1, hc2⟩
          have hp2_lim : globN s2 "heap_ptr" ≤ heapLimit := hA2.2.2.1
          exact hhf ⟨by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega,
                     by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega⟩
      exact hm23.trans hm12

/-- Weaken buffer, global, and record effects together, including empty masks
for record roots replaced by transaction initialization. -/
theorem worldStepSc_mono_mask {F : Type}
    {B1 B2 : BufList} {gw1 gw2 : List String}
    {keep1 keep2 : List (String × List Nat)}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hB : ∀ p ∈ B1, p ∈ B2)
    (hgw : ∀ g ∈ gw1, g ∈ gw2)
    (hkeep : ∀ rec ∈ keep2, ∀ k ∈ rec.2,
      ∃ ks, (rec.1, ks) ∈ keep1 ∧ k ∈ ks)
    (h : WorldStepSc (bufRegions B1) gw1 keep1 NoExtra s r post) :
    WorldStepSc (bufRegions B2) gw2 keep2 NoExtra s r post := by
  obtain ⟨⟨hAp, hhp, hG, hK, hW⟩, hsc⟩ := h
  have hsubR : ∀ i ∈ bufRegions B1 s, i ∈ bufRegions B2 s := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
    exact List.mem_map.2 ⟨p, hB p hp, rfl⟩
  refine ⟨⟨hAp, hhp, ?_, ?_, ?_⟩, hsc⟩
  · intro k hk
    apply hG k
    intro hm
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hm
    exact hk (List.mem_map.2 ⟨g, hgw g hg, rfl⟩)
  · intro rec hrec hnz k hk hno
    obtain ⟨ks, hks, hk'⟩ := hkeep rec hrec k hk
    exact hK (rec.1, ks) hks hnz k hk' (fun i hi => hno i (hsubR i hi))
  · intro S Nd hWT hD
    obtain ⟨S', Nd', hsub, hWT', hOG, hFO, _⟩ :=
      hW S Nd hWT (fun i hi j hj => hD i (hsubR i hi) j hj)
    refine ⟨S', Nd', hsub, hWT', hOG, ?_, trivial⟩
    intro a ha hhf
    apply hFO a _ hhf
    intro i hi
    rcases List.mem_append.1 hi with hi1 | hfg
    · rcases List.mem_append.1 hi1 with hwo | hR1
      · exact ha i (List.mem_append_left _ (List.mem_append_left _ hwo))
      · exact ha i (List.mem_append_left _ (List.mem_append_right _ (hsubR i hR1)))
    · exact ha i (List.mem_append_right _ hfg)

def withdrawalBufs : BufList :=
  [("bal_key_buf", 64), ("keccak_pad", 136), ("keccak_st", 200),
   ("mpt_nib_scratch", 64), ("sk_buf", 52)]

def withdrawalGlobals : List String := ["heap_ptr", "journal_n", "scratch_ptr", "ts"]

def withdrawalKeep : List (String × List Nat) :=
  [("ws", [0, 8, 16, 24, 32]),
   ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", []),
   ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]

theorem wkSc_state_fresh_tx_withdrawal :
    WorldKeepsSc WorldOK (bufRegions withdrawalBufs) withdrawalGlobals
      withdrawalKeep NoExtra (ofString "state_fresh_tx") := by
  obtain ⟨params, body, ret, hlookup, hbody⟩ := wkSc_state_fresh_tx
  refine ⟨params, body, ret, hlookup, ?_⟩
  intro F s hc hW hex hnt hres
  exact worldStepSc_mono_mask (B1 := []) (by simp)
    (by decide) (fun rec hrec k hk => ⟨rec.2, hrec, hk⟩)
    (hbody s hc hW hex hnt hres)

theorem validBufList_withdrawal : ValidBufList withdrawalBufs := by
  intro p hp
  simp only [withdrawalBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact ⟨64, by decide, by decide, le_rfl⟩
  · exact ⟨136, by decide, by decide, le_rfl⟩
  · exact ⟨200, by decide, by decide, le_rfl⟩
  · exact ⟨64, by decide, by decide, le_rfl⟩
  · exact ⟨64, by decide, by decide, by decide⟩

theorem withdrawalStep_trans {F : Type}
    {s1 s2 s3 : PanSemStateFiniteExact 64 F}
    {r1 r2 : Option (PanSemResultExact 64)}
    (h12 : WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra s1 r1 s2)
    (h23 : WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra s2 r2 s3) :
    WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra s1 r2 s3 := by
  apply worldStepSc_trans_mask validBufList_withdrawal (h12 := h12) (h23 := h23)
  · unfold bufRegions
    apply List.map_congr_left
    intro p hp
    have hnot : ofString p.1 ∉ withdrawalGlobals.map ofString := by
      simp only [withdrawalBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide
    have hg : globN s2 p.1 = globN s1 p.1 :=
      globN_eq_of_lookup (h12.1.2.2.1 (ofString p.1) hnot)
    simp only [bufferRegion, hg]
  · exact globN_eq_of_lookup (h12.1.2.2.1 (ofString "frame_mem_ptr") (by decide))
  · intro rec hrec k hk
    have hnot : ofString rec.1 ∉ withdrawalGlobals.map ofString := by
      simp only [withdrawalKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · decide
      · decide
      · cases hk
      · decide
    exact globN_eq_of_lookup (h12.1.2.2.1 (ofString rec.1) hnot)

/-- Program effects with the withdrawal-specific global and record masks. -/
def ProgWithdrawalStep (p : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    s.code = originalRuntimeCode → WorldOK s →
    (evaluateHOLFiniteState s p).1 ≠ some .timeOut →
    FlowingOrResumes (evaluateHOLFiniteState s p).1 →
    WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra
      s (evaluateHOLFiniteState s p).1 (evaluateHOLFiniteState s p).2

theorem progWithdrawalStep_seq {p q : ProgHOL 64}
    (hp : ProgWithdrawalStep p) (hq : ProgWithdrawalStep q) :
    ProgWithdrawalStep (.seq p q) := by
  intro F s hc hW hnt hfr
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s p).1
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases hr : evaluateHOLFiniteState s p with ⟨r, mid⟩
  simp only [hr] at hmeta hnt hfr ⊢
  cases r with
  | none =>
    have hs := hp s hc hW (by rw [hr]; simp) (by rw [hr]; exact Or.inl rfl)
    rw [hr] at hs
    exact withdrawalStep_trans hs
      (hq mid (hmeta.trans hc) (hs.worldOK_bufs validBufList_withdrawal hW) hnt hfr)
  | some r =>
    have hs := hp s hc hW (by rw [hr]; exact hnt) (by rw [hr]; exact hfr)
    simpa only [hr] using hs

/-- Standard effects can be weakened to the withdrawal record mask. -/
theorem progWithdrawalStep_of_progWStep {B : BufList} {gw : List String}
    {p : ProgHOL 64} (hB : ∀ b ∈ B, b ∈ withdrawalBufs)
    (hgw : ∀ g ∈ gw, g ∈ withdrawalGlobals) (hp : ProgWStep B gw p) :
    ProgWithdrawalStep p := by
  intro F s hc hW hnt hfr
  apply worldStepSc_mono_mask hB hgw _ (hp s hc hW hnt hfr)
  intro rec hrec k hk
  simp only [withdrawalKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
  rcases hrec with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [stdKeep], hk⟩
  · exact ⟨_, by simp [stdKeep], hk⟩
  · cases hk
  · exact ⟨_, by simp [stdKeep], hk⟩

theorem progWithdrawalStep_dec {x : MlS} {sh : ShapeHOL} {e : ExpHOL 64}
    {body : ProgHOL 64} (hb : ProgWithdrawalStep body) :
    ProgWithdrawalStep (.dec x sh e body) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_dec_total] at hnt hfr ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | val
  · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hev] at hnt hfr ⊢
    by_cases hok : shapeEqHOL sh (shapeOfHOLExact val) = true
    · simp only [hok, ↓reduceIte] at hnt hfr ⊢
      set s1 := setVarHOLFinite x val s
      have hW1 : WorldOK s1 := localsFree_worldOK s _ s.clock hW
      have hstep := hb s1 hc hW1 hnt hfr
      exact (WorldStepSc.of_pre_locals_clock hstep).with_locals_clock _ (evaluateHOLFiniteState s1 body).2.clock
    · simp [hok] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem progWithdrawalStep_call0 {fname : MlS} {args : List (ExpHOL 64)}
    (hf : WorldKeepsSc WorldOK (bufRegions withdrawalBufs)
      withdrawalGlobals withdrawalKeep NoExtra fname) :
    ProgWithdrawalStep (.call (some (none, none)) fname args) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        let ent := callEntryStateHOLFinite s callee
        have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hW
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, cpost⟩
        simp only [ent] at hrun
        simp only [hrun] at hnt hfr ⊢
        have hnt_c : (evaluateHOLFiniteState ent body').1 ≠ some .timeOut := by
          simp only [ent, hrun]; rintro rfl; simp at hnt
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | returned v =>
            dsimp only at hfr ⊢
            split
            · have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
              simp only [ent, hrun] at hspec
              exact (hspec (Or.inl ⟨v, rfl⟩)).from_entry
            · rename_i hbad; simp [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hres_ex : Resumes (some (.exception eid ev)) := by
              rcases hfr with h | h | h | hr <;> try simp at h
              exact hr
            have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
            simp only [ent, hrun] at hspec
            exact (hspec hres_ex).from_entry

/-- The credit loop fits the weakened mask needed after replacing `ts`. -/
theorem progWithdrawalStep_credit_loop
    (cond e_w e_amt : ExpHOL 64) (args_mul args_ce : List (ExpHOL 64)) :
    ProgWithdrawalStep
      (.while cond
        (.dec (ofString "w") .one e_w
          (.dec (ofString "amt") (.comb [.one, .one, .one, .one]) e_amt
            (.decCall (ofString "wei") (.comb [.one, .one, .one, .one])
              (ofString "u256_mul") args_mul
              (.seq (.call (some (none, none)) (ofString "create_ether") args_ce)
                (.seq (.assign .global (ofString "journal_n") (.const 0#64))
                  (.assign .local (ofString "i")
                    (.op .add [.var .local (ofString "i"), .const 1#64])))))))) := by
  apply progWithdrawalStep_of_progWStep (B := withdrawalBufs)
    (gw := ["heap_ptr", "journal_n", "scratch_ptr"])
    (fun _ h => h) (by decide)
  exact progWStep_withdrawal_loop withdrawalBufs _ validBufList_withdrawal
    (by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;> simp)
    (by decide) (fun _ h => h) cond e_w e_amt args_mul args_ce

/-- Initialize the fresh transaction and compose its effect with any
withdrawal-framed continuation, including the complete credit loop. -/
theorem progWithdrawalStep_fresh_then {p : ProgHOL 64}
    (hp : ProgWithdrawalStep p) :
    ProgWithdrawalStep
      (.seq (.call (some (none, none)) (ofString "state_fresh_tx") []) p) :=
  progWithdrawalStep_seq
    (progWithdrawalStep_call0 wkSc_state_fresh_tx_withdrawal) hp

/-- The full withdrawal body reduces to the incorporation suffix's world frame. -/
theorem wkSc_process_withdrawals_of_incorporate
    (hinc : WorldKeepsSc WorldOK (bufRegions withdrawalBufs) withdrawalGlobals
      withdrawalKeep NoExtra (ofString "incorporate_tx_into_block")) :
    WorldKeepsSc WorldOK (bufRegions withdrawalBufs) withdrawalGlobals
      withdrawalKeep NoExtra (ofString "process_withdrawals") := by
  refine ⟨_, _, _, lookup_process_withdrawals, ?_⟩
  have hbody : ProgWithdrawalStep
      (sourceFunctionEntry Guest.Software.guestFn_process_withdrawals).2.2.1 := by
    simp only [sourceFunctionEntry, Guest.Software.guestFn_process_withdrawals,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      Option.map_none, List.map_nil]
    apply progWithdrawalStep_fresh_then
    apply progWithdrawalStep_dec
    apply progWithdrawalStep_dec
    apply progWithdrawalStep_dec
    refine progWithdrawalStep_seq (progWithdrawalStep_credit_loop _ _ _ _ _) ?_
    refine progWithdrawalStep_seq (progWithdrawalStep_call0 hinc) ?_
    exact progWithdrawalStep_of_progWStep (B := []) (gw := [])
      (by simp) (by simp) (progWStep_return [] [] _)
  intro F s hc hW _ hnt hres
  exact hbody s hc hW hnt (Or.inr (Or.inr (Or.inr hres)))

/-- Incorporation composes the builder update and table merge under the
withdrawal mask, including their resumable exceptional exits. -/
theorem wkSc_incorporate_tx_into_block_of_steps
    (hbuilder : WorldKeepsSc WorldOK (bufRegions withdrawalBufs) withdrawalGlobals
      withdrawalKeep NoExtra (ofString "update_builder_from_tx"))
    (hmerge : WorldKeepsSc WorldOK (bufRegions withdrawalBufs) withdrawalGlobals
      withdrawalKeep NoExtra (ofString "merge_tx_into_block")) :
    WorldKeepsSc WorldOK (bufRegions withdrawalBufs) withdrawalGlobals
      withdrawalKeep NoExtra (ofString "incorporate_tx_into_block") := by
  have hlookup : originalRuntimeCode.lookup (ofString "incorporate_tx_into_block") =
      some (sourceFunctionEntry Guest.Software.guestFn_incorporate_tx_into_block).2 :=
    originalRuntimeCode_lookup_of_guestAst_getElem 428 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_incorporate_tx_into_block) rfl
  refine ⟨_, _, _, hlookup, ?_⟩
  have hbody : ProgWithdrawalStep
      (sourceFunctionEntry Guest.Software.guestFn_incorporate_tx_into_block).2.2.1 := by
    simp only [sourceFunctionEntry, Guest.Software.guestFn_incorporate_tx_into_block,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      Option.map_none, List.map_nil]
    refine progWithdrawalStep_seq (progWithdrawalStep_call0 hbuilder) ?_
    refine progWithdrawalStep_seq (progWithdrawalStep_call0 hmerge) ?_
    exact progWithdrawalStep_of_progWStep (B := []) (gw := [])
      (by simp) (by simp) (progWStep_return [] [] _)
  intro F s hc hW _ hnt hres
  exact hbody s hc hW hnt (Or.inr (Or.inr (Or.inr hres)))

/-- A union into an ordinary world table preserves the world when its new
footprint is confined to the old footprint and freshly allocated heap. -/
theorem unionExit_worldStepSc_nonValue {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hW : WorldOK s) (hbe : post.be = s.be)
    (ht : ∀ S, TablesTyped s S → locN s "dst" ∈ S ∧
      (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ locN s "dst") ∧
      (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ locN s "dst") ∧
      globN s "bal_accounts" ≠ locN s "dst" ∧
      (∀ ad ∈ balRecords s, memW s ad ≠ locN s "dst") ∧
      (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ locN s "dst"))
    (hu : UnionExit s post)
    (hprov : ∀ i ∈ htabFootprint post (locN s "dst"),
      (∃ j ∈ htabFootprint s (locN s "dst"), Inside i j.1 (j.1 + j.2)) ∨
      Inside i (globN s "heap_ptr")
        (globN s "heap_ptr" + (globN post "heap_ptr" - globN s "heap_ptr"))) :
    WorldStepSc (bufRegions []) ["heap_ptr"] stdKeep NoExtra s r post := by
  obtain ⟨hA, hwf, hh0, _, hhp, halloc, hframe, hglobals⟩ := hu
  have hstep := R16WkMarkAccountCreated.worldStep_of_htabExit_nonValue
    (r := r) (gw := ["heap_ptr"]) hW hbe
    hglobals hglobals ht hA hwf hh0 hhp
    (fun i hi => ⟨halloc i hi, hprov i hi⟩) hframe
  refine ⟨hstep, ?_⟩
  have hs : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    globN_eq_of_lookup (hglobals (ofString "scratch_ptr") (by decide))
  exact Nat.le_of_eq hs

/-- Each of the five ordinary block tables used by the merge has a distinct
world role, separate from the tables whose values carry further ownership. -/
theorem merge_bs_table_role {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S : List Nat} (hT : TablesTyped s S) {k : Nat}
    (hk : k ∈ [8, 16, 24, 40, 48]) (hbs : globN s "bs" ≠ 0)
    (hnz : memW s (globN s "bs" + k) ≠ 0) :
    memW s (globN s "bs" + k) ∈ S ∧
    ∃ role : String, (memW s (globN s "bs" + k), role) ∈ worldRoleSlots s ∧
      role ≠ "bs+32" ∧ role ≠ "ts+32" ∧ role ≠ "bal_accounts" ∧
      role ≠ "bal.stor" ∧ role ≠ "ws+32" := by
  have hslot : k ∈ bsTableSlots := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp [bsTableSlots]
  have hmem : memW s (globN s "bs" + k) ∈ S := by
    rcases hT.2.2.2.2.1 k hslot hbs with hz | hm
    · exact absurd hz hnz
    · exact hm
  refine ⟨hmem, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · refine ⟨"bs+8", ?_, by decide, by decide, by decide, by decide, by decide⟩
    apply R16WkMarkAccountCreated.mem_worldRoleSlots_recRole s "bs" _ _ hbs hnz
    simp [recRoles, hbs]
  · refine ⟨"bs+16", ?_, by decide, by decide, by decide, by decide, by decide⟩
    apply R16WkMarkAccountCreated.mem_worldRoleSlots_recRole s "bs" _ _ hbs hnz
    simp [recRoles, hbs]
  · refine ⟨"bs+24", ?_, by decide, by decide, by decide, by decide, by decide⟩
    apply R16WkMarkAccountCreated.mem_worldRoleSlots_recRole s "bs" _ _ hbs hnz
    simp [recRoles, hbs]
  · refine ⟨"bs+40", ?_, by decide, by decide, by decide, by decide, by decide⟩
    apply R16WkMarkAccountCreated.mem_worldRoleSlots_recRole s "bs" _ _ hbs hnz
    simp [recRoles, hbs]
  · refine ⟨"bs+48", ?_, by decide, by decide, by decide, by decide, by decide⟩
    apply R16WkMarkAccountCreated.mem_worldRoleSlots_recRole s "bs" _ _ hbs hnz
    simp [recRoles, hbs]

/-- Ordinary merge destinations cannot alias any value-owning table. -/
theorem merge_bs_table_nonValue {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S : List Nat} (hT : TablesTyped s S) {k : Nat}
    (hk : k ∈ [8, 16, 24, 40, 48]) (hbs : globN s "bs" ≠ 0)
    (hnz : memW s (globN s "bs" + k) ≠ 0) :
    let t := memW s (globN s "bs" + k)
    t ∈ S ∧ (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t) ∧
      (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t) ∧
      globN s "bal_accounts" ≠ t ∧ (∀ ad ∈ balRecords s, memW s ad ≠ t) ∧
      (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t) := by
  obtain ⟨ht, role, hr, hb, hts, hba, hstor, hws⟩ := merge_bs_table_role hT hk hbs hnz
  have hroles := hT.2.2.2.2.2.2.2.2.2.2.2
  have hne : ∀ u label, (u, label) ∈ worldRoleSlots s → role ≠ label →
      u ≠ memW s (globN s "bs" + k) := by
    intro u label hu hlabel
    exact (R16WkMarkAccountCreated.slot_ne_of_diff_nonshared_role hroles hr hu hlabel).symm
  refine ⟨ht, ?_, ?_, ?_, ?_, ?_⟩
  · intro hb0 heq
    apply hne _ "bs+32" ?_ hb heq
    apply R16WkMarkAccountCreated.mem_worldRoleSlots_recRole s "bs" 32 _ hb0
      (by rw [heq]; exact hnz)
    simp [recRoles, hb0]
  · intro ht0 heq
    apply hne _ "ts+32" ?_ hts heq
    apply R16WkMarkAccountCreated.mem_worldRoleSlots_recRole s "ts" 32 _ ht0
      (by rw [heq]; exact hnz)
    simp [recRoles, ht0]
  · intro heq
    apply hne _ "bal_accounts" ?_ hba heq
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [heq, hnz]⟩
    simp
  · intro ad had heq
    apply hne _ "bal.stor" ?_ hstor heq
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [heq, hnz]⟩
    apply List.mem_append.2; right
    exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
  · intro hw0 heq
    apply hne _ "ws+32" ?_ hws heq
    apply R16WkMarkAccountCreated.mem_worldRoleSlots_recRole s "ws" 32 _ hw0
      (by rw [heq]; exact hnz)
    simp [recRoles, hw0]

/-- Retain the footprint provenance established by the union loop invariant. -/
theorem htab_union_into_provenance_spec :
    FunSpec UnionArgWF
      (OnReturn (fun s post => HtabUnionInto.ExitR (locN s "dst") s post))
      (ofString "htab_union_into") := by
  refine ⟨_, _, _, HtabUnionInto.lookup_htab_union_into, ?_⟩
  intro F s0 hcode hP _ _ v hv
  suffices key : Wave8M19.Htab.Ret s0
      (sourceFnBody Guest.Software.guestFn_htab_union_into)
      (fun _ post => HtabUnionInto.ExitR (locN s0 "dst") s0 post) from key v hv
  change Wave8M19.Htab.Ret s0
    (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
      (extractFn Guest.Software.guestFn_htab_union_into).body) _
  dsimp only [extractFn, Guest.Software.guestFn_htab_union_into,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  apply Wave8M19.Htab.Ret.dec
  intro capv _
  set s1 := setVarHOLFinite (ofString "cap") capv s0 with hs1
  apply Wave8M19.Htab.Ret.dec
  intro iv _
  set s2 := setVarHOLFinite (ofString "i") iv s1 with hs2
  have hI2 : HtabUnionInto.UInv s0 s2 := by
    refine ⟨hcode, ?_, ?_, ?_⟩
    · simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "i" ≠ ofString "dst" by decide,
        show ofString "cap" ≠ ofString "dst" by decide]
    · exact LocalsOnly.setVar HtabUnionInto.localsOnly_unionArgWF
        (by simp only [List.mem_singleton]; rintro _ rfl; decide) iv s1
        (LocalsOnly.setVar HtabUnionInto.localsOnly_unionArgWF
          (by simp only [List.mem_singleton]; rintro _ rfl; decide) capv s0 hP)
    · have h0 := HtabUnionInto.ExitR.refl (locN s0 "dst") s0 hP.1 hP.2.1 hP.2.2
      have h2 : HtabUnionInto.ExitR (locN s0 "dst")
          { s0 with locals := s0.locals, clock := s0.clock }
          { s0 with locals := s2.locals, clock := s0.clock } := by
        rw [HtabUnionInto.exitR_locals]; exact h0
      exact h2
  apply Wave8M19.Htab.Ret.seq
  · intro w hw
    exfalso
    have hnr : Wave8M19.Htab.NoRet
        (.decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item")
          [.var .local (ofString "src"), .var .local (ofString "i")]
          (.seq
            (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0))
              (.call (some (none, none)) (ofString "htab_set")
                [.var .local (ofString "dst"), .rfield 1 (.var .local (ofString "s")),
                 .rfield 2 (.var .local (ofString "s"))]) .skip)
            (.assign .local (ofString "i")
              (.op .add [.var .local (ofString "i"), .const 1])))) :=
      Wave8M19.Htab.NoRet.decCall (Wave8M19.Htab.NoRet.seq
        (Wave8M19.Htab.NoRet.ite Wave8M19.Htab.NoRet.call0 Wave8M19.Htab.NoRet.skip)
        Wave8M19.Htab.NoRet.assign)
    exact Wave8M19.Htab.while_noRet _ _ (fun st v => hnr st v) _ s2 le_rfl w hw
  · intro u hu
    apply Wave8M19.Htab.Ret.ret
    intro val _
    have hIu : HtabUnionInto.UInv s0 u := by
      have := Wave8M19.Htab.while_inv (HtabUnionInto.UInv s0) _ _
        (fun x hx _ hfl => HtabUnionInto.union_iter
          R13SoloHtabSet.htab_set_spec_proof _ _ _ _ s0 x hx hfl)
        s2.clock s2 le_rfl hI2 (by rw [hu])
      rw [hu] at this
      exact this
    obtain ⟨_, _, _, hR⟩ := hIu
    have h2 : HtabUnionInto.ExitR (locN s0 "dst")
        { s0 with locals := s0.locals, clock := s0.clock }
        { u with locals := u.locals, clock := u.clock } := hR
    rw [← HtabUnionInto.exitR_locals (L1 := s0.locals) (k1 := s0.clock)
      (L2 := HolFiniteMapExact.resVarEq
        (HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite u).locals
          (ofString "i", s1.locals.lookup (ofString "i")))
        (ofString "cap", s0.locals.lookup (ofString "cap"))) (k2 := u.clock)] at h2
    exact h2

/-- Normal union returns preserve the world when the destination is one of the
five ordinary block tables. The source table is unrestricted. -/
theorem htab_union_into_bs_world_spec :
    FunSpec (fun s => WorldOK s ∧ ∃ k, k ∈ [8, 16, 24, 40, 48] ∧
      globN s "bs" ≠ 0 ∧ locN s "dst" = memW s (globN s "bs" + k) ∧
      locN s "dst" ≠ 0)
      (fun s r post => ∀ v, r = some (.returned v) →
        WorldStepSc (bufRegions []) ["heap_ptr"] stdKeep NoExtra s r post)
      (ofString "htab_union_into") := by
  obtain ⟨params, body, ret, hl, hb⟩ := htab_union_into_provenance_spec
  refine ⟨params, body, ret, hl, ?_⟩
  intro F s hc hP hex hnt v hv
  obtain ⟨hW, k, hk, hbs, hdst, hnz⟩ := hP
  have hnon : ∀ S, TablesTyped s S → locN s "dst" ∈ S ∧
      (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ locN s "dst") ∧
      (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ locN s "dst") ∧
      globN s "bal_accounts" ≠ locN s "dst" ∧
      (∀ ad ∈ balRecords s, memW s ad ≠ locN s "dst") ∧
      (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ locN s "dst") := by
    intro S hT
    rw [hdst] at hnz ⊢
    exact merge_bs_table_nonValue hT hk hbs hnz
  have harg : UnionArgWF s := by
    obtain ⟨S, hT, _⟩ := hW.2
    have ht := (hnon S hT).1
    exact ⟨hW.1, (hT.2.1 _ ht).1, fun i hi => ((hT.2.1 _ ht).2 i hi).1⟩
  have he := hb s hc harg hex hnt v hv
  have hbe := (M13.evaluateHOLFiniteState_guestInv_be s body hW.1.1).2
  exact unionExit_worldStepSc_nonValue hW hbe hnon he.toUnionExit
    (fun i hi => (he.2.2.2.2.2.1 i hi).2)

private theorem union_noCatchableRaise_mono {g1 g2 : MlS → Bool}
    (himp : ∀ f, g1 f = true → g2 f = true) :
    ∀ p : ProgHOL 64, noCatchableRaise g1 p = true → noCatchableRaise g2 p = true
  | .skip, _ | .«break», _ | .«continue», _ | .annot _ _, _ | .«return» _, _
  | .assign _ _ _, _ | .store _ _, _ | .storeByte _ _, _ | .store32 _ _, _
  | .shMemStore _ _ _, _ | .extCall _ _ _ _ _, _ | .primitive _ _ _, _ => rfl
  | .raise _ _, hp => hp
  | .dec _ _ _ b, hp => union_noCatchableRaise_mono himp b hp
  | .seq a b, hp | .ite _ a b, hp => by
      simp only [noCatchableRaise, Bool.and_eq_true] at hp ⊢
      exact ⟨union_noCatchableRaise_mono himp a hp.1,
        union_noCatchableRaise_mono himp b hp.2⟩
  | .while _ b, hp => union_noCatchableRaise_mono himp b hp
  | .decCall _ _ fn _ cont, hp => by
      simp only [noCatchableRaise, Bool.and_eq_true] at hp ⊢
      exact ⟨himp fn hp.1, union_noCatchableRaise_mono himp cont hp.2⟩
  | .call tail fn _, hp => by
      rcases tail with _ | ⟨_, hdl⟩
      · simp [noCatchableRaise] at hp
      · rcases hdl with _ | _
        · exact himp fn hp
        · simp [noCatchableRaise] at hp
  | .shMemLoad _ _ _ _, hp => by simp [noCatchableRaise] at hp

private def unionTrapCallees (f : MlS) : Bool :=
  trapOnlyCallees f || f == ofString "htab_item"

private theorem unionTrapCallees_good :
    ∀ f, unionTrapCallees f = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body, callee, rs) →
      noCatchableRaise unionTrapCallees body = true := by
  intro f hf values body callee rs hfound
  simp only [unionTrapCallees, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with hf | rfl
  · exact union_noCatchableRaise_mono (fun g hg => by simp [unionTrapCallees, hg])
      body (trapOnlyCallees_good f hf values body callee rs hfound)
  · obtain ⟨_, _, hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
    rw [lookup_htab_item_bal] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]
    decide

theorem htab_union_into_no_catchable_exn {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (e : MlS) (v : ValueHOL 64)
    (hne : e ≠ ofString "TrapErr") :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_union_into)).1 ≠
      some (.exception e v) :=
  evaluate_noCatchableRaise unionTrapCallees unionTrapCallees_good
    (sourceFnBody Guest.Software.guestFn_htab_union_into) (by decide) s hcode e v hne

/-- The ordinary block-table union frame also covers all resumable exits. -/
theorem wkSc_htab_union_into_bs :
    WorldKeepsSc (fun s => WorldOK s ∧ ∃ k, k ∈ [8, 16, 24, 40, 48] ∧
      globN s "bs" ≠ 0 ∧ locN s "dst" = memW s (globN s "bs" + k) ∧
      locN s "dst" ≠ 0)
      (bufRegions []) ["heap_ptr"] stdKeep NoExtra (ofString "htab_union_into") := by
  obtain ⟨params, body, ret, hl, hb⟩ := htab_union_into_bs_world_spec
  have hbody : body = sourceFnBody Guest.Software.guestFn_htab_union_into := by
    rw [HtabUnionInto.lookup_htab_union_into] at hl
    exact (Prod.mk.inj (Prod.mk.inj (Option.some.inj hl)).2).1.symm
  refine ⟨params, body, ret, hl, ?_⟩
  intro F s hc hP hex hnt hres
  rcases hres with ⟨v, hv⟩ | ⟨e, v, he, hne⟩
  · exact hb s hc hP hex hnt v hv
  · exfalso
    exact htab_union_into_no_catchable_exn s hc e v hne (by rwa [← hbody])

/-- Lift a callee world frame whose extra precondition is established at call entry. -/
theorem progWStep_call0_of_entry {B : BufList} {gw : List String}
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} {args : List (ExpHOL 64)}
    (hf : WorldKeepsSc P (bufRegions B) gw stdKeep NoExtra fname)
    (hentry : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode → WorldOK s → ∀ vs body callee ret,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vs →
      lookupCodeHOLFinite s.code.lookup fname vs = some (body, callee, ret) →
      P (callEntryStateHOLFinite s callee)) :
    ProgWStep B gw (.call (some (none, none)) fname args) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases ha : @evalListHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, ha] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, ha] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body, callee, ret⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        have hP := hentry s hc hW vs body callee ret
          (by rwa [evalListHOLFinite_eq_toExact]) hl
        rcases hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, post⟩
        simp only [hr] at hnt hfr ⊢
        have hnc : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 ≠
            some .timeOut := by rw [hr]; rintro rfl; simp at hnt
        have hs := FunSpec.at_lookup hf s hc vs body callee ret hl hP hnc
        rw [hr] at hs
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | returned v =>
            dsimp only at hfr ⊢
            split
            · exact (hs (Or.inl ⟨v, rfl⟩)).from_entry
            · rename_i hbad; simp [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hres : Resumes (some (.exception eid ev)) := by
              rcases hfr with h | h | h | h <;> try simp at h
              exact h
            exact (hs hres).from_entry

/-- Argument evaluation identifies the ordinary block-table destination at entry. -/
theorem union_bs_call_entry {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (off : BitVec 64) (hoff : off.toNat ∈ [8, 16, 24, 40, 48])
    (src : ExpHOL 64) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.load .one (.op .add [.var .global (ofString "bs"), .const off]), src] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_union_into") vs =
      some (body, callee, ret)) :
    WorldOK (callEntryStateHOLFinite s callee) ∧ ∃ k, k ∈ [8, 16, 24, 40, 48] ∧
      globN (callEntryStateHOLFinite s callee) "bs" ≠ 0 ∧
      locN (callEntryStateHOLFinite s callee) "dst" =
        memW (callEntryStateHOLFinite s callee) (globN (callEntryStateHOLFinite s callee) "bs" + k) := by
  have ha' := ha
  rw [evalListHOLFinite_eq_toExact] at ha'
  rcases he1 : evalAt s (.load .one (.op .add [.var .global (ofString "bs"), .const off])) with _ | v1
  · simp [evalListHOLExact, he1] at ha'
  · rcases he2 : evalAt s src with _ | v2
    · simp [evalListHOLExact, he1, he2] at ha'
    · have hv : vs = [v1, v2] := by
        simpa only [evalListHOLExact, he1, he2, Option.some.injEq] using ha'.symm
      subst vs
      have hp : callee.lookup (ofString "dst") = some v1 := by
        unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
        split at hl
        · cases hl
        · rename_i eb el er raw
          have heq := Option.some.inj hl
          cases heq
          unfold lookupCodeHOLExact at raw
          rw [hc, HtabUnionInto.lookup_htab_union_into] at raw
          dsimp only at raw
          split at raw
          · have hloc' := (Prod.mk.inj (Prod.mk.inj (Option.some.inj raw)).2).1
            subst el
            simp [HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "dst" ≠ ofString "src" by decide]
          · cases raw
      have hbound : off.toNat < sourceBase := by
        have hk := hoff
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with h | h | h | h | h <;> rw [h] <;> decide
      obtain ⟨w, rfl, hw, hbs⟩ := evalAt_loadG_nz s hW.1.1 "bs" off hbound v1 he1
      have hd : locN (callEntryStateHOLFinite s callee) "dst" =
          memW s (globN s "bs" + off.toNat) := by
        simp [locN, callEntryStateHOLFinite, hp, hw]
      exact ⟨localsFree_worldOK s callee (s.clock - 1) hW,
        off.toNat, hoff, hbs, hd⟩

/-- A union iteration cannot finish its insertion when the destination is null. -/
theorem union_zero_set_no_flow {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hz : locN s "dst" = 0) (rest : List (ExpHOL 64)) :
    ¬ Wave8M19.Htab.FlowR (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set")
        (.var .local (ofString "dst") :: rest))).1 := by
  intro hflow
  have hnr := Wave8M19.Htab.call0_noRetBrk s (ofString "htab_set")
    (.var .local (ofString "dst") :: rest)
  have hflow2 : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set") (.var .local (ofString "dst") :: rest))).1 = none ∨
    (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set") (.var .local (ofString "dst") :: rest))).1 = some .continue := by
    rcases hflow with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hnr.1.2
  obtain ⟨values, body, callee, ret, v, post, ha, hl, hr, _⟩ :=
    Wave8M19.Htab.call0_flow s _ _ hflow2
  obtain ⟨tv, vs, rfl, htv⟩ := Wave8M19.Htab.evalList_cons_inv s _ _ ha
  obtain ⟨_, hct⟩ := Wave8M19.Htab.lookupCodeHOLFinite_param_at s.code.lookup
    (ofString "htab_set") [] (ofString "t") .one
    [(ofString "key", .one), (ofString "value", .one)] _ _
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> decide)
    (by rw [hc]; exact EvmFrameSpecs.lookup_htab_set) (vpre := []) (by simp) hl
  have ht : callee.lookup (ofString "t") = s.locals.lookup (ofString "dst") := by
    rw [hct]
    simp only [evalHOLExact] at htv
    exact htv.symm
  have hn := FunSpec.at_lookup EvmFrameSpecs.nz_htab_set s hc _ body callee ret hl
    (guestInv_callEntry s callee hG) (by rw [hr]; simp)
  rw [hr] at hn
  have hne := hn (Or.inl ⟨v, rfl⟩)
  apply hne
  simpa only [locN, callEntryStateHOLFinite, ht] using hz

/-- A flowing conditional insertion into a null table must take the skip arm. -/
theorem union_zero_ite_flow {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hz : locN s "dst" = 0) (cond : ExpHOL 64) (rest : List (ExpHOL 64))
    (hf : Wave8M19.Htab.FlowR (evaluateHOLFiniteState s
      (.ite cond (.call (some (none, none)) (ofString "htab_set")
        (.var .local (ofString "dst") :: rest)) .skip)).1) :
    evaluateHOLFiniteState s
      (.ite cond (.call (some (none, none)) (ofString "htab_set")
        (.var .local (ofString "dst") :: rest)) .skip) = (none, s) := by
  rcases HtabUnionInto.ite_flow_split s _ _ _ hf with ⟨hy, _⟩ | ⟨_, hn⟩
  · exact (union_zero_set_no_flow s hc hG hz rest hy).elim
  · rw [hn, evaluateHOLFiniteState_skip]

/-- Null-destination union iterations only change locals and the clock. -/
theorem union_zero_iter {F : Type} (x : PanSemStateFiniteExact 64 F)
    (hc : x.code = originalRuntimeCode) (hG : GuestInv x) (hz : locN x "dst" = 0)
    (itemArgs : List (ExpHOL 64)) (cond : ExpHOL 64) (rest : List (ExpHOL 64))
    (inc : ExpHOL 64)
    (hf : Wave8M19.Htab.FlowR (evaluateHOLFiniteState (decClockHOLFinite x)
      (.decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item") itemArgs
        (.seq (.ite cond (.call (some (none, none)) (ofString "htab_set")
          (.var .local (ofString "dst") :: rest)) .skip)
          (.assign .local (ofString "i") inc)))).1) :
    let post := (evaluateHOLFiniteState (decClockHOLFinite x)
      (.decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item") itemArgs
        (.seq (.ite cond (.call (some (none, none)) (ofString "htab_set")
          (.var .local (ofString "dst") :: rest)) .skip)
          (.assign .local (ofString "i") inc)))).2
    post = { x with locals := post.locals, clock := post.clock } ∧
      post.locals.lookup (ofString "dst") = x.locals.lookup (ofString "dst") := by
  intro post
  obtain ⟨values, body, callee, ret, rv, cpost, ha, hl, hr, hcont, hp⟩ :=
    HtabUnionInto.decCall_flow (decClockHOLFinite x) _ _ _ _ _ hf
  have hro : FunSpec GuestInv
      (fun s r post => Resumes r → post = { s with locals := post.locals, clock := post.clock })
      (ofString "htab_item") := InitECandidate.Solver.Wave8Contracts.M15.ro_htab_item
  have hitem := FunSpec.at_lookup hro
    (decClockHOLFinite x) hc values body callee ret hl
    (guestInv_with_locals_clock x callee _ hG) (by rw [hr]; simp)
  rw [hr] at hitem
  have hcp : cpost = { x with locals := cpost.locals, clock := cpost.clock } :=
    hitem (Or.inl ⟨rv, rfl⟩)
  let s1 := setVarHOLFinite (ofString "s") rv { cpost with locals := x.locals }
  have hs1 : s1 = { x with locals := x.locals.update (ofString "s", rv), clock := cpost.clock } := by
    dsimp only [s1]; rw [hcp]; rfl
  have hG1 : GuestInv s1 := by rw [hs1]; exact guestInv_with_locals_clock x _ _ hG
  have hz1 : locN s1 "dst" = 0 := by
    rw [hs1]; simpa [locN, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "s" ≠ ofString "dst" by decide] using hz
  let ip : ProgHOL 64 := .ite cond
    (.call (some (none, none)) (ofString "htab_set") (.var .local (ofString "dst") :: rest)) .skip
  have hip : ∀ h : Wave8M19.Htab.FlowR (evaluateHOLFiniteState s1 ip).1,
      evaluateHOLFiniteState s1 ip = (none, s1) := fun h =>
    union_zero_ite_flow s1 (by rw [hs1]; exact hc) hG1 hz1 cond rest h
  rcases HtabUnionInto.seq_flow_split s1 ip (.assign .local (ofString "i") inc) hcont with
    ⟨mid, hm, ha', hseq⟩ | ⟨hne, hi, hseq⟩
  · have he := hip (Or.inl (by rw [hm]))
    have hmid : mid = s1 := by rw [he] at hm; exact (Prod.mk.inj hm).2.symm
    subst mid
    obtain ⟨iv, _, hasg⟩ := HtabUnionInto.assign_local_flow s1 _ _ ha'
    have hpost : post = { s1 with locals := (HolFiniteMapExact.resVarEq
        (setVarHOLFinite (ofString "i") iv s1).locals
        (ofString "s", x.locals.lookup (ofString "s"))) } := by
      dsimp only [post]; rw [hp]
      change { (evaluateHOLFiniteState s1 (.seq ip (.assign .local (ofString "i") inc))).2 with
        locals := HolFiniteMapExact.resVarEq
          (evaluateHOLFiniteState s1 (.seq ip (.assign .local (ofString "i") inc))).2.locals
          (ofString "s", x.locals.lookup (ofString "s")) } = _
      rw [hseq, hasg]; rfl
    rw [hpost, hs1]
    constructor
    · rfl
    · rw [PanRunBounded.resVarEq_lookup]
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "dst" ≠ ofString "s" by decide,
        show ofString "s" ≠ ofString "dst" by decide,
        show ofString "i" ≠ ofString "dst" by decide]
  · have he := hip hi
    simp [he] at hne

/-- A normally completed null-destination union loop preserves all nonlocal state. -/
theorem union_zero_loop {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s) (hz : locN s "dst" = 0)
    (guard cond inc : ExpHOL 64) (itemArgs rest : List (ExpHOL 64))
    (hf : (evaluateHOLFiniteState s (.while guard
      (.decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item") itemArgs
        (.seq (.ite cond (.call (some (none, none)) (ofString "htab_set")
          (.var .local (ofString "dst") :: rest)) .skip)
          (.assign .local (ofString "i") inc))))).1 = none) :
    let post := (evaluateHOLFiniteState s (.while guard
      (.decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item") itemArgs
        (.seq (.ite cond (.call (some (none, none)) (ofString "htab_set")
          (.var .local (ofString "dst") :: rest)) .skip)
          (.assign .local (ofString "i") inc))))).2
    post = { s with locals := post.locals, clock := post.clock } ∧
      post.locals.lookup (ofString "dst") = s.locals.lookup (ofString "dst") := by
  let I := fun x : PanSemStateFiniteExact 64 F =>
    x = { s with locals := x.locals, clock := x.clock } ∧
      x.locals.lookup (ofString "dst") = s.locals.lookup (ofString "dst")
  apply Wave8M19.Htab.while_inv I guard _ ?_ s.clock s le_rfl ⟨rfl, rfl⟩ hf
  intro x hx _ hflow
  have hcx : x.code = originalRuntimeCode := by rw [hx.1]; exact hc
  have hGx : GuestInv x := by rw [hx.1]; exact guestInv_with_locals_clock s _ _ hG
  have hzx : locN x "dst" = 0 := by simpa only [locN, hx.2] using hz
  obtain ⟨he, hd⟩ := union_zero_iter x hcx hGx hzx itemArgs cond rest inc hflow
  refine ⟨?_, hd.trans hx.2⟩
  rw [he]
  rw [hx.1]

/-- A successful union into a null destination is read-only outside locals and clock. -/
theorem htab_union_into_zero_spec :
    FunSpec (fun s => GuestInv s ∧ locN s "dst" = 0)
      (OnReturn (fun s post => post = { s with locals := post.locals, clock := post.clock }))
      (ofString "htab_union_into") := by
  refine ⟨_, _, _, HtabUnionInto.lookup_htab_union_into, ?_⟩
  intro F s0 hc hP _ _ v hv
  suffices key : Wave8M19.Htab.Ret s0
      (sourceFnBody Guest.Software.guestFn_htab_union_into)
      (fun _ post => post = { s0 with locals := post.locals, clock := post.clock }) from key v hv
  change Wave8M19.Htab.Ret s0
    (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
      (extractFn Guest.Software.guestFn_htab_union_into).body) _
  dsimp only [extractFn, Guest.Software.guestFn_htab_union_into,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  apply Wave8M19.Htab.Ret.dec
  intro capv _
  set s1 := setVarHOLFinite (ofString "cap") capv s0 with hs1
  apply Wave8M19.Htab.Ret.dec
  intro iv _
  set s2 := setVarHOLFinite (ofString "i") iv s1 with hs2
  have hG2 : GuestInv s2 := guestInv_with_locals_clock s0 s2.locals s2.clock hP.1
  have hz2 : locN s2 "dst" = 0 := by
    simpa [hs2, hs1, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "i" ≠ ofString "dst" by decide,
      show ofString "cap" ≠ ofString "dst" by decide] using hP.2
  apply Wave8M19.Htab.Ret.seq
  · intro w hw
    exfalso
    have hnr : Wave8M19.Htab.NoRet
        (.decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item")
          [.var .local (ofString "src"), .var .local (ofString "i")]
          (.seq
            (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0))
              (.call (some (none, none)) (ofString "htab_set")
                [.var .local (ofString "dst"), .rfield 1 (.var .local (ofString "s")),
                 .rfield 2 (.var .local (ofString "s"))]) .skip)
            (.assign .local (ofString "i")
              (.op .add [.var .local (ofString "i"), .const 1])))) :=
      Wave8M19.Htab.NoRet.decCall (Wave8M19.Htab.NoRet.seq
        (Wave8M19.Htab.NoRet.ite Wave8M19.Htab.NoRet.call0 Wave8M19.Htab.NoRet.skip)
        Wave8M19.Htab.NoRet.assign)
    exact Wave8M19.Htab.while_noRet _ _ (fun st v => hnr st v) _ s2 le_rfl w hw
  · intro u hu
    apply Wave8M19.Htab.Ret.ret
    intro val _
    have he := (union_zero_loop s2 hc hG2 hz2 _ _ _ _ _ (by rw [hu])).1
    rw [hu] at he
    dsimp only [Prod.snd] at he
    rw [he]
    rfl

/-- Null block-table destinations need no allocation frame: every resumable exit is read-only. -/
theorem wkSc_htab_union_into_zero :
    WorldKeepsSc (fun s => WorldOK s ∧ locN s "dst" = 0)
      (bufRegions []) ["heap_ptr"] stdKeep NoExtra (ofString "htab_union_into") := by
  obtain ⟨params, body, ret, hl, hb⟩ := htab_union_into_zero_spec
  have hbody : body = sourceFnBody Guest.Software.guestFn_htab_union_into := by
    rw [HtabUnionInto.lookup_htab_union_into] at hl
    exact (Prod.mk.inj (Prod.mk.inj (Option.some.inj hl)).2).1.symm
  refine ⟨params, body, ret, hl, ?_⟩
  intro F s hc hP hex hnt hres
  rcases hres with ⟨v, hv⟩ | ⟨e, v, he, hne⟩
  · have hp := hb s hc ⟨hP.1.1.1, hP.2⟩ hex hnt v hv
    rw [hp]
    exact (WorldStepSc.refl s (some (.returned v)) hP.1.1).with_locals_clock _ _
  · exfalso
    exact htab_union_into_no_catchable_exn s hc e v hne (by rwa [← hbody])

/-- Both null and allocated ordinary block tables share the same union frame. -/
theorem wkSc_htab_union_into_bs_all :
    WorldKeepsSc (fun s => WorldOK s ∧ ∃ k, k ∈ [8, 16, 24, 40, 48] ∧
      globN s "bs" ≠ 0 ∧ locN s "dst" = memW s (globN s "bs" + k))
      (bufRegions []) ["heap_ptr"] stdKeep NoExtra (ofString "htab_union_into") := by
  obtain ⟨params, body, ret, hl, hb⟩ := wkSc_htab_union_into_bs
  obtain ⟨params0, body0, ret0, hl0, hb0⟩ := wkSc_htab_union_into_zero
  have heq := Option.some.inj (hl.symm.trans hl0)
  cases heq
  refine ⟨params, body, ret, hl, ?_⟩
  intro F s hc hP hex hnt hres
  by_cases hz : locN s "dst" = 0
  · exact hb0 s hc ⟨hP.1, hz⟩ hex hnt hres
  · obtain ⟨hW, k, hk, hbs, hd⟩ := hP
    exact hb s hc ⟨hW, k, hk, hbs, hd, hz⟩ hex hnt hres

/-- Every ordinary block-table union call has its required entry frame. -/
theorem progWStep_union_bs (off : BitVec 64)
    (hoff : off.toNat ∈ [8, 16, 24, 40, 48]) (src : ExpHOL 64) :
    ProgWStep [] ["heap_ptr"]
      (.call (some (none, none)) (ofString "htab_union_into")
        [.load .one (.op .add [.var .global (ofString "bs"), .const off]), src]) := by
  apply progWStep_call0_of_entry wkSc_htab_union_into_bs_all
  intro F s hc hW vs body callee ret ha hl
  exact union_bs_call_entry s hc hW off hoff src vs body callee ret ha hl

/-- Ordinary table merging composes with any withdrawal-framed storage suffix. -/
theorem progWithdrawalStep_union_bs_then (off : BitVec 64)
    (hoff : off.toNat ∈ [8, 16, 24, 40, 48]) (src : ExpHOL 64)
    {p : ProgHOL 64} (hp : ProgWithdrawalStep p) :
    ProgWithdrawalStep
      (.seq (.call (some (none, none)) (ofString "htab_union_into")
        [.load .one (.op .add [.var .global (ofString "bs"), .const off]), src]) p) := by
  refine progWithdrawalStep_seq ?_ hp
  exact progWithdrawalStep_of_progWStep (by simp)
    (by simp [withdrawalGlobals]) (progWStep_union_bs off hoff src)

/-- The storage-table portion after the five ordinary block unions. -/
def mergeStorageSuffix : ProgHOL 64 :=
  match (sourceFunctionEntry Guest.Software.guestFn_merge_tx_into_block).2.2.1 with
  | .seq _ (.seq _ (.seq _ (.seq _ (.seq _ p)))) => p
  | _ => .skip

/-- The ordinary union prefix is fully discharged; only storage ownership remains. -/
theorem wkSc_merge_tx_into_block_of_storage_suffix
    (hsuffix : ProgWithdrawalStep mergeStorageSuffix) :
    WorldKeepsSc WorldOK (bufRegions withdrawalBufs) withdrawalGlobals
      withdrawalKeep NoExtra (ofString "merge_tx_into_block") := by
  have hlookup : originalRuntimeCode.lookup (ofString "merge_tx_into_block") =
      some (sourceFunctionEntry Guest.Software.guestFn_merge_tx_into_block).2 :=
    originalRuntimeCode_lookup_of_guestAst_getElem 401 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_merge_tx_into_block) rfl
  refine ⟨_, _, _, hlookup, ?_⟩
  have hbody : ProgWithdrawalStep
      (sourceFunctionEntry Guest.Software.guestFn_merge_tx_into_block).2.2.1 := by
    simp only [sourceFunctionEntry, Guest.Software.guestFn_merge_tx_into_block,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      Option.map_none, List.map_nil]
    refine progWithdrawalStep_union_bs_then 24 (by decide) _ ?_
    refine progWithdrawalStep_union_bs_then 8 (by decide) _ ?_
    refine progWithdrawalStep_union_bs_then 40 (by decide) _ ?_
    refine progWithdrawalStep_union_bs_then 16 (by decide) _ ?_
    refine progWithdrawalStep_union_bs_then 48 (by decide) _ ?_
    exact hsuffix
  intro F s hc hW _ hnt hres
  exact hbody s hc hW hnt (Or.inr (Or.inr (Or.inr hres)))

/-- Branches preserve the withdrawal mask, including resumable exits. -/
theorem progWithdrawalStep_ite {cond : ExpHOL 64} {yes no : ProgHOL 64}
    (hy : ProgWithdrawalStep yes) (hn : ProgWithdrawalStep no) :
    ProgWithdrawalStep (.ite cond yes no) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_ite] at hnt hfr ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) cond with _ | cv
  · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
  · rcases cv with ⟨⟨w⟩⟩ | _ | _
    · simp only [hev] at hnt hfr ⊢
      by_cases hw : w = 0
      · simp only [hw, ↓reduceIte] at hnt hfr ⊢; exact hn s hc hW hnt hfr
      · simp only [hw, ↓reduceIte] at hnt hfr ⊢; exact hy s hc hW hnt hfr
    · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error

/-- Loop composition for the withdrawal mask permits the replaced `ts` root. -/
theorem progWithdrawalStep_while {cond : ExpHOL 64} {body : ProgHOL 64}
    (hb : ProgWithdrawalStep body) :
    ProgWithdrawalStep (.while cond body) := by
  intro F s0 hc0 hW0 hnt0 hfr0
  suffices ∀ (k : Nat) (s : PanSemStateFiniteExact 64 F),
      s.clock = k → s.code = originalRuntimeCode → WorldOK s →
      (evaluateHOLFiniteState s (.while cond body)).1 ≠ some .timeOut →
      FlowingOrResumes (evaluateHOLFiniteState s (.while cond body)).1 →
      WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra
        s (evaluateHOLFiniteState s (.while cond body)).1
        (evaluateHOLFiniteState s (.while cond body)).2 from
    this s0.clock s0 rfl hc0 hW0 hnt0 hfr0
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro s hclk hc hW hnt hfr
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt hfr ⊢
    rcases hev : @evalHOLFinite 64 F _ s
        (fun a => Classical.propDecidable (s.memaddrs a)) cond with _ | cv
    · simp only [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hev] at hnt hfr ⊢
      rcases cv with ⟨⟨w⟩⟩ | _ | _
      · dsimp only at hnt hfr ⊢
        by_cases hw : w = 0
        · subst hw; exact WorldStepSc.refl s none hW.1
        · rw [if_pos hw] at hnt hfr ⊢
          by_cases hk0 : s.clock = 0
          · simp [hk0] at hnt
          · rw [if_neg hk0] at hnt hfr ⊢
            set sd := decClockHOLFinite s
            have hWd : WorldOK sd := localsFree_worldOK s s.locals (s.clock - 1) hW
            have hclk_le := evaluateHOLFiniteState_clock_le sd body
            have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata sd body).1
            rcases hbo : evaluateHOLFiniteState sd body with ⟨rb, mid⟩
            have hbo' : evaluateHOLFiniteState (decClockHOLFinite s) body = (rb, mid) := hbo
            simp only [sd, hbo'] at hnt hfr hclk_le hmeta ⊢
            have hmid_lt : mid.clock < k := by
              change mid.clock ≤ s.clock - 1 at hclk_le; omega
            have hnt_b : (evaluateHOLFiniteState sd body).1 ≠ some .timeOut := by
              rw [hbo]; rintro rfl; exact hnt rfl
            cases rb with
            | none =>
              have hsb := hb sd hc hWd hnt_b (by rw [hbo]; exact Or.inl rfl)
              rw [hbo] at hsb
              have hW_mid := hsb.worldOK_bufs validBufList_withdrawal hWd
              have hsb' : WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals
                  withdrawalKeep NoExtra s none mid :=
                (WorldStepSc.of_pre_locals_clock hsb).with_locals_clock mid.locals mid.clock
              exact withdrawalStep_trans hsb'
                (ih mid.clock hmid_lt mid rfl (hmeta.trans hc) hW_mid hnt hfr)
            | some r =>
              cases r with
              | «continue» =>
                have hsb := hb sd hc hWd hnt_b (by rw [hbo]; exact Or.inr (Or.inl rfl))
                rw [hbo] at hsb
                have hW_mid := hsb.worldOK_bufs validBufList_withdrawal hWd
                have hsb' : WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals
                    withdrawalKeep NoExtra s (some .continue) mid :=
                  (WorldStepSc.of_pre_locals_clock hsb).with_locals_clock mid.locals mid.clock
                exact withdrawalStep_trans hsb'
                  (ih mid.clock hmid_lt mid rfl (hmeta.trans hc) hW_mid hnt hfr)
              | «break» =>
                have hsb := hb sd hc hWd hnt_b (by rw [hbo]; exact Or.inr (Or.inr (Or.inl rfl)))
                rw [hbo] at hsb
                exact (WorldStepSc.of_pre_locals_clock hsb).with_locals_clock mid.locals mid.clock
              | timeOut => exact absurd rfl hnt
              | error => exact absurd hfr not_flowingOrResumes_error
              | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
              | returned v =>
                have hsb := hb sd hc hWd hnt_b
                  (by rw [hbo]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rfl⟩))))
                rw [hbo] at hsb
                exact (WorldStepSc.of_pre_locals_clock hsb).with_locals_clock mid.locals mid.clock
              | exception eid ev =>
                have hres_ex : Resumes (some (.exception eid ev)) := by
                  rcases hfr with h | h | h | hr <;> try simp at h
                  exact hr
                have hsb := hb sd hc hWd hnt_b (by rw [hbo]; exact Or.inr (Or.inr (Or.inr hres_ex)))
                rw [hbo] at hsb
                exact (WorldStepSc.of_pre_locals_clock hsb).with_locals_clock mid.locals mid.clock
      · exact absurd hfr not_flowingOrResumes_error
      · exact absurd hfr not_flowingOrResumes_error

/-- A reusable union entry condition for inner tables as well as ordinary roots. -/
def UnionNonValueEntry {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  WorldOK s ∧ ∀ S, TablesTyped s S → locN s "dst" ∈ S ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ locN s "dst") ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ locN s "dst") ∧
    globN s "bal_accounts" ≠ locN s "dst" ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ locN s "dst") ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ locN s "dst")

/-- The union frame depends on destination ownership rather than its root slot. -/
theorem wkSc_htab_union_into_nonValue :
    WorldKeepsSc UnionNonValueEntry (bufRegions []) ["heap_ptr"] stdKeep NoExtra
      (ofString "htab_union_into") := by
  obtain ⟨params, body, ret, hl, hb⟩ := htab_union_into_provenance_spec
  have hbody : body = sourceFnBody Guest.Software.guestFn_htab_union_into := by
    rw [HtabUnionInto.lookup_htab_union_into] at hl
    exact (Prod.mk.inj (Prod.mk.inj (Option.some.inj hl)).2).1.symm
  refine ⟨params, body, ret, hl, ?_⟩
  intro F s hc hP hex hnt hres
  rcases hres with ⟨v, hv⟩ | ⟨e, v, he, hne⟩
  · obtain ⟨hW, hnon⟩ := hP
    have harg : UnionArgWF s := by
      obtain ⟨S, hT, _⟩ := hW.2
      have ht := (hnon S hT).1
      exact ⟨hW.1, (hT.2.1 _ ht).1, fun i hi => ((hT.2.1 _ ht).2 i hi).1⟩
    have he := hb s hc harg hex hnt v hv
    have hbe := (M13.evaluateHOLFiniteState_guestInv_be s body hW.1.1).2
    exact unionExit_worldStepSc_nonValue hW hbe hnon he.toUnionExit
      (fun i hi => (he.2.2.2.2.2.1 i hi).2)
  · exact False.elim (htab_union_into_no_catchable_exn s hc e v hne (by rwa [← hbody]))

/-- Role separation also applies to shared inner-storage tables: sharing an
inner role never permits aliasing a value-owning outer table. -/
theorem unionNonValueEntry_of_role {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hW : WorldOK s) {role : String}
    (hr : (locN s "dst", role) ∈ worldRoleSlots s)
    (hb : role ≠ "bs+32") (hts : role ≠ "ts+32")
    (hba : role ≠ "bal_accounts") (hstor : role ≠ "bal.stor")
    (hws : role ≠ "ws+32") : UnionNonValueEntry s := by
  refine ⟨hW, ?_⟩
  intro S hT
  have hroles := hT.2.2.2.2.2.2.2.2.2.2.2
  have ht := (hroles.1 _ (List.mem_append_left _ hr)).1
  have hnz : locN s "dst" ≠ 0 := by
    have hf := (List.mem_filter.1 hr).2
    simpa using hf
  have hne : ∀ u label, (u, label) ∈ worldRoleSlots s → role ≠ label →
      u ≠ locN s "dst" := by
    intro u label hu hlabel
    exact (R16WkMarkAccountCreated.slot_ne_of_diff_nonshared_role hroles hr hu hlabel).symm
  refine ⟨ht, ?_, ?_, ?_, ?_, ?_⟩
  · intro hb0 heq
    apply hne _ "bs+32" ?_ hb heq
    apply R16WkMarkAccountCreated.mem_worldRoleSlots_recRole s "bs" 32 _ hb0
      (by rw [heq]; exact hnz)
    simp [recRoles, hb0]
  · intro ht0 heq
    apply hne _ "ts+32" ?_ hts heq
    apply R16WkMarkAccountCreated.mem_worldRoleSlots_recRole s "ts" 32 _ ht0
      (by rw [heq]; exact hnz)
    simp [recRoles, ht0]
  · intro heq
    apply hne _ "bal_accounts" ?_ hba heq
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [heq, hnz]⟩
    simp
  · intro ad had heq
    apply hne _ "bal.stor" ?_ hstor heq
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [heq, hnz]⟩
    apply List.mem_append.2; right
    exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
  · intro hw0 heq
    apply hne _ "ws+32" ?_ hws heq
    apply R16WkMarkAccountCreated.mem_worldRoleSlots_recRole s "ws" 32 _ hw0
      (by rw [heq]; exact hnz)
    simp [recRoles, hw0]

/-- An existing nonnull block inner table has the reusable union entry frame. -/
theorem unionNonValueEntry_bs_inner {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hW : WorldOK s) (hbs : globN s "bs" ≠ 0)
    (houter : memW s (globN s "bs" + 32) ≠ 0)
    (hinner : locN s "dst" ∈ htabValues s (memW s (globN s "bs" + 32)))
    (hnz : locN s "dst" ≠ 0) : UnionNonValueEntry s := by
  apply unionNonValueEntry_of_role hW (role := "bs.inner")
    ?_ (by decide) (by decide) (by decide) (by decide) (by decide)
  unfold worldRoleSlots
  apply List.mem_filter.2
  refine ⟨?_, by simpa using hnz⟩
  have hm : (locN s "dst", "bs.inner") ∈ nestRoles s "bs" "bs.inner" := by
    simp only [nestRoles, hbs, houter, ↓reduceIte]
    exact List.mem_map.2 ⟨locN s "dst", hinner, rfl⟩
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inr hm))

/-- Inner-storage unions cover both allocated and null values of the outer table. -/
theorem wkSc_htab_union_into_bs_inner :
    WorldKeepsSc (fun s => WorldOK s ∧ globN s "bs" ≠ 0 ∧
      memW s (globN s "bs" + 32) ≠ 0 ∧
      locN s "dst" ∈ htabValues s (memW s (globN s "bs" + 32)))
      (bufRegions []) ["heap_ptr"] stdKeep NoExtra (ofString "htab_union_into") := by
  obtain ⟨params, body, ret, hl, hb⟩ := wkSc_htab_union_into_nonValue
  obtain ⟨params0, body0, ret0, hl0, hb0⟩ := wkSc_htab_union_into_zero
  have heq := Option.some.inj (hl.symm.trans hl0)
  cases heq
  refine ⟨params, body, ret, hl, ?_⟩
  intro F s hc hP hex hnt hres
  by_cases hz : locN s "dst" = 0
  · exact hb0 s hc ⟨hP.1, hz⟩ hex hnt hres
  · exact hb s hc
      (unionNonValueEntry_bs_inner hP.1 hP.2.1 hP.2.2.1 hP.2.2.2 hz) hex hnt hres

/-- A successful outer-table lookup in the merge identifies an owned inner
storage table; the caller need not separately supply hash-table well-formedness. -/
theorem merge_outer_get_ret_in_values {F : Type}
    (s : PanSemStateFiniteExact 64 F) (tw kw : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hbs : globN s "bs" ≠ 0) (hnz : tw.toNat ≠ 0)
    (houter : tw.toNat = memW s (globN s "bs" + 32))
    (ht : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hk : s.locals.lookup (ofString "key") = some (.val (.word kw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_get)).1 =
      some (.returned v)) :
    ∃ f0 f1 : BitVec 64, v = .rStruct [.val (.word f0), .val (.word f1)] ∧
      (f0 ≠ 0 → f1.toNat ∈ htabValues s (memW s (globN s "bs" + 32))) := by
  obtain ⟨S, hT, _⟩ := hW.2
  have hmem : tw.toNat ∈ S := by
    have hr := hT.2.2.2.2.1 32 (by simp [bsTableSlots]) hbs
    rw [← houter] at hr
    exact hr.resolve_left hnz
  have htab := (hT.2.1 _ hmem).1
  obtain ⟨f0, f1, hv, hf⟩ := WkBal.htab_get_ret_in_values s tw kw hc ht hk htab v hret
  exact ⟨f0, f1, hv, by simpa only [houter] using hf⟩

/-- Transfer the merge loop's owned `binner` local to the union callee's
`dst` parameter, retaining the outer-table ownership witness. -/
theorem union_bs_inner_call_entry {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hbs : globN s "bs" ≠ 0) (houter : memW s (globN s "bs" + 32) ≠ 0)
    (hinner : locN s "binner" ∈ htabValues s (memW s (globN s "bs" + 32)))
    (src : ExpHOL 64) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "binner"), src] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_union_into") vs =
      some (body, callee, ret)) :
    WorldOK (callEntryStateHOLFinite s callee) ∧
      globN (callEntryStateHOLFinite s callee) "bs" ≠ 0 ∧
      memW (callEntryStateHOLFinite s callee)
        (globN (callEntryStateHOLFinite s callee) "bs" + 32) ≠ 0 ∧
      locN (callEntryStateHOLFinite s callee) "dst" ∈
        htabValues (callEntryStateHOLFinite s callee)
          (memW (callEntryStateHOLFinite s callee)
            (globN (callEntryStateHOLFinite s callee) "bs" + 32)) := by
  obtain ⟨dv, rest, rfl, hd⟩ := Wave8M19.Htab.evalList_cons_inv s _ _ ha
  obtain ⟨_, hp⟩ := Wave8M19.Htab.lookupCodeHOLFinite_param_at s.code.lookup
    (ofString "htab_union_into") [] (ofString "dst") .one
    [(ofString "src", .one)] _ _ (by simp; decide)
    (by rw [hc]; exact HtabUnionInto.lookup_htab_union_into)
    (vpre := []) (by simp) hl
  have hdst : callee.lookup (ofString "dst") = s.locals.lookup (ofString "binner") := by
    rw [hp]
    exact hd.symm
  have hn : locN (callEntryStateHOLFinite s callee) "dst" = locN s "binner" := by
    simp only [locN, callEntryStateHOLFinite, hdst]
  refine ⟨localsFree_worldOK s callee (s.clock - 1) hW, hbs, houter, ?_⟩
  rw [hn]
  exact hinner

/-- A hit in the block outer table supplies the inner-union entry condition,
including preservation across the read-only lookup and binding of `binner`. -/
theorem merge_outer_get_hit_union_entry {F : Type}
    (s : PanSemStateFiniteExact 64 F) (tw kw : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hbs : globN s "bs" ≠ 0) (hnz : tw.toNat ≠ 0)
    (houter : tw.toNat = memW s (globN s "bs" + 32))
    (ht : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hk : s.locals.lookup (ofString "key") = some (.val (.word kw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_get)).1 =
      some (.returned v)) :
    ∃ f0 f1 : BitVec 64, v = .rStruct [.val (.word f0), .val (.word f1)] ∧
      (f0 ≠ 0 → ∀ (L : HolFiniteMapExact MlS (ValueHOL 64))
        (src : ExpHOL 64) vs body callee ret,
        let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_get)).2
        let next := setVarHOLFinite (ofString "binner") (.val (.word f1))
          { post with locals := L }
        evalListHOLFinite next (h := fun a => Classical.propDecidable (next.memaddrs a))
          [.var .local (ofString "binner"), src] = some vs →
        lookupCodeHOLFinite next.code.lookup (ofString "htab_union_into") vs =
          some (body, callee, ret) →
        WorldOK (callEntryStateHOLFinite next callee) ∧
          globN (callEntryStateHOLFinite next callee) "bs" ≠ 0 ∧
          memW (callEntryStateHOLFinite next callee)
            (globN (callEntryStateHOLFinite next callee) "bs" + 32) ≠ 0 ∧
          locN (callEntryStateHOLFinite next callee) "dst" ∈
            htabValues (callEntryStateHOLFinite next callee)
              (memW (callEntryStateHOLFinite next callee)
                (globN (callEntryStateHOLFinite next callee) "bs" + 32))) := by
  obtain ⟨f0, f1, hv, hmem⟩ :=
    merge_outer_get_ret_in_values s tw kw hc hW hbs hnz houter ht hk v hret
  refine ⟨f0, f1, hv, ?_⟩
  intro hhit L src vs body callee ret post next ha hl
  have hframe := WkBal.locFrame_htab_get s hc
  have hn : next = { s with locals := L.update (ofString "binner", .val (.word f1)), clock := post.clock } := by
    dsimp only [next, setVarHOLFinite]
    rw [show post = { s with locals := post.locals, clock := post.clock } from hframe]
  apply union_bs_inner_call_entry next (by rw [hn]; exact hc)
    (by rw [hn]; exact localsFree_worldOK s _ _ hW)
    (by rw [hn]; exact hbs) (by rw [hn]; exact houter ▸ hnz) ?_ src vs body callee ret ha hl
  rw [hn]
  simpa [locN, HolFiniteMapExact.lookup_update, FUPDATE, htabValues, hdr, nodeF, memW, globN] using hmem hhit

/-- Execute the inner union with its ownership witness in the caller state. -/
theorem eval_call_union_bs_inner {F : Type} (s : PanSemStateFiniteExact 64 F)
    (src : ExpHOL 64) (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hbs : globN s "bs" ≠ 0) (houter : memW s (globN s "bs" + 32) ≠ 0)
    (hinner : locN s "binner" ∈ htabValues s (memW s (globN s "bs" + 32)))
    (hnt : (evaluateHOLFiniteState s (.call (some (none, none))
      (ofString "htab_union_into") [.var .local (ofString "binner"), src])).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s (.call (some (none, none))
      (ofString "htab_union_into") [.var .local (ofString "binner"), src])).1) :
    let out := evaluateHOLFiniteState s (.call (some (none, none))
      (ofString "htab_union_into") [.var .local (ofString "binner"), src])
    WorldStepSc (bufRegions []) ["heap_ptr"] stdKeep NoExtra s out.1 out.2 := by
  dsimp only
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases ha : @evalListHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "binner"), src] with _ | vs
  · simp [evalListHOLFinite, ha] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, ha] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_union_into") vs with
      _ | ⟨body, callee, ret⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        have hP := union_bs_inner_call_entry s hc hW hbs houter hinner src vs body callee ret
          (by rwa [evalListHOLFinite_eq_toExact]) hl
        rcases hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, post⟩
        simp only [hr] at hnt hfr ⊢
        have hnc : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 ≠
            some .timeOut := by rw [hr]; rintro rfl; simp at hnt
        have hs := FunSpec.at_lookup wkSc_htab_union_into_bs_inner s hc vs body callee ret hl hP hnc
        rw [hr] at hs
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | returned v =>
            dsimp only at hfr ⊢
            split
            · exact (hs (Or.inl ⟨v, rfl⟩)).from_entry
            · rename_i hbad; simp [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hres : Resumes (some (.exception eid ev)) := by
              rcases hfr with h | h | h | h <;> try simp at h
              exact h
            exact (hs hres).from_entry

/-- Insertion establishes ownership of its value whether it appends a new key
or replaces an existing key. Every resulting value is old or the inserted one. -/
theorem merge_set_values_membership {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {t value : Nat}
    (h : WkBal.HtabSetValuesPost s post t value) :
    value ∈ htabValues post t ∧
      ∀ x ∈ htabValues post t, x ∈ htabValues s t ∨ x = value := by
  rcases h with h | ⟨i, hi, h⟩
  · rw [h]
    constructor
    · simp
    · intro x hx
      simpa using hx
  · rw [h]
    constructor
    · exact List.mem_iff_getElem.2 ⟨i, by simp [hi], by simp⟩
    · intro x hx
      have hm := List.mem_or_eq_of_mem_set hx
      exact hm

/-- The outer insertion in the fresh-inner branch installs the new table
as a value and introduces no unrelated values. -/
theorem merge_outer_set_ret_values {F : Type}
    (s : PanSemStateFiniteExact 64 F) (tw kw iw : BitVec 64)
    (ht : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hk : s.locals.lookup (ofString "key") = some (.val (.word kw)))
    (hi : s.locals.lookup (ofString "value") = some (.val (.word iw)))
    (hA : ArenaReady s) (hT : HtabWF s tw.toNat)
    (halloc : ∀ i ∈ htabFootprint s tw.toNat, Allocated s i)
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_set)).1 =
      some (.returned v)) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_set)).2
    iw.toNat ∈ htabValues post tw.toNat ∧
      ∀ x ∈ htabValues post tw.toNat, x ∈ htabValues s tw.toNat ∨ x = iw.toNat := by
  have hv := WkBal.htab_set_body_values_exact s tw kw iw ht hk hi hA hT halloc v hret
  exact merge_set_values_membership hv.2

/-- After inserting a fresh inner table, its outer value membership supplies
the union call's ownership precondition. -/
theorem merge_inserted_inner_union_entry {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {t value : Nat}
    (hvalues : WkBal.HtabSetValuesPost s post t value)
    (hc : post.code = originalRuntimeCode) (hW : WorldOK post)
    (hbs : globN post "bs" ≠ 0)
    (ht : t = memW post (globN post "bs" + 32)) (hnz : t ≠ 0)
    (hi : locN post "binner" = value)
    (src : ExpHOL 64) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (ha : evalListHOLFinite post (h := fun a => Classical.propDecidable (post.memaddrs a))
      [.var .local (ofString "binner"), src] = some vs)
    (hl : lookupCodeHOLFinite post.code.lookup (ofString "htab_union_into") vs =
      some (body, callee, ret)) :
    WorldOK (callEntryStateHOLFinite post callee) ∧
      globN (callEntryStateHOLFinite post callee) "bs" ≠ 0 ∧
      memW (callEntryStateHOLFinite post callee)
        (globN (callEntryStateHOLFinite post callee) "bs" + 32) ≠ 0 ∧
      locN (callEntryStateHOLFinite post callee) "dst" ∈
        htabValues (callEntryStateHOLFinite post callee)
          (memW (callEntryStateHOLFinite post callee)
            (globN (callEntryStateHOLFinite post callee) "bs" + 32)) := by
  apply union_bs_inner_call_entry post hc hW hbs (ht ▸ hnz) ?_ src vs body callee ret ha hl
  rw [hi, ← ht]
  exact (merge_set_values_membership hvalues).1

/-- The merge lookup exposes its owned inner table directly to a continuation,
while restoring the caller's local binding on every resumable exit. -/
theorem merge_outer_get_continuation {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x : MlS)
    (tExp keyExp : ExpHOL 64) (cont : ProgHOL 64)
    (hW : WorldOK s) (hbs : globN s "bs" ≠ 0)
    (ht : ∀ tw : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) tExp =
        some (.val (.word tw)) → tw.toNat = memW s (globN s "bs" + 32))
    (hcont : ∀ (f0 f1 : BitVec 64) (ck : Nat),
      (f0 ≠ 0 → f1.toNat ∈ htabValues s (memW s (globN s "bs" + 32))) →
      let next := setVarHOLFinite x (.rStruct [.val (.word f0), .val (.word f1)])
        { s with clock := ck }
      (evaluateHOLFiniteState next cont).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState next cont).1 →
      WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra
        next (evaluateHOLFiniteState next cont).1 (evaluateHOLFiniteState next cont).2)
    (hnt : (evaluateHOLFiniteState s
      (.decCall x (.comb [.one, .one]) (ofString "htab_get") [tExp, keyExp] cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall x (.comb [.one, .one]) (ofString "htab_get") [tExp, keyExp] cont)).1) :
    WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra
      s (evaluateHOLFiniteState s
        (.decCall x (.comb [.one, .one]) (ofString "htab_get") [tExp, keyExp] cont)).1
        (evaluateHOLFiniteState s
        (.decCall x (.comb [.one, .one]) (ofString "htab_get") [tExp, keyExp] cont)).2 := by
  obtain ⟨tw, kw, f0, f1, ck, he, _, hnz, hm, hntc, hresc, hr, hp⟩ :=
    WkBal.decCall_htab_get_resumes s x tExp keyExp cont hW.1.1 hnt hres
  have heq := ht tw he
  have hn : tw.toNat ≠ 0 := by intro hz; apply hnz; exact BitVec.eq_of_toNat_eq hz
  obtain ⟨S, hT, _⟩ := hW.2
  have hmem : tw.toNat ∈ S := by
    have hs := hT.2.2.2.2.1 32 (by simp [bsTableSlots]) hbs
    rw [← heq] at hs
    exact hs.resolve_left hn
  have howned : f0 ≠ 0 → f1.toNat ∈ htabValues s (memW s (globN s "bs" + 32)) := by
    simpa only [heq] using hm (hT.2.1 _ hmem).1
  have hs := hcont f0 f1 ck howned hntc hresc
  rw [hr, hp]
  exact (WorldStepSc.of_pre_locals_clock (s := s) hs).with_locals_clock _ _

/-- Enumeration of the transaction outer table supplies owned inner values and
valid key slices to the storage-merge continuation. -/
theorem merge_outer_item_continuation {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x : MlS)
    (tExp ordExp : ExpHOL 64) (cont : ProgHOL 64)
    (hW : WorldOK s) (hts : globN s "ts" ≠ 0)
    (ht : ∀ tw : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) tExp =
        some (.val (.word tw)) → tw.toNat = memW s (globN s "ts" + 32))
    (hcont : ∀ (tw f0 f1 f2 : BitVec 64) (ck : Nat),
      tw.toNat = memW s (globN s "ts" + 32) →
      (f0 ≠ 0 →
        Inside (f1.toNat, hdr s tw.toNat 1) (hdr s tw.toNat 4)
          (hdr s tw.toNat 4 + (hdr s tw.toNat 10 + 1) * hdr s tw.toNat 1) ∧
        Inside (f1.toNat, hdr s tw.toNat 0) (hdr s tw.toNat 4)
          (hdr s tw.toNat 4 + (hdr s tw.toNat 10 + 1) * hdr s tw.toNat 1) ∧
        f2.toNat ∈ htabValues s tw.toNat) →
      let next := setVarHOLFinite x (.rStruct [.val (.word f0), .val (.word f1), .val (.word f2)])
        { s with clock := ck }
      (evaluateHOLFiniteState next cont).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState next cont).1 →
      WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra
        next (evaluateHOLFiniteState next cont).1 (evaluateHOLFiniteState next cont).2)
    (hnt : (evaluateHOLFiniteState s
      (.decCall x (.comb [.one, .one, .one]) (ofString "htab_item") [tExp, ordExp] cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall x (.comb [.one, .one, .one]) (ofString "htab_item") [tExp, ordExp] cont)).1) :
    WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra
      s (evaluateHOLFiniteState s
        (.decCall x (.comb [.one, .one, .one]) (ofString "htab_item") [tExp, ordExp] cont)).1
        (evaluateHOLFiniteState s
        (.decCall x (.comb [.one, .one, .one]) (ofString "htab_item") [tExp, ordExp] cont)).2 := by
  obtain ⟨tw, ordw, f0, f1, f2, ck, he, _, hnz, hm, hntc, hresc, hr, hp⟩ :=
    decCall_htab_item_resumes s x tExp ordExp cont hW.1.1 hnt hres
  have heq := ht tw he
  have hn : tw.toNat ≠ 0 := by intro hz; apply hnz; exact BitVec.eq_of_toNat_eq hz
  obtain ⟨S, hT, _⟩ := hW.2
  have hmem : tw.toNat ∈ S := by
    have hs := hT.2.2.2.2.2.1 32 (by simp [tsTableSlots]) hts
    rw [← heq] at hs
    exact hs.resolve_left hn
  have hs := hcont tw f0 f1 f2 ck heq (hm (hT.2.1 _ hmem).1) hntc hresc
  rw [hr, hp]
  exact (WorldStepSc.of_pre_locals_clock (s := s) hs).with_locals_clock _ _

/-- A read-only call carries a return-value fact into a continuation that may
fall through, break, continue, or resume. Catchable callee exceptions retain
the same world frame without running the continuation. -/
theorem eval_decCall_readOnly_with_return {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x fname : MlS)
    (sh : ShapeHOL) (args : List (ExpHOL 64)) (cont : ProgHOL 64)
    (Q : ValueHOL 64 → Prop)
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hf : ReadOnlyFn fname)
    (hq : ∀ vs body callee ret v post,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vs →
      lookupCodeHOLFinite s.code.lookup fname vs = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) → Q v)
    (hcont : ∀ v ck, Q v →
      let next := setVarHOLFinite x v { s with clock := ck }
      (evaluateHOLFiniteState next cont).1 ≠ some .timeOut →
      FlowingOrResumes (evaluateHOLFiniteState next cont).1 →
      WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra
        next (evaluateHOLFiniteState next cont).1 (evaluateHOLFiniteState next cont).2)
    (hnt : (evaluateHOLFiniteState s (.decCall x sh fname args cont)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s (.decCall x sh fname args cont)).1) :
    WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra
      s (evaluateHOLFiniteState s (.decCall x sh fname args cont)).1
        (evaluateHOLFiniteState s (.decCall x sh fname args cont)).2 := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp only [ha] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [ha] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body, callee, ret⟩
    · simp only [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        rcases hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, post⟩
        simp only [hr] at hnt hfr ⊢
        have hnc : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 ≠ some .timeOut := by
          rw [hr]; rintro rfl; exact hnt rfl
        have hframe := FunSpec.at_lookup hf s hc vs body callee ret hl
          (guestInv_callEntry s callee hW.1.1) hnc
        rw [hr] at hframe
        cases r with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some r =>
          cases r with
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | timeOut => exact absurd rfl hnt
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | returned v =>
            dsimp only at hnt hfr ⊢
            split at hnt
            · rename_i hshape
              rw [if_pos hshape] at hfr ⊢
              have hp := hframe (Or.inl ⟨v, rfl⟩)
              dsimp only at hp
              have hp' : { post with locals := s.locals } = { s with clock := post.clock } := by
                rw [hp]; rfl
              rw [hp'] at hnt hfr ⊢
              have hs := hcont v post.clock (hq vs body callee ret v post ha hl hr) hnt hfr
              exact (WorldStepSc.of_pre_locals_clock (s := s) hs).with_locals_clock _ _
            · rename_i hshape
              rw [if_neg hshape] at hfr
              exact absurd hfr not_flowingOrResumes_error
          | exception e v =>
            dsimp only at hfr ⊢
            have hres : Resumes (some (.exception e v)) := by
              rcases hfr with h | h | h | h <;> try simp at h
              exact h
            have hp := hframe hres
            dsimp only at hp
            rw [hp]
            exact (WorldStepSc.refl s none hW.1).with_locals_clock _ _

/-- Two word parameters are recovered independently of the return shape. -/
theorem lookup_two_word_result {fname p1 p2 : MlS} {body found : ProgHOL 64}
    {rs ret : ShapeHOL} {vals : List (ValueHOL 64)}
    {L : HolFiniteMapExact MlS (ValueHOL 64)} (hne : p1 ≠ p2)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one)], body, rs))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (found, L, ret)) :
    found = body ∧ ret = rs ∧ ∃ w1 w2 : BitVec 64,
      vals = [.val (.word w1), .val (.word w2)] ∧
      L.lookup p1 = some (.val (.word w1)) ∧ L.lookup p2 = some (.val (.word w2)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup fname vals found L ret hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
  · simp at hx
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, rfl, hL, rfl⟩ := hx
    refine ⟨rfl, rfl, w1, w2, rfl, ?_, ?_⟩
    · rw [← hL]; simp [hne]
    · rw [← hL]; simp
  · simp at hx

/-- Block outer lookup ownership is available on normal loop fall-through as
well as resumable exits. -/
theorem merge_outer_get_flow_continuation {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x : MlS)
    (tExp keyExp : ExpHOL 64) (cont : ProgHOL 64)
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hbs : globN s "bs" ≠ 0)
    (ht : ∀ tw : BitVec 64, evalAt s tExp = some (.val (.word tw)) →
      tw.toNat = memW s (globN s "bs" + 32))
    (hcont : ∀ (f0 f1 : BitVec 64) (ck : Nat),
      (f0 ≠ 0 → f1.toNat ∈ htabValues s (memW s (globN s "bs" + 32))) →
      let next := setVarHOLFinite x (.rStruct [.val (.word f0), .val (.word f1)])
        { s with clock := ck }
      (evaluateHOLFiniteState next cont).1 ≠ some .timeOut →
      FlowingOrResumes (evaluateHOLFiniteState next cont).1 →
      WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra
        next (evaluateHOLFiniteState next cont).1 (evaluateHOLFiniteState next cont).2)
    (hnt : (evaluateHOLFiniteState s
      (.decCall x (.comb [.one, .one]) (ofString "htab_get") [tExp, keyExp] cont)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.decCall x (.comb [.one, .one]) (ofString "htab_get") [tExp, keyExp] cont)).1) :
    WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra
      s (evaluateHOLFiniteState s
        (.decCall x (.comb [.one, .one]) (ofString "htab_get") [tExp, keyExp] cont)).1
        (evaluateHOLFiniteState s
        (.decCall x (.comb [.one, .one]) (ofString "htab_get") [tExp, keyExp] cont)).2 := by
  apply eval_decCall_readOnly_with_return s x _ _ _ cont
    (fun v => ∃ f0 f1 : BitVec 64, v = .rStruct [.val (.word f0), .val (.word f1)] ∧
      (f0 ≠ 0 → f1.toNat ∈ htabValues s (memW s (globN s "bs" + 32))))
    hc hW InitECandidate.Solver.Wave8Contracts.M15.ro_htab_get ?_ ?_ hnt hfr
  · intro vs body callee ret v post ha hl hr
    rw [hc] at hl
    obtain ⟨rfl, rfl, tw, kw, rfl, htw, hkw⟩ :=
      lookup_two_word_result (by decide) WkBal.lookup_htab_get hl
    have he : evalAt s tExp = some (.val (.word tw)) := by
      obtain ⟨v1, rest, hh, hv⟩ := Wave8M19.Htab.evalList_cons_inv s _ _ ha
      cases hh
      exact hv
    have heq := ht tw he
    have hent := guestInv_callEntry s callee hW.1.1
    have hret := congrArg Prod.fst hr
    have hnz := WkBal.htab_get_t_nonzero (callEntryStateHOLFinite s callee) tw kw hent htw hkw v hret
    have hWc : WorldOK (callEntryStateHOLFinite s callee) :=
      localsFree_worldOK s callee (s.clock - 1) hW
    exact merge_outer_get_ret_in_values (callEntryStateHOLFinite s callee) tw kw hc hWc hbs
      (by intro hz; apply hnz; exact BitVec.eq_of_toNat_eq hz) heq htw hkw v hret
  · intro v ck hv
    obtain ⟨f0, f1, rfl, hm⟩ := hv
    exact hcont f0 f1 ck hm

/-- Transaction outer enumeration supplies key bounds and inner ownership on
every flowing or resumable continuation outcome. -/
theorem merge_outer_item_flow_continuation {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x : MlS)
    (tExp ordExp : ExpHOL 64) (cont : ProgHOL 64)
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hts : globN s "ts" ≠ 0)
    (ht : ∀ tw : BitVec 64, evalAt s tExp = some (.val (.word tw)) →
      tw.toNat = memW s (globN s "ts" + 32))
    (hcont : ∀ (tw f0 f1 f2 : BitVec 64) (ck : Nat),
      tw.toNat = memW s (globN s "ts" + 32) →
      (f0 ≠ 0 →
        Inside (f1.toNat, hdr s tw.toNat 1) (hdr s tw.toNat 4)
          (hdr s tw.toNat 4 + (hdr s tw.toNat 10 + 1) * hdr s tw.toNat 1) ∧
        Inside (f1.toNat, hdr s tw.toNat 0) (hdr s tw.toNat 4)
          (hdr s tw.toNat 4 + (hdr s tw.toNat 10 + 1) * hdr s tw.toNat 1) ∧
        f2.toNat ∈ htabValues s tw.toNat) →
      let next := setVarHOLFinite x (.rStruct [.val (.word f0), .val (.word f1), .val (.word f2)])
        { s with clock := ck }
      (evaluateHOLFiniteState next cont).1 ≠ some .timeOut →
      FlowingOrResumes (evaluateHOLFiniteState next cont).1 →
      WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra
        next (evaluateHOLFiniteState next cont).1 (evaluateHOLFiniteState next cont).2)
    (hnt : (evaluateHOLFiniteState s
      (.decCall x (.comb [.one, .one, .one]) (ofString "htab_item") [tExp, ordExp] cont)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.decCall x (.comb [.one, .one, .one]) (ofString "htab_item") [tExp, ordExp] cont)).1) :
    WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra
      s (evaluateHOLFiniteState s
        (.decCall x (.comb [.one, .one, .one]) (ofString "htab_item") [tExp, ordExp] cont)).1
        (evaluateHOLFiniteState s
        (.decCall x (.comb [.one, .one, .one]) (ofString "htab_item") [tExp, ordExp] cont)).2 := by
  apply eval_decCall_readOnly_with_return s x _ _ _ cont
    (fun v => ∃ tw f0 f1 f2 : BitVec 64,
      tw.toNat = memW s (globN s "ts" + 32) ∧
      v = .rStruct [.val (.word f0), .val (.word f1), .val (.word f2)] ∧
      (f0 ≠ 0 →
        Inside (f1.toNat, hdr s tw.toNat 1) (hdr s tw.toNat 4)
          (hdr s tw.toNat 4 + (hdr s tw.toNat 10 + 1) * hdr s tw.toNat 1) ∧
        Inside (f1.toNat, hdr s tw.toNat 0) (hdr s tw.toNat 4)
          (hdr s tw.toNat 4 + (hdr s tw.toNat 10 + 1) * hdr s tw.toNat 1) ∧
        f2.toNat ∈ htabValues s tw.toNat))
    hc hW InitECandidate.Solver.Wave8Contracts.M15.ro_htab_item ?_ ?_ hnt hfr
  · intro vs body callee ret v post ha hl hr
    rw [hc] at hl
    obtain ⟨rfl, rfl, tw, ow, rfl, htw, how⟩ :=
      lookup_two_word_result (by decide) lookup_htab_item_bal hl
    have he : evalAt s tExp = some (.val (.word tw)) := by
      obtain ⟨v1, rest, hh, hv⟩ := Wave8M19.Htab.evalList_cons_inv s _ _ ha
      cases hh
      exact hv
    have heq := ht tw he
    have hret := congrArg Prod.fst hr
    have hnz := htab_item_t_nonzero (callEntryStateHOLFinite s callee) tw ow
      (guestInv_callEntry s callee hW.1.1) htw how v hret
    obtain ⟨S, hT, _⟩ := hW.2
    have hmem : tw.toNat ∈ S := by
      have hm := hT.2.2.2.2.2.1 32 (by simp [tsTableSlots]) hts
      rw [← heq] at hm
      exact hm.resolve_left (by intro hz; apply hnz; exact BitVec.eq_of_toNat_eq hz)
    have hWF : HtabWF (callEntryStateHOLFinite s callee) tw.toNat :=
      (WkBal.htabWF_with_locals s callee (s.clock - 1) tw.toNat).2 (hT.2.1 _ hmem).1
    obtain ⟨f0, f1, f2, hv, hm⟩ :=
      htab_item_ret_spec (callEntryStateHOLFinite s callee) tw ow htw how hWF v hret
    exact ⟨tw, f0, f1, f2, heq, hv, hm⟩
  · intro v ck hv
    obtain ⟨tw, f0, f1, f2, heq, rfl, hm⟩ := hv
    exact hcont tw f0 f1 f2 ck heq hm

/-- Assigning an owned inner table and immediately unioning into it preserves
the standard world frame. Invalid local assignments cannot flow. -/
theorem eval_merge_hit_assign_union {F : Type}
    (s : PanSemStateFiniteExact 64 F) (inner src : ExpHOL 64)
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hbs : globN s "bs" ≠ 0) (hout : memW s (globN s "bs" + 32) ≠ 0)
    (hi : ∀ v, evalAt s inner = some v → ∃ iw : BitVec 64,
      v = .val (.word iw) ∧ iw.toNat ∈ htabValues s (memW s (globN s "bs" + 32)))
    (hnt : (evaluateHOLFiniteState s (.seq (.assign .local (ofString "binner") inner)
      (.call (some (none, none)) (ofString "htab_union_into")
        [.var .local (ofString "binner"), src]))).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.seq (.assign .local (ofString "binner") inner)
      (.call (some (none, none)) (ofString "htab_union_into")
        [.var .local (ofString "binner"), src]))).1) :
    let out := evaluateHOLFiniteState s
      (.seq (.assign .local (ofString "binner") inner)
      (.call (some (none, none)) (ofString "htab_union_into")
        [.var .local (ofString "binner"), src]))
    WorldStepSc (bufRegions []) ["heap_ptr"] stdKeep NoExtra s out.1 out.2 := by
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hnt hfr ⊢
  rcases he : evalAt s inner with _ | v
  · simp only [evalAt] at he
    simp [he] at hfr
    exact absurd hfr not_flowingOrResumes_error
  · obtain ⟨iw, rfl, hm⟩ := hi v he
    simp only [evalAt] at he
    simp only [he] at hnt hfr ⊢
    by_cases hok : isValidValueHOLFinite s .local (ofString "binner") (.val (.word iw)) = true
    swap
    · simp only [hok] at hfr
      exact absurd hfr not_flowingOrResumes_error
    simp only [hok, ↓reduceIte, setKvarHOLFinite] at hnt hfr ⊢
    have hWn : WorldOK (setVarHOLFinite (ofString "binner") (.val (.word iw)) s) :=
      localsFree_worldOK s _ _ hW
    have hs := eval_call_union_bs_inner
      (setVarHOLFinite (ofString "binner") (.val (.word iw)) s) src hc hWn hbs hout
      (by simpa [locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        htabValues, hdr, nodeF, memW, globN] using hm) hnt hfr
    exact WorldStepSc.of_pre_locals_clock hs

/-- The actual merge hit branch selects the owned lookup value and executes
the inner union under the withdrawal mask. -/
theorem eval_merge_hit_branch {F : Type}
    (s : PanSemStateFiniteExact 64 F) (f0 f1 : BitVec 64) (miss : ProgHOL 64)
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hbs : globN s "bs" ≠ 0) (hout : memW s (globN s "bs" + 32) ≠ 0)
    (hm : s.locals.lookup (ofString "m") = some (.rStruct [.val (.word f0), .val (.word f1)]))
    (hflag : f0 ≠ 0)
    (hi : f1.toNat ∈ htabValues s (memW s (globN s "bs" + 32)))
    (hnt : (evaluateHOLFiniteState s
      (.seq (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
        miss (.assign .local (ofString "binner") (.rfield 1 (.var .local (ofString "m")))))
        (.call (some (none, none)) (ofString "htab_union_into")
          [.var .local (ofString "binner"), .rfield 2 (.var .local (ofString "s"))]))).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.seq (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
        miss (.assign .local (ofString "binner") (.rfield 1 (.var .local (ofString "m")))))
        (.call (some (none, none)) (ofString "htab_union_into")
          [.var .local (ofString "binner"), .rfield 2 (.var .local (ofString "s"))]))).1) :
    let out := evaluateHOLFiniteState s
      (.seq (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
        miss (.assign .local (ofString "binner") (.rfield 1 (.var .local (ofString "m")))))
        (.call (some (none, none)) (ofString "htab_union_into")
          [.var .local (ofString "binner"), .rfield 2 (.var .local (ofString "s"))]))
    WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra s out.1 out.2 := by
  have hcond : evalAt s (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64)) =
      some (.val (.word 0#64)) := by
    simpa [evalAt, evalHOLExact, hm, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] using hflag
  have hite : evaluateHOLFiniteState s
      (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
        miss (.assign .local (ofString "binner") (.rfield 1 (.var .local (ofString "m"))))) =
      evaluateHOLFiniteState s (.assign .local (ofString "binner") (.rfield 1 (.var .local (ofString "m")))) := by
    rw [evaluateHOLFiniteState_ite]
    dsimp only [evalAt] at hcond
    rw [hcond]
    simp
  have heq : evaluateHOLFiniteState s
      (.seq (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
        miss (.assign .local (ofString "binner") (.rfield 1 (.var .local (ofString "m")))))
        (.call (some (none, none)) (ofString "htab_union_into")
          [.var .local (ofString "binner"), .rfield 2 (.var .local (ofString "s"))])) =
      evaluateHOLFiniteState s
        (.seq (.assign .local (ofString "binner") (.rfield 1 (.var .local (ofString "m"))))
        (.call (some (none, none)) (ofString "htab_union_into")
          [.var .local (ofString "binner"), .rfield 2 (.var .local (ofString "s"))])) := by
    simp only [evaluateHOLFiniteState_seq_line780, hite]
  dsimp only
  rw [heq] at hnt hfr ⊢
  have hs := eval_merge_hit_assign_union s (.rfield 1 (.var .local (ofString "m")))
    (.rfield 2 (.var .local (ofString "s"))) hc hW hbs hout (by
      intro v hv
      have he : evalAt s (.rfield 1 (.var .local (ofString "m"))) = some (.val (.word f1)) := by
        simp [evalAt, evalHOLExact, hm]
      rw [he] at hv
      exact ⟨f1, (Option.some.inj hv).symm, hi⟩) hnt hfr
  apply worldStepSc_mono_mask (B1 := []) (B2 := withdrawalBufs)
    (gw1 := ["heap_ptr"]) (gw2 := withdrawalGlobals) (by simp) (by decide) _ hs
  intro rec hrec k hk
  simp only [withdrawalKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
  rcases hrec with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [stdKeep], hk⟩
  · exact ⟨_, by simp [stdKeep], hk⟩
  · cases hk
  · exact ⟨_, by simp [stdKeep], hk⟩

/-- A local allocation call can only fall through on a flowing or resumable
outcome: its allocator has no catchable exception. -/
theorem merge_new_call_flow_none {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x : MlS) (kw capw : BitVec 64)
    (hc : s.code = originalRuntimeCode)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (some (.local, x), none)) (ofString "htab_new")
        [.const kw, .const capw])).1) :
    (evaluateHOLFiniteState s
      (.call (some (some (.local, x), none)) (ofString "htab_new")
        [.const kw, .const capw])).1 = none := by
  rw [evaluateHOLFiniteState_call] at hfr ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const kw, .const capw] = some [.val (.word kw), .val (.word capw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hl := pan_two_word_lookup s.code.lookup (ofString "htab_new")
    (ofString "key_len") (ofString "cap") (sourceFnBody Guest.Software.guestFn_htab_new) kw capw
    (by decide) (by rw [hc]; exact R10Shards.SoloHtabNew.lookup_htab_new)
  rw [ha] at hfr ⊢
  dsimp only at hfr ⊢
  rw [hl] at hfr ⊢
  dsimp only at hfr ⊢
  split at hfr
  · simp [FlowingOrResumes, Resumes] at hfr
  · rename_i hnz
    rw [if_neg hnz]
    rcases hr : evaluateHOLFiniteState _ _ with ⟨r, post⟩
    rw [hr] at hfr
    cases r with
    | none => exact absurd hfr not_flowingOrResumes_error
    | some r =>
      cases r with
      | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
      | timeOut => simp [FlowingOrResumes, Resumes] at hfr
      | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
      | returned v =>
        dsimp only at hfr ⊢
        split at hfr
        · rename_i hshape
          rw [if_pos hshape]
          split at hfr
          · rename_i hvalid
            rw [if_pos hvalid]
          · exact absurd hfr not_flowingOrResumes_error
        · exact absurd hfr not_flowingOrResumes_error
      | exception e v =>
        have he : Resumes (some (.exception e v)) := by
          rcases hfr with h | h | h | h <;> try simp at h
          exact h
        obtain ⟨_, hv⟩ | ⟨e', v', hv, hne⟩ := he
        · cases hv
        · cases hv
          exact False.elim (WkBal.htab_new_no_catchable_exn (callEntryStateHOLFinite s _) hc e v hne
            (congrArg Prod.fst hr))

/-- Recover the fresh table and its entire allocation frame even when the
surrounding storage-loop iteration falls through rather than returns. -/
theorem merge_new_call_flow_props {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x : MlS) (kw capw : BitVec 64)
    (hAR : ArenaReady s) (hkl : kw.toNat ∈ htabKeyLens)
    (hcl : capw.toNat ≤ htabCapMax)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (some (.local, x), none)) (ofString "htab_new")
        [.const kw, .const capw])).1) :
    let post := (evaluateHOLFiniteState s
      (.call (some (some (.local, x), none)) (ofString "htab_new")
        [.const kw, .const capw])).2
    ∃ tw : BitVec 64,
      globN s "heap_ptr" ≤ tw.toNat ∧
      tw.toNat + 88 ≤ globN post "heap_ptr" ∧
      ArenaReady post ∧ post.be = s.be ∧
      globN post "scratch_ptr" = globN s "scratch_ptr" ∧
      globN post "frame_mem_ptr" = globN s "frame_mem_ptr" ∧
      HtabWF post tw.toNat ∧ hdr post tw.toNat 3 = 0 ∧
      hdr post tw.toNat 0 = kw.toNat ∧
      (∀ i ∈ htabFootprint post tw.toNat,
        Allocated post i ∧ Inside i (globN s "heap_ptr") (globN post "heap_ptr")) ∧
      FrameOutside s post [(globN s "scratch_ptr", 0)]
        (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = post.globals.lookup k) := by
  dsimp only
  let p : ProgHOL 64 := .call (some (some (.local, x), none)) (ofString "htab_new")
    [.const kw, .const capw]
  have hn : (evaluateHOLFiniteState s p).1 = none :=
    merge_new_call_flow_none s x kw capw hAR.1.code hfr
  have he : evaluateHOLFiniteState s (.seq p (.return (.const 0#64))) =
      (some (.returned (.val (.word 0#64))), (evaluateHOLFiniteState s p).2.emptyLocalsHOLFinite) := by
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hp : evaluateHOLFiniteState s p with ⟨r, post⟩
    rw [hp] at hn
    dsimp only at hn
    subst r
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
  have hnt : (evaluateHOLFiniteState s (.seq p (.return (.const 0#64)))).1 ≠ some .timeOut := by
    rw [he]; simp
  have hr : Resumes (evaluateHOLFiniteState s (.seq p (.return (.const 0#64)))).1 := by
    rw [he]; exact Or.inl ⟨_, rfl⟩
  obtain ⟨tw, mid, hlo, hhi, hAm, hbe, hsp, hfm, hwf, hcnt, hkey, hfp, hframe,
      hlocal, _, _, _, hseq⟩ :=
    WkBal.seq_call_htab_new_resumes s .local x kw capw (.return (.const 0#64))
      hAR hkl hcl (by intro h; cases h) hnt hr
  have hm : (evaluateHOLFiniteState s p).2.emptyLocalsHOLFinite = mid.emptyLocalsHOLFinite := by
    have h := congrArg Prod.snd hseq
    rw [he] at h
    simpa [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact] using h
  have hm' : (evaluateHOLFiniteState s p).2 =
      { mid with locals := (evaluateHOLFiniteState s p).2.locals } :=
    congrArg (fun t => { t with locals := (evaluateHOLFiniteState s p).2.locals }) hm
  change ∃ tw, _
  rw [show (evaluateHOLFiniteState s
    (.call (some (some (.local, x), none)) (ofString "htab_new")
      [.const kw, .const capw])).2 = { mid with locals := (evaluateHOLFiniteState s p).2.locals } from hm']
  exact ⟨tw, hlo, hhi, (arenaReady_with_locals mid _ _).2 hAm, hbe, hsp, hfm,
    (WkBal.htabWF_with_locals mid _ _ _).2 hwf, hcnt, hkey, hfp, hframe, (hlocal rfl).2.2⟩

/-- Fresh inner allocation preserves the world before the table is installed
in the block outer table. -/
theorem merge_new_call_worldStep {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x : MlS) (kw capw : BitVec 64)
    (hW : WorldOK s) (hkl : kw.toNat ∈ htabKeyLens)
    (hcl : capw.toNat ≤ htabCapMax)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (some (.local, x), none)) (ofString "htab_new")
        [.const kw, .const capw])).1) :
    let out := evaluateHOLFiniteState s
      (.call (some (some (.local, x), none)) (ofString "htab_new")
        [.const kw, .const capw])
    WorldStepSc (bufRegions []) ["heap_ptr"] stdKeep NoExtra s out.1 out.2 := by
  dsimp only
  let p : ProgHOL 64 := .call (some (some (.local, x), none)) (ofString "htab_new")
    [.const kw, .const capw]
  let post := (evaluateHOLFiniteState s p).2
  obtain ⟨tw, hlo, hhi, hA, hbe, hsp, hfm, _, _, _, _, hframe, hgl⟩ :=
    merge_new_call_flow_props s x kw capw hW.1 hkl hcl hfr
  change ArenaReady post at hA
  change post.be = s.be at hbe
  change globN post "scratch_ptr" = globN s "scratch_ptr" at hsp
  change globN post "frame_mem_ptr" = globN s "frame_mem_ptr" at hfm
  change tw.toNat + 88 ≤ globN post "heap_ptr" at hhi
  have hhp : globN s "heap_ptr" ≤ globN post "heap_ptr" := by omega
  have hdom : ∀ a : BitVec 64, post.memory a ≠ s.memory a → s.memaddrs a := by
    intro a hn
    by_contra ha
    exact hn (evaluateHOLFiniteState_mem_out_dom s p ha)
  have hframe' : ∀ a : BitVec 64,
      ¬ CellHits a.toNat (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") →
      post.memory a = s.memory a := by
    intro a ha
    by_cases heq : post.memory a = s.memory a
    · exact heq
    apply hframe a ?_ ha
    intro i hi hh
    simp only [List.mem_singleton] at hi
    subst i
    dsimp [CellHits] at hh
    have ha8 : a.toNat % 8 = 0 := by
      have hd := hdom a heq
      rw [hW.1.1.memaddrs, ordinaryDomain_iff] at hd
      exact hd.1
    have hs8 : globN s "scratch_ptr" % 8 = 0 := hW.1.2.2.2.2.2.2.2.2.1
    omega
  apply heapByteEff_to_worldStepSc (by simp) hW
  refine ⟨hA, hA.1.memaddrs.trans hW.1.1.memaddrs.symm, hhp, hfm,
    le_of_eq hsp, hbe, ?_, hdom, ?_, ?_⟩
  · intro k hk
    exact hgl k (by simpa using hk)
  · intro a hn
    have hh : CellHits a.toNat
        (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
      by_contra ha
      exact hn (hframe' a ha)
    have ha := hdom a hn
    rw [hW.1.1.memaddrs, ordinaryDomain_iff] at ha
    have hs8 : globN s "heap_ptr" % 8 = 0 := hW.1.2.2.2.2.2.2.1
    have hp8 := hA.2.2.2.2.2.2.1
    have hpmax := hA.2.2.1
    obtain ⟨h1, h2⟩ := hh
    exact Or.inr (Or.inr ⟨by dsimp [CellHitsPos, heapFree]; omega,
      by dsimp [heapFree]; omega, by dsimp [heapFree]; omega⟩)
  · intro b hb hn
    have hm : post.memory (panByteAlignHOL (BitVec.ofNat 64 b)) ≠
        s.memory (panByteAlignHOL (BitVec.ofNat 64 b)) := by
      intro hm
      apply hn
      unfold memB
      rw [hm, hbe]
    have hh : CellHits (panByteAlignHOL (BitVec.ofNat 64 b)).toNat
        (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
      by_contra ha
      exact hm (hframe' _ ha)
    have hal := panByteAlign_toNat64 (BitVec.ofNat 64 b)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb] at hal
    have hs8 : globN s "heap_ptr" % 8 = 0 := hW.1.2.2.2.2.2.2.1
    have hp8 := hA.2.2.2.2.2.2.1
    have hpmax := hA.2.2.1
    obtain ⟨h1, h2⟩ := hh
    exact Or.inr (Or.inr ⟨by dsimp [heapFree]; omega, by dsimp [heapFree]; omega⟩)

/-- The allocated inner table can be added to the ownership set before the
outer insertion; existing role slots and footprints are preserved. -/
theorem merge_new_call_owned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x : MlS) (kw capw : BitVec 64)
    (S Nd : List Nat) (hAR : ArenaReady s) (hWT : WorldTypedWith s S Nd)
    (hkl : kw.toNat ∈ htabKeyLens) (hcl : capw.toNat ≤ htabCapMax)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (some (.local, x), none)) (ofString "htab_new")
        [.const kw, .const capw])).1) :
    let post := (evaluateHOLFiniteState s
      (.call (some (some (.local, x), none)) (ofString "htab_new")
        [.const kw, .const capw])).2
    ∃ t, t ∉ S ∧ t ≠ 0 ∧
      hdr post t 0 = kw.toNat ∧ hdr post t 3 = 0 ∧
      (∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ t) ∧
      WorldTypedWith post (S ++ [t]) Nd ∧
      OwnedGrows s post (worldOwned s S Nd) (worldOwned post (S ++ [t]) Nd) ∧
      worldRoleSlots post = worldRoleSlots s ∧
      journalRoleSlots post = journalRoleSlots s ∧
      fixedObjects post = fixedObjects s ∧
      nodeExtents post Nd = nodeExtents s Nd ∧
      (∀ u ∈ S, hdr post u 0 = hdr s u 0) ∧
      (∀ u ∈ S, htabFootprint post u = htabFootprint s u) := by
  dsimp only
  let p : ProgHOL 64 := .call (some (some (.local, x), none)) (ofString "htab_new")
    [.const kw, .const capw]
  let post := (evaluateHOLFiniteState s p).2
  obtain ⟨tw, hlo, hhi, hA, hbe, hsp, _, hwf, hcnt, hkey, hfp, hframe, hgl⟩ :=
    merge_new_call_flow_props s x kw capw hAR hkl hcl hfr
  change tw.toNat + 88 ≤ globN post "heap_ptr" at hhi
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by omega
  have hd : ∀ a : BitVec 64, ¬ ordinaryDomain a → post.memory a = s.memory a := by
    intro a ha
    apply evaluateHOLFiniteState_mem_out_dom s p
    rwa [hAR.1.memaddrs]
  obtain ⟨hnS, hn0, hroles, hWT', hrest⟩ :=
    worldTypedWith_htab_new_sysTx hAR hA hbe hh hsp hwf hkey hfp hd hframe hgl hWT
  exact ⟨tw.toNat, hnS, hn0, hkey, hcnt, hroles, hWT', hrest⟩

/-- A fresh inner allocation composes with a withdrawal-framed continuation
on all flowing and resumable outcomes. -/
theorem progWithdrawalStep_new_then (x : MlS) (kw capw : BitVec 64)
    (hkl : kw.toNat ∈ htabKeyLens) (hcl : capw.toNat ≤ htabCapMax)
    {cont : ProgHOL 64} (hcont : ProgWithdrawalStep cont) :
    ProgWithdrawalStep (.seq
      (.call (some (some (.local, x), none)) (ofString "htab_new")
        [.const kw, .const capw]) cont) := by
  have hnew : ProgWithdrawalStep
      (.call (some (some (.local, x), none)) (ofString "htab_new")
        [.const kw, .const capw]) := by
    apply progWithdrawalStep_of_progWStep (B := []) (gw := ["heap_ptr"])
      (by simp) (by simp [withdrawalGlobals])
    intro F s hc hW hnt hfr
    exact merge_new_call_worldStep s x kw capw hW hkl hcl hfr
  intro F s hc hW hnt hfr
  exact progWithdrawalStep_seq hnew hcont s hc hW hnt hfr

/-- The concrete allocation at the start of the storage merge miss branch
fits the withdrawal mask. -/
theorem progWithdrawalStep_merge_new :
    ProgWithdrawalStep
      (.call (some (some (.local, ofString "binner"), none)) (ofString "htab_new")
        [.const 32#64, .const 8#64]) := by
  apply progWithdrawalStep_of_progWStep (B := []) (gw := ["heap_ptr"])
    (by simp) (by simp [withdrawalGlobals])
  intro F s hc hW hnt hfr
  exact merge_new_call_worldStep s _ _ _ hW (by decide) (by decide) hfr

/-- The fresh table is the word stored in the call destination, with all
other caller locals preserved.  Its footprint lies entirely in fresh heap. -/
theorem merge_new_call_binding {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x : MlS) (kw capw : BitVec 64)
    (hAR : ArenaReady s) (hkl : kw.toNat ∈ htabKeyLens)
    (hcl : capw.toNat ≤ htabCapMax)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (some (.local, x), none)) (ofString "htab_new")
        [.const kw, .const capw])).1) :
    let post := (evaluateHOLFiniteState s
      (.call (some (some (.local, x), none)) (ofString "htab_new")
        [.const kw, .const capw])).2
    ∃ tw : BitVec 64,
      post.locals.lookup x = some (.val (.word tw)) ∧
      (∀ y, y ≠ x → post.locals.lookup y = s.locals.lookup y) ∧
      globN s "heap_ptr" ≤ tw.toNat ∧
      tw.toNat + 88 ≤ globN post "heap_ptr" ∧
      HtabWF post tw.toNat ∧ hdr post tw.toNat 3 = 0 ∧
      hdr post tw.toNat 0 = kw.toNat ∧
      (∀ i ∈ htabFootprint post tw.toNat,
        Allocated post i ∧ Inside i (globN s "heap_ptr") (globN post "heap_ptr")) := by
  have hn := merge_new_call_flow_none s x kw capw hAR.1.code hfr
  dsimp only
  rw [evaluateHOLFiniteState_call] at hn ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const kw, .const capw] = some [.val (.word kw), .val (.word capw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hl := pan_two_word_lookup s.code.lookup (ofString "htab_new")
    (ofString "key_len") (ofString "cap") (sourceFnBody Guest.Software.guestFn_htab_new) kw capw
    (by decide) (by rw [hAR.1.code]; exact R10Shards.SoloHtabNew.lookup_htab_new)
  rw [ha] at hn ⊢
  dsimp only at hn ⊢
  rw [hl] at hn ⊢
  dsimp only at hn ⊢
  split at hn
  · simp at hn
  · rename_i hnz
    rw [if_neg hnz]
    let cmap := (HolFiniteMapExact.empty.update (ofString "key_len", ValueHOL.val (.word kw))).update
      (ofString "cap", ValueHOL.val (.word capw))
    let ent := callEntryStateHOLFinite s cmap
    have hAe : ArenaReady ent := (arenaReady_with_locals s cmap (s.clock - 1)).2 hAR
    have hk : ent.locals.lookup (ofString "key_len") = some (.val (.word kw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "cap" ≠ ofString "key_len" by decide]
    have hc : ent.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hr : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_htab_new) with ⟨r, sb⟩
    rw [show evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
      (sourceFnBody Guest.Software.guestFn_htab_new) = (r, sb) from hr] at hn
    cases r with
    | none => simp at hn
    | some r =>
      cases r with
      | returned v =>
        obtain ⟨tw, rfl, hlo, hhi, _, _, _, _, hwf, hcnt, hkey, hfp, _⟩ :=
          WkBal.htab_new_heap_props ent kw capw hAe hkl hcl hk hc v (congrArg Prod.fst hr)
        dsimp only at hn ⊢
        split at hn
        · rename_i hshape
          rw [if_pos hshape]
          split at hn
          · rename_i hvalid
            rw [if_pos hvalid]
            refine ⟨tw, ?_, ?_, hlo, ?_, ?_, ?_, ?_, ?_⟩
            · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            · intro y hy
              simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hy]
            · change tw.toNat + 88 ≤ globN sb "heap_ptr"
              simpa only [hr] using hhi
            · apply (WkBal.htabWF_with_locals sb _ _ _).2
              simpa [hr] using hwf
            · change hdr sb tw.toNat 3 = 0
              simpa only [hr] using hcnt
            · change hdr sb tw.toNat 0 = kw.toNat
              simpa only [hr] using hkey
            · change ∀ i ∈ htabFootprint sb tw.toNat,
                Allocated sb i ∧ Inside i (globN ent "heap_ptr") (globN sb "heap_ptr")
              simpa only [hr] using hfp
          · simp at hn
        · simp at hn
      | exception e v => simp at hn
      | error | «break» | «continue» | timeOut | finalFfi _ => simp at hn

/-- Adjoin precisely the table bound to the destination local to ownership. -/
theorem merge_new_call_bound_owned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x : MlS) (kw capw : BitVec 64)
    (S Nd : List Nat) (hAR : ArenaReady s) (hWT : WorldTypedWith s S Nd)
    (hkl : kw.toNat ∈ htabKeyLens) (hcl : capw.toNat ≤ htabCapMax)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (some (.local, x), none)) (ofString "htab_new")
        [.const kw, .const capw])).1) :
    let post := (evaluateHOLFiniteState s
      (.call (some (some (.local, x), none)) (ofString "htab_new")
        [.const kw, .const capw])).2
    ∃ tw : BitVec 64,
      post.locals.lookup x = some (.val (.word tw)) ∧
      (∀ y, y ≠ x → post.locals.lookup y = s.locals.lookup y) ∧
      tw.toNat ∉ S ∧ tw.toNat ≠ 0 ∧
      hdr post tw.toNat 0 = kw.toNat ∧ hdr post tw.toNat 3 = 0 ∧
      (∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ tw.toNat) ∧
      WorldTypedWith post (S ++ [tw.toNat]) Nd ∧
      OwnedGrows s post (worldOwned s S Nd) (worldOwned post (S ++ [tw.toNat]) Nd) ∧
      worldRoleSlots post = worldRoleSlots s ∧
      journalRoleSlots post = journalRoleSlots s ∧
      fixedObjects post = fixedObjects s ∧
      nodeExtents post Nd = nodeExtents s Nd ∧
      (∀ u ∈ S, hdr post u 0 = hdr s u 0) ∧
      (∀ u ∈ S, htabFootprint post u = htabFootprint s u) := by
  dsimp only
  let p : ProgHOL 64 := .call (some (some (.local, x), none)) (ofString "htab_new")
    [.const kw, .const capw]
  let post := (evaluateHOLFiniteState s p).2
  obtain ⟨tw, hbind, hlocals, hlo, hhi, hwf, hcnt, hkey, hfp⟩ :=
    merge_new_call_binding s x kw capw hAR hkl hcl hfr
  obtain ⟨_, _, _, hA, hbe, hsp, _, _, _, _, _, hframe, hgl⟩ :=
    merge_new_call_flow_props s x kw capw hAR hkl hcl hfr
  change tw.toNat + 88 ≤ globN post "heap_ptr" at hhi
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by omega
  have hd : ∀ a : BitVec 64, ¬ ordinaryDomain a → post.memory a = s.memory a := by
    intro a ha
    apply evaluateHOLFiniteState_mem_out_dom s p
    rwa [hAR.1.memaddrs]
  obtain ⟨hnS, hn0, hroles, hWT', hrest⟩ :=
    worldTypedWith_htab_new_sysTx hAR hA hbe hh hsp hwf hkey hfp hd hframe hgl hWT
  exact ⟨tw, hbind, hlocals, hnS, hn0, hkey, hcnt, hroles, hWT', hrest⟩

/-- A flowing or resumable outer insertion must actually fall through. -/
theorem merge_set_call_flow_none {F : Type}
    (s : PanSemStateFiniteExact 64 F) (et ek ev : ExpHOL 64)
    (tw kw vw : BitVec 64)
    (ht : evalAt s et = some (.val (.word tw)))
    (hk : evalAt s ek = some (.val (.word kw)))
    (hv : evalAt s ev = some (.val (.word vw)))
    (hc : s.code = originalRuntimeCode)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set") [et, ek, ev])).1) :
    (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set") [et, ek, ev])).1 = none := by
  rw [evaluateHOLFiniteState_call] at hfr ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [et, ek, ev] = some [.val (.word tw), .val (.word kw), .val (.word vw)] := by
    unfold evalAt at ht hk hv
    simp [evalListHOLFinite, evalListHOLExact, ht, hk, hv]
  have hl := pan_three_word_lookup s.code.lookup (ofString "htab_set")
    (ofString "t") (ofString "key") (ofString "value")
    (sourceFnBody Guest.Software.guestFn_htab_set) tw kw vw
    (by decide) (by decide) (by decide) (by rw [hc]; exact R16WkMarkAccountCreated.lookup_htab_set)
  rw [ha] at hfr ⊢
  dsimp only at hfr ⊢
  rw [hl] at hfr ⊢
  dsimp only at hfr ⊢
  split at hfr
  · simp [FlowingOrResumes, Resumes] at hfr
  · rename_i hnz
    rw [if_neg hnz]
    rcases hr : evaluateHOLFiniteState _ _ with ⟨r, post⟩
    rw [hr] at hfr
    cases r with
    | none => exact absurd hfr not_flowingOrResumes_error
    | some r =>
      cases r with
      | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
      | timeOut => simp [FlowingOrResumes, Resumes] at hfr
      | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
      | returned v =>
        dsimp only at hfr ⊢
        split at hfr
        · rename_i hshape
          rw [if_pos hshape]
        · exact absurd hfr not_flowingOrResumes_error
      | exception e v =>
        have he : Resumes (some (.exception e v)) := by
          rcases hfr with h | h | h | h <;> try simp at h
          exact h
        obtain ⟨_, hv⟩ | ⟨e', v', hv, hne⟩ := he
        · cases hv
        · cases hv
          exact False.elim (WkBal.htab_set_no_catchable_exn (callEntryStateHOLFinite s _) hc e v hne
            (congrArg Prod.fst hr))

/-- Fall-through insertion retains the table exit frame and exact value update. -/
theorem merge_set_call_flow_props {F : Type}
    (s : PanSemStateFiniteExact 64 F) (et ek ev : ExpHOL 64)
    (tw kw vw : BitVec 64)
    (ht : evalAt s et = some (.val (.word tw)))
    (hk : evalAt s ek = some (.val (.word kw)))
    (hv : evalAt s ev = some (.val (.word vw)))
    (hAR : ArenaReady s) (hwf : HtabWF s tw.toNat)
    (hal : ∀ i ∈ htabFootprint s tw.toNat, Allocated s i)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set") [et, ek, ev])).1) :
    let post := (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set") [et, ek, ev])).2
    SoloHtabSet.HtabExitAt tw.toNat s post ∧
    WkBal.HtabSetValuesPost s post tw.toNat vw.toNat ∧
    post.be = s.be ∧
    globN post "scratch_ptr" = globN s "scratch_ptr" ∧
    globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
  dsimp only
  let p : ProgHOL 64 := .call (some (none, none)) (ofString "htab_set") [et, ek, ev]
  have hn : (evaluateHOLFiniteState s p).1 = none :=
    merge_set_call_flow_none s et ek ev tw kw vw ht hk hv hAR.1.code hfr
  have he : evaluateHOLFiniteState s (.seq p (.return (.const 0#64))) =
      (some (.returned (.val (.word 0#64))), (evaluateHOLFiniteState s p).2.emptyLocalsHOLFinite) := by
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hp : evaluateHOLFiniteState s p with ⟨r, post⟩
    rw [hp] at hn
    dsimp only at hn
    subst r
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
  have hnt : (evaluateHOLFiniteState s (.seq p (.return (.const 0#64)))).1 ≠ some .timeOut := by
    rw [he]; simp
  have hr : Resumes (evaluateHOLFiniteState s (.seq p (.return (.const 0#64)))).1 := by
    rw [he]; exact Or.inl ⟨_, rfl⟩
  obtain ⟨mid, hexit, hvals, hbe, _, hsp, hfm, _, _, hseq⟩ :=
    WkBal.seq_call_htab_set_void_resumes s et ek ev (.return (.const 0#64))
      tw kw vw ht hk hv hAR hwf hal hnt hr
  have hm : (evaluateHOLFiniteState s p).2.emptyLocalsHOLFinite = mid.emptyLocalsHOLFinite := by
    have h := congrArg Prod.snd hseq
    rw [he] at h
    simpa [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact] using h
  have hm' : (evaluateHOLFiniteState s p).2 =
      { mid with locals := (evaluateHOLFiniteState s p).2.locals } :=
    congrArg (fun t => { t with locals := (evaluateHOLFiniteState s p).2.locals }) hm
  change SoloHtabSet.HtabExitAt tw.toNat s (evaluateHOLFiniteState s p).2 ∧ _
  rw [hm']
  refine ⟨?_, hvals, hbe, hsp, hfm⟩
  obtain ⟨hA, hW, h0, h1, hhp, hfp, hframe, hgl⟩ := hexit
  exact ⟨(arenaReady_with_locals mid _ _).2 hA,
    (WkBal.htabWF_with_locals mid _ _ _).2 hW, h0, h1, hhp, hfp, hframe, hgl⟩

/-- The void outer insertion preserves the fresh inner-table local binding. -/
theorem merge_set_call_flow_locals {F : Type}
    (s : PanSemStateFiniteExact 64 F) (et ek ev : ExpHOL 64)
    (tw kw vw : BitVec 64)
    (ht : evalAt s et = some (.val (.word tw)))
    (hk : evalAt s ek = some (.val (.word kw)))
    (hv : evalAt s ev = some (.val (.word vw)))
    (hc : s.code = originalRuntimeCode)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set") [et, ek, ev])).1) :
    (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set") [et, ek, ev])).2.locals = s.locals := by
  have hn := merge_set_call_flow_none s et ek ev tw kw vw ht hk hv hc hfr
  rw [evaluateHOLFiniteState_call] at hn ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [et, ek, ev] = some [.val (.word tw), .val (.word kw), .val (.word vw)] := by
    unfold evalAt at ht hk hv
    simp [evalListHOLFinite, evalListHOLExact, ht, hk, hv]
  have hl := pan_three_word_lookup s.code.lookup (ofString "htab_set")
    (ofString "t") (ofString "key") (ofString "value")
    (sourceFnBody Guest.Software.guestFn_htab_set) tw kw vw
    (by decide) (by decide) (by decide) (by rw [hc]; exact R16WkMarkAccountCreated.lookup_htab_set)
  rw [ha] at hn ⊢
  dsimp only at hn ⊢
  rw [hl] at hn ⊢
  dsimp only at hn ⊢
  split at hn
  · simp at hn
  · rename_i hnz
    rw [if_neg hnz]
    rcases hr : evaluateHOLFiniteState _ _ with ⟨r, post⟩
    rw [hr] at hn
    cases r with
    | none => simp at hn
    | some r =>
      cases r with
      | returned v =>
        dsimp only at hn ⊢
        split at hn
        · rename_i hshape
          rw [if_pos hshape]
        · simp at hn
      | exception e v => simp at hn
      | error | «break» | «continue» | timeOut | finalFfi _ => simp at hn

/-- Outer insertion carries the bound inner table into its resulting value list. -/
theorem merge_set_call_bound_member {F : Type}
    (s : PanSemStateFiniteExact 64 F) (et ek : ExpHOL 64)
    (tw kw iw : BitVec 64)
    (ht : evalAt s et = some (.val (.word tw)))
    (hk : evalAt s ek = some (.val (.word kw)))
    (hi : s.locals.lookup (ofString "binner") = some (.val (.word iw)))
    (hAR : ArenaReady s) (hwf : HtabWF s tw.toNat)
    (hal : ∀ i ∈ htabFootprint s tw.toNat, Allocated s i)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set")
        [et, ek, .var .local (ofString "binner")])).1) :
    let post := (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set")
        [et, ek, .var .local (ofString "binner")])).2
    post.locals.lookup (ofString "binner") = some (.val (.word iw)) ∧
      locN post "binner" ∈ htabValues post tw.toNat := by
  have hv : evalAt s (.var .local (ofString "binner")) = some (.val (.word iw)) := by
    simpa [evalAt, evalHOLExact] using hi
  have hp := merge_set_call_flow_props s et ek _ tw kw iw ht hk hv hAR hwf hal hfr
  have hl := merge_set_call_flow_locals s et ek _ tw kw iw ht hk hv hAR.1.code hfr
  dsimp only
  constructor
  · rw [hl]; exact hi
  · have hm := (merge_set_values_membership hp.2.1).1
    simpa [locN, hl, hi] using hm

/-- Insertion into an outer table preserves every separately owned inner table. -/
theorem merge_set_other_table_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t u : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd)
    (ht : t ∈ S) (hu : u ∈ S) (hne : u ≠ t)
    (he : SoloHtabSet.HtabExitAt t s post) :
    HtabWF post u ∧ htabFootprint post u = htabFootprint s u ∧
      (∀ k, k < 11 → hdr post u k = hdr s u k) := by
  obtain ⟨hAp, _, _, _, hhp, _, hfr, _⟩ := he
  have hf_al : (globN s "heap_ptr") % 8 = 0 ∧
      (globN post "heap_ptr" - globN s "heap_ptr") % 8 = 0 := by
    have h1 := hA.2.2.2.2.2.2.1
    have h2 := hAp.2.2.2.2.2.2.1
    omega
  have ht_al : ∀ j ∈ htabFootprint s t, j.1 % 8 = 0 ∧ j.2 % 8 = 0 := by
    intro j hj
    have hw := ((hW.1.2.1 t ht).1.1 j hj).2
    exact ⟨hw.1, hw.2.1⟩
  have hunhit : ∀ i ∈ htabFootprint s u, IvlUnhit s post i := by
    intro i hi
    exact R10Shards.P26_P28.ivlUnhit_of_frameOutside_aligned
      (htabFootprint_len_pos (hW.1.2.1 u hu).1 hi) hfr ht_al hf_al
      (fun j hj => hW.1.2.2.1 u hu t ht hne i hi j hj)
      (disj_fresh_of_zero_or_allocated hA.2 hAp.2 hhp
        (Or.inr ((hW.1.2.1 u hu).2 i hi).1))
  have hheader : (u, 88) ∈ htabFootprint s u := by simp [htabFootprint]
  have hfp := (hW.1.2.1 u hu).1.1
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have hh := htabFootprint_eq_of_hdr_unhit ((hfp _ hheader).2.1)
    (by have := (hfp _ hheader).1.2; dsimp at this; omega) (hunhit _ hheader)
  exact ⟨htabWF_congr_unhit hA.1 hAp.1 (hW.1.2.1 u hu).1 hunhit, hh.2, hh.1⟩

/-- Inserting an owned inner pointer preserves the outer table's value ownership. -/
theorem merge_set_values_owned {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {t value : Nat} {S : List Nat}
    (hv : WkBal.HtabSetValuesPost s post t value)
    (hold : HtabValuesIn s t S) (hvalue : value ∈ S) :
    HtabValuesIn post t S := by
  intro i hi
  have hm : nodeF post (hdr post t 5) (memW post (hdr post t 6 + 8 * i)) 8 ∈
      htabValues post t := List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
  rcases (merge_set_values_membership hv).2 _ hm with hm | heq
  · obtain ⟨j, hj, heq⟩ := List.mem_map.1 hm
    rw [← heq]
    exact hold j (List.mem_range.1 hj)
  · rw [heq]; exact hvalue

/-- The concrete outer insertion retains the inner binding and nested ownership facts. -/
theorem merge_set_call_nested_owned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (et ek : ExpHOL 64)
    (tw kw iw : BitVec 64) (S Nd : List Nat)
    (ht : evalAt s et = some (.val (.word tw)))
    (hk : evalAt s ek = some (.val (.word kw)))
    (hi : s.locals.lookup (ofString "binner") = some (.val (.word iw)))
    (hAR : ArenaReady s) (hWT : WorldTypedWith s S Nd)
    (htS : tw.toNat ∈ S) (hiS : iw.toNat ∈ S) (hne : iw.toNat ≠ tw.toNat)
    (howned : HtabValuesIn s tw.toNat S)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set")
        [et, ek, .var .local (ofString "binner")])).1) :
    let post := (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set")
        [et, ek, .var .local (ofString "binner")])).2
    post.locals.lookup (ofString "binner") = some (.val (.word iw)) ∧
    locN post "binner" ∈ htabValues post tw.toNat ∧
    HtabValuesIn post tw.toNat S ∧
    HtabWF post iw.toNat ∧
    htabFootprint post iw.toNat = htabFootprint s iw.toNat ∧
    (∀ k, k < 11 → hdr post iw.toNat k = hdr s iw.toNat k) := by
  have hv : evalAt s (.var .local (ofString "binner")) = some (.val (.word iw)) := by
    simpa [evalAt, evalHOLExact] using hi
  have hwf := (hWT.1.2.1 tw.toNat htS).1
  have hal : ∀ i ∈ htabFootprint s tw.toNat, Allocated s i :=
    fun i hi => ((hWT.1.2.1 tw.toNat htS).2 i hi).1
  have hp := merge_set_call_flow_props s et ek _ tw kw iw ht hk hv hAR hwf hal hfr
  have hm := merge_set_call_bound_member s et ek tw kw iw ht hk hi hAR hwf hal hfr
  exact ⟨hm.1, hm.2, merge_set_values_owned hp.2.1 howned hiS,
    merge_set_other_table_frame hAR hWT htS hiS hne hp.1⟩

/-- A fresh table with no world role cannot alias the block storage outer table. -/
theorem merge_fresh_inner_ne_outer {F : Type} {s : PanSemStateFiniteExact 64 F}
    {inner : Nat} (hbs : globN s "bs" ≠ 0)
    (hout : memW s (globN s "bs" + 32) ≠ 0)
    (hfresh : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ inner) :
    inner ≠ memW s (globN s "bs" + 32) := by
  have hm : (memW s (globN s "bs" + 32), "bs+32") ∈ worldRoleSlots s := by
    apply R16WkMarkAccountCreated.mem_worldRoleSlots_recRole s "bs" 32 _ hbs hout
    simp [recRoles, hbs]
  exact (hfresh _ (List.mem_append_left _ hm)).symm

/-- Outer insertion leaves every nonempty fixed world object untouched. -/
theorem merge_set_fixed_unhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post) :
    ∀ i ∈ fixedObjects s, i.2 ≠ 0 → IvlUnhit s post i := by
  obtain ⟨hAp, _, _, _, hhp, _, hfr, _⟩ := he
  have hf_al : (globN s "heap_ptr") % 8 = 0 ∧
      (globN post "heap_ptr" - globN s "heap_ptr") % 8 = 0 := by
    have h1 := hA.2.2.2.2.2.2.1
    have h2 := hAp.2.2.2.2.2.2.1
    omega
  have ht_al : ∀ j ∈ htabFootprint s t, j.1 % 8 = 0 ∧ j.2 % 8 = 0 := by
    intro j hj
    have hw := ((hW.1.2.1 t ht).1.1 j hj).2
    exact ⟨hw.1, hw.2.1⟩
  intro i hi hpos
  have hal : Allocated s i := by
    rcases hW.2.2.1.1 i hi with hz | ⟨hal, _⟩
    · exact False.elim (hpos hz)
    · exact hal
  exact R10Shards.P26_P28.ivlUnhit_of_frameOutside_aligned hpos hfr ht_al hf_al
    (fun j hj => (((hW.1.2.1 t ht).2 j hj).2 i hi).flip)
    (disj_fresh_of_zero_or_allocated hA.2 hAp.2 hhp (Or.inr hal))

/-- Outer insertion preserves the block record's pointer to that outer table. -/
theorem merge_set_bs_outer_kept {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post) (hbs : globN s "bs" ≠ 0) :
    globN post "bs" = globN s "bs" ∧
    memW post (globN post "bs" + 32) = memW s (globN s "bs" + 32) := by
  have hg : globN post "bs" = globN s "bs" :=
    globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString "bs") (by decide))
  have hm := typedRecord_mem_fixedObjects s (r := ("bs", 80)) (by simp [typedRecords])
  simp only [hbs, ↓reduceIte] at hm
  have hu := merge_set_fixed_unhit hA hW ht he _ hm (by simp)
  exact ⟨hg, rec_word_eq_of_unhit hA.2 hW.2.2.1 "bs" 80
    (by simp [typedRecords]) hg hbs hu (by decide) (by decide)⟩

/-- Installing a fresh block inner-table role preserves role compatibility. -/
theorem merge_roles_append_fresh {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S : List Nat} {sl jr : List (Nat × String)} {inner : Nat}
    (h : RolesOK s S sl jr) (hi : inner ∈ S)
    (hk : hdr s inner 0 = roleKeyLen "bs.inner")
    (hf : ∀ a ∈ sl ++ jr, a.1 ≠ inner) :
    RolesOK s S (sl ++ [(inner, "bs.inner")]) jr := by
  refine ⟨?_, List.pairwise_append.2 ⟨h.2.1, by simp, ?_⟩, ?_⟩
  · intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · rcases List.mem_append.1 ha with ha | ha
      · exact h.1 a (List.mem_append_left _ ha)
      · have he := List.mem_singleton.1 ha
        subst a
        exact ⟨hi, hk⟩
    · exact h.1 a (List.mem_append_right _ ha)
  · intro a ha b hb heq
    have hb := List.mem_singleton.1 hb
    subst b
    exact False.elim (hf a (List.mem_append_left _ ha) heq)
  · intro a ha b hb heq
    rcases List.mem_append.1 hb with hb | hb
    · rcases List.mem_append.1 hb with hb | hb
      · exact h.2.2 a ha b (List.mem_append_left _ hb) heq
      · have hb := List.mem_singleton.1 hb
        subst b
        exact False.elim (hf a (List.mem_append_right _ ha) heq)
    · exact h.2.2 a ha b (List.mem_append_right _ hb) heq

/-- Outer insertion introduces only the installed block-inner role. -/
theorem merge_set_nestRoles_provenance {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {t inner : Nat}
    (hbs : globN s "bs" ≠ 0) (ht : t = memW s (globN s "bs" + 32))
    (ht0 : t ≠ 0) (hg : globN post "bs" = globN s "bs")
    (hp : memW post (globN post "bs" + 32) = t)
    (hv : WkBal.HtabSetValuesPost s post t inner) :
    (inner, "bs.inner") ∈ nestRoles post "bs" "bs.inner" ∧
    ∀ a ∈ nestRoles post "bs" "bs.inner",
      a ∈ nestRoles s "bs" "bs.inner" ∨ a = (inner, "bs.inner") := by
  have hpost : nestRoles post "bs" "bs.inner" =
      (htabValues post t).map (fun v => (v, "bs.inner")) := by
    have hbpost : globN post "bs" ≠ 0 := by rwa [hg]
    simp [nestRoles, hbpost, hp, ht0]
  have hpre : nestRoles s "bs" "bs.inner" =
      (htabValues s t).map (fun v => (v, "bs.inner")) := by
    simp [nestRoles, hbs, ← ht, ht0]
  rw [hpost, hpre]
  refine ⟨List.mem_map.2 ⟨inner, (merge_set_values_membership hv).1, rfl⟩, ?_⟩
  intro a ha
  obtain ⟨v, hv', rfl⟩ := List.mem_map.1 ha
  rcases (merge_set_values_membership hv).2 v hv' with hold | heq
  · exact Or.inl (List.mem_map.2 ⟨v, hold, rfl⟩)
  · exact Or.inr (by rw [heq])

/-- Replace the nested block-role segment using old-or-fresh provenance. -/
theorem merge_roles_replace_inner {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S : List Nat} {pre old new suf jr : List (Nat × String)} {inner : Nat}
    (h : RolesOK s S (pre ++ old ++ suf) jr)
    (hi : inner ∈ S) (hk : hdr s inner 0 = roleKeyLen "bs.inner")
    (hf : ∀ a ∈ (pre ++ old ++ suf) ++ jr, a.1 ≠ inner)
    (hp : ∀ a ∈ new, a ∈ old ∨ a = (inner, "bs.inner"))
    (hr : ∀ a ∈ new, a.2 = "bs.inner") :
    RolesOK s S (pre ++ new ++ suf) jr := by
  have hold : ∀ a ∈ old, a ∈ pre ++ old ++ suf := by
    intro a ha; simp only [List.mem_append]; exact Or.inl (Or.inr ha)
  have hpre : ∀ a ∈ pre, a ∈ pre ++ old ++ suf := by
    intro a ha; simp only [List.mem_append]; exact Or.inl (Or.inl ha)
  have hsuf : ∀ a ∈ suf, a ∈ pre ++ old ++ suf := by
    intro a ha; exact List.mem_append_right _ ha
  have hprov : ∀ a ∈ pre ++ new ++ suf,
      a ∈ pre ++ old ++ suf ∨ a = (inner, "bs.inner") := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · rcases List.mem_append.1 ha with ha | ha
      · exact Or.inl (hpre a ha)
      · exact (hp a ha).imp (hold a) id
    · exact Or.inl (hsuf a ha)
  have hpair := List.pairwise_append.1 h.2.1
  have hleft := List.pairwise_append.1 hpair.1
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · rcases hprov a ha with ha | rfl
      · exact h.1 a (List.mem_append_left _ ha)
      · exact ⟨hi, hk⟩
    · exact h.1 a (List.mem_append_right _ ha)
  · apply List.pairwise_append.2
    refine ⟨List.pairwise_append.2 ⟨hleft.1, ?_, ?_⟩, hpair.2.1, ?_⟩
    · have hall : ∀ l : List (Nat × String), (∀ a ∈ l, a.2 = "bs.inner") →
          l.Pairwise (fun a b => a.1 = b.1 → a.2 = b.2 ∧ a.2 ∈ sharedRoles) := by
        intro l
        induction l with
        | nil => simp
        | cons a l ih =>
          intro hh
          apply List.pairwise_cons.2
          refine ⟨?_, ih (fun b hb => hh b (List.mem_cons_of_mem _ hb))⟩
          intro b hb heq
          have ha := hh a (List.mem_cons_self)
          have hb' := hh b (List.mem_cons_of_mem _ hb)
          exact ⟨ha.trans hb'.symm, by rw [ha]; simp [sharedRoles]⟩
      exact hall new hr
    · intro a ha b hb heq
      rcases hp b hb with hb | rfl
      · exact hleft.2.2 a ha b hb heq
      · exact False.elim (hf a (List.mem_append_left _ (hpre a ha)) heq)
    · intro a ha b hb heq
      rcases List.mem_append.1 ha with ha | ha
      · exact hpair.2.2 a (List.mem_append_left _ ha) b hb heq
      · rcases hp a ha with ha | rfl
        · exact hpair.2.2 a (List.mem_append_right _ ha) b hb heq
        · exact False.elim (hf b (List.mem_append_left _ (hsuf b hb)) heq.symm)
  · intro a ha b hb heq
    rcases List.mem_append.1 hb with hb | hb
    · rcases hprov b hb with hb | rfl
      · exact h.2.2 a ha b (List.mem_append_left _ hb) heq
      · exact False.elim (hf a (List.mem_append_right _ ha) heq)
    · exact h.2.2 a ha b (List.mem_append_right _ hb) heq

/-- Transport filtered nested roles across insertion and preserved key-length headers. -/
theorem merge_roles_transport_inner {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    {pre suf jr : List (Nat × String)} {t inner : Nat}
    (h : RolesOK s S (pre ++ (nestRoles s "bs" "bs.inner").filter
      (fun a => a.1 != 0) ++ suf) jr)
    (hi : inner ∈ S) (hk : hdr s inner 0 = roleKeyLen "bs.inner")
    (hf : ∀ a ∈ (pre ++ (nestRoles s "bs" "bs.inner").filter
      (fun a => a.1 != 0) ++ suf) ++ jr, a.1 ≠ inner)
    (hh : ∀ u ∈ S, hdr post u 0 = hdr s u 0)
    (hbs : globN s "bs" ≠ 0) (ht : t = memW s (globN s "bs" + 32))
    (ht0 : t ≠ 0) (hg : globN post "bs" = globN s "bs")
    (hp : memW post (globN post "bs" + 32) = t)
    (hv : WkBal.HtabSetValuesPost s post t inner) :
    RolesOK post S (pre ++ (nestRoles post "bs" "bs.inner").filter
      (fun a => a.1 != 0) ++ suf) jr := by
  have hprov := (merge_set_nestRoles_provenance hbs ht ht0 hg hp hv).2
  have hnew := merge_roles_replace_inner h hi hk hf
    (new := (nestRoles post "bs" "bs.inner").filter (fun a => a.1 != 0))
    (by
      intro a ha
      obtain ⟨ha, hn⟩ := List.mem_filter.1 ha
      rcases hprov a ha with ha | ha
      · exact Or.inl (List.mem_filter.2 ⟨ha, hn⟩)
      · exact Or.inr ha)
    (by
      intro a ha
      have ha := (List.mem_filter.1 ha).1
      unfold nestRoles at ha
      split at ha
      · simp at ha
      · split at ha
        · simp at ha
        · obtain ⟨v, _, rfl⟩ := List.mem_map.1 ha
          rfl)
  refine ⟨?_, hnew.2⟩
  intro a ha
  obtain ⟨hm, hk'⟩ := hnew.1 a ha
  exact ⟨hm, (hh a.1 hm).trans hk'⟩

/-- Table insertion preserves journal roles and journal typing. -/
theorem merge_set_journal_kept {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post) :
    journalRoleSlots post = journalRoleSlots s ∧ JournalTyped post S := by
  have hg := he.2.2.2.2.2.2.2
  have hsp : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    globN_eq_of_lookup (hg (ofString "scratch_ptr") (by decide))
  have hag : AllocatorGrows s post := ⟨he.2.2.2.2.1, by rw [hsp]⟩
  have hcore : ∀ g ∈ coreWorldGlobals, globN post g = globN s g := by
    intro g hg'
    apply globN_eq_of_lookup (hg (ofString g) ?_)
    revert g hg'; decide
  apply R10Shards.P26_P28.journalRoleSlots_eq_of_unhit hA.1 he.1.1 hA.2 hag
    (fun _ hx => hx) hW.2.1 hW.2.2.1 hcore
  · intro hnz
    have hm := typedRecord_mem_fixedObjects s (r := ("ts", 72)) (by simp [typedRecords])
    simp only [hnz, ↓reduceIte] at hm
    exact merge_set_fixed_unhit hA hW ht he _ hm (by simp)
  · intro hnz
    apply merge_set_fixed_unhit hA hW ht he
    · unfold fixedObjects
      apply List.mem_append.2; left
      apply List.mem_append.2; left
      apply List.mem_append.2; right
      simp [hnz]
    · dsimp; omega

/-- Insertion preserves all aligned table-role fields of a fixed world record. -/
theorem merge_set_recRoles_kept {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post)
    (g : String) (sz : Nat) (ks : List (Nat × String))
    (hrec : (g, sz) ∈ typedRecords) (hsz : sz ≠ 0)
    (hg : ofString g ≠ ofString "heap_ptr")
    (hks : ∀ k ∈ ks, k.1 % 8 = 0 ∧ k.1 + 8 ≤ sz) :
    recRoles post g ks = recRoles s g ks := by
  have hglob : globN post g = globN s g := by
    apply globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString g) ?_)
    simpa using hg
  unfold recRoles
  rw [hglob]
  split
  · rfl
  · rename_i hnz
    have hm := typedRecord_mem_fixedObjects s (r := (g, sz)) hrec
    simp only [hnz, ↓reduceIte] at hm
    have hu := merge_set_fixed_unhit hA hW ht he _ hm hsz
    apply List.map_congr_left
    intro k hk
    have hw := rec_word_eq_of_unhit hA.2 hW.2.2.1 g sz hrec hglob hnz hu
      (hks k hk).1 (hks k hk).2
    rw [hglob] at hw
    exact congrArg (fun v => (v, k.2)) hw

/-- Insertion preserves the complete value lists of other owned tables. -/
theorem merge_set_other_values_kept {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t u : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd)
    (ht : t ∈ S) (hu : u ∈ S) (hne : u ≠ t)
    (he : SoloHtabSet.HtabExitAt t s post) :
    htabValues post u = htabValues s u := by
  obtain ⟨hAp, _, _, _, hhp, _, hfr, _⟩ := he
  have hf_al : (globN s "heap_ptr") % 8 = 0 ∧
      (globN post "heap_ptr" - globN s "heap_ptr") % 8 = 0 := by
    have h1 := hA.2.2.2.2.2.2.1
    have h2 := hAp.2.2.2.2.2.2.1
    omega
  have ht_al : ∀ j ∈ htabFootprint s t, j.1 % 8 = 0 ∧ j.2 % 8 = 0 := by
    intro j hj
    have hw := ((hW.1.2.1 t ht).1.1 j hj).2
    exact ⟨hw.1, hw.2.1⟩
  apply htabValues_eq_of_unhit (hW.1.2.1 u hu).1
  intro i hi
  exact R10Shards.P26_P28.ivlUnhit_of_frameOutside_aligned
    (htabFootprint_len_pos (hW.1.2.1 u hu).1 hi) hfr ht_al hf_al
    (fun j hj => hW.1.2.2.1 u hu t ht hne i hi j hj)
    (disj_fresh_of_zero_or_allocated hA.2 hAp.2 hhp
      (Or.inr ((hW.1.2.1 u hu).2 i hi).1))

/-- Insertion preserves nested roles of a separately owned record-rooted table. -/
theorem merge_set_other_nestRoles_kept {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post)
    (g r : String) (sz : Nat) (hrec : (g, sz) ∈ typedRecords)
    (hsz : 40 ≤ sz) (hg : ofString g ≠ ofString "heap_ptr")
    (hroot : globN s g ≠ 0 → RootIn S (memW s (globN s g + 32)))
    (hne : globN s g ≠ 0 → memW s (globN s g + 32) ≠ 0 →
      memW s (globN s g + 32) ≠ t) :
    nestRoles post g r = nestRoles s g r := by
  have hglob : globN post g = globN s g :=
    globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString g) (by simpa using hg))
  unfold nestRoles
  rw [hglob]
  by_cases hn : globN s g = 0
  · simp [hn]
  have hr := merge_set_recRoles_kept hA hW ht he g sz [(32, r)] hrec
    (by omega) hg (by simp; omega)
  simp only [recRoles, hglob, hn, ↓reduceIte, List.map_cons, List.map_nil] at hr
  have hp : memW post (globN s g + 32) = memW s (globN s g + 32) := by
    exact congrArg (fun l : List (Nat × String) => (l.headD (0, "")).1) hr
  rw [hp]
  by_cases hz : memW s (globN s g + 32) = 0
  · simp [hz]
  have hu : memW s (globN s g + 32) ∈ S := (hroot hn).resolve_left hz
  rw [merge_set_other_values_kept hA hW ht hu (hne hn hz) he]

/-- Insertion into a table distinct from the BAL root preserves record enumeration. -/
theorem merge_set_balRecords_kept {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post)
    (hne : globN s "bal_accounts" ≠ t) :
    balRecords post = balRecords s := by
  have hg : globN post "bal_accounts" = globN s "bal_accounts" :=
    globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString "bal_accounts") (by decide))
  change (if globN post "bal_accounts" = 0 then [] else
    htabValues post (globN post "bal_accounts")) =
    (if globN s "bal_accounts" = 0 then [] else htabValues s (globN s "bal_accounts"))
  rw [hg]
  by_cases hz : globN s "bal_accounts" = 0
  · simp [hz]
  have hu : globN s "bal_accounts" ∈ S :=
    (hW.1.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots])).resolve_left hz
  rw [merge_set_other_values_kept hA hW ht hu hne he]

/-- The transaction's nested roles survive insertion into the block storage outer table. -/
theorem merge_set_ts_nestRoles_kept {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post)
    (hbs : globN s "bs" ≠ 0) (ht0 : t ≠ 0)
    (htbs : t = memW s (globN s "bs" + 32)) :
    nestRoles post "ts" "ts.inner" = nestRoles s "ts" "ts.inner" := by
  apply merge_set_other_nestRoles_kept hA hW ht he "ts" "ts.inner" 72
    (by simp [typedRecords]) (by decide) (by decide)
  · exact hW.1.2.2.2.2.2.1 32 (by simp [tsTableSlots])
  · intro hts hu
    have hb : (t, "bs+32") ∈ worldRoleSlots s := by
      rw [htbs]
      apply R16WkMarkAccountCreated.mem_worldRoleSlots_recRole s "bs" 32 _ hbs
        (by rwa [← htbs])
      simp [recRoles, hbs]
    have hx : (memW s (globN s "ts" + 32), "ts+32") ∈ worldRoleSlots s := by
      apply R16WkMarkAccountCreated.mem_worldRoleSlots_recRole s "ts" 32 _ hts hu
      simp [recRoles, hts]
    exact R16WkMarkAccountCreated.slot_ne_of_diff_nonshared_role
      hW.1.2.2.2.2.2.2.2.2.2.2.2 hx hb (by decide)

/-- Block storage insertion cannot change the enumeration of BAL accounts. -/
theorem merge_set_bs_balRecords_kept {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post)
    (hbs : globN s "bs" ≠ 0) (ht0 : t ≠ 0)
    (htbs : t = memW s (globN s "bs" + 32)) :
    balRecords post = balRecords s := by
  apply merge_set_balRecords_kept hA hW ht he
  by_cases hz : globN s "bal_accounts" = 0
  · rw [hz]; exact Ne.symm ht0
  have hb : (t, "bs+32") ∈ worldRoleSlots s := by
    rw [htbs]
    apply R16WkMarkAccountCreated.mem_worldRoleSlots_recRole s "bs" 32 _ hbs
      (by rwa [← htbs])
    simp [recRoles, hbs]
  have hx : (globN s "bal_accounts", "bal_accounts") ∈ worldRoleSlots s := by
    simp [worldRoleSlots, hz]
  exact R16WkMarkAccountCreated.slot_ne_of_diff_nonshared_role
    hW.1.2.2.2.2.2.2.2.2.2.2.2 hx hb (by decide)

/-- Every aligned field of an existing BAL account record survives table insertion. -/
theorem merge_set_bal_record_fields_kept {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t ad : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post) (had : ad ∈ balRecords s)
    (k : Nat) (hk : k % 8 = 0) (hkb : k + 8 ≤ 40) :
    memW post (ad + k) = memW s (ad + k) := by
  have hm : (ad, 40) ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append_right
    exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
  have hu := merge_set_fixed_unhit hA hW ht he _ hm (by simp)
  obtain hz | ⟨hal, hw⟩ := hW.2.2.1.1 _ hm
  · simp at hz
  have hb := (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hA.2 hal).2
  apply memW_eq_of_ivlUnhit hu
  · have ha := hw.1
    omega
  · exact hb
  · constructor <;> omega

/-- The BAL role segment is unchanged by insertion into the block outer table. -/
theorem merge_set_bal_roles_kept {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post)
    (hbs : globN s "bs" ≠ 0) (ht0 : t ≠ 0)
    (htbs : t = memW s (globN s "bs" + 32)) :
    (balRecords post).flatMap (fun ad =>
      [(memW post ad, "bal.stor"), (memW post (ad + 8), "bal.reads")]) =
    (balRecords s).flatMap (fun ad =>
      [(memW s ad, "bal.stor"), (memW s (ad + 8), "bal.reads")]) := by
  rw [merge_set_bs_balRecords_kept hA hW ht he hbs ht0 htbs]
  apply List.flatMap_congr
  intro ad had
  have h0 := merge_set_bal_record_fields_kept hA hW ht he had 0 (by decide) (by decide)
  have h8 := merge_set_bal_record_fields_kept hA hW ht he had 8 (by decide) (by decide)
  simp only [Nat.add_zero] at h0
  rw [h0, h8]

/-- Insertion preserves the key-length header of every owned table. -/
theorem merge_set_key_lengths_kept {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post) :
    ∀ u ∈ S, hdr post u 0 = hdr s u 0 := by
  intro u hu
  by_cases hn : u = t
  · subst u
    exact he.2.2.1
  · exact (merge_set_other_table_frame hA hW ht hu hn he).2.2 0 (by decide)

/-- All world roles remain compatible when a fresh block-inner role is installed. -/
theorem merge_set_world_roles {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t inner : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post)
    (hbs : globN s "bs" ≠ 0) (ht0 : t ≠ 0)
    (htbs : t = memW s (globN s "bs" + 32))
    (hi : inner ∈ S) (hk : hdr s inner 0 = roleKeyLen "bs.inner")
    (hf : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ inner)
    (hv : WkBal.HtabSetValuesPost s post t inner) :
    RolesOK post S (worldRoleSlots post) (journalRoleSlots post) := by
  have hj := (merge_set_journal_kept hA hW ht he).1
  have hws := merge_set_recRoles_kept hA hW ht he "ws" 40
    [(16, "ws+16"), (32, "ws+32")] (by simp [typedRecords]) (by decide)
    (by decide) (by decide)
  have hbr := merge_set_recRoles_kept hA hW ht he "bs" 80
    [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
      (40, "bs+40"), (48, "bs+48"), (72, "bs+72")]
    (by simp [typedRecords]) (by decide) (by decide) (by decide)
  have htr := merge_set_recRoles_kept hA hW ht he "ts" 72
    [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
      (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")]
    (by simp [typedRecords]) (by decide) (by decide) (by decide)
  have hba : globN post "bal_accounts" = globN s "bal_accounts" :=
    globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString "bal_accounts") (by decide))
  have hbi : globN post "bal_idx_accts" = globN s "bal_idx_accts" :=
    globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString "bal_idx_accts") (by decide))
  have hbj : globN post "bal_idx_stor" = globN s "bal_idx_stor" :=
    globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString "bal_idx_stor") (by decide))
  have htn := merge_set_ts_nestRoles_kept hA hW ht he hbs ht0 htbs
  have hbal := merge_set_bal_roles_kept hA hW ht he hbs ht0 htbs
  have hp := merge_set_bs_outer_kept hA hW ht he hbs
  let pre := (recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] ++
    recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
      (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] ++
    recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
      (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] ++
    [(globN s "bal_accounts", "bal_accounts"), (globN s "bal_idx_accts", "bal_idx_accts"),
      (globN s "bal_idx_stor", "bal_idx_stor")]).filter (fun a => a.1 != 0)
  let suf := (nestRoles s "ts" "ts.inner" ++ (balRecords s).flatMap
    (fun ad => [(memW s ad, "bal.stor"), (memW s (ad + 8), "bal.reads")])).filter
    (fun a => a.1 != 0)
  have hpre : worldRoleSlots s = pre ++
      (nestRoles s "bs" "bs.inner").filter (fun a => a.1 != 0) ++ suf := by
    simp only [worldRoleSlots, pre, suf, List.filter_append, List.append_assoc]
  have hpost : worldRoleSlots post = pre ++
      (nestRoles post "bs" "bs.inner").filter (fun a => a.1 != 0) ++ suf := by
    simp only [worldRoleSlots, hws, hbr, htr, hba, hbi, hbj, htn, hbal,
      pre, suf, List.filter_append, List.append_assoc]
  rw [hpost, hj]
  apply merge_roles_transport_inner (s := s) (t := t) (inner := inner)
  · rw [← hpre]; exact hW.1.2.2.2.2.2.2.2.2.2.2.2
  · exact hi
  · exact hk
  · rwa [← hpre]
  · exact merge_set_key_lengths_kept hA hW ht he
  · exact hbs
  · exact htbs
  · exact ht0
  · exact hp.1
  · exact hp.2.trans htbs.symm
  · exact hv

/-- Insertion frames every other table in the word-addressed memory view. -/
theorem merge_set_other_table_unhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post) :
    ∀ u ∈ S, u ≠ t → ∀ i ∈ htabFootprint s u,
      R16WkMarkAccountCreated.M08IvlUnhit s post i := by
  intro u hu hn i hi
  apply R16WkMarkAccountCreated.m08_ivlUnhit_of_frameOutside he.2.2.2.2.2.2.1
  · intro j hj
    exact ((hW.1.2.1 t ht).1.1 j hj).2.1
  · exact hA.2.2.2.2.2.2.1
  · intro j hj
    exact hW.1.2.2.1 u hu t ht hn i hi j hj
  · exact R16WkMarkAccountCreated.disj_fresh_of_zero_or_allocated hA.2 he.1.2
      he.2.2.2.2.1 (Or.inr ((hW.1.2.1 u hu).2 i hi).1)

/-- Insertion leaves low sentinel words unchanged. -/
theorem merge_set_low_words_kept {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post) :
    memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧
      memW post 16 = memW s 16 := by
  have hlow : ∀ a : Nat, a + 8 ≤ sourceBase → memW post a = memW s a := by
    intro a ha
    have hsb : sourceBase < 2 ^ 64 := by decide
    have ha' : a < 2 ^ 64 := by omega
    have hm := he.2.2.2.2.2.2.1 (BitVec.ofNat 64 a)
      (fun j hj hc => by
        obtain ⟨h1, _⟩ := hc
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha'] at h1
        have hlo := ((hW.1.2.1 t ht).1.1 j hj).1.1
        omega)
      (fun hc => by
        obtain ⟨h1, _⟩ := hc
        dsimp at h1
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha'] at h1
        have hlo := hA.2.1
        omega)
    unfold memW
    rw [hm]
  exact ⟨hlow 0 (by decide), hlow 8 (by decide), hlow 16 (by decide)⟩

/-- Block outer insertion preserves BAL objects and the typing of their lists. -/
theorem merge_set_bal_objects_kept {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post)
    (hbs : globN s "bs" ≠ 0) (ht0 : t ≠ 0)
    (htbs : t = memW s (globN s "bs" + 32)) :
    balObjects post = balObjects s ∧
    (∀ ad ∈ balRecords post, memW post ad = memW s ad ∧
      memW post (ad + 8) = memW s (ad + 8) ∧
      htabValues post (memW post ad) = htabValues s (memW s ad) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat), LstOK post (memW post (ad + k))) ∧
      (∀ l ∈ htabValues post (memW post ad), LstOK post l)) := by
  have hb : (t, "bs+32") ∈ worldRoleSlots s := by
    rw [htbs]
    apply R16WkMarkAccountCreated.mem_worldRoleSlots_recRole s "bs" 32 _ hbs
      (by rwa [← htbs])
    simp [recRoles, hbs]
  apply R16WkMarkAccountCreated.balObjects_eq_of_unhit_except hA.2 hW.1 hW.2.2.1
    (globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString "bal_accounts") (by decide)))
    (merge_set_other_table_unhit hA hW ht he)
  · constructor
    · by_cases hz : globN s "bal_accounts" = 0
      · rw [hz]; exact Ne.symm ht0
      have hx : (globN s "bal_accounts", "bal_accounts") ∈ worldRoleSlots s := by
        simp [worldRoleSlots, hz]
      exact R16WkMarkAccountCreated.slot_ne_of_diff_nonshared_role
        hW.1.2.2.2.2.2.2.2.2.2.2.2 hx hb (by decide)
    · intro ad had
      by_cases hz : memW s ad = 0
      · rw [hz]; exact Ne.symm ht0
      have hx : (memW s ad, "bal.stor") ∈ worldRoleSlots s := by
        unfold worldRoleSlots
        apply List.mem_filter.2
        refine ⟨List.mem_append_right _ ?_, by simpa using hz⟩
        exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
      exact R16WkMarkAccountCreated.slot_ne_of_diff_nonshared_role
        hW.1.2.2.2.2.2.2.2.2.2.2.2 hx hb (by decide)
  · intro i hi hn
    have hm : i ∈ fixedObjects s := List.mem_append_right _ hi
    apply R16WkMarkAccountCreated.m08_ivlUnhit_of_frameOutside he.2.2.2.2.2.2.1
    · intro j hj; exact ((hW.1.2.1 t ht).1.1 j hj).2.1
    · exact hA.2.2.2.2.2.2.1
    · intro j hj; exact (((hW.1.2.1 t ht).2 j hj).2 i hm).flip
    · apply R16WkMarkAccountCreated.disj_fresh_of_zero_or_allocated hA.2 he.1.2
        he.2.2.2.2.1
      rcases hW.2.2.1.1 i hm with hz | ⟨hal, _⟩
      · exact Or.inl hz
      · exact Or.inr hal
  · exact merge_set_low_words_kept hA hW ht he

/-- Fixed objects are framed in the word-addressed view, including empty objects. -/
theorem merge_set_fixed_word_unhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post) :
    ∀ i ∈ fixedObjects s, R16WkMarkAccountCreated.M08IvlUnhit s post i := by
  intro i hi
  apply R16WkMarkAccountCreated.m08_ivlUnhit_of_frameOutside he.2.2.2.2.2.2.1
  · intro j hj; exact ((hW.1.2.1 t ht).1.1 j hj).2.1
  · exact hA.2.2.2.2.2.2.1
  · intro j hj; exact (((hW.1.2.1 t ht).2 j hj).2 i hi).flip
  · apply R16WkMarkAccountCreated.disj_fresh_of_zero_or_allocated hA.2 he.1.2
      he.2.2.2.2.1
    rcases hW.2.2.1.1 i hi with hz | ⟨hal, _⟩
    · exact Or.inl hz
    · exact Or.inr hal

/-- Block output objects retain their extents across an owned table insertion. -/
theorem merge_set_blockOutObjects_kept {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post) :
    blockOutObjects post = blockOutObjects s ∧
      (globN post "bo" ≠ 0 → ∀ k ∈ ([40, 72] : List Nat),
        memW post (globN post "bo" + k) ≠ 0 →
        LstOK post (memW post (globN post "bo" + k))) := by
  have hg : globN post "bo" = globN s "bo" :=
    globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString "bo") (by decide))
  have hu : globN s "bo" ≠ 0 → R16WkMarkAccountCreated.M08IvlUnhit s post
      (globN s "bo", 88) := by
    intro hn
    have hm := typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by simp [typedRecords])
    simp only [hn, ↓reduceIte] at hm
    exact merge_set_fixed_word_unhit hA hW ht he _ hm
  have hw : globN s "bo" ≠ 0 → ∀ k, k % 8 = 0 → k + 8 ≤ 88 →
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := by
    intro hn k hk hkb
    simpa [hg] using InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
      hA.2 hW.2.2.1 "bo" 88 (by decide) hg hn (hu hn) hk hkb
  have hz := merge_set_low_words_kept hA hW ht he
  have hh := InitECandidate.Solver.Wave8Contracts.M08.blockOutObjects_eq_of_bo_unhit
    hA.2 hW.2.2.1 hg hW.1.2.2.2.2.2.2.2.2.2.2.1
    (fun h => hw h 24 (by decide) (by decide))
    (fun h => hw h 32 (by decide) (by decide))
    (fun h => hw h 40 (by decide) (by decide))
    (fun h => hw h 56 (by decide) (by decide))
    (fun h => hw h 72 (by decide) (by decide))
    (fun h => hw h 80 (by decide) (by decide))
    (fun _ _ => by simp [hz.1, hz.2.2])
    (fun _ _ => by simp [hz.1, hz.2.2])
    (fun h h40 => merge_set_fixed_word_unhit hA hW ht he _ (by
      unfold fixedObjects
      apply List.mem_append_left
      apply List.mem_append_right
      simp [blockOutObjects, h, h40]))
    (fun h h72 => merge_set_fixed_word_unhit hA hW ht he _ (by
      unfold fixedObjects
      apply List.mem_append_left
      apply List.mem_append_right
      simp [blockOutObjects, h, h72]))
  exact hh

/-- Inserting a block inner pointer preserves fixed-object extents and typing. -/
theorem merge_set_fixed_typed {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post)
    (hbs : globN s "bs" ≠ 0) (ht0 : t ≠ 0)
    (htbs : t = memW s (globN s "bs" + 32)) :
    fixedObjects post = fixedObjects s ∧ FixedTyped post := by
  have hgs := InitECandidate.Solver.Wave8Contracts.M08.worldGlobalsSame_of_kept
    (gw := ["heap_ptr"]) he.2.2.2.2.2.2.2 (fun _ h => Or.inl (by simpa using h))
  have hb := (merge_set_blockOutObjects_kept hA hW ht he).1
  have hbal := (merge_set_bal_objects_kept hA hW ht he hbs ht0 htbs).1
  have hf := InitECandidate.Solver.Wave8Contracts.M08.fixedObjects_eq_of_parts hgs hb hbal
  have hag : AllocatorGrows s post := by
    refine ⟨he.2.2.2.2.1, ?_⟩
    rw [globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString "scratch_ptr") (by decide))]
  exact ⟨hf, InitECandidate.Solver.Wave8Contracts.M08.fixedTyped_transfer
    hA.1 he.1.1 hag hW.2.2.1 hf⟩

/-- The updated table's footprint remains separate from other owned objects. -/
theorem merge_set_footprint_disjoint {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post) :
    ∀ i ∈ htabFootprint post t,
      (∀ u ∈ S, u ≠ t → ∀ j ∈ htabFootprint s u, Disj i j) ∧
      (∀ j ∈ fixedObjects s, Disj i j) ∧
      (∀ o ∈ nodeExtents s Nd, Disj i o) := by
  intro i hi
  rcases (he.2.2.2.2.2.1 i hi).2 with ⟨k, hk, hin⟩ | hfresh
  · refine ⟨?_, ?_, ?_⟩
    · intro u hu hn j hj
      exact InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_left hin
        (hW.1.2.2.1 t ht u hu hn.symm k hk j hj)
    · intro j hj
      exact InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_left hin
        (((hW.1.2.1 t ht).2 k hk).2 j hj)
    · intro o ho
      exact InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_left hin
        ((hW.2.2.2.2.1 o ho).1 t ht k hk).flip
  · have hf : ∀ j, (j.2 = 0 ∨ Allocated s j) → Disj i j := by
      intro j hj
      exact (InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_right hfresh
        (R16WkMarkAccountCreated.disj_fresh_of_zero_or_allocated hA.2 he.1.2
          he.2.2.2.2.1 hj)).flip
    refine ⟨?_, ?_, ?_⟩
    · intro u hu _ j hj
      exact hf j (Or.inr ((hW.1.2.1 u hu).2 j hj).1)
    · intro j hj
      apply hf
      rcases hW.2.2.1.1 j hj with hz | ⟨hal, _⟩
      · exact Or.inl hz
      · exact Or.inr hal
    · intro o ho
      apply hf
      unfold nodeExtents at ho
      obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
      rcases hno with rfl | rfl
      · exact Or.inr (hW.2.2.2.1.1 n hn).2.1
      · unfold nodePath
        split_ifs with hc
        · rcases (hW.2.2.2.1.1 n hn).2.2.2.2.2.2.1 hc.1 with hz | ⟨_, hal, _⟩
          · exact False.elim (hc.2 hz)
          · exact Or.inr hal
        · exact Or.inl rfl

/-- Table well-formedness, allocation, and separation survive outer insertion. -/
theorem merge_set_tables_geometry {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post)
    (hfix : fixedObjects post = fixedObjects s) :
    (∀ u ∈ S, HtabWF post u ∧ ∀ i ∈ htabFootprint post u,
      Allocated post i ∧ ∀ j ∈ fixedObjects post, Disj i j) ∧
    (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ∀ i ∈ htabFootprint post u,
      ∀ j ∈ htabFootprint post v, Disj i j) := by
  have hag : AllocatorGrows s post := by
    refine ⟨he.2.2.2.2.1, ?_⟩
    rw [globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString "scratch_ptr") (by decide))]
  have hd := merge_set_footprint_disjoint hA hW ht he
  have ho := fun {u : Nat} (hu : u ∈ S) (hn : u ≠ t) =>
    merge_set_other_table_frame (post := post) hA hW ht hu hn
  constructor
  · intro u hu
    by_cases hn : u = t
    · subst u
      rw [hfix]
      exact ⟨he.2.1, fun i hi => ⟨(he.2.2.2.2.2.1 i hi).1, (hd i hi).2.1⟩⟩
    · obtain ⟨hwf, hfp, _⟩ := ho hu hn he
      rw [hfp, hfix]
      exact ⟨hwf, fun i hi => ⟨hag.allocated ((hW.1.2.1 u hu).2 i hi).1,
        ((hW.1.2.1 u hu).2 i hi).2⟩⟩
  · intro u hu v hv hn i hi j hj
    by_cases hut : u = t
    · subst u
      rw [(ho hv hn.symm he).2.1] at hj
      exact (hd i hi).1 v hv hn.symm j hj
    · by_cases hvt : v = t
      · subst v
        rw [(ho hu hut he).2.1] at hi
        exact ((hd j hj).1 u hu hut i hi).flip
      · rw [(ho hu hut he).2.1] at hi
        rw [(ho hv hvt he).2.1] at hj
        exact hW.1.2.2.1 u hu v hv hn i hi j hj

/-- Every aligned pointer field in a typed world record survives insertion. -/
theorem merge_set_record_word_kept {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post)
    (g : String) (sz k : Nat) (hr : (g, sz) ∈ typedRecords)
    (hg : ofString g ≠ ofString "heap_ptr") (hn : globN s g ≠ 0)
    (hk : k % 8 = 0) (hb : k + 8 ≤ sz) :
    memW post (globN post g + k) = memW s (globN s g + k) := by
  have hglob : globN post g = globN s g :=
    globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString g) (by simpa using hg))
  have hm := typedRecord_mem_fixedObjects s hr
  simp only [hn, ↓reduceIte] at hm
  exact InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
    hA.2 hW.2.2.1 g sz hr hglob hn (merge_set_fixed_word_unhit hA hW ht he _ hm) hk hb

/-- Insertion preserves all direct world table roots. -/
theorem merge_set_direct_roots {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post) :
    (∀ k ∈ wsTableSlots, globN post "ws" ≠ 0 → RootIn S (memW post (globN post "ws" + k))) ∧
    (∀ k ∈ bsTableSlots, globN post "bs" ≠ 0 → RootIn S (memW post (globN post "bs" + k))) ∧
    (∀ k ∈ tsTableSlots, globN post "ts" ≠ 0 → RootIn S (memW post (globN post "ts" + k))) ∧
    (∀ g ∈ globalTableRoots, RootIn S (globN post g)) := by
  have hgs := InitECandidate.Solver.Wave8Contracts.M08.worldGlobalsSame_of_kept
    (gw := ["heap_ptr"]) he.2.2.2.2.2.2.2 (fun _ h => Or.inl (by simpa using h))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk hn
    rw [hgs.1 ("ws", 40) (by simp [globalBuffers])] at hn
    have hb : k % 8 = 0 ∧ k + 8 ≤ 40 := by
      simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> decide
    rw [merge_set_record_word_kept hA hW ht he "ws" 40 k (by decide) (by decide) hn hb.1 hb.2]
    exact hW.1.2.2.2.1 k hk hn
  · intro k hk hn
    rw [hgs.1 ("bs", 80) (by simp [globalBuffers])] at hn
    have hb : k % 8 = 0 ∧ k + 8 ≤ 80 := by
      simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [merge_set_record_word_kept hA hW ht he "bs" 80 k (by decide) (by decide) hn hb.1 hb.2]
    exact hW.1.2.2.2.2.1 k hk hn
  · intro k hk hn
    rw [hgs.1 ("ts", 72) (by simp [globalBuffers])] at hn
    have hb : k % 8 = 0 ∧ k + 8 ≤ 72 := by
      simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [merge_set_record_word_kept hA hW ht he "ts" 72 k (by decide) (by decide) hn hb.1 hb.2]
    exact hW.1.2.2.2.2.2.1 k hk hn
  · intro g hg
    rw [hgs.2.1 g hg]
    exact hW.1.2.2.2.2.2.2.1 g hg

/-- Installing a fresh block inner pointer preserves the complete table invariant. -/
theorem merge_set_tables_typed {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t inner : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post)
    (hbs : globN s "bs" ≠ 0) (ht0 : t ≠ 0)
    (htbs : t = memW s (globN s "bs" + 32))
    (hi : inner ∈ S) (hk : hdr s inner 0 = roleKeyLen "bs.inner")
    (hf : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ inner)
    (hv : WkBal.HtabSetValuesPost s post t inner) :
    TablesTyped post S := by
  have hfix := (merge_set_fixed_typed hA hW ht he hbs ht0 htbs).1
  have hgeom := merge_set_tables_geometry hA hW ht he hfix
  have hroots := merge_set_direct_roots hA hW ht he
  have hbal := merge_set_bal_objects_kept hA hW ht he hbs ht0 htbs
  refine ⟨hW.1.1, hgeom.1, hgeom.2, hroots.1, hroots.2.1, hroots.2.2.1,
    hroots.2.2.2, ?_, ?_, ?_, (merge_set_blockOutObjects_kept hA hW ht he).2,
    merge_set_world_roles hA hW ht he hbs ht0 htbs hi hk hf hv⟩
  · intro _ _
    have hp := (merge_set_bs_outer_kept hA hW ht he hbs).2
    rw [hp, ← htbs]
    apply merge_set_values_owned hv _ hi
    rw [htbs]
    exact hW.1.2.2.2.2.2.2.2.1 hbs (htbs ▸ ht)
  · intro hn hu
    have hg : globN post "ts" = globN s "ts" :=
      globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString "ts") (by decide))
    rw [hg] at hn
    have hp := merge_set_record_word_kept hA hW ht he "ts" 72 32
      (by decide) (by decide) hn (by decide) (by decide)
    rw [hp] at hu ⊢
    have hunz : memW s (globN s "ts" + 32) ≠ 0 := by
      have hh := (hW.1.2.1 _ hu).1.1 (memW s (globN s "ts" + 32), 88)
        (by simp [htabFootprint])
      have hh' := hh.1.1
      have hs : 0 < sourceBase := by decide
      dsimp at hh'
      omega
    have hb : (t, "bs+32") ∈ worldRoleSlots s := by
      rw [htbs]
      apply R16WkMarkAccountCreated.mem_worldRoleSlots_recRole s "bs" 32 _ hbs
        (by rwa [← htbs])
      simp [recRoles, hbs]
    have hx : (memW s (globN s "ts" + 32), "ts+32") ∈ worldRoleSlots s := by
      apply R16WkMarkAccountCreated.mem_worldRoleSlots_recRole s "ts" 32 _ hn hunz
      simp [recRoles, hn]
    have hne := R16WkMarkAccountCreated.slot_ne_of_diff_nonshared_role
      hW.1.2.2.2.2.2.2.2.2.2.2.2 hx hb (by decide)
    exact InitECandidate.Solver.Wave8Contracts.M08.htabValuesIn_congr_unhit
      (hW.1.2.1 _ hu).1 (merge_set_other_table_unhit hA hW ht he _ hu hne)
      (fun _ hm => hm) (hW.1.2.2.2.2.2.2.2.2.1 hn hu)
  · intro ad had
    have hads : ad ∈ balRecords s := by
      rwa [merge_set_bs_balRecords_kept hA hW ht he hbs ht0 htbs] at had
    obtain ⟨e0, e8, _, hl, hll⟩ := hbal.2 ad had
    have h := hW.1.2.2.2.2.2.2.2.2.2.1 ad hads
    exact ⟨e0 ▸ h.1, e8 ▸ h.2.1, hl, hll⟩

/-- Insertion frames both trie records and their byte-valued nibble paths. -/
theorem merge_set_nodes_kept {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post) (hbe : post.be = s.be) :
    NodeHeap post Nd ∧ nodeExtents post Nd = nodeExtents s Nd := by
  have hag : AllocatorGrows s post := by
    refine ⟨he.2.2.2.2.1, ?_⟩
    rw [globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString "scratch_ptr") (by decide))]
  apply R16Shards.nodeHeap_congr_unhit hA.1 he.1.1 hbe hag hW.2.2.2.1
  intro o ho
  have ha : o = (0, 0) ∨ Allocated s o := by
    unfold nodeExtents at ho
    obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
    rcases hno with rfl | rfl
    · exact Or.inr (hW.2.2.2.1.1 n hn).2.1
    · unfold nodePath
      split_ifs with hc
      · rcases (hW.2.2.2.1.1 n hn).2.2.2.2.2.2.1 hc.1 with hz | ⟨_, hal, _⟩
        · exact False.elim (hc.2 hz)
        · exact Or.inr hal
      · exact Or.inl rfl
  apply R16Shards.ivlUnhit_of_frameOutside_aligned he.2.2.2.2.2.2.1
  · intro hz
    unfold nodeExtents at ho
    obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
    rcases hno with rfl | rfl
    · have hp : 0 < nodeSize (memW s n) := by
        unfold nodeSize
        split_ifs <;> decide
      exact False.elim (Nat.ne_of_gt hp hz)
    · unfold nodePath at hz ⊢
      split_ifs with hc
      · simp [hc] at hz
      · rfl
  · intro j hj
    have hw := ((hW.1.2.1 t ht).1.1 j hj).2
    exact ⟨hw.1, hw.2.1⟩
  · have h1 : globN s "heap_ptr" % 8 = 0 := hA.2.2.2.2.2.2.1
    have h2 : globN post "heap_ptr" % 8 = 0 := he.1.2.2.2.2.2.2.1
    exact ⟨h1, by omega⟩
  · exact (hW.2.2.2.2.1 o ho).1 t ht
  · apply R16WkMarkAccountCreated.disj_fresh_of_zero_or_allocated hA.2 he.1.2 he.2.2.2.2.1
    rcases ha with rfl | hal
    · exact Or.inl rfl
    · exact Or.inr hal

/-- Block outer insertion preserves trie geometry and all witness trie roots. -/
theorem merge_set_tries_typed {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post) (hbe : post.be = s.be)
    (hbs : globN s "bs" ≠ 0) (ht0 : t ≠ 0)
    (htbs : t = memW s (globN s "bs" + 32)) :
    TriesTypedWith post S Nd := by
  obtain ⟨hN, hne⟩ := merge_set_nodes_kept hA hW ht he hbe
  have hfix := (merge_set_fixed_typed hA hW ht he hbs ht0 htbs).1
  refine ⟨hN, ?_, ?_⟩
  · rw [hne, hfix]
    intro o ho
    refine ⟨?_, (hW.2.2.2.2.1 o ho).2⟩
    intro u hu i hi
    by_cases hut : u = t
    · subst u
      exact ((merge_set_footprint_disjoint hA hW ht he i hi).2.2 o ho).flip
    · rw [(merge_set_other_table_frame hA hW ht hu hut he).2.1] at hi
      exact (hW.2.2.2.2.1 o ho).1 u hu i hi
  · intro hn
    have hg : globN post "ws" = globN s "ws" :=
      globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString "ws") (by decide))
    rw [hg] at hn
    have e24 : memW post (globN post "ws" + 24) = memW s (globN s "ws" + 24) :=
      merge_set_record_word_kept hA hW ht he "ws" 40 24
      (by decide) (by decide) hn (by decide) (by decide)
    have e32 : memW post (globN post "ws" + 32) = memW s (globN s "ws" + 32) :=
      merge_set_record_word_kept hA hW ht he "ws" 40 32
      (by decide) (by decide) hn (by decide) (by decide)
    rw [e24, e32]
    refine ⟨(hW.2.2.2.2.2 hn).1, ?_⟩
    intro hu i hi
    have huz : memW s (globN s "ws" + 32) ≠ 0 :=
      WkBal.htab_nonzero_of_wf (hW.1.2.1 _ hu).1
    have hb : (t, "bs+32") ∈ worldRoleSlots s := by
      rw [htbs]
      apply R16WkMarkAccountCreated.mem_worldRoleSlots_recRole s "bs" 32 _ hbs
        (by rwa [← htbs])
      simp [recRoles, hbs]
    have hx : (memW s (globN s "ws" + 32), "ws+32") ∈ worldRoleSlots s := by
      apply R16WkMarkAccountCreated.mem_worldRoleSlots_recRole s "ws" 32 _ hn huz
      simp [recRoles, hn]
    have hut := R16WkMarkAccountCreated.slot_ne_of_diff_nonshared_role
      hW.1.2.2.2.2.2.2.2.2.2.2.2 hx hb (by decide)
    have hh := (merge_set_other_table_frame hA hW ht hu hut he).2.2
    have hv := merge_set_other_values_kept hA hW ht hu hut he
    rw [hh 3 (by decide)] at hi
    have hget := congrArg (fun l : List Nat => l[i]?) hv
    simp only [htabValues, List.getElem?_map, List.getElem?_range,
      hh 3 (by decide), hi, Option.map_some, Option.some.injEq] at hget
    rw [hget]
    exact (hW.2.2.2.2.2 hn).2 hu i hi

/-- Full world typing survives installing a fresh inner table in the block outer table. -/
theorem merge_set_world_typed {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t inner : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post) (hbe : post.be = s.be)
    (hbs : globN s "bs" ≠ 0) (ht0 : t ≠ 0)
    (htbs : t = memW s (globN s "bs" + 32))
    (hi : inner ∈ S) (hk : hdr s inner 0 = roleKeyLen "bs.inner")
    (hf : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ inner)
    (hv : WkBal.HtabSetValuesPost s post t inner) :
    WorldTypedWith post S Nd := by
  exact ⟨merge_set_tables_typed hA hW ht he hbs ht0 htbs hi hk hf hv,
    (merge_set_journal_kept hA hW ht he).2,
    (merge_set_fixed_typed hA hW ht he hbs ht0 htbs).2,
    merge_set_tries_typed hA hW ht he hbe hbs ht0 htbs⟩

/-- Outer insertion preserves the existential world invariant using the same
table and node witnesses. -/
theorem merge_set_world_ok {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {t inner : Nat}
    (hW : WorldOK s)
    (he : SoloHtabSet.HtabExitAt t s post) (hbe : post.be = s.be)
    (hbs : globN s "bs" ≠ 0) (ht0 : t ≠ 0)
    (htbs : t = memW s (globN s "bs" + 32))
    (howned : ∀ S Nd, WorldTypedWith s S Nd → t ∈ S ∧ inner ∈ S)
    (hk : hdr s inner 0 = roleKeyLen "bs.inner")
    (hf : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ inner)
    (hv : WkBal.HtabSetValuesPost s post t inner) :
    WorldOK post := by
  obtain ⟨S, htyped⟩ := hW.2
  obtain ⟨Nd, htyped⟩ := (WkBal.worldTyped_iff_with s S).1 htyped
  obtain ⟨ht, hi⟩ := howned S Nd htyped
  refine ⟨he.1, S, (WkBal.worldTyped_iff_with post S).2 ⟨Nd, ?_⟩⟩
  exact merge_set_world_typed hW.1 htyped ht he hbe hbs ht0 htbs hi hk hf hv

/-- Outer insertion only reuses existing owned intervals or allocates fresh heap. -/
theorem merge_set_owned_grows {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post) (hbe : post.be = s.be)
    (hbs : globN s "bs" ≠ 0) (ht0 : t ≠ 0)
    (htbs : t = memW s (globN s "bs" + 32)) :
    OwnedGrows s post (worldOwned s S Nd) (worldOwned post S Nd) := by
  have hfix := (merge_set_fixed_typed hA hW ht he hbs ht0 htbs).1
  have hnodes := (merge_set_nodes_kept hA hW ht he hbe).2
  intro o ho
  unfold worldOwned at ho
  rcases List.mem_append.1 ho with ho | ho
  · rcases List.mem_append.1 ho with ho | ho
    · obtain ⟨u, hu, hi⟩ := List.mem_flatMap.1 ho
      by_cases hut : u = t
      · subst u
        rcases (he.2.2.2.2.2.1 o hi).2 with ⟨j, hj, hin⟩ | hin
        · exact Or.inr (Or.inl ⟨j, List.mem_append_left _
            (List.mem_append_left _ (List.mem_flatMap.2 ⟨t, ht, hj⟩)), hin⟩)
        · exact Or.inr (Or.inr ⟨hin.1, by
            have hh := he.2.2.2.2.1
            dsimp [Inside] at hin ⊢
            omega⟩)
      · rw [(merge_set_other_table_frame hA hW ht hu hut he).2.1] at hi
        exact Or.inr (Or.inl ⟨o, List.mem_append_left _
          (List.mem_append_left _ (List.mem_flatMap.2 ⟨u, hu, hi⟩)), le_rfl, le_rfl⟩)
    · rw [hfix] at ho
      exact Or.inr (Or.inl ⟨o, List.mem_append_left _
        (List.mem_append_right _ ho), le_rfl, le_rfl⟩)
  · rw [hnodes] at ho
    exact Or.inr (Or.inl ⟨o, List.mem_append_right _ ho, le_rfl, le_rfl⟩)

/-- The complete relational world step for installing a fresh block inner table. -/
theorem merge_set_worldStepSc {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {t inner : Nat} (hW : WorldOK s)
    (he : SoloHtabSet.HtabExitAt t s post) (hbe : post.be = s.be)
    (hbs : globN s "bs" ≠ 0) (ht0 : t ≠ 0)
    (htbs : t = memW s (globN s "bs" + 32))
    (howned : ∀ S Nd, WorldTypedWith s S Nd → t ∈ S ∧ inner ∈ S)
    (hk : hdr s inner 0 = roleKeyLen "bs.inner")
    (hf : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ inner)
    (hv : WkBal.HtabSetValuesPost s post t inner) :
    WorldStepSc (bufRegions []) ["heap_ptr"] stdKeep NoExtra s r post := by
  have hsp : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString "scratch_ptr") (by decide))
  refine ⟨⟨he.1, he.2.2.2.2.1, he.2.2.2.2.2.2.2, ?_, ?_⟩, by rw [hsp]⟩
  · obtain ⟨S, hw⟩ := hW.2
    obtain ⟨Nd, hw⟩ := (WkBal.worldTyped_iff_with s S).1 hw
    have ht := (howned S Nd hw).1
    intro rec hrec hn k hks _
    have hrec_sz : ∃ sz, (rec.1, sz) ∈ typedRecords ∧
        ofString rec.1 ≠ ofString "heap_ptr" ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
      simp only [stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · refine ⟨40, by decide, by decide, ?_⟩; simp at hks; omega
      · refine ⟨80, by decide, by decide, ?_⟩; simp at hks; omega
      · refine ⟨72, by decide, by decide, ?_⟩; simp at hks; omega
      · refine ⟨88, by decide, by decide, ?_⟩; simp at hks; omega
    obtain ⟨sz, hrec, hg, hk8, hbound⟩ := hrec_sz
    have hh := merge_set_record_word_kept hW.1 hw ht he rec.1 sz k hrec hg hn hk8 hbound
    rwa [globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString rec.1)
      (by simpa using hg))] at hh
  · intro S Nd hw _
    obtain ⟨ht, hi⟩ := howned S Nd hw
    refine ⟨S, Nd, fun _ h => h,
      merge_set_world_typed hW.1 hw ht he hbe hbs ht0 htbs hi hk hf hv,
      merge_set_owned_grows hW.1 hw ht he hbe hbs ht0 htbs, ?_, trivial⟩
    intro a hkeep hfree
    apply he.2.2.2.2.2.2.1 a
    · intro j hj hh
      apply hkeep j _ hh
      apply List.mem_append_left
      apply List.mem_append_left
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_flatMap.2 ⟨t, ht, hj⟩))
    · intro hh
      apply hfree
      have hpmax := he.1.2.2.1
      obtain ⟨h1, h2⟩ := hh
      unfold heapFree CellHits at *
      dsimp at h1 h2 ⊢
      omega

/-- The evaluator-level outer insertion inherits the complete world step. -/
theorem merge_set_call_worldStepSc {F : Type}
    (s : PanSemStateFiniteExact 64 F) (et ek ev : ExpHOL 64)
    (tw kw iw : BitVec 64)
    (ht : evalAt s et = some (.val (.word tw)))
    (hk : evalAt s ek = some (.val (.word kw)))
    (hi : evalAt s ev = some (.val (.word iw)))
    (hW : WorldOK s) (hbs : globN s "bs" ≠ 0) (ht0 : tw.toNat ≠ 0)
    (htbs : tw.toNat = memW s (globN s "bs" + 32))
    (howned : ∀ S Nd, WorldTypedWith s S Nd → tw.toNat ∈ S ∧ iw.toNat ∈ S)
    (hkey : hdr s iw.toNat 0 = roleKeyLen "bs.inner")
    (hf : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ iw.toNat)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set") [et, ek, ev])).1) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set") [et, ek, ev])
    WorldStepSc (bufRegions []) ["heap_ptr"] stdKeep NoExtra s out.1 out.2 := by
  obtain ⟨S, hw⟩ := hW.2
  obtain ⟨Nd, hw⟩ := (WkBal.worldTyped_iff_with s S).1 hw
  have htab := (hw.1.2.1 tw.toNat (howned S Nd hw).1).1
  obtain ⟨he, hv, hbe, _, _⟩ := merge_set_call_flow_props s et ek ev tw kw iw
    ht hk hi hW.1 htab
      (fun i him => ((hw.1.2.1 tw.toNat (howned S Nd hw).1).2 i him).1) hfr
  exact merge_set_worldStepSc hW he hbe hbs ht0 htbs howned hkey hf hv

/-- Installing the fresh inner table establishes the entry frame for its union. -/
theorem merge_set_call_union_entry {F : Type}
    (s : PanSemStateFiniteExact 64 F) (et ek : ExpHOL 64)
    (tw kw iw : BitVec 64)
    (ht : evalAt s et = some (.val (.word tw)))
    (hk : evalAt s ek = some (.val (.word kw)))
    (hi : s.locals.lookup (ofString "binner") = some (.val (.word iw)))
    (hW : WorldOK s) (hbs : globN s "bs" ≠ 0) (ht0 : tw.toNat ≠ 0)
    (htbs : tw.toNat = memW s (globN s "bs" + 32))
    (howned : ∀ S Nd, WorldTypedWith s S Nd → tw.toNat ∈ S ∧ iw.toNat ∈ S)
    (hkey : hdr s iw.toNat 0 = roleKeyLen "bs.inner")
    (hf : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ iw.toNat)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set")
        [et, ek, .var .local (ofString "binner")])).1) :
    let post := (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set")
        [et, ek, .var .local (ofString "binner")])).2
    WorldOK post ∧ globN post "bs" ≠ 0 ∧
      memW post (globN post "bs" + 32) ≠ 0 ∧
      locN post "binner" ∈ htabValues post (memW post (globN post "bs" + 32)) := by
  have hiv : evalAt s (.var .local (ofString "binner")) = some (.val (.word iw)) := by
    simpa [evalAt, evalHOLExact] using hi
  have hs := merge_set_call_worldStepSc s et ek _ tw kw iw ht hk hiv
    hW hbs ht0 htbs howned hkey hf hfr
  obtain ⟨S, hw⟩ := hW.2
  obtain ⟨Nd, hw⟩ := (WkBal.worldTyped_iff_with s S).1 hw
  have htS := (howned S Nd hw).1
  have hwf := (hw.1.2.1 tw.toNat htS).1
  have hal : ∀ i ∈ htabFootprint s tw.toNat, Allocated s i :=
    fun i him => ((hw.1.2.1 tw.toNat htS).2 i him).1
  have hp := merge_set_call_flow_props s et ek _ tw kw iw ht hk hiv hW.1 hwf hal hfr
  have hm := merge_set_call_bound_member s et ek tw kw iw ht hk hi hW.1 hwf hal hfr
  have hg := globN_eq_of_lookup (hp.1.2.2.2.2.2.2.2 (ofString "bs") (by decide))
  have hb := merge_set_bs_outer_kept hW.1 hw htS hp.1 hbs
  dsimp only
  refine ⟨hs.worldOK_bufs (by intro p hp; simp at hp) hW, ?_, ?_, ?_⟩
  · rwa [hg]
  · rwa [hb.2, ← htbs]
  · rw [hb.2, ← htbs]
    exact hm.2

/-- Standard heap-only effects fit the storage merge's withdrawal mask. -/
theorem merge_heap_step_withdrawal {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (h : WorldStepSc (bufRegions []) ["heap_ptr"] stdKeep NoExtra s r post) :
    WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra s r post := by
  apply worldStepSc_mono_mask (B1 := []) (B2 := withdrawalBufs)
    (gw1 := ["heap_ptr"]) (gw2 := withdrawalGlobals) (by simp) (by decide) _ h
  intro rec hrec k hk
  simp only [withdrawalKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
  rcases hrec with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [stdKeep], hk⟩
  · exact ⟨_, by simp [stdKeep], hk⟩
  · cases hk
  · exact ⟨_, by simp [stdKeep], hk⟩

/-- The insertion and subsequent inner union compose on every flowing merge exit. -/
theorem eval_merge_set_then_union {F : Type}
    (s : PanSemStateFiniteExact 64 F) (et ek src : ExpHOL 64)
    (tw kw iw : BitVec 64)
    (ht : evalAt s et = some (.val (.word tw)))
    (hk : evalAt s ek = some (.val (.word kw)))
    (hi : s.locals.lookup (ofString "binner") = some (.val (.word iw)))
    (hc : s.code = originalRuntimeCode)
    (hW : WorldOK s) (hbs : globN s "bs" ≠ 0) (ht0 : tw.toNat ≠ 0)
    (htbs : tw.toNat = memW s (globN s "bs" + 32))
    (howned : ∀ S Nd, WorldTypedWith s S Nd → tw.toNat ∈ S ∧ iw.toNat ∈ S)
    (hkey : hdr s iw.toNat 0 = roleKeyLen "bs.inner")
    (hf : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ iw.toNat)
    (hnt : (evaluateHOLFiniteState s (.seq
      (.call (some (none, none)) (ofString "htab_set")
        [et, ek, .var .local (ofString "binner")])
      (.call (some (none, none)) (ofString "htab_union_into")
        [.var .local (ofString "binner"), src]))).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s (.seq
      (.call (some (none, none)) (ofString "htab_set")
        [et, ek, .var .local (ofString "binner")])
      (.call (some (none, none)) (ofString "htab_union_into")
        [.var .local (ofString "binner"), src]))).1) :
    let out := evaluateHOLFiniteState s (.seq
      (.call (some (none, none)) (ofString "htab_set")
        [et, ek, .var .local (ofString "binner")])
      (.call (some (none, none)) (ofString "htab_union_into")
        [.var .local (ofString "binner"), src]))
    WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra s out.1 out.2 := by
  have hiv : evalAt s (.var .local (ofString "binner")) = some (.val (.word iw)) := by
    simpa [evalAt, evalHOLExact] using hi
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases he : evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set")
        [et, ek, .var .local (ofString "binner")]) with ⟨r, mid⟩
  simp only [he] at hnt hfr ⊢
  cases r with
  | none =>
    have hflow : FlowingOrResumes (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "htab_set")
          [et, ek, .var .local (ofString "binner")])).1 := by
      rw [he]; exact Or.inl rfl
    have hs := merge_set_call_worldStepSc s et ek _ tw kw iw ht hk hiv
      hW hbs ht0 htbs howned hkey hf hflow
    have hp := merge_set_call_union_entry s et ek tw kw iw ht hk hi
      hW hbs ht0 htbs howned hkey hf hflow
    rw [he] at hs hp
    have hcm := (PanRunBounded.evaluateHOLFiniteState_metadata s
      (.call (some (none, none)) (ofString "htab_set")
        [et, ek, .var .local (ofString "binner")])).1
    rw [he] at hcm
    exact withdrawalStep_trans (merge_heap_step_withdrawal hs)
      (merge_heap_step_withdrawal (eval_call_union_bs_inner mid src (hcm.trans hc)
        hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 hnt hfr))
  | some r =>
    have hflow : FlowingOrResumes (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "htab_set")
          [et, ek, .var .local (ofString "binner")])).1 := by
      rwa [he]
    have hn := merge_set_call_flow_none s et ek _ tw kw iw ht hk hiv hc hflow
    rw [he] at hn
    contradiction

/-- Exact transaction-initialization export for the frozen C08 contract. -/
theorem wk_state_fresh_tx :
    WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr", "journal_n", "ts"]
      [("ws", [0, 8, 16, 24, 32]),
       ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "state_fresh_tx") := by
  obtain ⟨params, body, ret, hl, hb⟩ := wkSc_state_fresh_tx
  refine ⟨params, body, ret, hl, ?_⟩
  intro F s hc hW hex hnt hres
  exact (hb s hc hW hex hnt hres).1

/-- Allocation exposes its actual fresh binding to the storage continuation. -/
theorem eval_merge_new_continuation {F : Type}
    (s : PanSemStateFiniteExact 64 F) (cont : ProgHOL 64)
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hcont : ∀ (post : PanSemStateFiniteExact 64 F) (iw : BitVec 64),
      post.code = originalRuntimeCode → WorldOK post →
      post.locals.lookup (ofString "binner") = some (.val (.word iw)) →
      (∀ y, y ≠ ofString "binner" → post.locals.lookup y = s.locals.lookup y) →
      hdr post iw.toNat 0 = 32 →
      (∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ iw.toNat) →
      (evaluateHOLFiniteState post cont).1 ≠ some .timeOut →
      FlowingOrResumes (evaluateHOLFiniteState post cont).1 →
      WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra
        post (evaluateHOLFiniteState post cont).1 (evaluateHOLFiniteState post cont).2)
    (hnt : (evaluateHOLFiniteState s (.seq
      (.call (some (some (.local, ofString "binner"), none)) (ofString "htab_new")
        [.const 32#64, .const 8#64]) cont)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s (.seq
      (.call (some (some (.local, ofString "binner"), none)) (ofString "htab_new")
        [.const 32#64, .const 8#64]) cont)).1) :
    let out := evaluateHOLFiniteState s (.seq
      (.call (some (some (.local, ofString "binner"), none)) (ofString "htab_new")
        [.const 32#64, .const 8#64]) cont)
    WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra
      s out.1 out.2 := by
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases he : evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "binner"), none)) (ofString "htab_new")
        [.const 32#64, .const 8#64]) with ⟨r, post⟩
  simp only [he] at hnt hfr ⊢
  have hflow : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "binner"), none)) (ofString "htab_new")
        [.const 32#64, .const 8#64])).1 := by
    rw [he]
    cases r with
    | none => exact Or.inl rfl
    | some r => exact hfr
  have hn := merge_new_call_flow_none s (ofString "binner") 32#64 8#64 hc hflow
  rw [he] at hn
  cases hn
  have hs := merge_new_call_worldStep s (ofString "binner") 32#64 8#64
    hW (by decide) (by decide) hflow
  rw [he] at hs
  obtain ⟨S, hw⟩ := hW.2
  obtain ⟨Nd, hw⟩ := (WkBal.worldTyped_iff_with s S).1 hw
  have ho := merge_new_call_bound_owned s (ofString "binner") 32#64 8#64 S Nd
    hW.1 hw (by decide) (by decide) hflow
  rw [he] at ho
  obtain ⟨iw, hi, hl, _, _, hk, _, hf, _⟩ := ho
  have hm := (PanRunBounded.evaluateHOLFiniteState_metadata s
      (.call (some (some (.local, ofString "binner"), none)) (ofString "htab_new")
        [.const 32#64, .const 8#64])).1
  rw [he] at hm
  exact withdrawalStep_trans (merge_heap_step_withdrawal hs)
    (hcont post iw (hm.trans hc) (hs.worldOK_bufs (by intro p hp; simp at hp) hW)
      hi hl hk hf hnt hfr)

/-- Insertion needs the fresh inner table only in the caller-selected typings. -/
theorem merge_set_worldStepIn {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {t inner : Nat} {S Nd : List Nat}
    (hA : ArenaReady s) (hw : WorldTypedWith s S Nd) (ht : t ∈ S)
    (he : SoloHtabSet.HtabExitAt t s post) (hbe : post.be = s.be)
    (hbs : globN s "bs" ≠ 0) (ht0 : t ≠ 0)
    (htbs : t = memW s (globN s "bs" + 32))
    (hk : hdr s inner 0 = roleKeyLen "bs.inner")
    (hf : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ inner)
    (hv : WkBal.HtabSetValuesPost s post t inner) :
    WorldStepIn (fun _ => [t, inner]) (bufRegions []) ["heap_ptr"] stdKeep NoExtra s r post ∧
      globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by
  have hsp : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString "scratch_ptr") (by decide))
  refine ⟨⟨he.1, he.2.2.2.2.1, he.2.2.2.2.2.2.2, ?_, ?_⟩, by rw [hsp]⟩
  · intro rec hrec hn k hks _
    have hrec_sz : ∃ sz, (rec.1, sz) ∈ typedRecords ∧
        ofString rec.1 ≠ ofString "heap_ptr" ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
      simp only [stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · refine ⟨40, by decide, by decide, ?_⟩; simp at hks; omega
      · refine ⟨80, by decide, by decide, ?_⟩; simp at hks; omega
      · refine ⟨72, by decide, by decide, ?_⟩; simp at hks; omega
      · refine ⟨88, by decide, by decide, ?_⟩; simp at hks; omega
    obtain ⟨sz, hrec, hg, hk8, hbound⟩ := hrec_sz
    have hh := merge_set_record_word_kept hA hw ht he rec.1 sz k hrec hg hn hk8 hbound
    rwa [globN_eq_of_lookup (he.2.2.2.2.2.2.2 (ofString rec.1)
      (by simpa using hg))] at hh
  · intro S' Nd' hw' howned _
    have ht' : t ∈ S' := howned t (by simp)
    have hi' : inner ∈ S' := howned inner (by simp)
    refine ⟨S', Nd', fun _ h => h,
      merge_set_world_typed hA hw' ht' he hbe hbs ht0 htbs hi' hk hf hv,
      merge_set_owned_grows hA hw' ht' he hbe hbs ht0 htbs, ?_, trivial⟩
    intro a hkeep hfree
    apply he.2.2.2.2.2.2.1 a
    · intro j hj hh
      apply hkeep j _ hh
      apply List.mem_append_left
      apply List.mem_append_left
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_flatMap.2 ⟨t, ht', hj⟩))
    · intro hh
      apply hfree
      have hpmax := he.1.2.2.1
      obtain ⟨h1, h2⟩ := hh
      unfold heapFree CellHits at *
      dsimp at h1 h2 ⊢
      omega

/-- The evaluator insertion respects the caller's selected ownership witnesses. -/
theorem merge_set_call_worldStepIn {F : Type}
    (s : PanSemStateFiniteExact 64 F) (et ek ev : ExpHOL 64)
    (tw kw iw : BitVec 64) (S Nd : List Nat)
    (ht : evalAt s et = some (.val (.word tw)))
    (hk : evalAt s ek = some (.val (.word kw)))
    (hi : evalAt s ev = some (.val (.word iw)))
    (hA : ArenaReady s) (hw : WorldTypedWith s S Nd) (htS : tw.toNat ∈ S)
    (hbs : globN s "bs" ≠ 0) (ht0 : tw.toNat ≠ 0)
    (htbs : tw.toNat = memW s (globN s "bs" + 32))
    (hkey : hdr s iw.toNat 0 = roleKeyLen "bs.inner")
    (hf : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ iw.toNat)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set") [et, ek, ev])).1) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set") [et, ek, ev])
    WorldStepIn (fun _ => [tw.toNat, iw.toNat]) (bufRegions []) ["heap_ptr"]
      stdKeep NoExtra s out.1 out.2 ∧
      globN out.2 "scratch_ptr" ≤ globN s "scratch_ptr" := by
  obtain ⟨he, hv, hbe, _, _⟩ := merge_set_call_flow_props s et ek ev tw kw iw
    ht hk hi hA (hw.1.2.1 tw.toNat htS).1
      (fun i him => ((hw.1.2.1 tw.toNat htS).2 i him).1) hfr
  exact merge_set_worldStepIn hA hw htS he hbe hbs ht0 htbs hkey hf hv

/-- A selected ownership witness suffices to enter the union after insertion. -/
theorem merge_set_call_union_entry_with {F : Type}
    (s : PanSemStateFiniteExact 64 F) (et ek : ExpHOL 64)
    (tw kw iw : BitVec 64) (S Nd : List Nat)
    (ht : evalAt s et = some (.val (.word tw)))
    (hk : evalAt s ek = some (.val (.word kw)))
    (hi : s.locals.lookup (ofString "binner") = some (.val (.word iw)))
    (hA : ArenaReady s) (hw : WorldTypedWith s S Nd)
    (htS : tw.toNat ∈ S) (hiS : iw.toNat ∈ S)
    (hbs : globN s "bs" ≠ 0) (ht0 : tw.toNat ≠ 0)
    (htbs : tw.toNat = memW s (globN s "bs" + 32))
    (hkey : hdr s iw.toNat 0 = roleKeyLen "bs.inner")
    (hf : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ iw.toNat)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set")
        [et, ek, .var .local (ofString "binner")])).1) :
    let post := (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set")
        [et, ek, .var .local (ofString "binner")])).2
    WorldOK post ∧ WorldTypedWith post S Nd ∧ globN post "bs" ≠ 0 ∧
      memW post (globN post "bs" + 32) ≠ 0 ∧
      locN post "binner" ∈ htabValues post (memW post (globN post "bs" + 32)) := by
  have hiv : evalAt s (.var .local (ofString "binner")) = some (.val (.word iw)) := by
    simpa [evalAt, evalHOLExact] using hi
  have hwf := (hw.1.2.1 tw.toNat htS).1
  have hal : ∀ i ∈ htabFootprint s tw.toNat, Allocated s i :=
    fun i him => ((hw.1.2.1 tw.toNat htS).2 i him).1
  have hp := merge_set_call_flow_props s et ek _ tw kw iw ht hk hiv hA hwf hal hfr
  have hm := merge_set_call_bound_member s et ek tw kw iw ht hk hi hA hwf hal hfr
  have hb := merge_set_bs_outer_kept hA hw htS hp.1 hbs
  have hwp := merge_set_world_typed hA hw htS hp.1 hp.2.2.1 hbs ht0 htbs
    hiS hkey hf hp.2.1
  dsimp only
  refine ⟨⟨hp.1.1, S, (WkBal.worldTyped_iff_with _ S).2 ⟨Nd, hwp⟩⟩,
    hwp, ?_, ?_, ?_⟩
  · rwa [hb.1]
  · rwa [hb.2, ← htbs]
  · rw [hb.2, ← htbs]
    exact hm.2

/-- Caller-selected heap effects fit the withdrawal frame without losing ownership guards. -/
theorem merge_heap_stepIn_withdrawal
    {T : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat}
    {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)}
    (h : WorldStepIn T (bufRegions []) ["heap_ptr"] stdKeep NoExtra s r post) :
    WorldStepIn T (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra s r post := by
  obtain ⟨hA, hhp, hG, hK, hW⟩ := h
  refine ⟨hA, hhp, ?_, ?_, ?_⟩
  · intro k hk
    apply hG k
    intro hm
    apply hk
    have he : k = ofString "heap_ptr" := by simpa using hm
    simp [withdrawalGlobals, he]
  · intro rec hrec hn k hk hno
    have hkeep : ∃ ks, (rec.1, ks) ∈ stdKeep ∧ k ∈ ks := by
      simp only [withdrawalKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp [stdKeep], hk⟩
      · exact ⟨_, by simp [stdKeep], hk⟩
      · cases hk
      · exact ⟨_, by simp [stdKeep], hk⟩
    obtain ⟨ks, hks, hk'⟩ := hkeep
    exact hK (rec.1, ks) hks hn k hk' (by simp [bufRegions])
  · intro S Nd hw ht _
    obtain ⟨S', Nd', hsub, hw', hg, hframe, hq⟩ := hW S Nd hw ht (by simp [bufRegions, IvlsDisj])
    refine ⟨S', Nd', hsub, hw', hg, ?_, hq⟩
    intro a ha hfree
    apply hframe a _ hfree
    intro i hi hhit
    simp only [bufRegions, List.map_nil, List.append_nil] at hi
    rcases List.mem_append.1 hi with hi | hi
    · exact ha i (List.mem_append_left _ (List.mem_append_left _ hi)) hhit
    · exact ha i (List.mem_append_right _ hi) hhit

/-- Allocation and insertion share the extended table witness used by the inner union. -/
theorem merge_new_set_union_entry {F : Type}
    (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat)
    (hA : ArenaReady s) (hw : WorldTypedWith s S Nd)
    (hnew : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "binner"), none)) (ofString "htab_new")
        [.const 32#64, .const 8#64])).1) :
    let mid := (evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "binner"), none)) (ofString "htab_new")
        [.const 32#64, .const 8#64])).2
    ∃ iw : BitVec 64, mid.locals.lookup (ofString "binner") = some (.val (.word iw)) ∧
      ∀ (et ek : ExpHOL 64) (tw kw : BitVec 64),
      evalAt mid et = some (.val (.word tw)) →
      evalAt mid ek = some (.val (.word kw)) →
      tw.toNat ∈ S → globN mid "bs" ≠ 0 → tw.toNat ≠ 0 →
      tw.toNat = memW mid (globN mid "bs" + 32) →
      FlowingOrResumes (evaluateHOLFiniteState mid
        (.call (some (none, none)) (ofString "htab_set")
          [et, ek, .var .local (ofString "binner")])).1 →
      let post := (evaluateHOLFiniteState mid
        (.call (some (none, none)) (ofString "htab_set")
          [et, ek, .var .local (ofString "binner")])).2
      WorldOK post ∧ WorldTypedWith post (S ++ [iw.toNat]) Nd ∧
        globN post "bs" ≠ 0 ∧ memW post (globN post "bs" + 32) ≠ 0 ∧
        locN post "binner" ∈ htabValues post (memW post (globN post "bs" + 32)) := by
  dsimp only
  obtain ⟨iw, hi, _, _, _, hk, _, hf, hw', _⟩ :=
    merge_new_call_bound_owned s (ofString "binner") 32#64 8#64 S Nd
      hA hw (by decide) (by decide) hnew
  obtain ⟨_, _, _, hAm, _⟩ := merge_new_call_flow_props s (ofString "binner")
    32#64 8#64 hA (by decide) (by decide) hnew
  refine ⟨iw, hi, ?_⟩
  intro et ek tw kw ht hkey htS hbs ht0 htbs hset
  exact merge_set_call_union_entry_with _ et ek tw kw iw (S ++ [iw.toNat]) Nd
    ht hkey hi hAm hw' (List.mem_append_left _ htS) (by simp) hbs ht0 htbs
    (by rw [show roleKeyLen "bs.inner" = 32 by decide]; exact hk) hf hset

/-- A guarded insertion composes with an ordinary withdrawal-framed suffix. -/
theorem withdrawalStepIn_trans
    {T : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat}
    {F : Type} {s1 s2 s3 : PanSemStateFiniteExact 64 F}
    {r1 r2 : Option (PanSemResultExact 64)}
    (h12 : WorldStepIn T (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra s1 r1 s2)
    (hsc12 : globN s2 "scratch_ptr" ≤ globN s1 "scratch_ptr")
    (h23 : WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra s2 r2 s3) :
    WorldStepIn T (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra s1 r2 s3 ∧
      globN s3 "scratch_ptr" ≤ globN s1 "scratch_ptr" := by
  have hbuf : bufRegions withdrawalBufs s2 = bufRegions withdrawalBufs s1 := by
    unfold bufRegions
    apply List.map_congr_left
    intro p hp
    have hn : ofString p.1 ∉ withdrawalGlobals.map ofString := by
      simp only [withdrawalBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide
    have hg := globN_eq_of_lookup (h12.2.2.1 (ofString p.1) hn)
    simp only [bufferRegion, hg]
  have hframe : globN s2 "frame_mem_ptr" = globN s1 "frame_mem_ptr" :=
    globN_eq_of_lookup (h12.2.2.1 (ofString "frame_mem_ptr") (by decide))
  have hroots : ∀ rec ∈ withdrawalKeep, ∀ k ∈ rec.2,
      globN s2 rec.1 = globN s1 rec.1 := by
    intro rec hrec k hk
    apply globN_eq_of_lookup (h12.2.2.1 (ofString rec.1) ?_)
    simp only [withdrawalKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
    rcases hrec with rfl | rfl | rfl | rfl
    · decide
    · decide
    · cases hk
    · decide
  obtain ⟨hA2, hhp12, hG12, hK12, hW12⟩ := h12
  obtain ⟨⟨hA3, hhp23, hG23, hK23, hW23⟩, hsc23⟩ := h23
  refine ⟨⟨hA3, le_trans hhp12 hhp23,
    fun k hk => (hG12 k hk).trans (hG23 k hk), ?_, ?_⟩, le_trans hsc23 hsc12⟩
  · intro rec hrec hnz k hk hno
    have hg := hroots rec hrec k hk
    have h2 := hK23 rec hrec (by rw [hg]; exact hnz) k hk
      (by change ∀ i ∈ bufRegions withdrawalBufs s2, ¬ CellHits (globN s2 rec.1 + k) i
          rw [hbuf, hg]; exact hno)
    rw [hg] at h2
    exact h2.trans (hK12 rec hrec hnz k hk hno)
  · intro S Nd hWT1 hT hD1
    obtain ⟨S2, Nd2, hsub12, hWT2, hOG12, hFO12, _⟩ := hW12 S Nd hWT1 hT hD1
    obtain ⟨S3, Nd3, hsub23, hWT3, hOG23, hFO23, _⟩ :=
      hW23 S2 Nd2 hWT2 (validBufList_disj validBufList_withdrawal hWT2)
    refine ⟨S3, Nd3, fun t ht => hsub23 t (hsub12 t ht), hWT3, ?_, ?_, trivial⟩
    · intro o ho
      rcases hOG23 o ho with rfl | ⟨j, hj, hin_oj⟩ | hin_o23
      · exact Or.inl rfl
      · rcases hOG12 j hj with rfl | ⟨k, hk, hin_jk⟩ | hin_j12
        · left
          rcases o with ⟨o1, o2⟩
          dsimp only [Inside] at hin_oj
          have ho1 : o1 = 0 := by omega
          have ho2 : o2 = 0 := by omega
          rw [ho1, ho2]
        · exact Or.inr (Or.inl ⟨k, hk, le_trans hin_jk.1 hin_oj.1, le_trans hin_oj.2 hin_jk.2⟩)
        · exact Or.inr (Or.inr ⟨le_trans hin_j12.1 hin_oj.1,
            le_trans hin_oj.2 (le_trans hin_j12.2 hhp23)⟩)
      · exact Or.inr (Or.inr ⟨le_trans hhp12 hin_o23.1, hin_o23.2⟩)
    · intro a ha hhf
      have hm12 : s2.memory a = s1.memory a := hFO12 a ha hhf
      have hm23 : s3.memory a = s2.memory a := by
        apply hFO23 a
        · intro i hi hch
          obtain ⟨hc1, hc2⟩ := hch
          rcases List.mem_append.1 hi with hi1 | hfg2
          · rcases List.mem_append.1 hi1 with hwo2 | hR2
            · rcases hOG12 i hwo2 with rfl | ⟨k, hk, hin_ik⟩ | hin_i12
              · dsimp only at hc2; omega
              · exact ha k (List.mem_append_left _ (List.mem_append_left _ hk))
                  ⟨by dsimp only [Inside] at hin_ik; omega,
                   by dsimp only [Inside] at hin_ik; omega⟩
              · have hp2_lim : globN s2 "heap_ptr" ≤ heapLimit := hA2.2.2.1
                exact hhf ⟨by unfold heapFree; dsimp only [Inside] at hin_i12 ⊢; omega,
                           by unfold heapFree; dsimp only [Inside] at hin_i12 ⊢; omega⟩
            · change i ∈ bufRegions withdrawalBufs s2 at hR2
              rw [hbuf] at hR2
              exact ha i (List.mem_append_left _ (List.mem_append_right _ hR2)) ⟨hc1, hc2⟩
          · simp only [List.mem_singleton] at hfg2
            subst hfg2
            exact ha (freeGap s1) (List.mem_append_right _ (List.mem_singleton.2 rfl))
              ⟨by unfold freeGap at hc1 ⊢; dsimp only at hc1 ⊢; omega,
               by unfold freeGap at hc2 ⊢; dsimp only at hc2 ⊢; omega⟩
        · intro ⟨hc1, hc2⟩
          have hp2_lim : globN s2 "heap_ptr" ≤ heapLimit := hA2.2.2.1
          exact hhf ⟨by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega,
                     by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega⟩
      exact hm23.trans hm12

/-- Insertion followed by union preserves the caller-selected ownership frame. -/
theorem eval_merge_set_then_union_with {F : Type}
    (s : PanSemStateFiniteExact 64 F) (et ek src : ExpHOL 64)
    (tw kw iw : BitVec 64) (S Nd : List Nat)
    (ht : evalAt s et = some (.val (.word tw)))
    (hk : evalAt s ek = some (.val (.word kw)))
    (hi : s.locals.lookup (ofString "binner") = some (.val (.word iw)))
    (hc : s.code = originalRuntimeCode)
    (hA : ArenaReady s) (hw : WorldTypedWith s S Nd)
    (htS : tw.toNat ∈ S) (hiS : iw.toNat ∈ S)
    (hbs : globN s "bs" ≠ 0) (ht0 : tw.toNat ≠ 0)
    (htbs : tw.toNat = memW s (globN s "bs" + 32))
    (hkey : hdr s iw.toNat 0 = roleKeyLen "bs.inner")
    (hf : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ iw.toNat)
    (hnt : (evaluateHOLFiniteState s (.seq
      (.call (some (none, none)) (ofString "htab_set")
        [et, ek, .var .local (ofString "binner")])
      (.call (some (none, none)) (ofString "htab_union_into")
        [.var .local (ofString "binner"), src]))).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s (.seq
      (.call (some (none, none)) (ofString "htab_set")
        [et, ek, .var .local (ofString "binner")])
      (.call (some (none, none)) (ofString "htab_union_into")
        [.var .local (ofString "binner"), src]))).1) :
    let out := evaluateHOLFiniteState s (.seq
      (.call (some (none, none)) (ofString "htab_set")
        [et, ek, .var .local (ofString "binner")])
      (.call (some (none, none)) (ofString "htab_union_into")
        [.var .local (ofString "binner"), src]))
    WorldStepIn (fun _ => [tw.toNat, iw.toNat]) (bufRegions withdrawalBufs)
      withdrawalGlobals withdrawalKeep NoExtra s out.1 out.2 ∧
      globN out.2 "scratch_ptr" ≤ globN s "scratch_ptr" := by
  have hiv : evalAt s (.var .local (ofString "binner")) = some (.val (.word iw)) := by
    simpa [evalAt, evalHOLExact] using hi
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases he : evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set")
        [et, ek, .var .local (ofString "binner")]) with ⟨r, mid⟩
  simp only [he] at hnt hfr ⊢
  cases r with
  | none =>
    have hflow : FlowingOrResumes (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "htab_set")
          [et, ek, .var .local (ofString "binner")])).1 := by
      rw [he]; exact Or.inl rfl
    have hs := merge_set_call_worldStepIn s et ek _ tw kw iw S Nd ht hk hiv
      hA hw htS hbs ht0 htbs hkey hf hflow
    have hp := merge_set_call_union_entry_with s et ek tw kw iw S Nd ht hk hi
      hA hw htS hiS hbs ht0 htbs hkey hf hflow
    rw [he] at hs hp
    have hcm := (PanRunBounded.evaluateHOLFiniteState_metadata s
      (.call (some (none, none)) (ofString "htab_set")
        [et, ek, .var .local (ofString "binner")])).1
    rw [he] at hcm
    exact withdrawalStepIn_trans (merge_heap_stepIn_withdrawal hs.1) hs.2
      (merge_heap_step_withdrawal (eval_call_union_bs_inner mid src (hcm.trans hc)
        hp.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2 hnt hfr))
  | some r =>
    have hflow : FlowingOrResumes (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "htab_set")
          [et, ek, .var .local (ofString "binner")])).1 := by
      rwa [he]
    have hn := merge_set_call_flow_none s et ek _ tw kw iw ht hk hiv hc hflow
    rw [he] at hn
    contradiction

/-- A guarded suffix can use ownership explicitly supplied by the prefix. -/
theorem withdrawalStepSc_trans_owned
    {T : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat}
    {F : Type} {s1 s2 s3 : PanSemStateFiniteExact 64 F}
    {r1 r2 : Option (PanSemResultExact 64)}
    (h12 : WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra s1 r1 s2)
    (howned : ∀ S Nd, WorldTypedWith s1 S Nd →
      ∃ S2 Nd2, (∀ t ∈ S, t ∈ S2) ∧ WorldTypedWith s2 S2 Nd2 ∧
        OwnedGrows s1 s2 (worldOwned s1 S Nd) (worldOwned s2 S2 Nd2) ∧
        (∀ t ∈ T s2, t ∈ S2))
    (h23 : WorldStepIn T (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra s2 r2 s3)
    (hsc23 : globN s3 "scratch_ptr" ≤ globN s2 "scratch_ptr") :
    WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra s1 r2 s3 := by
  have hbuf : bufRegions withdrawalBufs s2 = bufRegions withdrawalBufs s1 := by
    unfold bufRegions
    apply List.map_congr_left
    intro p hp
    have hn : ofString p.1 ∉ withdrawalGlobals.map ofString := by
      simp only [withdrawalBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide
    have hg := globN_eq_of_lookup (h12.1.2.2.1 (ofString p.1) hn)
    simp only [bufferRegion, hg]
  have hframe : globN s2 "frame_mem_ptr" = globN s1 "frame_mem_ptr" :=
    globN_eq_of_lookup (h12.1.2.2.1 (ofString "frame_mem_ptr") (by decide))
  have hroots : ∀ rec ∈ withdrawalKeep, ∀ k ∈ rec.2,
      globN s2 rec.1 = globN s1 rec.1 := by
    intro rec hrec k hk
    apply globN_eq_of_lookup (h12.1.2.2.1 (ofString rec.1) ?_)
    simp only [withdrawalKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
    rcases hrec with rfl | rfl | rfl | rfl
    · decide
    · decide
    · cases hk
    · decide
  obtain ⟨⟨hA2, hhp12, hG12, hK12, hW12⟩, hsc12⟩ := h12
  obtain ⟨hA3, hhp23, hG23, hK23, hW23⟩ := h23
  refine ⟨⟨hA3, le_trans hhp12 hhp23,
    fun k hk => (hG12 k hk).trans (hG23 k hk), ?_, ?_⟩, le_trans hsc23 hsc12⟩
  · intro rec hrec hnz k hk hno
    have hg := hroots rec hrec k hk
    have h2 := hK23 rec hrec (by rw [hg]; exact hnz) k hk
      (by change ∀ i ∈ bufRegions withdrawalBufs s2, ¬ CellHits (globN s2 rec.1 + k) i
          rw [hbuf, hg]; exact hno)
    rw [hg] at h2
    exact h2.trans (hK12 rec hrec hnz k hk hno)
  · intro S Nd hWT1 hD1
    obtain ⟨_, _, _, _, _, hFO12, _⟩ := hW12 S Nd hWT1 hD1
    obtain ⟨S2, Nd2, hsub12, hWT2, hOG12, hT⟩ := howned S Nd hWT1
    obtain ⟨S3, Nd3, hsub23, hWT3, hOG23, hFO23, _⟩ :=
      hW23 S2 Nd2 hWT2 hT (validBufList_disj validBufList_withdrawal hWT2)
    refine ⟨S3, Nd3, fun t ht => hsub23 t (hsub12 t ht), hWT3, ?_, ?_, trivial⟩
    · intro o ho
      rcases hOG23 o ho with rfl | ⟨j, hj, hin_oj⟩ | hin_o23
      · exact Or.inl rfl
      · rcases hOG12 j hj with rfl | ⟨k, hk, hin_jk⟩ | hin_j12
        · left
          rcases o with ⟨o1, o2⟩
          dsimp only [Inside] at hin_oj
          have ho1 : o1 = 0 := by omega
          have ho2 : o2 = 0 := by omega
          rw [ho1, ho2]
        · exact Or.inr (Or.inl ⟨k, hk, le_trans hin_jk.1 hin_oj.1, le_trans hin_oj.2 hin_jk.2⟩)
        · exact Or.inr (Or.inr ⟨le_trans hin_j12.1 hin_oj.1,
            le_trans hin_oj.2 (le_trans hin_j12.2 hhp23)⟩)
      · exact Or.inr (Or.inr ⟨le_trans hhp12 hin_o23.1, hin_o23.2⟩)
    · intro a ha hhf
      have hm12 : s2.memory a = s1.memory a := hFO12 a ha hhf
      have hm23 : s3.memory a = s2.memory a := by
        apply hFO23 a
        · intro i hi hch
          obtain ⟨hc1, hc2⟩ := hch
          rcases List.mem_append.1 hi with hi1 | hfg2
          · rcases List.mem_append.1 hi1 with hwo2 | hR2
            · rcases hOG12 i hwo2 with rfl | ⟨k, hk, hin_ik⟩ | hin_i12
              · dsimp only at hc2; omega
              · exact ha k (List.mem_append_left _ (List.mem_append_left _ hk))
                  ⟨by dsimp only [Inside] at hin_ik; omega,
                   by dsimp only [Inside] at hin_ik; omega⟩
              · have hp2_lim : globN s2 "heap_ptr" ≤ heapLimit := hA2.2.2.1
                exact hhf ⟨by unfold heapFree; dsimp only [Inside] at hin_i12 ⊢; omega,
                           by unfold heapFree; dsimp only [Inside] at hin_i12 ⊢; omega⟩
            · change i ∈ bufRegions withdrawalBufs s2 at hR2
              rw [hbuf] at hR2
              exact ha i (List.mem_append_left _ (List.mem_append_right _ hR2)) ⟨hc1, hc2⟩
          · simp only [List.mem_singleton] at hfg2
            subst hfg2
            exact ha (freeGap s1) (List.mem_append_right _ (List.mem_singleton.2 rfl))
              ⟨by unfold freeGap at hc1 ⊢; dsimp only at hc1 ⊢; omega,
               by unfold freeGap at hc2 ⊢; dsimp only at hc2 ⊢; omega⟩
        · intro ⟨hc1, hc2⟩
          have hp2_lim : globN s2 "heap_ptr" ≤ heapLimit := hA2.2.2.1
          exact hhf ⟨by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega,
                     by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega⟩
      exact hm23.trans hm12

/-- Fresh allocation supplies the selected witness for insertion and inner union. -/
theorem eval_merge_new_set_then_union {F : Type}
    (s : PanSemStateFiniteExact 64 F) (et ek src : ExpHOL 64)
    (tw kw : BitVec 64) (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (howned : ∀ S Nd, WorldTypedWith s S Nd → tw.toNat ∈ S)
    (hentry : ∀ (mid : PanSemStateFiniteExact 64 F) (iw : BitVec 64),
      WorldStepSc (bufRegions []) ["heap_ptr"] stdKeep NoExtra s none mid →
      WorldOK mid → mid.locals.lookup (ofString "binner") = some (.val (.word iw)) →
      (∀ y, y ≠ ofString "binner" → mid.locals.lookup y = s.locals.lookup y) →
      evalAt mid et = some (.val (.word tw)) ∧
      evalAt mid ek = some (.val (.word kw)) ∧ globN mid "bs" ≠ 0 ∧
      tw.toNat ≠ 0 ∧ tw.toNat = memW mid (globN mid "bs" + 32))
    (hnt : (evaluateHOLFiniteState s (.seq
      (.call (some (some (.local, ofString "binner"), none)) (ofString "htab_new")
        [.const 32#64, .const 8#64])
      (.seq (.call (some (none, none)) (ofString "htab_set")
        [et, ek, .var .local (ofString "binner")])
        (.call (some (none, none)) (ofString "htab_union_into")
          [.var .local (ofString "binner"), src])))).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s (.seq
      (.call (some (some (.local, ofString "binner"), none)) (ofString "htab_new")
        [.const 32#64, .const 8#64])
      (.seq (.call (some (none, none)) (ofString "htab_set")
        [et, ek, .var .local (ofString "binner")])
        (.call (some (none, none)) (ofString "htab_union_into")
          [.var .local (ofString "binner"), src])))).1) :
    let out := evaluateHOLFiniteState s (.seq
      (.call (some (some (.local, ofString "binner"), none)) (ofString "htab_new")
        [.const 32#64, .const 8#64])
      (.seq (.call (some (none, none)) (ofString "htab_set")
        [et, ek, .var .local (ofString "binner")])
        (.call (some (none, none)) (ofString "htab_union_into")
          [.var .local (ofString "binner"), src])))
    WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra s out.1 out.2 := by
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases he : evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "binner"), none)) (ofString "htab_new")
        [.const 32#64, .const 8#64]) with ⟨r, mid⟩
  simp only [he] at hnt hfr ⊢
  have hflow : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "binner"), none)) (ofString "htab_new")
        [.const 32#64, .const 8#64])).1 := by
    rw [he]
    cases r with
    | none => exact Or.inl rfl
    | some r => exact hfr
  have hn := merge_new_call_flow_none s (ofString "binner") 32#64 8#64 hc hflow
  rw [he] at hn
  cases hn
  have hs := merge_new_call_worldStep s (ofString "binner") 32#64 8#64
    hW (by decide) (by decide) hflow
  rw [he] at hs
  have hWm := hs.worldOK_bufs (by intro p hp; simp at hp) hW
  obtain ⟨S, hw⟩ := hW.2
  obtain ⟨Nd, hw⟩ := (WkBal.worldTyped_iff_with s S).1 hw
  have ho := merge_new_call_bound_owned s (ofString "binner") 32#64 8#64 S Nd
    hW.1 hw (by decide) (by decide) hflow
  rw [he] at ho
  obtain ⟨iw, hi, hl, _, _, hkey, _, hf, hw', _⟩ := ho
  obtain ⟨ht, hk, hbs, ht0, htbs⟩ := hentry mid iw hs hWm hi hl
  have hm := (PanRunBounded.evaluateHOLFiniteState_metadata s
      (.call (some (some (.local, ofString "binner"), none)) (ofString "htab_new")
        [.const 32#64, .const 8#64])).1
  rw [he] at hm
  have hsu := eval_merge_set_then_union_with mid et ek src tw kw iw (S ++ [iw.toNat]) Nd
    ht hk hi (hm.trans hc) hWm.1 hw' (List.mem_append_left _ (howned S Nd hw))
    (by simp) hbs ht0 htbs (by exact hkey) hf hnt hfr
  apply withdrawalStepSc_trans_owned (merge_heap_step_withdrawal hs) ?_ hsu.1 hsu.2
  intro S0 Nd0 hw0
  have ho0 := merge_new_call_bound_owned s (ofString "binner") 32#64 8#64 S0 Nd0
    hW.1 hw0 (by decide) (by decide) hflow
  rw [he] at ho0
  obtain ⟨iw0, hi0, _, _, _, _, _, _, hw0', hg0, _⟩ := ho0
  have hiw : iw0 = iw := by rw [hi] at hi0; cases hi0; rfl
  subst iw0
  refine ⟨S0 ++ [iw.toNat], Nd0, fun t ht => List.mem_append_left _ ht, hw0', hg0, ?_⟩
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact List.mem_append_left _ (howned S0 Nd0 hw0)
  · simp

/-- The concrete fresh-inner branch keeps its outer pointer and key across allocation. -/
theorem eval_merge_new_set_union_locals {F : Type}
    (s : PanSemStateFiniteExact 64 F) (tw f0 kw vw : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (ht : s.locals.lookup (ofString "bouter") = some (.val (.word tw)))
    (hk : s.locals.lookup (ofString "s") = some (.rStruct [.val (.word f0), .val (.word kw), .val (.word vw)]))
    (hbs : globN s "bs" ≠ 0) (ht0 : tw.toNat ≠ 0)
    (htbs : tw.toNat = memW s (globN s "bs" + 32))
    (hnt : (evaluateHOLFiniteState s (.seq
      (.call (some (some (.local, ofString "binner"), none)) (ofString "htab_new")
        [.const 32#64, .const 8#64])
      (.seq (.call (some (none, none)) (ofString "htab_set")
        [.var .local (ofString "bouter"), .rfield 1 (.var .local (ofString "s")), .var .local (ofString "binner")])
        (.call (some (none, none)) (ofString "htab_union_into")
          [.var .local (ofString "binner"), .rfield 2 (.var .local (ofString "s"))])))).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s (.seq
      (.call (some (some (.local, ofString "binner"), none)) (ofString "htab_new")
        [.const 32#64, .const 8#64])
      (.seq (.call (some (none, none)) (ofString "htab_set")
        [.var .local (ofString "bouter"), .rfield 1 (.var .local (ofString "s")), .var .local (ofString "binner")])
        (.call (some (none, none)) (ofString "htab_union_into")
          [.var .local (ofString "binner"), .rfield 2 (.var .local (ofString "s"))])))).1) :
    let out := evaluateHOLFiniteState s (.seq
      (.call (some (some (.local, ofString "binner"), none)) (ofString "htab_new")
        [.const 32#64, .const 8#64])
      (.seq (.call (some (none, none)) (ofString "htab_set")
        [.var .local (ofString "bouter"), .rfield 1 (.var .local (ofString "s")), .var .local (ofString "binner")])
        (.call (some (none, none)) (ofString "htab_union_into")
          [.var .local (ofString "binner"), .rfield 2 (.var .local (ofString "s"))])))
    WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra s out.1 out.2 := by
  apply eval_merge_new_set_then_union s _ _ _ tw kw hc hW ?_ ?_ hnt hfr
  · intro S Nd hw
    have hT := (WkBal.worldTyped_iff_with s S).2 ⟨Nd, hw⟩
    have hr := hT.1.2.2.2.2.1 32 (by simp [bsTableSlots]) hbs
    rw [← htbs] at hr
    exact hr.resolve_left ht0
  · intro mid iw hs _ _ hl
    have htm := (hl (ofString "bouter") (by decide)).trans ht
    have hkm := (hl (ofString "s") (by decide)).trans hk
    have hgb : globN mid "bs" = globN s "bs" :=
      globN_eq_of_lookup (hs.1.2.2.1 (ofString "bs") (by decide))
    have hmem := hs.1.2.2.2.1 ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72])
      (by simp [stdKeep]) hbs 32 (by simp) (by simp [bufRegions])
    refine ⟨by simp [evalAt, evalHOLExact, htm], by simp [evalAt, evalHOLExact, hkm],
      by rwa [hgb], ht0, ?_⟩
    rw [hgb]
    exact htbs.trans hmem.symm

theorem merge_eval_seq_assoc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b c : ProgHOL 64) :
    evaluateHOLFiniteState s (.seq (.seq a b) c) =
      evaluateHOLFiniteState s (.seq a (.seq b c)) := by
  simp only [evaluateHOLFiniteState_seq_line780]
  cases he : evaluateHOLFiniteState s a with
  | mk r mid => cases r <;> rfl

def mergeFreshInner : ProgHOL 64 :=
  .seq (.call (some (some (.local, ofString "binner"), none)) (ofString "htab_new")
    [.const 32#64, .const 8#64])
    (.call (some (none, none)) (ofString "htab_set")
      [.var .local (ofString "bouter"), .rfield 1 (.var .local (ofString "s")), .var .local (ofString "binner")])

def mergeInnerBranch : ProgHOL 64 :=
  .seq (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
    mergeFreshInner (.assign .local (ofString "binner") (.rfield 1 (.var .local (ofString "m")))))
    (.call (some (none, none)) (ofString "htab_union_into")
      [.var .local (ofString "binner"), .rfield 2 (.var .local (ofString "s"))])

/-- Both lookup outcomes preserve the withdrawal frame in the actual merge branch. -/
theorem eval_merge_inner_branch {F : Type}
    (s : PanSemStateFiniteExact 64 F) (tw f0 kw vw m0 m1 : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (ht : s.locals.lookup (ofString "bouter") = some (.val (.word tw)))
    (hk : s.locals.lookup (ofString "s") = some (.rStruct [.val (.word f0), .val (.word kw), .val (.word vw)]))
    (hm : s.locals.lookup (ofString "m") = some (.rStruct [.val (.word m0), .val (.word m1)]))
    (hbs : globN s "bs" ≠ 0) (ht0 : tw.toNat ≠ 0)
    (htbs : tw.toNat = memW s (globN s "bs" + 32))
    (hi : m0 ≠ 0 → m1.toNat ∈ htabValues s (memW s (globN s "bs" + 32)))
    (hnt : (evaluateHOLFiniteState s mergeInnerBranch).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s mergeInnerBranch).1) :
    WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra
      s (evaluateHOLFiniteState s mergeInnerBranch).1 (evaluateHOLFiniteState s mergeInnerBranch).2 := by
  by_cases hz : m0 = 0
  · subst m0
    have hcond : evalAt s (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64)) =
        some (.val (.word 1#64)) := by
      simp [evalAt, evalHOLExact, hm, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have heq : evaluateHOLFiniteState s mergeInnerBranch =
        evaluateHOLFiniteState s (.seq mergeFreshInner
          (.call (some (none, none)) (ofString "htab_union_into")
            [.var .local (ofString "binner"), .rfield 2 (.var .local (ofString "s"))])) := by
      unfold mergeInnerBranch
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
      dsimp only [evalAt] at hcond
      rw [hcond]
      simp only [show (1#64 : BitVec 64) ≠ 0 by decide, ↓reduceIte]
      rw [evaluateHOLFiniteState_seq_line780]
    rw [heq] at hnt hfr ⊢
    unfold mergeFreshInner at hnt hfr ⊢
    rw [merge_eval_seq_assoc] at hnt hfr ⊢
    exact eval_merge_new_set_union_locals s tw f0 kw vw hc hW ht hk hbs ht0 htbs hnt hfr
  · exact eval_merge_hit_branch s m0 m1 mergeFreshInner hc hW hbs
      (by rwa [← htbs]) hm hz (hi hz) hnt hfr

def mergeGetInner : ProgHOL 64 :=
  .decCall (ofString "m") (.comb [.one, .one]) (ofString "htab_get")
    [.var .local (ofString "bouter"), .rfield 1 (.var .local (ofString "s"))]
    (.dec (ofString "binner") .one (.const 0#64) mergeInnerBranch)

/-- Lookup, local initialization, and both inner-table paths compose. -/
theorem eval_merge_get_inner {F : Type}
    (s : PanSemStateFiniteExact 64 F) (tw f0 kw vw : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (ht : s.locals.lookup (ofString "bouter") = some (.val (.word tw)))
    (hk : s.locals.lookup (ofString "s") = some (.rStruct [.val (.word f0), .val (.word kw), .val (.word vw)]))
    (hbs : globN s "bs" ≠ 0) (ht0 : tw.toNat ≠ 0)
    (htbs : tw.toNat = memW s (globN s "bs" + 32))
    (hnt : (evaluateHOLFiniteState s mergeGetInner).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s mergeGetInner).1) :
    WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra
      s (evaluateHOLFiniteState s mergeGetInner).1 (evaluateHOLFiniteState s mergeGetInner).2 := by
  apply merge_outer_get_flow_continuation s (ofString "m") _ _ _ hc hW hbs ?_ ?_ hnt hfr
  · intro t ht'
    have ht'' : evalAt s (.var .local (ofString "bouter")) = some (.val (.word tw)) := by
      simp [evalAt, evalHOLExact, ht]
    rw [ht''] at ht'
    cases ht'
    exact htbs
  · intro m0 m1 ck hi
    dsimp only
    intro hnt hfr
    rw [evaluateHOLFiniteState_dec_total] at hnt hfr ⊢
    simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt hfr ⊢
    let mid := setVarHOLFinite (ofString "binner") (.val (.word 0#64))
      (setVarHOLFinite (ofString "m") (.rStruct [.val (.word m0), .val (.word m1)]) {s with clock := ck})
    have hWm : WorldOK mid := localsFree_worldOK s _ _ hW
    have hs := eval_merge_inner_branch mid tw f0 kw vw m0 m1 hc hWm
      (by simpa [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "binner" ≠ ofString "bouter" by decide,
        show ofString "m" ≠ ofString "bouter" by decide] using ht)
      (by simpa [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "binner" ≠ ofString "s" by decide,
        show ofString "m" ≠ ofString "s" by decide] using hk)
      (by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "binner" ≠ ofString "m" by decide])
      hbs ht0 htbs hi hnt hfr
    exact (WorldStepSc.of_pre_locals_clock hs).with_locals_clock _
      (evaluateHOLFiniteState mid mergeInnerBranch).2.clock

def mergeOccupiedInner : ProgHOL 64 :=
  .ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0#64))
    mergeGetInner .skip

/-- Empty enumeration slots are skipped; occupied slots execute the inner merge. -/
theorem eval_merge_occupied_inner {F : Type}
    (s : PanSemStateFiniteExact 64 F) (tw f0 kw vw : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (ht : s.locals.lookup (ofString "bouter") = some (.val (.word tw)))
    (hk : s.locals.lookup (ofString "s") = some (.rStruct [.val (.word f0), .val (.word kw), .val (.word vw)]))
    (hbs : globN s "bs" ≠ 0) (ht0 : tw.toNat ≠ 0)
    (htbs : tw.toNat = memW s (globN s "bs" + 32))
    (hnt : (evaluateHOLFiniteState s mergeOccupiedInner).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s mergeOccupiedInner).1) :
    WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra
      s (evaluateHOLFiniteState s mergeOccupiedInner).1 (evaluateHOLFiniteState s mergeOccupiedInner).2 := by
  unfold mergeOccupiedInner at hnt hfr ⊢
  rw [evaluateHOLFiniteState_ite] at hnt hfr ⊢
  by_cases hz : f0 = 0
  · subst f0
    simp only [evalHOLExact, hk, List.getElem?_cons_zero,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hnt hfr ⊢
    simp at hnt hfr ⊢
    exact WorldStepSc.refl s _ hW.1
  · have he : evalAt s (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0#64)) =
        some (.val (.word 1#64)) := by
      simpa [evalAt, evalHOLExact, hk, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] using hz
    unfold evalAt at he
    rw [he] at hnt hfr ⊢
    simp only [show (1#64 : BitVec 64) ≠ 0 by decide, ↓reduceIte] at hnt hfr ⊢
    exact eval_merge_get_inner s tw f0 kw vw hc hW ht hk hbs ht0 htbs hnt hfr

/-- Local cursor updates preserve the withdrawal frame on every flowing exit. -/
theorem progWithdrawalStep_assign_local (x : MlS) (e : ExpHOL 64) :
    ProgWithdrawalStep (.assign .local x e) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_assign] at hnt hfr ⊢
  rcases he : evalAt s e with _ | v
  · unfold evalAt at he
    simp only [he] at hfr
    exact absurd hfr not_flowingOrResumes_error
  · unfold evalAt at he
    simp only [he] at hnt hfr ⊢
    by_cases hv : isValidValueHOLFinite s .local x v = true
    · simp only [hv, ↓reduceIte, setKvarHOLFinite] at hnt hfr ⊢
      exact (WorldStepSc.refl s none hW.1).with_locals_clock _ s.clock
    · simp only [hv] at hfr
      exact absurd hfr not_flowingOrResumes_error

/-- A pointwise prefix effect suffices when the suffix has an unconditional contract. -/
theorem eval_withdrawal_then {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p q : ProgHOL 64) (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hp : (evaluateHOLFiniteState s p).1 ≠ some .timeOut →
      FlowingOrResumes (evaluateHOLFiniteState s p).1 →
      WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra
        s (evaluateHOLFiniteState s p).1 (evaluateHOLFiniteState s p).2)
    (hq : ProgWithdrawalStep q)
    (hnt : (evaluateHOLFiniteState s (.seq p q)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s (.seq p q)).1) :
    WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra
      s (evaluateHOLFiniteState s (.seq p q)).1 (evaluateHOLFiniteState s (.seq p q)).2 := by
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s p).1
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases hr : evaluateHOLFiniteState s p with ⟨r, mid⟩
  simp only [hr] at hmeta hnt hfr ⊢
  cases r with
  | none =>
    have hs := hp (by rw [hr]; simp) (by rw [hr]; exact Or.inl rfl)
    rw [hr] at hs
    exact withdrawalStep_trans hs
      (hq mid (hmeta.trans hc) (hs.worldOK_bufs validBufList_withdrawal hW) hnt hfr)
  | some r =>
    have hs := hp (by rw [hr]; exact hnt) (by rw [hr]; exact hfr)
    simpa only [hr] using hs

def mergeOccupiedThenIncrement : ProgHOL 64 :=
  .seq mergeOccupiedInner (.assign .local (ofString "i")
    (.op .add [.var .local (ofString "i"), .const 1#64]))

theorem eval_merge_occupied_then_increment {F : Type}
    (s : PanSemStateFiniteExact 64 F) (tw f0 kw vw : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (ht : s.locals.lookup (ofString "bouter") = some (.val (.word tw)))
    (hk : s.locals.lookup (ofString "s") = some (.rStruct [.val (.word f0), .val (.word kw), .val (.word vw)]))
    (hbs : globN s "bs" ≠ 0) (ht0 : tw.toNat ≠ 0)
    (htbs : tw.toNat = memW s (globN s "bs" + 32))
    (hnt : (evaluateHOLFiniteState s mergeOccupiedThenIncrement).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s mergeOccupiedThenIncrement).1) :
    WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra
      s (evaluateHOLFiniteState s mergeOccupiedThenIncrement).1
        (evaluateHOLFiniteState s mergeOccupiedThenIncrement).2 := by
  exact eval_withdrawal_then s _ _ hc hW
    (eval_merge_occupied_inner s tw f0 kw vw hc hW ht hk hbs ht0 htbs)
    (progWithdrawalStep_assign_local _ _) hnt hfr

def mergeStorageBody : ProgHOL 64 :=
  .decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item")
    [.var .local (ofString "outer"), .var .local (ofString "i")]
    mergeOccupiedThenIncrement

/-- A complete storage-loop iteration enumerates, merges, and advances its cursor. -/
theorem eval_merge_storage_body {F : Type}
    (s : PanSemStateFiniteExact 64 F) (tw ow : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (ht : s.locals.lookup (ofString "bouter") = some (.val (.word tw)))
    (ho : s.locals.lookup (ofString "outer") = some (.val (.word ow)))
    (hbs : globN s "bs" ≠ 0) (ht0 : tw.toNat ≠ 0)
    (htbs : tw.toNat = memW s (globN s "bs" + 32))
    (hts : globN s "ts" ≠ 0)
    (hots : ow.toNat = memW s (globN s "ts" + 32))
    (hnt : (evaluateHOLFiniteState s mergeStorageBody).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s mergeStorageBody).1) :
    WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra
      s (evaluateHOLFiniteState s mergeStorageBody).1 (evaluateHOLFiniteState s mergeStorageBody).2 := by
  apply merge_outer_item_flow_continuation s (ofString "s") _ _ _ hc hW hts ?_ ?_ hnt hfr
  · intro t he
    have he' : evalAt s (.var .local (ofString "outer")) = some (.val (.word ow)) := by
      simp [evalAt, evalHOLExact, ho]
    rw [he'] at he
    cases he
    exact hots
  · intro t f0 kw vw ck _ _
    dsimp only
    intro hnt hfr
    apply eval_merge_occupied_then_increment
      (setVarHOLFinite (ofString "s") (.rStruct [.val (.word f0), .val (.word kw), .val (.word vw)])
        {s with clock := ck}) tw f0 kw vw hc
      (localsFree_worldOK s _ ck hW) ?_ ?_ hbs ht0 htbs hnt hfr
    · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "s" ≠ ofString "bouter" by decide] using ht
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

/-- The storage body never assigns its two outer-table pointers or cached capacity. -/
theorem merge_storage_body_roots {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hflow : Flowing (evaluateHOLFiniteState s mergeStorageBody).1) :
    ∀ x ∈ [ofString "outer", ofString "bouter", ofString "cap"],
      (evaluateHOLFiniteState s mergeStorageBody).2.locals.lookup x = s.locals.lookup x := by
  intro x hx
  apply evaluate_avoidsLocal_flowing x mergeStorageBody ?_ s hflow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> decide

/-- The block outer-table pointer is stable under the withdrawal frame. -/
theorem merge_withdrawal_bs_outer_kept {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hbs : globN s "bs" ≠ 0)
    (hs : WorldStepSc (bufRegions withdrawalBufs) withdrawalGlobals withdrawalKeep NoExtra s r post)
    (hno : ∀ i ∈ bufRegions withdrawalBufs s, ¬ CellHits (globN s "bs" + 32) i) :
    globN post "bs" = globN s "bs" ∧
      memW post (globN post "bs" + 32) = memW s (globN s "bs" + 32) := by
  have hg := globN_eq_of_lookup (hs.1.2.2.1 (ofString "bs") (by decide))
  refine ⟨hg, ?_⟩
  rw [hg]
  exact hs.1.2.2.2.1 ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72])
    (by decide) hbs 32 (by decide) hno

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
