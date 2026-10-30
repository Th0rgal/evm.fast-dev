import InitECandidate.Solver.GuestTrapOutcomes
import Flapjack.Pancake.Semantics.ByteAlignBridge
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.GuestTrapAndLookup

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestExceptionShapes
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestFrameMemKeep

theorem evaluate_call_trap_with_no_none {F : Type}
    (state : PanSemStateFiniteExact 64 F) (codeVal : BitVec 64)
    (hcode : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "trap_with") [.const codeVal])).1 ≠ none := by
  rw [evaluateHOLFiniteState_call]
  have hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const codeVal] =
      some [.val (.word codeVal)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hlookup := pan_one_word_lookup state.code.lookup (ofString "trap_with") (ofString "code")
    (sourceFnBody Guest.Software.guestFn_trap_with) codeVal (by rw [hcode]; exact lookup_trap_with)
  rw [hargs]
  dsimp only
  rw [hlookup]
  dsimp only
  split
  · simp
  · have hout := evaluate_trap_with_body_outcomes
      (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
    rcases hbody : evaluateHOLFiniteState
      (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
      (sourceFnBody Guest.Software.guestFn_trap_with) with ⟨res, st⟩
    rw [hbody] at hout
    cases res with
    | none => exact absurd rfl hout.1
    | some r =>
      cases r with
      | returned v => exact absurd rfl (hout.2.1 v)
      | «break» | «continue» | error | timeOut | finalFfi _ | exception _ _ => simp

theorem evaluate_call_trap_with_no_return {F : Type}
    (state : PanSemStateFiniteExact 64 F) (codeVal : BitVec 64) (w : ValueHOL 64)
    (hcode : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "trap_with") [.const codeVal])).1 ≠ some (.returned w) := by
  rw [evaluateHOLFiniteState_call]
  have hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const codeVal] =
      some [.val (.word codeVal)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hlookup := pan_one_word_lookup state.code.lookup (ofString "trap_with") (ofString "code")
    (sourceFnBody Guest.Software.guestFn_trap_with) codeVal (by rw [hcode]; exact lookup_trap_with)
  rw [hargs]
  dsimp only
  rw [hlookup]
  dsimp only
  split
  · simp
  · have hout := evaluate_trap_with_body_outcomes
      (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
    rcases hbody : evaluateHOLFiniteState
      (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
      (sourceFnBody Guest.Software.guestFn_trap_with) with ⟨res, st⟩
    rw [hbody] at hout
    cases res with
    | none => exact absurd rfl hout.1
    | some r =>
      cases r with
      | returned v => exact absurd rfl (hout.2.1 v)
      | «break» | «continue» | error | timeOut | finalFfi _ | exception _ _ => simp

theorem panByteAlign_toNat64 (address : BitVec 64) :
    (panByteAlignHOL address).toNat = address.toNat / 8 * 8 := by
  have bound : address.toNat / 8 * 8 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) address.isLt
  simpa [panByteAlignHOL, BitVec.toNat_ofNat] using Nat.mod_eq_of_lt bound

theorem and_neg8_eq_panByteAlign (w : BitVec 64) :
    w &&& ((0 : BitVec 64) - 8) = panByteAlignHOL w := by
  rw [← riscvByteAlignHOL_eq_panByteAlignHOL]
  change w &&& (0 - 8) = (w >>> 3) <<< 3
  apply BitVec.eq_of_getLsbD_eq
  intro bit bounded
  interval_cases bit <;> simp [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]

theorem and_neg8_toNat (w : BitVec 64) :
    (w &&& ((0 : BitVec 64) - 8)).toNat = w.toNat / 8 * 8 := by
  rw [and_neg8_eq_panByteAlign, panByteAlign_toNat64]

theorem sub_and_neg8_ge_high (ptr size : BitVec 64)
    (hlt : ptr.toNat < size.toNat) (hsize : size.toNat ≤ 1024) :
    2 ^ 64 - 1032 ≤ ((ptr - size) &&& ((0 : BitVec 64) - 8)).toNat := by
  have hp : ptr.toNat < 2 ^ 64 := ptr.isLt
  have hs : size.toNat < 2 ^ 64 := size.isLt
  have hsub : (ptr - size).toNat = 2 ^ 64 - size.toNat + ptr.toNat := by
    rw [BitVec.toNat_sub]
    omega
  rw [and_neg8_toNat]
  omega

theorem sub_and_neg8_le_ptr (ptr size : BitVec 64)
    (hle : size.toNat ≤ ptr.toNat) :
    ((ptr - size) &&& ((0 : BitVec 64) - 8)).toNat ≤ ptr.toNat := by
  have hp : ptr.toNat < 2 ^ 64 := ptr.isLt
  have hs : size.toNat < 2 ^ 64 := size.isLt
  have hsub : (ptr - size).toNat = ptr.toNat - size.toNat := by
    rw [BitVec.toNat_sub]
    omega
  rw [and_neg8_toNat]
  omega

end InitECandidate.Solver.GuestTrapAndLookup
