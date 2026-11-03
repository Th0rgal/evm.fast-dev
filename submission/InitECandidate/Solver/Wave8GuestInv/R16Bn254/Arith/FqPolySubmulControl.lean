import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolySubmulSource

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanRunBounded

theorem polySubmul_guard {F : Type} (state : PanSemStateFiniteExact 64 F) (i db : Nat)
    (hib : i ≤ db+1) (hdbb : db < 13)
    (hi : state.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 i))))
    (hdb : state.locals.lookup (ofString "db") = some (.val (.word (BitVec.ofNat 64 db)))) :
    arithEval state (.cmp .notLower (polySubmulVar "db") (polySubmulVar "i")) =
      some (.val (.word (if i ≤ db then 1 else 0))) := by
  have hi64 : i < 18446744073709551616 := by omega
  have hdb64 : db < 18446744073709551616 := by omega
  simp [arithEval,polySubmulVar,evalHOLExact,hi,hdb,Compiler.Encoders.Asm.wordCmpHOL,
    BitVec.lt_def,Nat.mod_eq_of_lt hi64,Nat.mod_eq_of_lt hdb64]

theorem polySubmulBody_keeps {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (hn : name ∈ [ofString "a",ofString "b",ofString "q",ofString "s",ofString "db"])
    (hr : evaluateHOLFiniteState state polySubmulBody = (none,post)) :
    post.locals.lookup name = state.locals.lookup name := by
  have h := evaluate_avoidsLocal_flowing name polySubmulBody (polySubmulBody_avoids name hn) state
    (Or.inl (by rw [hr]))
  rw [hr] at h
  exact h

theorem polySubmulBody_index {F : Type} (state post : PanSemStateFiniteExact 64 F) (i : Nat)
    (hi : state.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 i))))
    (hr : evaluateHOLFiniteState state polySubmulBody = (none,post)) :
    post.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (i+1)))) := by
  have h := polySubmulBody_counter state (BitVec.ofNat 64 i) hi
  dsimp only at h
  rw [hr] at h
  have he : BitVec.ofNat 64 (i+1) = BitVec.ofNat 64 i + 1 := BitVec.ofNat_add i 1
  rw [he]
  exact h (Or.inl rfl)

end InitECandidate.Solver.Wave8GuestInv.Arith
