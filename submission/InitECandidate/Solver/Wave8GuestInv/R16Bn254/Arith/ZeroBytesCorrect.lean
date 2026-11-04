import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ZeroBytesLoop

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem zeroBytes32_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (base : BitVec 64) (bytes : Nat → UInt8) (ret : ValueHOL 64)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word base)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word 32)))
    (hreads : ZeroBytes32Reads s base bytes)
    (hr : evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_is_zero_bytes) =
      (some (.returned ret), post)) :
    (ret = .val (.word 1) ∧ ∀ j, j < 32 → bytes j = 0) ∨
    (ret = .val (.word 0) ∧ ¬ ∀ j, j < 32 → bytes j = 0) := by
  rw [zeroBytes_source_eq] at hr
  obtain ⟨value, hinit, hshape, inner, hbody⟩ := arith_dec_returned hr
  have hv : value = .val (.word 0) := by
    simpa [evalHOLFinite, evalHOLExact] using hinit.symm
  subst value
  let entry := setVarHOLFinite (ofString "i") (.val (.word 0)) s
  have hp' : entry.locals.lookup (ofString "p") = some (.val (.word base)) := by
    simpa [entry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "i" ≠ ofString "p" by decide] using hp
  have hn' : entry.locals.lookup (ofString "n") = some (.val (.word 32)) := by
    simpa [entry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "i" ≠ ofString "n" by decide] using hn
  have hs := zeroBytesLoop_spec entry base bytes 0 (by decide) hp'
    (by simp [entry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hn' hreads
  rcases arith_seq_returned hbody with hret | ⟨mid, hnone, hreturn⟩
  · change evaluateHOLFiniteState entry zeroBytesLoop = _ at hret
    rw [hret] at hs
    obtain ⟨he,hz⟩ := hs.2 ret rfl
    exact Or.inr ⟨he, fun h => hz (fun j _ hj => h j hj)⟩
  · change evaluateHOLFiniteState entry zeroBytesLoop = _ at hnone
    rw [hnone] at hs
    have he : ret = .val (.word 1) := by
      have hreturn' : evaluateHOLFiniteState mid (.return (.const 1)) =
          (some (.returned (.val (.word 1))), emptyLocalsHOLFinite mid) := by
        simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
      rw [hreturn'] at hreturn
      simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using (Prod.mk.inj hreturn).1.symm
    exact Or.inl ⟨he, fun j hj => hs.1 rfl j (by omega) hj⟩

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
