import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind3Descent

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanRunBounded

theorem mpt_avoids_none {F : Type} (s t : PanSemStateFiniteExact 64 F)
    (p : ProgHOL 64) (name : MlS) (ha : avoidsLocal name p = true)
    (he : evaluateHOLFiniteState s p = (none, t)) :
    t.locals.lookup name = s.locals.lookup name := by
  have h := evaluate_avoidsLocal_flowing name p ha s (by simp [he, Flowing])
  simpa only [he] using h

theorem mpt_loadByte_inv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (v : ValueHOL 64)
    (h : evalAt s (.loadByte e) = some v) :
    ∃ a b : BitVec 64, evalAt s e = some (.val (.word a)) ∧
      v = .val (.word b) ∧ b.toNat = memB s a.toNat := by
  simp only [evalAt, evalHOLExact] at h
  split at h
  · rename_i a ha
    cases hm : s.memory (panByteAlignHOL a) with
    | word w =>
      simp only [panMemLoadByteHOL, hm] at h
      split at h
      · rename_i hd
        simp only [Option.map_some, Option.some.injEq] at h
        refine ⟨a, _, ha, h.symm, ?_⟩
        simp [memB, BitVec.ofNat_toNat, hm]
      · simp at h
  · cases h

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
