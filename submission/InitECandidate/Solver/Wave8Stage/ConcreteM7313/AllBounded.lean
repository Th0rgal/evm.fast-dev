import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded28
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded29
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded30
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded31
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded32
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded33
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded50

/-!
# Proofs-free Stage 5 `stepCost ≤ 7313` composition (`AllBounded`)

Certifies `Bounded GlobalFrameInfo.info StackPasses.nativeStubs` directly by kernel
reduction, composes the landed `Bounded28..33` (`96` functions) and `Bounded50` (`14`
functions) segments, and packages the multi-segment `Bounded GlobalFrameInfo.info`
combinators used by `ConcreteBackendBound` across chunks `00..50` without importing
`InitECandidate.Proofs`.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 10000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.AllBounded
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open BackendDecomposition StackPasses StackToLabClock LoweredBudget

wave8_certified_reduce costRaise :=
  stepCost (lowerEntry GlobalFrameInfo.info
    (raiseStubLocation, WordToStack.Native.raiseStubNative false registers)).2

wave8_certified_reduce costStoreConsts :=
  stepCost (lowerEntry GlobalFrameInfo.info
    (storeConstsStubLocation, WordToStack.Native.storeConstsStubNative registers)).2

theorem raiseStub_bounded :
    stepCost (lowerEntry GlobalFrameInfo.info
      (raiseStubLocation, WordToStack.Native.raiseStubNative false registers)).2 ≤ 7313 := by
  rw [costRaise_eq]
  decide

theorem storeConstsStub_bounded :
    stepCost (lowerEntry GlobalFrameInfo.info
      (storeConstsStubLocation, WordToStack.Native.storeConstsStubNative registers)).2 ≤ 7313 := by
  rw [costStoreConsts_eq]
  decide

/-- Both native word-to-stack runtime stubs satisfy `stepCost ≤ 7313` under
`GlobalFrameInfo.info`. -/
theorem nativeStubs_bounded : Bounded GlobalFrameInfo.info nativeStubs := by
  unfold nativeStubs
  apply bounded_cons _ _ _ raiseStub_bounded
  apply bounded_cons _ _ _ storeConstsStub_bounded
  exact bounded_nil GlobalFrameInfo.info

/-- Combined `Chunk28..33` bodies (`512..607`, `96` functions). -/
noncomputable def bodies28To33 : List (Nat × HolProg 64) :=
  Chunk28.bodies ++ Chunk29.bodies ++ Chunk30.bodies ++
    Chunk31.bodies ++ Chunk32.bodies ++ Chunk33.bodies

/-- `stepCost ≤ 7313` across all `96` lowered bodies in `Chunk28..33`. -/
theorem bounded28To33 : Bounded GlobalFrameInfo.info bodies28To33 := by
  unfold bodies28To33
  refine bounded_append GlobalFrameInfo.info _ _ ?_ Bounded33.bounded
  refine bounded_append GlobalFrameInfo.info _ _ ?_ Bounded32.bounded
  refine bounded_append GlobalFrameInfo.info _ _ ?_ Bounded31.bounded
  refine bounded_append GlobalFrameInfo.info _ _ ?_ Bounded30.bounded
  exact bounded_append GlobalFrameInfo.info _ _ Bounded28.bounded Bounded29.bounded

/-- `stepCost ≤ 7313` across `Chunk50` (`864..877`, `14` functions). -/
theorem bounded50 : Bounded GlobalFrameInfo.info Chunk50.bodies :=
  Bounded50.bounded

/-- Transport `Bounded GlobalFrameInfo.info` to any frame-info map proven equal to
`GlobalFrameInfo.info` (e.g. `Frames50.info`). -/
theorem bounded_of_info_eq {info : Spt Nat} {table : List (Nat × HolProg 64)}
    (hinfo : info = GlobalFrameInfo.info)
    (h : Bounded GlobalFrameInfo.info table) :
    Bounded info table := by
  subst hinfo
  exact h

/-- Compose the full guest body table `bodies00To27 ++ bodies28To33 ++ bodies34To49 ++ Chunk50.bodies`
with `nativeStubs` under `GlobalFrameInfo.info`. -/
theorem all_bounded_of_segments
    (bodies00To27 bodies34To49 : List (Nat × HolProg 64))
    (hb00To27 : Bounded GlobalFrameInfo.info bodies00To27)
    (hb34To49 : Bounded GlobalFrameInfo.info bodies34To49) :
    Bounded GlobalFrameInfo.info
      (nativeStubs ++ (bodies00To27 ++ bodies28To33 ++ bodies34To49 ++ Chunk50.bodies)) := by
  apply bounded_append GlobalFrameInfo.info nativeStubs _ nativeStubs_bounded
  refine bounded_append GlobalFrameInfo.info _ _ ?_ bounded50
  refine bounded_append GlobalFrameInfo.info _ _ ?_ hb34To49
  exact bounded_append GlobalFrameInfo.info _ _ hb00To27 bounded28To33

/-- Transport a full-table `Bounded GlobalFrameInfo.info (nativeStubs ++ bodies)` proof across
an equality on `bodies` and `info`. -/
theorem all_bounded_of_eq {info : Spt Nat} {bodies targetBodies : List (Nat × HolProg 64)}
    (hinfo : info = GlobalFrameInfo.info)
    (hbodies : bodies = targetBodies)
    (h : Bounded GlobalFrameInfo.info (nativeStubs ++ bodies)) :
    Bounded info (nativeStubs ++ targetBodies) := by
  subst hinfo
  subst hbodies
  exact h

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.AllBounded
