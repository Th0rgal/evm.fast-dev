import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Table28_50
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded28
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded29
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded30
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded31
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded32
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded33
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded34
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded35
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded36
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded37
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded38
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded39
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded40
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded41
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded42
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded43
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded44
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded45
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded46
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded47
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded48
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded49
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded50

/-! Assembled `stepCost ≤ 7313` certificate for Stream D (`Bounded28..Bounded50`, functions `512..877`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded28_50
open LoweredBudget

theorem bounded28 : Bounded GlobalFrameInfo.info Table28_50.bodies28 := Bounded28.bounded

theorem bounded29 : Bounded GlobalFrameInfo.info Table28_50.bodies29 :=
  bounded_append GlobalFrameInfo.info _ _ bounded28 Bounded29.bounded

theorem bounded30 : Bounded GlobalFrameInfo.info Table28_50.bodies30 :=
  bounded_append GlobalFrameInfo.info _ _ bounded29 Bounded30.bounded

theorem bounded31 : Bounded GlobalFrameInfo.info Table28_50.bodies31 :=
  bounded_append GlobalFrameInfo.info _ _ bounded30 Bounded31.bounded

theorem bounded32 : Bounded GlobalFrameInfo.info Table28_50.bodies32 :=
  bounded_append GlobalFrameInfo.info _ _ bounded31 Bounded32.bounded

theorem bounded33 : Bounded GlobalFrameInfo.info Table28_50.bodies33 :=
  bounded_append GlobalFrameInfo.info _ _ bounded32 Bounded33.bounded

theorem bounded34 : Bounded GlobalFrameInfo.info Table28_50.bodies34 :=
  bounded_append GlobalFrameInfo.info _ _ bounded33 Bounded34.bounded

theorem bounded35 : Bounded GlobalFrameInfo.info Table28_50.bodies35 :=
  bounded_append GlobalFrameInfo.info _ _ bounded34 Bounded35.bounded

theorem bounded36 : Bounded GlobalFrameInfo.info Table28_50.bodies36 :=
  bounded_append GlobalFrameInfo.info _ _ bounded35 Bounded36.bounded

theorem bounded37 : Bounded GlobalFrameInfo.info Table28_50.bodies37 :=
  bounded_append GlobalFrameInfo.info _ _ bounded36 Bounded37.bounded

theorem bounded38 : Bounded GlobalFrameInfo.info Table28_50.bodies38 :=
  bounded_append GlobalFrameInfo.info _ _ bounded37 Bounded38.bounded

theorem bounded39 : Bounded GlobalFrameInfo.info Table28_50.bodies39 :=
  bounded_append GlobalFrameInfo.info _ _ bounded38 Bounded39.bounded

theorem bounded40 : Bounded GlobalFrameInfo.info Table28_50.bodies40 :=
  bounded_append GlobalFrameInfo.info _ _ bounded39 Bounded40.bounded

theorem bounded41 : Bounded GlobalFrameInfo.info Table28_50.bodies41 :=
  bounded_append GlobalFrameInfo.info _ _ bounded40 Bounded41.bounded

theorem bounded42 : Bounded GlobalFrameInfo.info Table28_50.bodies42 :=
  bounded_append GlobalFrameInfo.info _ _ bounded41 Bounded42.bounded

theorem bounded43 : Bounded GlobalFrameInfo.info Table28_50.bodies43 :=
  bounded_append GlobalFrameInfo.info _ _ bounded42 Bounded43.bounded

theorem bounded44 : Bounded GlobalFrameInfo.info Table28_50.bodies44 :=
  bounded_append GlobalFrameInfo.info _ _ bounded43 Bounded44.bounded

theorem bounded45 : Bounded GlobalFrameInfo.info Table28_50.bodies45 :=
  bounded_append GlobalFrameInfo.info _ _ bounded44 Bounded45.bounded

theorem bounded46 : Bounded GlobalFrameInfo.info Table28_50.bodies46 :=
  bounded_append GlobalFrameInfo.info _ _ bounded45 Bounded46.bounded

theorem bounded47 : Bounded GlobalFrameInfo.info Table28_50.bodies47 :=
  bounded_append GlobalFrameInfo.info _ _ bounded46 Bounded47.bounded

theorem bounded48 : Bounded GlobalFrameInfo.info Table28_50.bodies48 :=
  bounded_append GlobalFrameInfo.info _ _ bounded47 Bounded48.bounded

theorem bounded49 : Bounded GlobalFrameInfo.info Table28_50.bodies49 :=
  bounded_append GlobalFrameInfo.info _ _ bounded48 Bounded49.bounded

theorem bounded50 : Bounded GlobalFrameInfo.info Table28_50.bodies50 :=
  bounded_append GlobalFrameInfo.info _ _ bounded49 Bounded50.bounded

theorem bounded : Bounded GlobalFrameInfo.info Table28_50.bodies :=
  bounded50

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded28_50
