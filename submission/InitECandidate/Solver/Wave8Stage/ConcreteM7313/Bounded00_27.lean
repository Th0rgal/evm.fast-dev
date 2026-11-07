import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Table04
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Table05_27
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded00
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded01
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded02
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded03
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded04
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded05
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded06
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded07
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded08
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded09
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded10
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded11
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded12
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded13
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded14
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded15
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded16
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded17
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded18
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded19
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded20
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded21
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded22
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded23
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded24
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded25
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded26
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded27

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded00_27
open LoweredBudget

theorem bounded00 : Bounded GlobalFrameInfo.info Table00.bodies := Bounded00.bounded
theorem bounded01 : Bounded GlobalFrameInfo.info Table01.bodies :=
  bounded_append GlobalFrameInfo.info _ _ bounded00 Bounded01.bounded
theorem bounded02 : Bounded GlobalFrameInfo.info Table02.bodies :=
  bounded_append GlobalFrameInfo.info _ _ bounded01 Bounded02.bounded
theorem bounded03 : Bounded GlobalFrameInfo.info Table03.bodies :=
  bounded_append GlobalFrameInfo.info _ _ bounded02 Bounded03.bounded
theorem bounded04 : Bounded GlobalFrameInfo.info Table04.bodies :=
  bounded_append GlobalFrameInfo.info _ _ bounded03 Bounded04.bounded

theorem bounded05 : Bounded GlobalFrameInfo.info Table05_27.bodies05 := Bounded05.bounded
theorem bounded06 : Bounded GlobalFrameInfo.info Table05_27.bodies06 :=
  bounded_append GlobalFrameInfo.info _ _ bounded05 Bounded06.bounded
theorem bounded07 : Bounded GlobalFrameInfo.info Table05_27.bodies07 :=
  bounded_append GlobalFrameInfo.info _ _ bounded06 Bounded07.bounded
theorem bounded08 : Bounded GlobalFrameInfo.info Table05_27.bodies08 :=
  bounded_append GlobalFrameInfo.info _ _ bounded07 Bounded08.bounded
theorem bounded09 : Bounded GlobalFrameInfo.info Table05_27.bodies09 :=
  bounded_append GlobalFrameInfo.info _ _ bounded08 Bounded09.bounded
theorem bounded10 : Bounded GlobalFrameInfo.info Table05_27.bodies10 :=
  bounded_append GlobalFrameInfo.info _ _ bounded09 Bounded10.bounded
theorem bounded11 : Bounded GlobalFrameInfo.info Table05_27.bodies11 :=
  bounded_append GlobalFrameInfo.info _ _ bounded10 Bounded11.bounded
theorem bounded12 : Bounded GlobalFrameInfo.info Table05_27.bodies12 :=
  bounded_append GlobalFrameInfo.info _ _ bounded11 Bounded12.bounded
theorem bounded13 : Bounded GlobalFrameInfo.info Table05_27.bodies13 :=
  bounded_append GlobalFrameInfo.info _ _ bounded12 Bounded13.bounded
theorem bounded14 : Bounded GlobalFrameInfo.info Table05_27.bodies14 :=
  bounded_append GlobalFrameInfo.info _ _ bounded13 Bounded14.bounded
theorem bounded15 : Bounded GlobalFrameInfo.info Table05_27.bodies15 :=
  bounded_append GlobalFrameInfo.info _ _ bounded14 Bounded15.bounded
theorem bounded16 : Bounded GlobalFrameInfo.info Table05_27.bodies16 :=
  bounded_append GlobalFrameInfo.info _ _ bounded15 Bounded16.bounded
theorem bounded17 : Bounded GlobalFrameInfo.info Table05_27.bodies17 :=
  bounded_append GlobalFrameInfo.info _ _ bounded16 Bounded17.bounded
theorem bounded18 : Bounded GlobalFrameInfo.info Table05_27.bodies18 :=
  bounded_append GlobalFrameInfo.info _ _ bounded17 Bounded18.bounded
theorem bounded19 : Bounded GlobalFrameInfo.info Table05_27.bodies19 :=
  bounded_append GlobalFrameInfo.info _ _ bounded18 Bounded19.bounded
theorem bounded20 : Bounded GlobalFrameInfo.info Table05_27.bodies20 :=
  bounded_append GlobalFrameInfo.info _ _ bounded19 Bounded20.bounded
theorem bounded21 : Bounded GlobalFrameInfo.info Table05_27.bodies21 :=
  bounded_append GlobalFrameInfo.info _ _ bounded20 Bounded21.bounded
theorem bounded22 : Bounded GlobalFrameInfo.info Table05_27.bodies22 :=
  bounded_append GlobalFrameInfo.info _ _ bounded21 Bounded22.bounded
theorem bounded23 : Bounded GlobalFrameInfo.info Table05_27.bodies23 :=
  bounded_append GlobalFrameInfo.info _ _ bounded22 Bounded23.bounded
theorem bounded24 : Bounded GlobalFrameInfo.info Table05_27.bodies24 :=
  bounded_append GlobalFrameInfo.info _ _ bounded23 Bounded24.bounded
theorem bounded25 : Bounded GlobalFrameInfo.info Table05_27.bodies25 :=
  bounded_append GlobalFrameInfo.info _ _ bounded24 Bounded25.bounded
theorem bounded26 : Bounded GlobalFrameInfo.info Table05_27.bodies26 :=
  bounded_append GlobalFrameInfo.info _ _ bounded25 Bounded26.bounded
theorem bounded27 : Bounded GlobalFrameInfo.info Table05_27.bodies27 :=
  bounded_append GlobalFrameInfo.info _ _ bounded26 Bounded27.bounded

theorem bounded05_27 : Bounded GlobalFrameInfo.info Table05_27.bodies := bounded27

theorem bounded : Bounded GlobalFrameInfo.info (Table04.bodies ++ Table05_27.bodies) :=
  bounded_append GlobalFrameInfo.info _ _ bounded04 bounded05_27

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded00_27
