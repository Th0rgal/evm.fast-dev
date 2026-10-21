import InitECandidate.Proofs.FrontendStages.Loop.Translate242
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody258_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody258_1 : HolLoopProg 64 :=
.mark loopBody258_0

def loopBody258_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody258_3 : HolLoopProg 64 :=
.mark loopBody258_2

def loopBody258_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody258_5 : HolLoopProg 64 :=
.mark loopBody258_4

def loopBody258_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody258_7 : HolLoopProg 64 :=
.mark loopBody258_6

def loopBody258_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody258_9 : HolLoopProg 64 :=
.mark loopBody258_8

def loopBody258_10 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 4 (Flapjack.RegImm.reg 5) loopBody258_9 loopBody258_5 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.ls PUnit.unit))

def loopBody258_11 : HolLoopProg 64 :=
.mark loopBody258_10

def loopBody258_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody258_13 : HolLoopProg 64 :=
.mark loopBody258_12

def loopBody258_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody258_15 : HolLoopProg 64 :=
.mark loopBody258_14

def loopBody258_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 3 3

def loopBody258_17 : HolLoopProg 64 :=
.mark loopBody258_16

def loopBody258_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 3)

def loopBody258_19 : HolLoopProg 64 :=
.mark loopBody258_18

def loopBody258_20 : HolLoopProg 64 :=
.seq loopBody258_19 loopBody258_1

def loopBody258_21 : HolLoopProg 64 :=
.mark loopBody258_20

def loopBody258_22 : HolLoopProg 64 :=
.seq loopBody258_17 loopBody258_21

def loopBody258_23 : HolLoopProg 64 :=
.mark loopBody258_22

def loopBody258_24 : HolLoopProg 64 :=
.seq loopBody258_15 loopBody258_23

def loopBody258_25 : HolLoopProg 64 :=
.mark loopBody258_24

def loopBody258_26 : HolLoopProg 64 :=
.seq loopBody258_25 loopBody258_1

def loopBody258_27 : HolLoopProg 64 :=
.mark loopBody258_26

def loopBody258_28 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody258_27 loopBody258_1 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))

def loopBody258_29 : HolLoopProg 64 :=
.mark loopBody258_28

def loopBody258_30 : HolLoopProg 64 :=
.seq loopBody258_29 loopBody258_1

def loopBody258_31 : HolLoopProg 64 :=
.mark loopBody258_30

def loopBody258_32 : HolLoopProg 64 :=
.seq loopBody258_13 loopBody258_31

def loopBody258_33 : HolLoopProg 64 :=
.mark loopBody258_32

def loopBody258_34 : HolLoopProg 64 :=
.seq loopBody258_11 loopBody258_33

def loopBody258_35 : HolLoopProg 64 :=
.mark loopBody258_34

def loopBody258_36 : HolLoopProg 64 :=
.seq loopBody258_7 loopBody258_35

def loopBody258_37 : HolLoopProg 64 :=
.mark loopBody258_36

def loopBody258_38 : HolLoopProg 64 :=
.seq loopBody258_5 loopBody258_37

def loopBody258_39 : HolLoopProg 64 :=
.mark loopBody258_38

def loopBody258_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 2)

def loopBody258_41 : HolLoopProg 64 :=
.mark loopBody258_40

def loopBody258_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody258_43 : HolLoopProg 64 :=
.mark loopBody258_42

def loopBody258_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 179) [3, 4] none

def loopBody258_45 : HolLoopProg 64 :=
.mark loopBody258_44

def loopBody258_46 : HolLoopProg 64 :=
.seq loopBody258_45 loopBody258_1

def loopBody258_47 : HolLoopProg 64 :=
.mark loopBody258_46

def loopBody258_48 : HolLoopProg 64 :=
.seq loopBody258_43 loopBody258_47

def loopBody258_49 : HolLoopProg 64 :=
.mark loopBody258_48

def loopBody258_50 : HolLoopProg 64 :=
.seq loopBody258_41 loopBody258_49

def loopBody258_51 : HolLoopProg 64 :=
.mark loopBody258_50

def loopBody258_52 : HolLoopProg 64 :=
.seq loopBody258_39 loopBody258_51

def loopBody258_53 : HolLoopProg 64 :=
.mark loopBody258_52

def loopBody258_54 : HolLoopProg 64 :=
.seq loopBody258_3 loopBody258_53

def loopBody258_55 : HolLoopProg 64 :=
.mark loopBody258_54

def loopBody258_56 : HolLoopProg 64 :=
.seq loopBody258_1 loopBody258_55

def loopBody258_57 : HolLoopProg 64 :=
.mark loopBody258_56

def output258 : Nat × List Nat × HolLoopProg 64 :=
  (322, [0, 1], loopBody258_57)
end InitECandidate.Proofs.FrontendStages.Loop
