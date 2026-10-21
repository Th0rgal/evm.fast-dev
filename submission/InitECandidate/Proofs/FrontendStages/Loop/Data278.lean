import InitECandidate.Proofs.FrontendStages.Loop.Translate262
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody278_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody278_1 : HolLoopProg 64 :=
.mark loopBody278_0

def loopBody278_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody278_3 : HolLoopProg 64 :=
.mark loopBody278_2

def loopBody278_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody278_5 : HolLoopProg 64 :=
.mark loopBody278_4

def loopBody278_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody278_7 : HolLoopProg 64 :=
.mark loopBody278_6

def loopBody278_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.tick

def loopBody278_9 : HolLoopProg 64 :=
.mark loopBody278_8

def loopBody278_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.lookup 0#5)

def loopBody278_11 : HolLoopProg 64 :=
.mark loopBody278_10

def loopBody278_12 : HolLoopProg 64 :=
.seq loopBody278_11 loopBody278_1

def loopBody278_13 : HolLoopProg 64 :=
.mark loopBody278_12

def loopBody278_14 : HolLoopProg 64 :=
.seq loopBody278_13 loopBody278_1

def loopBody278_15 : HolLoopProg 64 :=
.mark loopBody278_14

def loopBody278_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.const 100#64, Flapjack.HolLoopExp.var 3])

def loopBody278_17 : HolLoopProg 64 :=
.mark loopBody278_16

def loopBody278_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 4)

def loopBody278_19 : HolLoopProg 64 :=
.mark loopBody278_18

def loopBody278_20 : HolLoopProg 64 :=
.seq loopBody278_19 loopBody278_1

def loopBody278_21 : HolLoopProg 64 :=
.mark loopBody278_20

def loopBody278_22 : HolLoopProg 64 :=
.seq loopBody278_21 loopBody278_1

def loopBody278_23 : HolLoopProg 64 :=
.mark loopBody278_22

def loopBody278_24 : HolLoopProg 64 :=
.seq loopBody278_17 loopBody278_23

def loopBody278_25 : HolLoopProg 64 :=
.mark loopBody278_24

def loopBody278_26 : HolLoopProg 64 :=
.seq loopBody278_1 loopBody278_25

def loopBody278_27 : HolLoopProg 64 :=
.mark loopBody278_26

def loopBody278_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 6#64)

def loopBody278_29 : HolLoopProg 64 :=
.mark loopBody278_28

def loopBody278_30 : HolLoopProg 64 :=
.seq loopBody278_29 loopBody278_7

def loopBody278_31 : HolLoopProg 64 :=
.mark loopBody278_30

def loopBody278_32 : HolLoopProg 64 :=
.seq loopBody278_27 loopBody278_31

def loopBody278_33 : HolLoopProg 64 :=
.mark loopBody278_32

def loopBody278_34 : HolLoopProg 64 :=
.seq loopBody278_15 loopBody278_33

def loopBody278_35 : HolLoopProg 64 :=
.mark loopBody278_34

def loopBody278_36 : HolLoopProg 64 :=
.seq loopBody278_9 loopBody278_35

def loopBody278_37 : HolLoopProg 64 :=
.mark loopBody278_36

def loopBody278_38 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.imm 1#64) loopBody278_7 loopBody278_37 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)

def loopBody278_39 : HolLoopProg 64 :=
.mark loopBody278_38

def loopBody278_40 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 341) ([4, 5]) (some (4, loopBody278_39, loopBody278_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody278_41 : HolLoopProg 64 :=
.mark loopBody278_40

def loopBody278_42 : HolLoopProg 64 :=
.seq loopBody278_41 loopBody278_1

def loopBody278_43 : HolLoopProg 64 :=
.mark loopBody278_42

def loopBody278_44 : HolLoopProg 64 :=
.seq loopBody278_5 loopBody278_43

def loopBody278_45 : HolLoopProg 64 :=
.mark loopBody278_44

def loopBody278_46 : HolLoopProg 64 :=
.seq loopBody278_3 loopBody278_45

def loopBody278_47 : HolLoopProg 64 :=
.mark loopBody278_46

def loopBody278_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody278_49 : HolLoopProg 64 :=
.mark loopBody278_48

def loopBody278_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody278_51 : HolLoopProg 64 :=
.mark loopBody278_50

def loopBody278_52 : HolLoopProg 64 :=
.seq loopBody278_51 loopBody278_1

def loopBody278_53 : HolLoopProg 64 :=
.mark loopBody278_52

def loopBody278_54 : HolLoopProg 64 :=
.seq loopBody278_49 loopBody278_53

def loopBody278_55 : HolLoopProg 64 :=
.mark loopBody278_54

def loopBody278_56 : HolLoopProg 64 :=
.seq loopBody278_47 loopBody278_55

def loopBody278_57 : HolLoopProg 64 :=
.mark loopBody278_56

def loopBody278_58 : HolLoopProg 64 :=
.seq loopBody278_1 loopBody278_57

def loopBody278_59 : HolLoopProg 64 :=
.mark loopBody278_58

def loopBody278_60 : HolLoopProg 64 :=
.seq loopBody278_1 loopBody278_59

def loopBody278_61 : HolLoopProg 64 :=
.mark loopBody278_60

def loopBody278_62 : HolLoopProg 64 :=
.seq loopBody278_1 loopBody278_61

def loopBody278_63 : HolLoopProg 64 :=
.mark loopBody278_62

def loopBody278_64 : HolLoopProg 64 :=
.seq loopBody278_1 loopBody278_63

def loopBody278_65 : HolLoopProg 64 :=
.mark loopBody278_64

def output278 : Nat × List Nat × HolLoopProg 64 :=
  (342, [0, 1], loopBody278_65)
end InitECandidate.Proofs.FrontendStages.Loop
