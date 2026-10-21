import InitECandidate.Proofs.FrontendStages.Loop.Translate767
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody783_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody783_1 : HolLoopProg 64 :=
.mark loopBody783_0

def loopBody783_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody783_3 : HolLoopProg 64 :=
.mark loopBody783_2

def loopBody783_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody783_5 : HolLoopProg 64 :=
.mark loopBody783_4

def loopBody783_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody783_7 : HolLoopProg 64 :=
.mark loopBody783_6

def loopBody783_8 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 88) ([5, 6]) (some (5, loopBody783_7, loopBody783_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody783_9 : HolLoopProg 64 :=
.mark loopBody783_8

def loopBody783_10 : HolLoopProg 64 :=
.seq loopBody783_9 loopBody783_1

def loopBody783_11 : HolLoopProg 64 :=
.mark loopBody783_10

def loopBody783_12 : HolLoopProg 64 :=
.seq loopBody783_5 loopBody783_11

def loopBody783_13 : HolLoopProg 64 :=
.mark loopBody783_12

def loopBody783_14 : HolLoopProg 64 :=
.seq loopBody783_3 loopBody783_13

def loopBody783_15 : HolLoopProg 64 :=
.mark loopBody783_14

def loopBody783_16 : HolLoopProg 64 :=
.seq loopBody783_1 loopBody783_15

def loopBody783_17 : HolLoopProg 64 :=
.mark loopBody783_16

def loopBody783_18 : HolLoopProg 64 :=
.seq loopBody783_1 loopBody783_17

def loopBody783_19 : HolLoopProg 64 :=
.mark loopBody783_18

def loopBody783_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 4#64])

def loopBody783_21 : HolLoopProg 64 :=
.mark loopBody783_20

def loopBody783_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 2)

def loopBody783_23 : HolLoopProg 64 :=
.mark loopBody783_22

def loopBody783_24 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 89) ([5, 6]) (some (5, loopBody783_7, loopBody783_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody783_25 : HolLoopProg 64 :=
.mark loopBody783_24

def loopBody783_26 : HolLoopProg 64 :=
.seq loopBody783_25 loopBody783_1

def loopBody783_27 : HolLoopProg 64 :=
.mark loopBody783_26

def loopBody783_28 : HolLoopProg 64 :=
.seq loopBody783_23 loopBody783_27

def loopBody783_29 : HolLoopProg 64 :=
.mark loopBody783_28

def loopBody783_30 : HolLoopProg 64 :=
.seq loopBody783_21 loopBody783_29

def loopBody783_31 : HolLoopProg 64 :=
.mark loopBody783_30

def loopBody783_32 : HolLoopProg 64 :=
.seq loopBody783_1 loopBody783_31

def loopBody783_33 : HolLoopProg 64 :=
.mark loopBody783_32

def loopBody783_34 : HolLoopProg 64 :=
.seq loopBody783_1 loopBody783_33

def loopBody783_35 : HolLoopProg 64 :=
.mark loopBody783_34

def loopBody783_36 : HolLoopProg 64 :=
.seq loopBody783_19 loopBody783_35

def loopBody783_37 : HolLoopProg 64 :=
.mark loopBody783_36

def loopBody783_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 12#64])

def loopBody783_39 : HolLoopProg 64 :=
.mark loopBody783_38

def loopBody783_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody783_41 : HolLoopProg 64 :=
.mark loopBody783_40

def loopBody783_42 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.ln)) (some 89) ([5, 6]) (some (5, loopBody783_7, loopBody783_1, (Flapjack.Spt.ln)))

def loopBody783_43 : HolLoopProg 64 :=
.mark loopBody783_42

def loopBody783_44 : HolLoopProg 64 :=
.seq loopBody783_43 loopBody783_1

def loopBody783_45 : HolLoopProg 64 :=
.mark loopBody783_44

def loopBody783_46 : HolLoopProg 64 :=
.seq loopBody783_41 loopBody783_45

def loopBody783_47 : HolLoopProg 64 :=
.mark loopBody783_46

def loopBody783_48 : HolLoopProg 64 :=
.seq loopBody783_39 loopBody783_47

def loopBody783_49 : HolLoopProg 64 :=
.mark loopBody783_48

def loopBody783_50 : HolLoopProg 64 :=
.seq loopBody783_1 loopBody783_49

def loopBody783_51 : HolLoopProg 64 :=
.mark loopBody783_50

def loopBody783_52 : HolLoopProg 64 :=
.seq loopBody783_1 loopBody783_51

def loopBody783_53 : HolLoopProg 64 :=
.mark loopBody783_52

def loopBody783_54 : HolLoopProg 64 :=
.seq loopBody783_37 loopBody783_53

def loopBody783_55 : HolLoopProg 64 :=
.mark loopBody783_54

def loopBody783_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody783_57 : HolLoopProg 64 :=
.mark loopBody783_56

def loopBody783_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody783_59 : HolLoopProg 64 :=
.mark loopBody783_58

def loopBody783_60 : HolLoopProg 64 :=
.seq loopBody783_59 loopBody783_1

def loopBody783_61 : HolLoopProg 64 :=
.mark loopBody783_60

def loopBody783_62 : HolLoopProg 64 :=
.seq loopBody783_57 loopBody783_61

def loopBody783_63 : HolLoopProg 64 :=
.mark loopBody783_62

def loopBody783_64 : HolLoopProg 64 :=
.seq loopBody783_55 loopBody783_63

def loopBody783_65 : HolLoopProg 64 :=
.mark loopBody783_64

def output783 : Nat × List Nat × HolLoopProg 64 :=
  (847, [0, 1, 2, 3], loopBody783_65)
end InitECandidate.Proofs.FrontendStages.Loop
