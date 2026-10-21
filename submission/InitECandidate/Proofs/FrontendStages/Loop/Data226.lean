import InitECandidate.Proofs.FrontendStages.Loop.Translate210
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody226_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody226_1 : HolLoopProg 64 :=
.mark loopBody226_0

def loopBody226_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody226_3 : HolLoopProg 64 :=
.mark loopBody226_2

def loopBody226_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody226_5 : HolLoopProg 64 :=
.mark loopBody226_4

def loopBody226_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody226_7 : HolLoopProg 64 :=
.mark loopBody226_6

def loopBody226_8 : HolLoopProg 64 :=
.call (some ([2, 3], Flapjack.Spt.ln)) (some 186) ([4, 5]) (some (4, loopBody226_7, loopBody226_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody226_9 : HolLoopProg 64 :=
.mark loopBody226_8

def loopBody226_10 : HolLoopProg 64 :=
.seq loopBody226_9 loopBody226_1

def loopBody226_11 : HolLoopProg 64 :=
.mark loopBody226_10

def loopBody226_12 : HolLoopProg 64 :=
.seq loopBody226_5 loopBody226_11

def loopBody226_13 : HolLoopProg 64 :=
.mark loopBody226_12

def loopBody226_14 : HolLoopProg 64 :=
.seq loopBody226_3 loopBody226_13

def loopBody226_15 : HolLoopProg 64 :=
.mark loopBody226_14

def loopBody226_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody226_17 : HolLoopProg 64 :=
.mark loopBody226_16

def loopBody226_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody226_19 : HolLoopProg 64 :=
.mark loopBody226_18

def loopBody226_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody226_21 : HolLoopProg 64 :=
.mark loopBody226_20

def loopBody226_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody226_23 : HolLoopProg 64 :=
.mark loopBody226_22

def loopBody226_24 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 5 (Flapjack.RegImm.reg 6) loopBody226_21 loopBody226_23 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))

def loopBody226_25 : HolLoopProg 64 :=
.mark loopBody226_24

def loopBody226_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody226_27 : HolLoopProg 64 :=
.mark loopBody226_26

def loopBody226_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody226_29 : HolLoopProg 64 :=
.mark loopBody226_28

def loopBody226_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4, 5, 6]

def loopBody226_31 : HolLoopProg 64 :=
.mark loopBody226_30

def loopBody226_32 : HolLoopProg 64 :=
.seq loopBody226_31 loopBody226_1

def loopBody226_33 : HolLoopProg 64 :=
.mark loopBody226_32

def loopBody226_34 : HolLoopProg 64 :=
.seq loopBody226_19 loopBody226_33

def loopBody226_35 : HolLoopProg 64 :=
.mark loopBody226_34

def loopBody226_36 : HolLoopProg 64 :=
.seq loopBody226_23 loopBody226_35

def loopBody226_37 : HolLoopProg 64 :=
.mark loopBody226_36

def loopBody226_38 : HolLoopProg 64 :=
.seq loopBody226_29 loopBody226_37

def loopBody226_39 : HolLoopProg 64 :=
.mark loopBody226_38

def loopBody226_40 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody226_39 loopBody226_1 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody226_41 : HolLoopProg 64 :=
.mark loopBody226_40

def loopBody226_42 : HolLoopProg 64 :=
.seq loopBody226_41 loopBody226_1

def loopBody226_43 : HolLoopProg 64 :=
.mark loopBody226_42

def loopBody226_44 : HolLoopProg 64 :=
.seq loopBody226_27 loopBody226_43

def loopBody226_45 : HolLoopProg 64 :=
.mark loopBody226_44

def loopBody226_46 : HolLoopProg 64 :=
.seq loopBody226_25 loopBody226_45

def loopBody226_47 : HolLoopProg 64 :=
.mark loopBody226_46

def loopBody226_48 : HolLoopProg 64 :=
.seq loopBody226_19 loopBody226_47

def loopBody226_49 : HolLoopProg 64 :=
.mark loopBody226_48

def loopBody226_50 : HolLoopProg 64 :=
.seq loopBody226_17 loopBody226_49

def loopBody226_51 : HolLoopProg 64 :=
.mark loopBody226_50

def loopBody226_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody226_53 : HolLoopProg 64 :=
.mark loopBody226_52

def loopBody226_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.load (Flapjack.HolLoopExp.var 3))

def loopBody226_55 : HolLoopProg 64 :=
.mark loopBody226_54

def loopBody226_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 8#64]))

def loopBody226_57 : HolLoopProg 64 :=
.mark loopBody226_56

def loopBody226_58 : HolLoopProg 64 :=
.seq loopBody226_57 loopBody226_33

def loopBody226_59 : HolLoopProg 64 :=
.mark loopBody226_58

def loopBody226_60 : HolLoopProg 64 :=
.seq loopBody226_55 loopBody226_59

def loopBody226_61 : HolLoopProg 64 :=
.mark loopBody226_60

def loopBody226_62 : HolLoopProg 64 :=
.seq loopBody226_53 loopBody226_61

def loopBody226_63 : HolLoopProg 64 :=
.mark loopBody226_62

def loopBody226_64 : HolLoopProg 64 :=
.seq loopBody226_51 loopBody226_63

def loopBody226_65 : HolLoopProg 64 :=
.mark loopBody226_64

def loopBody226_66 : HolLoopProg 64 :=
.seq loopBody226_15 loopBody226_65

def loopBody226_67 : HolLoopProg 64 :=
.mark loopBody226_66

def loopBody226_68 : HolLoopProg 64 :=
.seq loopBody226_1 loopBody226_67

def loopBody226_69 : HolLoopProg 64 :=
.mark loopBody226_68

def loopBody226_70 : HolLoopProg 64 :=
.seq loopBody226_1 loopBody226_69

def loopBody226_71 : HolLoopProg 64 :=
.mark loopBody226_70

def loopBody226_72 : HolLoopProg 64 :=
.seq loopBody226_1 loopBody226_71

def loopBody226_73 : HolLoopProg 64 :=
.mark loopBody226_72

def loopBody226_74 : HolLoopProg 64 :=
.seq loopBody226_1 loopBody226_73

def loopBody226_75 : HolLoopProg 64 :=
.mark loopBody226_74

def output226 : Nat × List Nat × HolLoopProg 64 :=
  (290, [0, 1], loopBody226_75)
end InitECandidate.Proofs.FrontendStages.Loop
