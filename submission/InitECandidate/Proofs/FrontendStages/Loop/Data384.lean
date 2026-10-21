import InitECandidate.Proofs.FrontendStages.Loop.Translate368
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody384_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody384_1 : HolLoopProg 64 :=
.mark loopBody384_0

def loopBody384_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 216#64]))

def loopBody384_3 : HolLoopProg 64 :=
.mark loopBody384_2

def loopBody384_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 0)

def loopBody384_5 : HolLoopProg 64 :=
.mark loopBody384_4

def loopBody384_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody384_7 : HolLoopProg 64 :=
.mark loopBody384_6

def loopBody384_8 : HolLoopProg 64 :=
.call (some
  ([4, 5],
    Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 186) ([6, 7]) (some (6, loopBody384_7, loopBody384_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody384_9 : HolLoopProg 64 :=
.mark loopBody384_8

def loopBody384_10 : HolLoopProg 64 :=
.seq loopBody384_9 loopBody384_1

def loopBody384_11 : HolLoopProg 64 :=
.mark loopBody384_10

def loopBody384_12 : HolLoopProg 64 :=
.seq loopBody384_5 loopBody384_11

def loopBody384_13 : HolLoopProg 64 :=
.mark loopBody384_12

def loopBody384_14 : HolLoopProg 64 :=
.seq loopBody384_3 loopBody384_13

def loopBody384_15 : HolLoopProg 64 :=
.mark loopBody384_14

def loopBody384_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody384_17 : HolLoopProg 64 :=
.mark loopBody384_16

def loopBody384_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody384_19 : HolLoopProg 64 :=
.mark loopBody384_18

def loopBody384_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody384_21 : HolLoopProg 64 :=
.mark loopBody384_20

def loopBody384_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody384_23 : HolLoopProg 64 :=
.mark loopBody384_22

def loopBody384_24 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 7 (Flapjack.RegImm.reg 8) loopBody384_21 loopBody384_23 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody384_25 : HolLoopProg 64 :=
.mark loopBody384_24

def loopBody384_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody384_27 : HolLoopProg 64 :=
.mark loopBody384_26

def loopBody384_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody384_29 : HolLoopProg 64 :=
.mark loopBody384_28

def loopBody384_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody384_31 : HolLoopProg 64 :=
.mark loopBody384_30

def loopBody384_32 : HolLoopProg 64 :=
.seq loopBody384_31 loopBody384_1

def loopBody384_33 : HolLoopProg 64 :=
.mark loopBody384_32

def loopBody384_34 : HolLoopProg 64 :=
.seq loopBody384_29 loopBody384_33

def loopBody384_35 : HolLoopProg 64 :=
.mark loopBody384_34

def loopBody384_36 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody384_35 loopBody384_1 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody384_37 : HolLoopProg 64 :=
.mark loopBody384_36

def loopBody384_38 : HolLoopProg 64 :=
.seq loopBody384_37 loopBody384_1

def loopBody384_39 : HolLoopProg 64 :=
.mark loopBody384_38

def loopBody384_40 : HolLoopProg 64 :=
.seq loopBody384_27 loopBody384_39

def loopBody384_41 : HolLoopProg 64 :=
.mark loopBody384_40

def loopBody384_42 : HolLoopProg 64 :=
.seq loopBody384_25 loopBody384_41

def loopBody384_43 : HolLoopProg 64 :=
.mark loopBody384_42

def loopBody384_44 : HolLoopProg 64 :=
.seq loopBody384_19 loopBody384_43

def loopBody384_45 : HolLoopProg 64 :=
.mark loopBody384_44

def loopBody384_46 : HolLoopProg 64 :=
.seq loopBody384_17 loopBody384_45

def loopBody384_47 : HolLoopProg 64 :=
.mark loopBody384_46

def loopBody384_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.var 1]))

def loopBody384_49 : HolLoopProg 64 :=
.mark loopBody384_48

def loopBody384_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 2)

def loopBody384_51 : HolLoopProg 64 :=
.mark loopBody384_50

def loopBody384_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 3)

def loopBody384_53 : HolLoopProg 64 :=
.mark loopBody384_52

def loopBody384_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody384_55 : HolLoopProg 64 :=
.mark loopBody384_54

def loopBody384_56 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.ln)) (some 447) ([7, 8, 9]) (some (7, loopBody384_55, loopBody384_1, (Flapjack.Spt.ln)))

def loopBody384_57 : HolLoopProg 64 :=
.mark loopBody384_56

def loopBody384_58 : HolLoopProg 64 :=
.seq loopBody384_57 loopBody384_1

def loopBody384_59 : HolLoopProg 64 :=
.mark loopBody384_58

def loopBody384_60 : HolLoopProg 64 :=
.seq loopBody384_53 loopBody384_59

def loopBody384_61 : HolLoopProg 64 :=
.mark loopBody384_60

def loopBody384_62 : HolLoopProg 64 :=
.seq loopBody384_51 loopBody384_61

def loopBody384_63 : HolLoopProg 64 :=
.mark loopBody384_62

def loopBody384_64 : HolLoopProg 64 :=
.seq loopBody384_49 loopBody384_63

def loopBody384_65 : HolLoopProg 64 :=
.mark loopBody384_64

def loopBody384_66 : HolLoopProg 64 :=
.seq loopBody384_1 loopBody384_65

def loopBody384_67 : HolLoopProg 64 :=
.mark loopBody384_66

def loopBody384_68 : HolLoopProg 64 :=
.seq loopBody384_1 loopBody384_67

def loopBody384_69 : HolLoopProg 64 :=
.mark loopBody384_68

def loopBody384_70 : HolLoopProg 64 :=
.seq loopBody384_47 loopBody384_69

def loopBody384_71 : HolLoopProg 64 :=
.mark loopBody384_70

def loopBody384_72 : HolLoopProg 64 :=
.seq loopBody384_71 loopBody384_35

def loopBody384_73 : HolLoopProg 64 :=
.mark loopBody384_72

def loopBody384_74 : HolLoopProg 64 :=
.seq loopBody384_15 loopBody384_73

def loopBody384_75 : HolLoopProg 64 :=
.mark loopBody384_74

def loopBody384_76 : HolLoopProg 64 :=
.seq loopBody384_1 loopBody384_75

def loopBody384_77 : HolLoopProg 64 :=
.mark loopBody384_76

def loopBody384_78 : HolLoopProg 64 :=
.seq loopBody384_1 loopBody384_77

def loopBody384_79 : HolLoopProg 64 :=
.mark loopBody384_78

def loopBody384_80 : HolLoopProg 64 :=
.seq loopBody384_1 loopBody384_79

def loopBody384_81 : HolLoopProg 64 :=
.mark loopBody384_80

def loopBody384_82 : HolLoopProg 64 :=
.seq loopBody384_1 loopBody384_81

def loopBody384_83 : HolLoopProg 64 :=
.mark loopBody384_82

def output384 : Nat × List Nat × HolLoopProg 64 :=
  (448, [0, 1, 2, 3], loopBody384_83)
end InitECandidate.Proofs.FrontendStages.Loop
