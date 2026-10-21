import InitECandidate.Proofs.FrontendStages.Loop.Translate757
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody773_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody773_1 : HolLoopProg 64 :=
.mark loopBody773_0

def loopBody773_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 8#64]))

def loopBody773_3 : HolLoopProg 64 :=
.mark loopBody773_2

def loopBody773_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 0#64]))

def loopBody773_5 : HolLoopProg 64 :=
.mark loopBody773_4

def loopBody773_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 16#64)

def loopBody773_7 : HolLoopProg 64 :=
.mark loopBody773_6

def loopBody773_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody773_9 : HolLoopProg 64 :=
.mark loopBody773_8

def loopBody773_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody773_11 : HolLoopProg 64 :=
.mark loopBody773_10

def loopBody773_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody773_13 : HolLoopProg 64 :=
.mark loopBody773_12

def loopBody773_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody773_15 : HolLoopProg 64 :=
.mark loopBody773_14

def loopBody773_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody773_17 : HolLoopProg 64 :=
.mark loopBody773_16

def loopBody773_18 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.less) 6 (Flapjack.RegImm.reg 7) loopBody773_15 loopBody773_17 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody773_19 : HolLoopProg 64 :=
.mark loopBody773_18

def loopBody773_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody773_21 : HolLoopProg 64 :=
.mark loopBody773_20

def loopBody773_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 2,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 3#64)]))

def loopBody773_23 : HolLoopProg 64 :=
.mark loopBody773_22

def loopBody773_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 16#64]))

def loopBody773_25 : HolLoopProg 64 :=
.mark loopBody773_24

def loopBody773_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 33#64)

def loopBody773_27 : HolLoopProg 64 :=
.mark loopBody773_26

def loopBody773_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.arith (Flapjack.LoopArith.longMul 8 8 6 7)

def loopBody773_29 : HolLoopProg 64 :=
.mark loopBody773_28

def loopBody773_30 : HolLoopProg 64 :=
.seq loopBody773_29 loopBody773_1

def loopBody773_31 : HolLoopProg 64 :=
.mark loopBody773_30

def loopBody773_32 : HolLoopProg 64 :=
.seq loopBody773_27 loopBody773_31

def loopBody773_33 : HolLoopProg 64 :=
.mark loopBody773_32

def loopBody773_34 : HolLoopProg 64 :=
.seq loopBody773_25 loopBody773_33

def loopBody773_35 : HolLoopProg 64 :=
.mark loopBody773_34

def loopBody773_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 64#64, Flapjack.HolLoopExp.var 8,
      Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 32#64])])

def loopBody773_37 : HolLoopProg 64 :=
.mark loopBody773_36

def loopBody773_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 9)

def loopBody773_39 : HolLoopProg 64 :=
.mark loopBody773_38

def loopBody773_40 : HolLoopProg 64 :=
.seq loopBody773_39 loopBody773_1

def loopBody773_41 : HolLoopProg 64 :=
.mark loopBody773_40

def loopBody773_42 : HolLoopProg 64 :=
.seq loopBody773_41 loopBody773_1

def loopBody773_43 : HolLoopProg 64 :=
.mark loopBody773_42

def loopBody773_44 : HolLoopProg 64 :=
.seq loopBody773_37 loopBody773_43

def loopBody773_45 : HolLoopProg 64 :=
.mark loopBody773_44

def loopBody773_46 : HolLoopProg 64 :=
.seq loopBody773_35 loopBody773_45

def loopBody773_47 : HolLoopProg 64 :=
.mark loopBody773_46

def loopBody773_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 1#64])

def loopBody773_49 : HolLoopProg 64 :=
.mark loopBody773_48

def loopBody773_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 6)

def loopBody773_51 : HolLoopProg 64 :=
.mark loopBody773_50

def loopBody773_52 : HolLoopProg 64 :=
.seq loopBody773_51 loopBody773_1

def loopBody773_53 : HolLoopProg 64 :=
.mark loopBody773_52

def loopBody773_54 : HolLoopProg 64 :=
.seq loopBody773_53 loopBody773_1

def loopBody773_55 : HolLoopProg 64 :=
.mark loopBody773_54

def loopBody773_56 : HolLoopProg 64 :=
.seq loopBody773_49 loopBody773_55

def loopBody773_57 : HolLoopProg 64 :=
.mark loopBody773_56

def loopBody773_58 : HolLoopProg 64 :=
.seq loopBody773_1 loopBody773_57

def loopBody773_59 : HolLoopProg 64 :=
.mark loopBody773_58

def loopBody773_60 : HolLoopProg 64 :=
.seq loopBody773_47 loopBody773_59

def loopBody773_61 : HolLoopProg 64 :=
.mark loopBody773_60

def loopBody773_62 : HolLoopProg 64 :=
.seq loopBody773_23 loopBody773_61

def loopBody773_63 : HolLoopProg 64 :=
.mark loopBody773_62

def loopBody773_64 : HolLoopProg 64 :=
.seq loopBody773_1 loopBody773_63

def loopBody773_65 : HolLoopProg 64 :=
.mark loopBody773_64

def loopBody773_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody773_67 : HolLoopProg 64 :=
.mark loopBody773_66

def loopBody773_68 : HolLoopProg 64 :=
.seq loopBody773_65 loopBody773_67

def loopBody773_69 : HolLoopProg 64 :=
.mark loopBody773_68

def loopBody773_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody773_71 : HolLoopProg 64 :=
.mark loopBody773_70

def loopBody773_72 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody773_69 loopBody773_71 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody773_73 : HolLoopProg 64 :=
.mark loopBody773_72

def loopBody773_74 : HolLoopProg 64 :=
.seq loopBody773_73 loopBody773_1

def loopBody773_75 : HolLoopProg 64 :=
.mark loopBody773_74

def loopBody773_76 : HolLoopProg 64 :=
.seq loopBody773_21 loopBody773_75

def loopBody773_77 : HolLoopProg 64 :=
.mark loopBody773_76

def loopBody773_78 : HolLoopProg 64 :=
.seq loopBody773_19 loopBody773_77

def loopBody773_79 : HolLoopProg 64 :=
.mark loopBody773_78

def loopBody773_80 : HolLoopProg 64 :=
.seq loopBody773_13 loopBody773_79

def loopBody773_81 : HolLoopProg 64 :=
.mark loopBody773_80

def loopBody773_82 : HolLoopProg 64 :=
.seq loopBody773_11 loopBody773_81

def loopBody773_83 : HolLoopProg 64 :=
.mark loopBody773_82

def loopBody773_84 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody773_83 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody773_85 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody773_86 : HolLoopProg 64 :=
.mark loopBody773_85

def loopBody773_87 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody773_88 : HolLoopProg 64 :=
.mark loopBody773_87

def loopBody773_89 : HolLoopProg 64 :=
.seq loopBody773_88 loopBody773_1

def loopBody773_90 : HolLoopProg 64 :=
.mark loopBody773_89

def loopBody773_91 : HolLoopProg 64 :=
.seq loopBody773_86 loopBody773_90

def loopBody773_92 : HolLoopProg 64 :=
.mark loopBody773_91

def loopBody773_93 : HolLoopProg 64 :=
.seq loopBody773_84 loopBody773_92

def loopBody773_94 : HolLoopProg 64 :=
.seq loopBody773_9 loopBody773_93

def loopBody773_95 : HolLoopProg 64 :=
.seq loopBody773_1 loopBody773_94

def loopBody773_96 : HolLoopProg 64 :=
.seq loopBody773_7 loopBody773_95

def loopBody773_97 : HolLoopProg 64 :=
.seq loopBody773_1 loopBody773_96

def loopBody773_98 : HolLoopProg 64 :=
.seq loopBody773_5 loopBody773_97

def loopBody773_99 : HolLoopProg 64 :=
.seq loopBody773_1 loopBody773_98

def loopBody773_100 : HolLoopProg 64 :=
.seq loopBody773_3 loopBody773_99

def loopBody773_101 : HolLoopProg 64 :=
.seq loopBody773_1 loopBody773_100

def output773 : Nat × List Nat × HolLoopProg 64 :=
  (837, [0], loopBody773_101)
end InitECandidate.Proofs.FrontendStages.Loop
