import InitECandidate.Proofs.FrontendStages.Loop.Translate299
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody315_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody315_1 : HolLoopProg 64 :=
.mark loopBody315_0

def loopBody315_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody315_3 : HolLoopProg 64 :=
.mark loopBody315_2

def loopBody315_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody315_5 : HolLoopProg 64 :=
.mark loopBody315_4

def loopBody315_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody315_7 : HolLoopProg 64 :=
.mark loopBody315_6

def loopBody315_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody315_9 : HolLoopProg 64 :=
.mark loopBody315_8

def loopBody315_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody315_11 : HolLoopProg 64 :=
.mark loopBody315_10

def loopBody315_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody315_13 : HolLoopProg 64 :=
.mark loopBody315_12

def loopBody315_14 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 5 (Flapjack.RegImm.reg 6) loopBody315_11 loopBody315_13 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody315_15 : HolLoopProg 64 :=
.mark loopBody315_14

def loopBody315_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody315_17 : HolLoopProg 64 :=
.mark loopBody315_16

def loopBody315_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.var 3])

def loopBody315_19 : HolLoopProg 64 :=
.mark loopBody315_18

def loopBody315_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 4 4

def loopBody315_21 : HolLoopProg 64 :=
.mark loopBody315_20

def loopBody315_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody315_23 : HolLoopProg 64 :=
.mark loopBody315_22

def loopBody315_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody315_25 : HolLoopProg 64 :=
.mark loopBody315_24

def loopBody315_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody315_27 : HolLoopProg 64 :=
.mark loopBody315_26

def loopBody315_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody315_29 : HolLoopProg 64 :=
.mark loopBody315_28

def loopBody315_30 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.RegImm.reg 7) loopBody315_27 loopBody315_29 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody315_31 : HolLoopProg 64 :=
.mark loopBody315_30

def loopBody315_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody315_33 : HolLoopProg 64 :=
.mark loopBody315_32

def loopBody315_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 1#64])

def loopBody315_35 : HolLoopProg 64 :=
.mark loopBody315_34

def loopBody315_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 4)

def loopBody315_37 : HolLoopProg 64 :=
.mark loopBody315_36

def loopBody315_38 : HolLoopProg 64 :=
.seq loopBody315_37 loopBody315_1

def loopBody315_39 : HolLoopProg 64 :=
.mark loopBody315_38

def loopBody315_40 : HolLoopProg 64 :=
.seq loopBody315_39 loopBody315_1

def loopBody315_41 : HolLoopProg 64 :=
.mark loopBody315_40

def loopBody315_42 : HolLoopProg 64 :=
.seq loopBody315_35 loopBody315_41

def loopBody315_43 : HolLoopProg 64 :=
.mark loopBody315_42

def loopBody315_44 : HolLoopProg 64 :=
.seq loopBody315_1 loopBody315_43

def loopBody315_45 : HolLoopProg 64 :=
.mark loopBody315_44

def loopBody315_46 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody315_45 loopBody315_1 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody315_47 : HolLoopProg 64 :=
.mark loopBody315_46

def loopBody315_48 : HolLoopProg 64 :=
.seq loopBody315_47 loopBody315_1

def loopBody315_49 : HolLoopProg 64 :=
.mark loopBody315_48

def loopBody315_50 : HolLoopProg 64 :=
.seq loopBody315_33 loopBody315_49

def loopBody315_51 : HolLoopProg 64 :=
.mark loopBody315_50

def loopBody315_52 : HolLoopProg 64 :=
.seq loopBody315_31 loopBody315_51

def loopBody315_53 : HolLoopProg 64 :=
.mark loopBody315_52

def loopBody315_54 : HolLoopProg 64 :=
.seq loopBody315_25 loopBody315_53

def loopBody315_55 : HolLoopProg 64 :=
.mark loopBody315_54

def loopBody315_56 : HolLoopProg 64 :=
.seq loopBody315_23 loopBody315_55

def loopBody315_57 : HolLoopProg 64 :=
.mark loopBody315_56

def loopBody315_58 : HolLoopProg 64 :=
.seq loopBody315_21 loopBody315_57

def loopBody315_59 : HolLoopProg 64 :=
.mark loopBody315_58

def loopBody315_60 : HolLoopProg 64 :=
.seq loopBody315_19 loopBody315_59

def loopBody315_61 : HolLoopProg 64 :=
.mark loopBody315_60

def loopBody315_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 1#64])

def loopBody315_63 : HolLoopProg 64 :=
.mark loopBody315_62

def loopBody315_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 4)

def loopBody315_65 : HolLoopProg 64 :=
.mark loopBody315_64

def loopBody315_66 : HolLoopProg 64 :=
.seq loopBody315_65 loopBody315_1

def loopBody315_67 : HolLoopProg 64 :=
.mark loopBody315_66

def loopBody315_68 : HolLoopProg 64 :=
.seq loopBody315_67 loopBody315_1

def loopBody315_69 : HolLoopProg 64 :=
.mark loopBody315_68

def loopBody315_70 : HolLoopProg 64 :=
.seq loopBody315_63 loopBody315_69

def loopBody315_71 : HolLoopProg 64 :=
.mark loopBody315_70

def loopBody315_72 : HolLoopProg 64 :=
.seq loopBody315_1 loopBody315_71

def loopBody315_73 : HolLoopProg 64 :=
.mark loopBody315_72

def loopBody315_74 : HolLoopProg 64 :=
.seq loopBody315_61 loopBody315_73

def loopBody315_75 : HolLoopProg 64 :=
.mark loopBody315_74

def loopBody315_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody315_77 : HolLoopProg 64 :=
.mark loopBody315_76

def loopBody315_78 : HolLoopProg 64 :=
.seq loopBody315_75 loopBody315_77

def loopBody315_79 : HolLoopProg 64 :=
.mark loopBody315_78

def loopBody315_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody315_81 : HolLoopProg 64 :=
.mark loopBody315_80

def loopBody315_82 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody315_79 loopBody315_81 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody315_83 : HolLoopProg 64 :=
.mark loopBody315_82

def loopBody315_84 : HolLoopProg 64 :=
.seq loopBody315_83 loopBody315_1

def loopBody315_85 : HolLoopProg 64 :=
.mark loopBody315_84

def loopBody315_86 : HolLoopProg 64 :=
.seq loopBody315_17 loopBody315_85

def loopBody315_87 : HolLoopProg 64 :=
.mark loopBody315_86

def loopBody315_88 : HolLoopProg 64 :=
.seq loopBody315_15 loopBody315_87

def loopBody315_89 : HolLoopProg 64 :=
.mark loopBody315_88

def loopBody315_90 : HolLoopProg 64 :=
.seq loopBody315_9 loopBody315_89

def loopBody315_91 : HolLoopProg 64 :=
.mark loopBody315_90

def loopBody315_92 : HolLoopProg 64 :=
.seq loopBody315_7 loopBody315_91

def loopBody315_93 : HolLoopProg 64 :=
.mark loopBody315_92

def loopBody315_94 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody315_93 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))

def loopBody315_95 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 2,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.var 2])
        (Flapjack.HolLoopExp.const 2#64)])

def loopBody315_96 : HolLoopProg 64 :=
.mark loopBody315_95

def loopBody315_97 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody315_98 : HolLoopProg 64 :=
.mark loopBody315_97

def loopBody315_99 : HolLoopProg 64 :=
.seq loopBody315_98 loopBody315_1

def loopBody315_100 : HolLoopProg 64 :=
.mark loopBody315_99

def loopBody315_101 : HolLoopProg 64 :=
.seq loopBody315_96 loopBody315_100

def loopBody315_102 : HolLoopProg 64 :=
.mark loopBody315_101

def loopBody315_103 : HolLoopProg 64 :=
.seq loopBody315_94 loopBody315_102

def loopBody315_104 : HolLoopProg 64 :=
.seq loopBody315_5 loopBody315_103

def loopBody315_105 : HolLoopProg 64 :=
.seq loopBody315_1 loopBody315_104

def loopBody315_106 : HolLoopProg 64 :=
.seq loopBody315_3 loopBody315_105

def loopBody315_107 : HolLoopProg 64 :=
.seq loopBody315_1 loopBody315_106

def output315 : Nat × List Nat × HolLoopProg 64 :=
  (379, [0, 1], loopBody315_107)
end InitECandidate.Proofs.FrontendStages.Loop
