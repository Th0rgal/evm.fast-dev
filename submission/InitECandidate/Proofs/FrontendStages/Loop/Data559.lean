import InitECandidate.Proofs.FrontendStages.Loop.Translate543
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody559_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody559_1 : HolLoopProg 64 :=
.mark loopBody559_0

def loopBody559_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 16#64)

def loopBody559_3 : HolLoopProg 64 :=
.mark loopBody559_2

def loopBody559_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody559_5 : HolLoopProg 64 :=
.mark loopBody559_4

def loopBody559_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody559_7 : HolLoopProg 64 :=
.mark loopBody559_6

def loopBody559_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 5 (Flapjack.RegImm.reg 6) loopBody559_5 loopBody559_7 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody559_9 : HolLoopProg 64 :=
.mark loopBody559_8

def loopBody559_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody559_11 : HolLoopProg 64 :=
.mark loopBody559_10

def loopBody559_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.xor
    [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.var 3])

def loopBody559_13 : HolLoopProg 64 :=
.mark loopBody559_12

def loopBody559_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody559_15 : HolLoopProg 64 :=
.mark loopBody559_14

def loopBody559_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody559_17 : HolLoopProg 64 :=
.mark loopBody559_16

def loopBody559_18 : HolLoopProg 64 :=
.seq loopBody559_15 loopBody559_17

def loopBody559_19 : HolLoopProg 64 :=
.mark loopBody559_18

def loopBody559_20 : HolLoopProg 64 :=
.seq loopBody559_13 loopBody559_19

def loopBody559_21 : HolLoopProg 64 :=
.mark loopBody559_20

def loopBody559_22 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody559_21 loopBody559_17 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody559_23 : HolLoopProg 64 :=
.mark loopBody559_22

def loopBody559_24 : HolLoopProg 64 :=
.seq loopBody559_23 loopBody559_17

def loopBody559_25 : HolLoopProg 64 :=
.mark loopBody559_24

def loopBody559_26 : HolLoopProg 64 :=
.seq loopBody559_11 loopBody559_25

def loopBody559_27 : HolLoopProg 64 :=
.mark loopBody559_26

def loopBody559_28 : HolLoopProg 64 :=
.seq loopBody559_9 loopBody559_27

def loopBody559_29 : HolLoopProg 64 :=
.mark loopBody559_28

def loopBody559_30 : HolLoopProg 64 :=
.seq loopBody559_3 loopBody559_29

def loopBody559_31 : HolLoopProg 64 :=
.mark loopBody559_30

def loopBody559_32 : HolLoopProg 64 :=
.seq loopBody559_1 loopBody559_31

def loopBody559_33 : HolLoopProg 64 :=
.mark loopBody559_32

def loopBody559_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 32#64)

def loopBody559_35 : HolLoopProg 64 :=
.mark loopBody559_34

def loopBody559_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or
    [Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.var 2],
      Flapjack.HolLoopExp.op Flapjack.BinOp.and
        [Flapjack.HolLoopExp.op Flapjack.BinOp.xor [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 4294967295#64],
          Flapjack.HolLoopExp.var 3]])

def loopBody559_37 : HolLoopProg 64 :=
.mark loopBody559_36

def loopBody559_38 : HolLoopProg 64 :=
.seq loopBody559_37 loopBody559_19

def loopBody559_39 : HolLoopProg 64 :=
.mark loopBody559_38

def loopBody559_40 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody559_39 loopBody559_17 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody559_41 : HolLoopProg 64 :=
.mark loopBody559_40

def loopBody559_42 : HolLoopProg 64 :=
.seq loopBody559_41 loopBody559_17

def loopBody559_43 : HolLoopProg 64 :=
.mark loopBody559_42

def loopBody559_44 : HolLoopProg 64 :=
.seq loopBody559_11 loopBody559_43

def loopBody559_45 : HolLoopProg 64 :=
.mark loopBody559_44

def loopBody559_46 : HolLoopProg 64 :=
.seq loopBody559_9 loopBody559_45

def loopBody559_47 : HolLoopProg 64 :=
.mark loopBody559_46

def loopBody559_48 : HolLoopProg 64 :=
.seq loopBody559_35 loopBody559_47

def loopBody559_49 : HolLoopProg 64 :=
.mark loopBody559_48

def loopBody559_50 : HolLoopProg 64 :=
.seq loopBody559_1 loopBody559_49

def loopBody559_51 : HolLoopProg 64 :=
.mark loopBody559_50

def loopBody559_52 : HolLoopProg 64 :=
.seq loopBody559_33 loopBody559_51

def loopBody559_53 : HolLoopProg 64 :=
.mark loopBody559_52

def loopBody559_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 48#64)

def loopBody559_55 : HolLoopProg 64 :=
.mark loopBody559_54

def loopBody559_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.xor
    [Flapjack.HolLoopExp.op Flapjack.BinOp.or
        [Flapjack.HolLoopExp.var 1,
          Flapjack.HolLoopExp.op Flapjack.BinOp.xor
            [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 4294967295#64]],
      Flapjack.HolLoopExp.var 3])

def loopBody559_57 : HolLoopProg 64 :=
.mark loopBody559_56

def loopBody559_58 : HolLoopProg 64 :=
.seq loopBody559_57 loopBody559_19

def loopBody559_59 : HolLoopProg 64 :=
.mark loopBody559_58

def loopBody559_60 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody559_59 loopBody559_17 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody559_61 : HolLoopProg 64 :=
.mark loopBody559_60

def loopBody559_62 : HolLoopProg 64 :=
.seq loopBody559_61 loopBody559_17

def loopBody559_63 : HolLoopProg 64 :=
.mark loopBody559_62

def loopBody559_64 : HolLoopProg 64 :=
.seq loopBody559_11 loopBody559_63

def loopBody559_65 : HolLoopProg 64 :=
.mark loopBody559_64

def loopBody559_66 : HolLoopProg 64 :=
.seq loopBody559_9 loopBody559_65

def loopBody559_67 : HolLoopProg 64 :=
.mark loopBody559_66

def loopBody559_68 : HolLoopProg 64 :=
.seq loopBody559_55 loopBody559_67

def loopBody559_69 : HolLoopProg 64 :=
.mark loopBody559_68

def loopBody559_70 : HolLoopProg 64 :=
.seq loopBody559_1 loopBody559_69

def loopBody559_71 : HolLoopProg 64 :=
.mark loopBody559_70

def loopBody559_72 : HolLoopProg 64 :=
.seq loopBody559_53 loopBody559_71

def loopBody559_73 : HolLoopProg 64 :=
.mark loopBody559_72

def loopBody559_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 64#64)

def loopBody559_75 : HolLoopProg 64 :=
.mark loopBody559_74

def loopBody559_76 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 5 (Flapjack.RegImm.reg 6) loopBody559_5 loopBody559_7 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody559_77 : HolLoopProg 64 :=
.mark loopBody559_76

def loopBody559_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or
    [Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.var 3],
      Flapjack.HolLoopExp.op Flapjack.BinOp.and
        [Flapjack.HolLoopExp.var 2,
          Flapjack.HolLoopExp.op Flapjack.BinOp.xor
            [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 4294967295#64]]])

def loopBody559_79 : HolLoopProg 64 :=
.mark loopBody559_78

def loopBody559_80 : HolLoopProg 64 :=
.seq loopBody559_79 loopBody559_19

def loopBody559_81 : HolLoopProg 64 :=
.mark loopBody559_80

def loopBody559_82 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody559_81 loopBody559_17 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody559_83 : HolLoopProg 64 :=
.mark loopBody559_82

def loopBody559_84 : HolLoopProg 64 :=
.seq loopBody559_83 loopBody559_17

def loopBody559_85 : HolLoopProg 64 :=
.mark loopBody559_84

def loopBody559_86 : HolLoopProg 64 :=
.seq loopBody559_11 loopBody559_85

def loopBody559_87 : HolLoopProg 64 :=
.mark loopBody559_86

def loopBody559_88 : HolLoopProg 64 :=
.seq loopBody559_77 loopBody559_87

def loopBody559_89 : HolLoopProg 64 :=
.mark loopBody559_88

def loopBody559_90 : HolLoopProg 64 :=
.seq loopBody559_75 loopBody559_89

def loopBody559_91 : HolLoopProg 64 :=
.mark loopBody559_90

def loopBody559_92 : HolLoopProg 64 :=
.seq loopBody559_1 loopBody559_91

def loopBody559_93 : HolLoopProg 64 :=
.mark loopBody559_92

def loopBody559_94 : HolLoopProg 64 :=
.seq loopBody559_73 loopBody559_93

def loopBody559_95 : HolLoopProg 64 :=
.mark loopBody559_94

def loopBody559_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.xor
    [Flapjack.HolLoopExp.var 1,
      Flapjack.HolLoopExp.op Flapjack.BinOp.or
        [Flapjack.HolLoopExp.var 2,
          Flapjack.HolLoopExp.op Flapjack.BinOp.xor
            [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 4294967295#64]]])

def loopBody559_97 : HolLoopProg 64 :=
.mark loopBody559_96

def loopBody559_98 : HolLoopProg 64 :=
.seq loopBody559_97 loopBody559_19

def loopBody559_99 : HolLoopProg 64 :=
.mark loopBody559_98

def loopBody559_100 : HolLoopProg 64 :=
.seq loopBody559_95 loopBody559_99

def loopBody559_101 : HolLoopProg 64 :=
.mark loopBody559_100

def output559 : Nat × List Nat × HolLoopProg 64 :=
  (623, [0, 1, 2, 3], loopBody559_101)
end InitECandidate.Proofs.FrontendStages.Loop
