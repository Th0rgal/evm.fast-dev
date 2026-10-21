import InitECandidate.Proofs.FrontendStages.Loop.Translate552
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody568_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody568_1 : HolLoopProg 64 :=
.mark loopBody568_0

def loopBody568_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody568_3 : HolLoopProg 64 :=
.mark loopBody568_2

def loopBody568_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody568_5 : HolLoopProg 64 :=
.mark loopBody568_4

def loopBody568_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody568_7 : HolLoopProg 64 :=
.mark loopBody568_6

def loopBody568_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody568_9 : HolLoopProg 64 :=
.mark loopBody568_8

def loopBody568_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody568_11 : HolLoopProg 64 :=
.mark loopBody568_10

def loopBody568_12 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 6 (Flapjack.RegImm.reg 7) loopBody568_9 loopBody568_11 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody568_13 : HolLoopProg 64 :=
.mark loopBody568_12

def loopBody568_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody568_15 : HolLoopProg 64 :=
.mark loopBody568_14

def loopBody568_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
    [Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 1#64],
      Flapjack.HolLoopExp.var 4])

def loopBody568_17 : HolLoopProg 64 :=
.mark loopBody568_16

def loopBody568_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 5) (Flapjack.HolLoopExp.const 2#64))

def loopBody568_19 : HolLoopProg 64 :=
.mark loopBody568_18

def loopBody568_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 1)

def loopBody568_21 : HolLoopProg 64 :=
.mark loopBody568_20

def loopBody568_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 1#64)

def loopBody568_23 : HolLoopProg 64 :=
.mark loopBody568_22

def loopBody568_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody568_25 : HolLoopProg 64 :=
.mark loopBody568_24

def loopBody568_26 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 8 (Flapjack.RegImm.reg 9) loopBody568_23 loopBody568_25 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody568_27 : HolLoopProg 64 :=
.mark loopBody568_26

def loopBody568_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 8)

def loopBody568_29 : HolLoopProg 64 :=
.mark loopBody568_28

def loopBody568_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsr
        (Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.add
            [Flapjack.HolLoopExp.var 0,
              Flapjack.HolLoopExp.shift Flapjack.Shift.lsl
                (Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 5)
                  (Flapjack.HolLoopExp.const 2#64))
                (Flapjack.HolLoopExp.const 3#64)]))
        (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl
          (Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 3#64])
          (Flapjack.HolLoopExp.const 3#64)),
      Flapjack.HolLoopExp.const 255#64])

def loopBody568_31 : HolLoopProg 64 :=
.mark loopBody568_30

def loopBody568_32 : HolLoopProg 64 :=
.seq loopBody568_31 loopBody568_1

def loopBody568_33 : HolLoopProg 64 :=
.mark loopBody568_32

def loopBody568_34 : HolLoopProg 64 :=
.seq loopBody568_33 loopBody568_1

def loopBody568_35 : HolLoopProg 64 :=
.mark loopBody568_34

def loopBody568_36 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody568_35 loopBody568_1 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody568_37 : HolLoopProg 64 :=
.mark loopBody568_36

def loopBody568_38 : HolLoopProg 64 :=
.seq loopBody568_37 loopBody568_1

def loopBody568_39 : HolLoopProg 64 :=
.mark loopBody568_38

def loopBody568_40 : HolLoopProg 64 :=
.seq loopBody568_29 loopBody568_39

def loopBody568_41 : HolLoopProg 64 :=
.mark loopBody568_40

def loopBody568_42 : HolLoopProg 64 :=
.seq loopBody568_27 loopBody568_41

def loopBody568_43 : HolLoopProg 64 :=
.mark loopBody568_42

def loopBody568_44 : HolLoopProg 64 :=
.seq loopBody568_21 loopBody568_43

def loopBody568_45 : HolLoopProg 64 :=
.mark loopBody568_44

def loopBody568_46 : HolLoopProg 64 :=
.seq loopBody568_19 loopBody568_45

def loopBody568_47 : HolLoopProg 64 :=
.mark loopBody568_46

def loopBody568_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.var 4])

def loopBody568_49 : HolLoopProg 64 :=
.mark loopBody568_48

def loopBody568_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.storeByte 7 8

def loopBody568_51 : HolLoopProg 64 :=
.mark loopBody568_50

def loopBody568_52 : HolLoopProg 64 :=
.seq loopBody568_51 loopBody568_1

def loopBody568_53 : HolLoopProg 64 :=
.mark loopBody568_52

def loopBody568_54 : HolLoopProg 64 :=
.seq loopBody568_15 loopBody568_53

def loopBody568_55 : HolLoopProg 64 :=
.mark loopBody568_54

def loopBody568_56 : HolLoopProg 64 :=
.seq loopBody568_49 loopBody568_55

def loopBody568_57 : HolLoopProg 64 :=
.mark loopBody568_56

def loopBody568_58 : HolLoopProg 64 :=
.seq loopBody568_47 loopBody568_57

def loopBody568_59 : HolLoopProg 64 :=
.mark loopBody568_58

def loopBody568_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 1#64])

def loopBody568_61 : HolLoopProg 64 :=
.mark loopBody568_60

def loopBody568_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 7)

def loopBody568_63 : HolLoopProg 64 :=
.mark loopBody568_62

def loopBody568_64 : HolLoopProg 64 :=
.seq loopBody568_63 loopBody568_1

def loopBody568_65 : HolLoopProg 64 :=
.mark loopBody568_64

def loopBody568_66 : HolLoopProg 64 :=
.seq loopBody568_65 loopBody568_1

def loopBody568_67 : HolLoopProg 64 :=
.mark loopBody568_66

def loopBody568_68 : HolLoopProg 64 :=
.seq loopBody568_61 loopBody568_67

def loopBody568_69 : HolLoopProg 64 :=
.mark loopBody568_68

def loopBody568_70 : HolLoopProg 64 :=
.seq loopBody568_1 loopBody568_69

def loopBody568_71 : HolLoopProg 64 :=
.mark loopBody568_70

def loopBody568_72 : HolLoopProg 64 :=
.seq loopBody568_59 loopBody568_71

def loopBody568_73 : HolLoopProg 64 :=
.mark loopBody568_72

def loopBody568_74 : HolLoopProg 64 :=
.seq loopBody568_11 loopBody568_73

def loopBody568_75 : HolLoopProg 64 :=
.mark loopBody568_74

def loopBody568_76 : HolLoopProg 64 :=
.seq loopBody568_1 loopBody568_75

def loopBody568_77 : HolLoopProg 64 :=
.mark loopBody568_76

def loopBody568_78 : HolLoopProg 64 :=
.seq loopBody568_17 loopBody568_77

def loopBody568_79 : HolLoopProg 64 :=
.mark loopBody568_78

def loopBody568_80 : HolLoopProg 64 :=
.seq loopBody568_1 loopBody568_79

def loopBody568_81 : HolLoopProg 64 :=
.mark loopBody568_80

def loopBody568_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody568_83 : HolLoopProg 64 :=
.mark loopBody568_82

def loopBody568_84 : HolLoopProg 64 :=
.seq loopBody568_81 loopBody568_83

def loopBody568_85 : HolLoopProg 64 :=
.mark loopBody568_84

def loopBody568_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody568_87 : HolLoopProg 64 :=
.mark loopBody568_86

def loopBody568_88 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody568_85 loopBody568_87 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody568_89 : HolLoopProg 64 :=
.mark loopBody568_88

def loopBody568_90 : HolLoopProg 64 :=
.seq loopBody568_89 loopBody568_1

def loopBody568_91 : HolLoopProg 64 :=
.mark loopBody568_90

def loopBody568_92 : HolLoopProg 64 :=
.seq loopBody568_15 loopBody568_91

def loopBody568_93 : HolLoopProg 64 :=
.mark loopBody568_92

def loopBody568_94 : HolLoopProg 64 :=
.seq loopBody568_13 loopBody568_93

def loopBody568_95 : HolLoopProg 64 :=
.mark loopBody568_94

def loopBody568_96 : HolLoopProg 64 :=
.seq loopBody568_7 loopBody568_95

def loopBody568_97 : HolLoopProg 64 :=
.mark loopBody568_96

def loopBody568_98 : HolLoopProg 64 :=
.seq loopBody568_5 loopBody568_97

def loopBody568_99 : HolLoopProg 64 :=
.mark loopBody568_98

def loopBody568_100 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody568_99 (Flapjack.Spt.ln)

def loopBody568_101 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody568_102 : HolLoopProg 64 :=
.mark loopBody568_101

def loopBody568_103 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody568_104 : HolLoopProg 64 :=
.mark loopBody568_103

def loopBody568_105 : HolLoopProg 64 :=
.seq loopBody568_104 loopBody568_1

def loopBody568_106 : HolLoopProg 64 :=
.mark loopBody568_105

def loopBody568_107 : HolLoopProg 64 :=
.seq loopBody568_102 loopBody568_106

def loopBody568_108 : HolLoopProg 64 :=
.mark loopBody568_107

def loopBody568_109 : HolLoopProg 64 :=
.seq loopBody568_100 loopBody568_108

def loopBody568_110 : HolLoopProg 64 :=
.seq loopBody568_3 loopBody568_109

def loopBody568_111 : HolLoopProg 64 :=
.seq loopBody568_1 loopBody568_110

def output568 : Nat × List Nat × HolLoopProg 64 :=
  (632, [0, 1, 2, 3], loopBody568_111)
end InitECandidate.Proofs.FrontendStages.Loop
