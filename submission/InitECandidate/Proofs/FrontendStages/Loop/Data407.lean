import InitECandidate.Proofs.FrontendStages.Loop.Translate391
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody407_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody407_1 : HolLoopProg 64 :=
.mark loopBody407_0

def loopBody407_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 16#64]))

def loopBody407_3 : HolLoopProg 64 :=
.mark loopBody407_2

def loopBody407_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody407_5 : HolLoopProg 64 :=
.mark loopBody407_4

def loopBody407_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody407_7 : HolLoopProg 64 :=
.mark loopBody407_6

def loopBody407_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody407_9 : HolLoopProg 64 :=
.mark loopBody407_8

def loopBody407_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody407_11 : HolLoopProg 64 :=
.mark loopBody407_10

def loopBody407_12 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 3 (Flapjack.RegImm.reg 4) loopBody407_9 loopBody407_11 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody407_13 : HolLoopProg 64 :=
.mark loopBody407_12

def loopBody407_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody407_15 : HolLoopProg 64 :=
.mark loopBody407_14

def loopBody407_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 2#64)

def loopBody407_17 : HolLoopProg 64 :=
.mark loopBody407_16

def loopBody407_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 2)

def loopBody407_19 : HolLoopProg 64 :=
.mark loopBody407_18

def loopBody407_20 : HolLoopProg 64 :=
.seq loopBody407_19 loopBody407_1

def loopBody407_21 : HolLoopProg 64 :=
.mark loopBody407_20

def loopBody407_22 : HolLoopProg 64 :=
.seq loopBody407_21 loopBody407_1

def loopBody407_23 : HolLoopProg 64 :=
.mark loopBody407_22

def loopBody407_24 : HolLoopProg 64 :=
.seq loopBody407_17 loopBody407_23

def loopBody407_25 : HolLoopProg 64 :=
.mark loopBody407_24

def loopBody407_26 : HolLoopProg 64 :=
.seq loopBody407_1 loopBody407_25

def loopBody407_27 : HolLoopProg 64 :=
.mark loopBody407_26

def loopBody407_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 8#64)

def loopBody407_29 : HolLoopProg 64 :=
.mark loopBody407_28

def loopBody407_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody407_31 : HolLoopProg 64 :=
.mark loopBody407_30

def loopBody407_32 : HolLoopProg 64 :=
.seq loopBody407_29 loopBody407_31

def loopBody407_33 : HolLoopProg 64 :=
.mark loopBody407_32

def loopBody407_34 : HolLoopProg 64 :=
.seq loopBody407_27 loopBody407_33

def loopBody407_35 : HolLoopProg 64 :=
.mark loopBody407_34

def loopBody407_36 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.imm 0#64) loopBody407_35 loopBody407_1 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))

def loopBody407_37 : HolLoopProg 64 :=
.mark loopBody407_36

def loopBody407_38 : HolLoopProg 64 :=
.seq loopBody407_37 loopBody407_1

def loopBody407_39 : HolLoopProg 64 :=
.mark loopBody407_38

def loopBody407_40 : HolLoopProg 64 :=
.seq loopBody407_15 loopBody407_39

def loopBody407_41 : HolLoopProg 64 :=
.mark loopBody407_40

def loopBody407_42 : HolLoopProg 64 :=
.seq loopBody407_13 loopBody407_41

def loopBody407_43 : HolLoopProg 64 :=
.mark loopBody407_42

def loopBody407_44 : HolLoopProg 64 :=
.seq loopBody407_7 loopBody407_43

def loopBody407_45 : HolLoopProg 64 :=
.mark loopBody407_44

def loopBody407_46 : HolLoopProg 64 :=
.seq loopBody407_5 loopBody407_45

def loopBody407_47 : HolLoopProg 64 :=
.mark loopBody407_46

def loopBody407_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 1#64])

def loopBody407_49 : HolLoopProg 64 :=
.mark loopBody407_48

def loopBody407_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.var 2)

def loopBody407_51 : HolLoopProg 64 :=
.mark loopBody407_50

def loopBody407_52 : HolLoopProg 64 :=
.seq loopBody407_51 loopBody407_1

def loopBody407_53 : HolLoopProg 64 :=
.mark loopBody407_52

def loopBody407_54 : HolLoopProg 64 :=
.seq loopBody407_53 loopBody407_1

def loopBody407_55 : HolLoopProg 64 :=
.mark loopBody407_54

def loopBody407_56 : HolLoopProg 64 :=
.seq loopBody407_49 loopBody407_55

def loopBody407_57 : HolLoopProg 64 :=
.mark loopBody407_56

def loopBody407_58 : HolLoopProg 64 :=
.seq loopBody407_1 loopBody407_57

def loopBody407_59 : HolLoopProg 64 :=
.mark loopBody407_58

def loopBody407_60 : HolLoopProg 64 :=
.seq loopBody407_47 loopBody407_59

def loopBody407_61 : HolLoopProg 64 :=
.mark loopBody407_60

def loopBody407_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 16#64])

def loopBody407_63 : HolLoopProg 64 :=
.mark loopBody407_62

def loopBody407_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 3)

def loopBody407_65 : HolLoopProg 64 :=
.mark loopBody407_64

def loopBody407_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 2) 4

def loopBody407_67 : HolLoopProg 64 :=
.mark loopBody407_66

def loopBody407_68 : HolLoopProg 64 :=
.seq loopBody407_67 loopBody407_1

def loopBody407_69 : HolLoopProg 64 :=
.mark loopBody407_68

def loopBody407_70 : HolLoopProg 64 :=
.seq loopBody407_65 loopBody407_69

def loopBody407_71 : HolLoopProg 64 :=
.mark loopBody407_70

def loopBody407_72 : HolLoopProg 64 :=
.seq loopBody407_71 loopBody407_1

def loopBody407_73 : HolLoopProg 64 :=
.mark loopBody407_72

def loopBody407_74 : HolLoopProg 64 :=
.seq loopBody407_5 loopBody407_73

def loopBody407_75 : HolLoopProg 64 :=
.mark loopBody407_74

def loopBody407_76 : HolLoopProg 64 :=
.seq loopBody407_1 loopBody407_75

def loopBody407_77 : HolLoopProg 64 :=
.mark loopBody407_76

def loopBody407_78 : HolLoopProg 64 :=
.seq loopBody407_63 loopBody407_77

def loopBody407_79 : HolLoopProg 64 :=
.mark loopBody407_78

def loopBody407_80 : HolLoopProg 64 :=
.seq loopBody407_1 loopBody407_79

def loopBody407_81 : HolLoopProg 64 :=
.mark loopBody407_80

def loopBody407_82 : HolLoopProg 64 :=
.seq loopBody407_61 loopBody407_81

def loopBody407_83 : HolLoopProg 64 :=
.mark loopBody407_82

def loopBody407_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.add
            [Flapjack.HolLoopExp.load
                (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                  [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
              Flapjack.HolLoopExp.const 8#64]),
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 1) (Flapjack.HolLoopExp.const 5#64)]))

def loopBody407_85 : HolLoopProg 64 :=
.mark loopBody407_84

def loopBody407_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.load
              (Flapjack.HolLoopExp.op Flapjack.BinOp.add
                [Flapjack.HolLoopExp.load
                    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                      [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
                  Flapjack.HolLoopExp.const 8#64]),
            Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 1) (Flapjack.HolLoopExp.const 5#64)],
        Flapjack.HolLoopExp.const 8#64]))

def loopBody407_87 : HolLoopProg 64 :=
.mark loopBody407_86

def loopBody407_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.load
              (Flapjack.HolLoopExp.op Flapjack.BinOp.add
                [Flapjack.HolLoopExp.load
                    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                      [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
                  Flapjack.HolLoopExp.const 8#64]),
            Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 1) (Flapjack.HolLoopExp.const 5#64)],
        Flapjack.HolLoopExp.const 16#64]))

def loopBody407_89 : HolLoopProg 64 :=
.mark loopBody407_88

def loopBody407_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.load
              (Flapjack.HolLoopExp.op Flapjack.BinOp.add
                [Flapjack.HolLoopExp.load
                    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                      [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
                  Flapjack.HolLoopExp.const 8#64]),
            Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 1) (Flapjack.HolLoopExp.const 5#64)],
        Flapjack.HolLoopExp.const 24#64]))

def loopBody407_91 : HolLoopProg 64 :=
.mark loopBody407_90

def loopBody407_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2, 3, 4, 5]

def loopBody407_93 : HolLoopProg 64 :=
.mark loopBody407_92

def loopBody407_94 : HolLoopProg 64 :=
.seq loopBody407_93 loopBody407_1

def loopBody407_95 : HolLoopProg 64 :=
.mark loopBody407_94

def loopBody407_96 : HolLoopProg 64 :=
.seq loopBody407_91 loopBody407_95

def loopBody407_97 : HolLoopProg 64 :=
.mark loopBody407_96

def loopBody407_98 : HolLoopProg 64 :=
.seq loopBody407_89 loopBody407_97

def loopBody407_99 : HolLoopProg 64 :=
.mark loopBody407_98

def loopBody407_100 : HolLoopProg 64 :=
.seq loopBody407_87 loopBody407_99

def loopBody407_101 : HolLoopProg 64 :=
.mark loopBody407_100

def loopBody407_102 : HolLoopProg 64 :=
.seq loopBody407_85 loopBody407_101

def loopBody407_103 : HolLoopProg 64 :=
.mark loopBody407_102

def loopBody407_104 : HolLoopProg 64 :=
.seq loopBody407_83 loopBody407_103

def loopBody407_105 : HolLoopProg 64 :=
.mark loopBody407_104

def loopBody407_106 : HolLoopProg 64 :=
.seq loopBody407_3 loopBody407_105

def loopBody407_107 : HolLoopProg 64 :=
.mark loopBody407_106

def loopBody407_108 : HolLoopProg 64 :=
.seq loopBody407_1 loopBody407_107

def loopBody407_109 : HolLoopProg 64 :=
.mark loopBody407_108

def output407 : Nat × List Nat × HolLoopProg 64 :=
  (471, [], loopBody407_109)
end InitECandidate.Proofs.FrontendStages.Loop
