import InitECandidate.Proofs.FrontendStages.Loop.Translate386
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody402_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody402_1 : HolLoopProg 64 :=
.mark loopBody402_0

def loopBody402_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 64#64]))

def loopBody402_3 : HolLoopProg 64 :=
.mark loopBody402_2

def loopBody402_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody402_5 : HolLoopProg 64 :=
.mark loopBody402_4

def loopBody402_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody402_7 : HolLoopProg 64 :=
.mark loopBody402_6

def loopBody402_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody402_9 : HolLoopProg 64 :=
.mark loopBody402_8

def loopBody402_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody402_11 : HolLoopProg 64 :=
.mark loopBody402_10

def loopBody402_12 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 3 (Flapjack.RegImm.reg 4) loopBody402_9 loopBody402_11 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody402_13 : HolLoopProg 64 :=
.mark loopBody402_12

def loopBody402_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody402_15 : HolLoopProg 64 :=
.mark loopBody402_14

def loopBody402_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 4#64)

def loopBody402_17 : HolLoopProg 64 :=
.mark loopBody402_16

def loopBody402_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 2)

def loopBody402_19 : HolLoopProg 64 :=
.mark loopBody402_18

def loopBody402_20 : HolLoopProg 64 :=
.seq loopBody402_19 loopBody402_1

def loopBody402_21 : HolLoopProg 64 :=
.mark loopBody402_20

def loopBody402_22 : HolLoopProg 64 :=
.seq loopBody402_21 loopBody402_1

def loopBody402_23 : HolLoopProg 64 :=
.mark loopBody402_22

def loopBody402_24 : HolLoopProg 64 :=
.seq loopBody402_17 loopBody402_23

def loopBody402_25 : HolLoopProg 64 :=
.mark loopBody402_24

def loopBody402_26 : HolLoopProg 64 :=
.seq loopBody402_1 loopBody402_25

def loopBody402_27 : HolLoopProg 64 :=
.mark loopBody402_26

def loopBody402_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 8#64)

def loopBody402_29 : HolLoopProg 64 :=
.mark loopBody402_28

def loopBody402_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody402_31 : HolLoopProg 64 :=
.mark loopBody402_30

def loopBody402_32 : HolLoopProg 64 :=
.seq loopBody402_29 loopBody402_31

def loopBody402_33 : HolLoopProg 64 :=
.mark loopBody402_32

def loopBody402_34 : HolLoopProg 64 :=
.seq loopBody402_27 loopBody402_33

def loopBody402_35 : HolLoopProg 64 :=
.mark loopBody402_34

def loopBody402_36 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.imm 0#64) loopBody402_35 loopBody402_1 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody402_37 : HolLoopProg 64 :=
.mark loopBody402_36

def loopBody402_38 : HolLoopProg 64 :=
.seq loopBody402_37 loopBody402_1

def loopBody402_39 : HolLoopProg 64 :=
.mark loopBody402_38

def loopBody402_40 : HolLoopProg 64 :=
.seq loopBody402_15 loopBody402_39

def loopBody402_41 : HolLoopProg 64 :=
.mark loopBody402_40

def loopBody402_42 : HolLoopProg 64 :=
.seq loopBody402_13 loopBody402_41

def loopBody402_43 : HolLoopProg 64 :=
.mark loopBody402_42

def loopBody402_44 : HolLoopProg 64 :=
.seq loopBody402_7 loopBody402_43

def loopBody402_45 : HolLoopProg 64 :=
.mark loopBody402_44

def loopBody402_46 : HolLoopProg 64 :=
.seq loopBody402_5 loopBody402_45

def loopBody402_47 : HolLoopProg 64 :=
.mark loopBody402_46

def loopBody402_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 64#64])

def loopBody402_49 : HolLoopProg 64 :=
.mark loopBody402_48

def loopBody402_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.var 0])

def loopBody402_51 : HolLoopProg 64 :=
.mark loopBody402_50

def loopBody402_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 3)

def loopBody402_53 : HolLoopProg 64 :=
.mark loopBody402_52

def loopBody402_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 2) 4

def loopBody402_55 : HolLoopProg 64 :=
.mark loopBody402_54

def loopBody402_56 : HolLoopProg 64 :=
.seq loopBody402_55 loopBody402_1

def loopBody402_57 : HolLoopProg 64 :=
.mark loopBody402_56

def loopBody402_58 : HolLoopProg 64 :=
.seq loopBody402_53 loopBody402_57

def loopBody402_59 : HolLoopProg 64 :=
.mark loopBody402_58

def loopBody402_60 : HolLoopProg 64 :=
.seq loopBody402_59 loopBody402_1

def loopBody402_61 : HolLoopProg 64 :=
.mark loopBody402_60

def loopBody402_62 : HolLoopProg 64 :=
.seq loopBody402_51 loopBody402_61

def loopBody402_63 : HolLoopProg 64 :=
.mark loopBody402_62

def loopBody402_64 : HolLoopProg 64 :=
.seq loopBody402_1 loopBody402_63

def loopBody402_65 : HolLoopProg 64 :=
.mark loopBody402_64

def loopBody402_66 : HolLoopProg 64 :=
.seq loopBody402_49 loopBody402_65

def loopBody402_67 : HolLoopProg 64 :=
.mark loopBody402_66

def loopBody402_68 : HolLoopProg 64 :=
.seq loopBody402_1 loopBody402_67

def loopBody402_69 : HolLoopProg 64 :=
.mark loopBody402_68

def loopBody402_70 : HolLoopProg 64 :=
.seq loopBody402_47 loopBody402_69

def loopBody402_71 : HolLoopProg 64 :=
.mark loopBody402_70

def loopBody402_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 184#64])

def loopBody402_73 : HolLoopProg 64 :=
.mark loopBody402_72

def loopBody402_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.load
              (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
            Flapjack.HolLoopExp.const 184#64]),
      Flapjack.HolLoopExp.var 0])

def loopBody402_75 : HolLoopProg 64 :=
.mark loopBody402_74

def loopBody402_76 : HolLoopProg 64 :=
.seq loopBody402_75 loopBody402_61

def loopBody402_77 : HolLoopProg 64 :=
.mark loopBody402_76

def loopBody402_78 : HolLoopProg 64 :=
.seq loopBody402_1 loopBody402_77

def loopBody402_79 : HolLoopProg 64 :=
.mark loopBody402_78

def loopBody402_80 : HolLoopProg 64 :=
.seq loopBody402_73 loopBody402_79

def loopBody402_81 : HolLoopProg 64 :=
.mark loopBody402_80

def loopBody402_82 : HolLoopProg 64 :=
.seq loopBody402_1 loopBody402_81

def loopBody402_83 : HolLoopProg 64 :=
.mark loopBody402_82

def loopBody402_84 : HolLoopProg 64 :=
.seq loopBody402_71 loopBody402_83

def loopBody402_85 : HolLoopProg 64 :=
.mark loopBody402_84

def loopBody402_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody402_87 : HolLoopProg 64 :=
.mark loopBody402_86

def loopBody402_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody402_89 : HolLoopProg 64 :=
.mark loopBody402_88

def loopBody402_90 : HolLoopProg 64 :=
.seq loopBody402_89 loopBody402_1

def loopBody402_91 : HolLoopProg 64 :=
.mark loopBody402_90

def loopBody402_92 : HolLoopProg 64 :=
.seq loopBody402_87 loopBody402_91

def loopBody402_93 : HolLoopProg 64 :=
.mark loopBody402_92

def loopBody402_94 : HolLoopProg 64 :=
.seq loopBody402_85 loopBody402_93

def loopBody402_95 : HolLoopProg 64 :=
.mark loopBody402_94

def loopBody402_96 : HolLoopProg 64 :=
.seq loopBody402_3 loopBody402_95

def loopBody402_97 : HolLoopProg 64 :=
.mark loopBody402_96

def loopBody402_98 : HolLoopProg 64 :=
.seq loopBody402_1 loopBody402_97

def loopBody402_99 : HolLoopProg 64 :=
.mark loopBody402_98

def output402 : Nat × List Nat × HolLoopProg 64 :=
  (466, [0], loopBody402_99)
end InitECandidate.Proofs.FrontendStages.Loop
