import InitECandidate.Proofs.FrontendStages.Loop.Translate455
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody471_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody471_1 : HolLoopProg 64 :=
.mark loopBody471_0

def loopBody471_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 3#64)

def loopBody471_3 : HolLoopProg 64 :=
.mark loopBody471_2

def loopBody471_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody471_5 : HolLoopProg 64 :=
.mark loopBody471_4

def loopBody471_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ls PUnit.unit)) (some 466) ([2]) (some (2, loopBody471_5, loopBody471_1, (Flapjack.Spt.ls PUnit.unit)))

def loopBody471_7 : HolLoopProg 64 :=
.mark loopBody471_6

def loopBody471_8 : HolLoopProg 64 :=
.seq loopBody471_7 loopBody471_1

def loopBody471_9 : HolLoopProg 64 :=
.mark loopBody471_8

def loopBody471_10 : HolLoopProg 64 :=
.seq loopBody471_3 loopBody471_9

def loopBody471_11 : HolLoopProg 64 :=
.mark loopBody471_10

def loopBody471_12 : HolLoopProg 64 :=
.seq loopBody471_1 loopBody471_11

def loopBody471_13 : HolLoopProg 64 :=
.mark loopBody471_12

def loopBody471_14 : HolLoopProg 64 :=
.seq loopBody471_1 loopBody471_13

def loopBody471_15 : HolLoopProg 64 :=
.mark loopBody471_14

def loopBody471_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody471_17 : HolLoopProg 64 :=
.mark loopBody471_16

def loopBody471_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 16#64]))

def loopBody471_19 : HolLoopProg 64 :=
.mark loopBody471_18

def loopBody471_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody471_21 : HolLoopProg 64 :=
.mark loopBody471_20

def loopBody471_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody471_23 : HolLoopProg 64 :=
.mark loopBody471_22

def loopBody471_24 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notLower) 2 (Flapjack.RegImm.reg 3) loopBody471_21 loopBody471_23 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)

def loopBody471_25 : HolLoopProg 64 :=
.mark loopBody471_24

def loopBody471_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody471_27 : HolLoopProg 64 :=
.mark loopBody471_26

def loopBody471_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 2#64)

def loopBody471_29 : HolLoopProg 64 :=
.mark loopBody471_28

def loopBody471_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 1)

def loopBody471_31 : HolLoopProg 64 :=
.mark loopBody471_30

def loopBody471_32 : HolLoopProg 64 :=
.seq loopBody471_31 loopBody471_1

def loopBody471_33 : HolLoopProg 64 :=
.mark loopBody471_32

def loopBody471_34 : HolLoopProg 64 :=
.seq loopBody471_33 loopBody471_1

def loopBody471_35 : HolLoopProg 64 :=
.mark loopBody471_34

def loopBody471_36 : HolLoopProg 64 :=
.seq loopBody471_29 loopBody471_35

def loopBody471_37 : HolLoopProg 64 :=
.mark loopBody471_36

def loopBody471_38 : HolLoopProg 64 :=
.seq loopBody471_1 loopBody471_37

def loopBody471_39 : HolLoopProg 64 :=
.mark loopBody471_38

def loopBody471_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 8#64)

def loopBody471_41 : HolLoopProg 64 :=
.mark loopBody471_40

def loopBody471_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 1

def loopBody471_43 : HolLoopProg 64 :=
.mark loopBody471_42

def loopBody471_44 : HolLoopProg 64 :=
.seq loopBody471_41 loopBody471_43

def loopBody471_45 : HolLoopProg 64 :=
.mark loopBody471_44

def loopBody471_46 : HolLoopProg 64 :=
.seq loopBody471_39 loopBody471_45

def loopBody471_47 : HolLoopProg 64 :=
.mark loopBody471_46

def loopBody471_48 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.imm 0#64) loopBody471_47 loopBody471_1 (Flapjack.Spt.ls PUnit.unit)

def loopBody471_49 : HolLoopProg 64 :=
.mark loopBody471_48

def loopBody471_50 : HolLoopProg 64 :=
.seq loopBody471_49 loopBody471_1

def loopBody471_51 : HolLoopProg 64 :=
.mark loopBody471_50

def loopBody471_52 : HolLoopProg 64 :=
.seq loopBody471_27 loopBody471_51

def loopBody471_53 : HolLoopProg 64 :=
.mark loopBody471_52

def loopBody471_54 : HolLoopProg 64 :=
.seq loopBody471_25 loopBody471_53

def loopBody471_55 : HolLoopProg 64 :=
.mark loopBody471_54

def loopBody471_56 : HolLoopProg 64 :=
.seq loopBody471_19 loopBody471_55

def loopBody471_57 : HolLoopProg 64 :=
.mark loopBody471_56

def loopBody471_58 : HolLoopProg 64 :=
.seq loopBody471_17 loopBody471_57

def loopBody471_59 : HolLoopProg 64 :=
.mark loopBody471_58

def loopBody471_60 : HolLoopProg 64 :=
.seq loopBody471_15 loopBody471_59

def loopBody471_61 : HolLoopProg 64 :=
.mark loopBody471_60

def loopBody471_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody471_63 : HolLoopProg 64 :=
.mark loopBody471_62

def loopBody471_64 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 534) ([2, 3]) (some (2, loopBody471_5, loopBody471_1, (Flapjack.Spt.ln)))

def loopBody471_65 : HolLoopProg 64 :=
.mark loopBody471_64

def loopBody471_66 : HolLoopProg 64 :=
.seq loopBody471_65 loopBody471_1

def loopBody471_67 : HolLoopProg 64 :=
.mark loopBody471_66

def loopBody471_68 : HolLoopProg 64 :=
.seq loopBody471_63 loopBody471_67

def loopBody471_69 : HolLoopProg 64 :=
.mark loopBody471_68

def loopBody471_70 : HolLoopProg 64 :=
.seq loopBody471_23 loopBody471_69

def loopBody471_71 : HolLoopProg 64 :=
.mark loopBody471_70

def loopBody471_72 : HolLoopProg 64 :=
.seq loopBody471_1 loopBody471_71

def loopBody471_73 : HolLoopProg 64 :=
.mark loopBody471_72

def loopBody471_74 : HolLoopProg 64 :=
.seq loopBody471_1 loopBody471_73

def loopBody471_75 : HolLoopProg 64 :=
.mark loopBody471_74

def loopBody471_76 : HolLoopProg 64 :=
.seq loopBody471_61 loopBody471_75

def loopBody471_77 : HolLoopProg 64 :=
.mark loopBody471_76

def loopBody471_78 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 486) ([2]) (some (2, loopBody471_5, loopBody471_1, (Flapjack.Spt.ln)))

def loopBody471_79 : HolLoopProg 64 :=
.mark loopBody471_78

def loopBody471_80 : HolLoopProg 64 :=
.seq loopBody471_79 loopBody471_1

def loopBody471_81 : HolLoopProg 64 :=
.mark loopBody471_80

def loopBody471_82 : HolLoopProg 64 :=
.seq loopBody471_21 loopBody471_81

def loopBody471_83 : HolLoopProg 64 :=
.mark loopBody471_82

def loopBody471_84 : HolLoopProg 64 :=
.seq loopBody471_1 loopBody471_83

def loopBody471_85 : HolLoopProg 64 :=
.mark loopBody471_84

def loopBody471_86 : HolLoopProg 64 :=
.seq loopBody471_1 loopBody471_85

def loopBody471_87 : HolLoopProg 64 :=
.mark loopBody471_86

def loopBody471_88 : HolLoopProg 64 :=
.seq loopBody471_77 loopBody471_87

def loopBody471_89 : HolLoopProg 64 :=
.mark loopBody471_88

def loopBody471_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody471_91 : HolLoopProg 64 :=
.mark loopBody471_90

def loopBody471_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody471_93 : HolLoopProg 64 :=
.mark loopBody471_92

def loopBody471_94 : HolLoopProg 64 :=
.seq loopBody471_93 loopBody471_1

def loopBody471_95 : HolLoopProg 64 :=
.mark loopBody471_94

def loopBody471_96 : HolLoopProg 64 :=
.seq loopBody471_91 loopBody471_95

def loopBody471_97 : HolLoopProg 64 :=
.mark loopBody471_96

def loopBody471_98 : HolLoopProg 64 :=
.seq loopBody471_89 loopBody471_97

def loopBody471_99 : HolLoopProg 64 :=
.mark loopBody471_98

def output471 : Nat × List Nat × HolLoopProg 64 :=
  (535, [0], loopBody471_99)
end InitECandidate.Proofs.FrontendStages.Loop
