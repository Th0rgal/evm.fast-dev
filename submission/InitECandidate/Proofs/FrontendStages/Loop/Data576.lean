import InitECandidate.Proofs.FrontendStages.Loop.Translate560
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody576_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody576_1 : HolLoopProg 64 :=
.mark loopBody576_0

def loopBody576_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody576_3 : HolLoopProg 64 :=
.mark loopBody576_2

def loopBody576_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody576_5 : HolLoopProg 64 :=
.mark loopBody576_4

def loopBody576_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody576_7 : HolLoopProg 64 :=
.mark loopBody576_6

def loopBody576_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody576_9 : HolLoopProg 64 :=
.mark loopBody576_8

def loopBody576_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 18446744073709551615#64)

def loopBody576_11 : HolLoopProg 64 :=
.mark loopBody576_10

def loopBody576_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 4294967295#64)

def loopBody576_13 : HolLoopProg 64 :=
.mark loopBody576_12

def loopBody576_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 0#64)

def loopBody576_15 : HolLoopProg 64 :=
.mark loopBody576_14

def loopBody576_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 18446744069414584321#64)

def loopBody576_17 : HolLoopProg 64 :=
.mark loopBody576_16

def loopBody576_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody576_19 : HolLoopProg 64 :=
.mark loopBody576_18

def loopBody576_20 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 106) ([5, 6, 7, 8, 9, 10, 11, 12]) (some (5, loopBody576_19, loopBody576_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody576_21 : HolLoopProg 64 :=
.mark loopBody576_20

def loopBody576_22 : HolLoopProg 64 :=
.seq loopBody576_21 loopBody576_1

def loopBody576_23 : HolLoopProg 64 :=
.mark loopBody576_22

def loopBody576_24 : HolLoopProg 64 :=
.seq loopBody576_17 loopBody576_23

def loopBody576_25 : HolLoopProg 64 :=
.mark loopBody576_24

def loopBody576_26 : HolLoopProg 64 :=
.seq loopBody576_15 loopBody576_25

def loopBody576_27 : HolLoopProg 64 :=
.mark loopBody576_26

def loopBody576_28 : HolLoopProg 64 :=
.seq loopBody576_13 loopBody576_27

def loopBody576_29 : HolLoopProg 64 :=
.mark loopBody576_28

def loopBody576_30 : HolLoopProg 64 :=
.seq loopBody576_11 loopBody576_29

def loopBody576_31 : HolLoopProg 64 :=
.mark loopBody576_30

def loopBody576_32 : HolLoopProg 64 :=
.seq loopBody576_9 loopBody576_31

def loopBody576_33 : HolLoopProg 64 :=
.mark loopBody576_32

def loopBody576_34 : HolLoopProg 64 :=
.seq loopBody576_7 loopBody576_33

def loopBody576_35 : HolLoopProg 64 :=
.mark loopBody576_34

def loopBody576_36 : HolLoopProg 64 :=
.seq loopBody576_5 loopBody576_35

def loopBody576_37 : HolLoopProg 64 :=
.mark loopBody576_36

def loopBody576_38 : HolLoopProg 64 :=
.seq loopBody576_3 loopBody576_37

def loopBody576_39 : HolLoopProg 64 :=
.mark loopBody576_38

def loopBody576_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody576_41 : HolLoopProg 64 :=
.mark loopBody576_40

def loopBody576_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody576_43 : HolLoopProg 64 :=
.mark loopBody576_42

def loopBody576_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody576_45 : HolLoopProg 64 :=
.mark loopBody576_44

def loopBody576_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody576_47 : HolLoopProg 64 :=
.mark loopBody576_46

def loopBody576_48 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.RegImm.reg 7) loopBody576_45 loopBody576_47 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody576_49 : HolLoopProg 64 :=
.mark loopBody576_48

def loopBody576_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody576_51 : HolLoopProg 64 :=
.mark loopBody576_50

def loopBody576_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 117) [5, 6, 7, 8, 9, 10, 11, 12] none

def loopBody576_53 : HolLoopProg 64 :=
.mark loopBody576_52

def loopBody576_54 : HolLoopProg 64 :=
.seq loopBody576_53 loopBody576_1

def loopBody576_55 : HolLoopProg 64 :=
.mark loopBody576_54

def loopBody576_56 : HolLoopProg 64 :=
.seq loopBody576_17 loopBody576_55

def loopBody576_57 : HolLoopProg 64 :=
.mark loopBody576_56

def loopBody576_58 : HolLoopProg 64 :=
.seq loopBody576_15 loopBody576_57

def loopBody576_59 : HolLoopProg 64 :=
.mark loopBody576_58

def loopBody576_60 : HolLoopProg 64 :=
.seq loopBody576_13 loopBody576_59

def loopBody576_61 : HolLoopProg 64 :=
.mark loopBody576_60

def loopBody576_62 : HolLoopProg 64 :=
.seq loopBody576_11 loopBody576_61

def loopBody576_63 : HolLoopProg 64 :=
.mark loopBody576_62

def loopBody576_64 : HolLoopProg 64 :=
.seq loopBody576_9 loopBody576_63

def loopBody576_65 : HolLoopProg 64 :=
.mark loopBody576_64

def loopBody576_66 : HolLoopProg 64 :=
.seq loopBody576_7 loopBody576_65

def loopBody576_67 : HolLoopProg 64 :=
.mark loopBody576_66

def loopBody576_68 : HolLoopProg 64 :=
.seq loopBody576_5 loopBody576_67

def loopBody576_69 : HolLoopProg 64 :=
.mark loopBody576_68

def loopBody576_70 : HolLoopProg 64 :=
.seq loopBody576_3 loopBody576_69

def loopBody576_71 : HolLoopProg 64 :=
.mark loopBody576_70

def loopBody576_72 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody576_71 loopBody576_1 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody576_73 : HolLoopProg 64 :=
.mark loopBody576_72

def loopBody576_74 : HolLoopProg 64 :=
.seq loopBody576_73 loopBody576_1

def loopBody576_75 : HolLoopProg 64 :=
.mark loopBody576_74

def loopBody576_76 : HolLoopProg 64 :=
.seq loopBody576_51 loopBody576_75

def loopBody576_77 : HolLoopProg 64 :=
.mark loopBody576_76

def loopBody576_78 : HolLoopProg 64 :=
.seq loopBody576_49 loopBody576_77

def loopBody576_79 : HolLoopProg 64 :=
.mark loopBody576_78

def loopBody576_80 : HolLoopProg 64 :=
.seq loopBody576_43 loopBody576_79

def loopBody576_81 : HolLoopProg 64 :=
.mark loopBody576_80

def loopBody576_82 : HolLoopProg 64 :=
.seq loopBody576_41 loopBody576_81

def loopBody576_83 : HolLoopProg 64 :=
.mark loopBody576_82

def loopBody576_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5, 6, 7, 8]

def loopBody576_85 : HolLoopProg 64 :=
.mark loopBody576_84

def loopBody576_86 : HolLoopProg 64 :=
.seq loopBody576_85 loopBody576_1

def loopBody576_87 : HolLoopProg 64 :=
.mark loopBody576_86

def loopBody576_88 : HolLoopProg 64 :=
.seq loopBody576_9 loopBody576_87

def loopBody576_89 : HolLoopProg 64 :=
.mark loopBody576_88

def loopBody576_90 : HolLoopProg 64 :=
.seq loopBody576_7 loopBody576_89

def loopBody576_91 : HolLoopProg 64 :=
.mark loopBody576_90

def loopBody576_92 : HolLoopProg 64 :=
.seq loopBody576_5 loopBody576_91

def loopBody576_93 : HolLoopProg 64 :=
.mark loopBody576_92

def loopBody576_94 : HolLoopProg 64 :=
.seq loopBody576_3 loopBody576_93

def loopBody576_95 : HolLoopProg 64 :=
.mark loopBody576_94

def loopBody576_96 : HolLoopProg 64 :=
.seq loopBody576_83 loopBody576_95

def loopBody576_97 : HolLoopProg 64 :=
.mark loopBody576_96

def loopBody576_98 : HolLoopProg 64 :=
.seq loopBody576_39 loopBody576_97

def loopBody576_99 : HolLoopProg 64 :=
.mark loopBody576_98

def loopBody576_100 : HolLoopProg 64 :=
.seq loopBody576_1 loopBody576_99

def loopBody576_101 : HolLoopProg 64 :=
.mark loopBody576_100

def loopBody576_102 : HolLoopProg 64 :=
.seq loopBody576_1 loopBody576_101

def loopBody576_103 : HolLoopProg 64 :=
.mark loopBody576_102

def output576 : Nat × List Nat × HolLoopProg 64 :=
  (640, [0, 1, 2, 3], loopBody576_103)
end InitECandidate.Proofs.FrontendStages.Loop
