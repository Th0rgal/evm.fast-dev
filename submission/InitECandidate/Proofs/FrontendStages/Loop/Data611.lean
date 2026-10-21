import InitECandidate.Proofs.FrontendStages.Loop.Translate595
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody611_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody611_1 : HolLoopProg 64 :=
.mark loopBody611_0

def loopBody611_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody611_3 : HolLoopProg 64 :=
.mark loopBody611_2

def loopBody611_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 0) (Flapjack.HolLoopExp.const 5#64))

def loopBody611_5 : HolLoopProg 64 :=
.mark loopBody611_4

def loopBody611_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody611_7 : HolLoopProg 64 :=
.mark loopBody611_6

def loopBody611_8 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 78) ([3, 4]) (some (3, loopBody611_7, loopBody611_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody611_9 : HolLoopProg 64 :=
.mark loopBody611_8

def loopBody611_10 : HolLoopProg 64 :=
.seq loopBody611_9 loopBody611_1

def loopBody611_11 : HolLoopProg 64 :=
.mark loopBody611_10

def loopBody611_12 : HolLoopProg 64 :=
.seq loopBody611_5 loopBody611_11

def loopBody611_13 : HolLoopProg 64 :=
.mark loopBody611_12

def loopBody611_14 : HolLoopProg 64 :=
.seq loopBody611_3 loopBody611_13

def loopBody611_15 : HolLoopProg 64 :=
.mark loopBody611_14

def loopBody611_16 : HolLoopProg 64 :=
.seq loopBody611_1 loopBody611_15

def loopBody611_17 : HolLoopProg 64 :=
.mark loopBody611_16

def loopBody611_18 : HolLoopProg 64 :=
.seq loopBody611_1 loopBody611_17

def loopBody611_19 : HolLoopProg 64 :=
.mark loopBody611_18

def loopBody611_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 1)

def loopBody611_21 : HolLoopProg 64 :=
.mark loopBody611_20

def loopBody611_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 15230403791020821917#64)

def loopBody611_23 : HolLoopProg 64 :=
.mark loopBody611_22

def loopBody611_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 754611498739239741#64)

def loopBody611_25 : HolLoopProg 64 :=
.mark loopBody611_24

def loopBody611_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 7381016538464732716#64)

def loopBody611_27 : HolLoopProg 64 :=
.mark loopBody611_26

def loopBody611_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1011752739694698287#64)

def loopBody611_29 : HolLoopProg 64 :=
.mark loopBody611_28

def loopBody611_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody611_31 : HolLoopProg 64 :=
.mark loopBody611_30

def loopBody611_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 2) 7

def loopBody611_33 : HolLoopProg 64 :=
.mark loopBody611_32

def loopBody611_34 : HolLoopProg 64 :=
.seq loopBody611_33 loopBody611_1

def loopBody611_35 : HolLoopProg 64 :=
.mark loopBody611_34

def loopBody611_36 : HolLoopProg 64 :=
.seq loopBody611_31 loopBody611_35

def loopBody611_37 : HolLoopProg 64 :=
.mark loopBody611_36

def loopBody611_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody611_39 : HolLoopProg 64 :=
.mark loopBody611_38

def loopBody611_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 8#64]) 7

def loopBody611_41 : HolLoopProg 64 :=
.mark loopBody611_40

def loopBody611_42 : HolLoopProg 64 :=
.seq loopBody611_41 loopBody611_1

def loopBody611_43 : HolLoopProg 64 :=
.mark loopBody611_42

def loopBody611_44 : HolLoopProg 64 :=
.seq loopBody611_39 loopBody611_43

def loopBody611_45 : HolLoopProg 64 :=
.mark loopBody611_44

def loopBody611_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody611_47 : HolLoopProg 64 :=
.mark loopBody611_46

def loopBody611_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 16#64]) 7

def loopBody611_49 : HolLoopProg 64 :=
.mark loopBody611_48

def loopBody611_50 : HolLoopProg 64 :=
.seq loopBody611_49 loopBody611_1

def loopBody611_51 : HolLoopProg 64 :=
.mark loopBody611_50

def loopBody611_52 : HolLoopProg 64 :=
.seq loopBody611_47 loopBody611_51

def loopBody611_53 : HolLoopProg 64 :=
.mark loopBody611_52

def loopBody611_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 6)

def loopBody611_55 : HolLoopProg 64 :=
.mark loopBody611_54

def loopBody611_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 24#64]) 7

def loopBody611_57 : HolLoopProg 64 :=
.mark loopBody611_56

def loopBody611_58 : HolLoopProg 64 :=
.seq loopBody611_57 loopBody611_1

def loopBody611_59 : HolLoopProg 64 :=
.mark loopBody611_58

def loopBody611_60 : HolLoopProg 64 :=
.seq loopBody611_55 loopBody611_59

def loopBody611_61 : HolLoopProg 64 :=
.mark loopBody611_60

def loopBody611_62 : HolLoopProg 64 :=
.seq loopBody611_61 loopBody611_1

def loopBody611_63 : HolLoopProg 64 :=
.mark loopBody611_62

def loopBody611_64 : HolLoopProg 64 :=
.seq loopBody611_53 loopBody611_63

def loopBody611_65 : HolLoopProg 64 :=
.mark loopBody611_64

def loopBody611_66 : HolLoopProg 64 :=
.seq loopBody611_45 loopBody611_65

def loopBody611_67 : HolLoopProg 64 :=
.mark loopBody611_66

def loopBody611_68 : HolLoopProg 64 :=
.seq loopBody611_37 loopBody611_67

def loopBody611_69 : HolLoopProg 64 :=
.mark loopBody611_68

def loopBody611_70 : HolLoopProg 64 :=
.seq loopBody611_29 loopBody611_69

def loopBody611_71 : HolLoopProg 64 :=
.mark loopBody611_70

def loopBody611_72 : HolLoopProg 64 :=
.seq loopBody611_1 loopBody611_71

def loopBody611_73 : HolLoopProg 64 :=
.mark loopBody611_72

def loopBody611_74 : HolLoopProg 64 :=
.seq loopBody611_27 loopBody611_73

def loopBody611_75 : HolLoopProg 64 :=
.mark loopBody611_74

def loopBody611_76 : HolLoopProg 64 :=
.seq loopBody611_1 loopBody611_75

def loopBody611_77 : HolLoopProg 64 :=
.mark loopBody611_76

def loopBody611_78 : HolLoopProg 64 :=
.seq loopBody611_25 loopBody611_77

def loopBody611_79 : HolLoopProg 64 :=
.mark loopBody611_78

def loopBody611_80 : HolLoopProg 64 :=
.seq loopBody611_1 loopBody611_79

def loopBody611_81 : HolLoopProg 64 :=
.mark loopBody611_80

def loopBody611_82 : HolLoopProg 64 :=
.seq loopBody611_23 loopBody611_81

def loopBody611_83 : HolLoopProg 64 :=
.mark loopBody611_82

def loopBody611_84 : HolLoopProg 64 :=
.seq loopBody611_1 loopBody611_83

def loopBody611_85 : HolLoopProg 64 :=
.mark loopBody611_84

def loopBody611_86 : HolLoopProg 64 :=
.seq loopBody611_21 loopBody611_85

def loopBody611_87 : HolLoopProg 64 :=
.mark loopBody611_86

def loopBody611_88 : HolLoopProg 64 :=
.seq loopBody611_1 loopBody611_87

def loopBody611_89 : HolLoopProg 64 :=
.mark loopBody611_88

def loopBody611_90 : HolLoopProg 64 :=
.seq loopBody611_19 loopBody611_89

def loopBody611_91 : HolLoopProg 64 :=
.mark loopBody611_90

def loopBody611_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody611_93 : HolLoopProg 64 :=
.mark loopBody611_92

def loopBody611_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody611_95 : HolLoopProg 64 :=
.mark loopBody611_94

def loopBody611_96 : HolLoopProg 64 :=
.seq loopBody611_95 loopBody611_1

def loopBody611_97 : HolLoopProg 64 :=
.mark loopBody611_96

def loopBody611_98 : HolLoopProg 64 :=
.seq loopBody611_93 loopBody611_97

def loopBody611_99 : HolLoopProg 64 :=
.mark loopBody611_98

def loopBody611_100 : HolLoopProg 64 :=
.seq loopBody611_91 loopBody611_99

def loopBody611_101 : HolLoopProg 64 :=
.mark loopBody611_100

def output611 : Nat × List Nat × HolLoopProg 64 :=
  (675, [0, 1], loopBody611_101)
end InitECandidate.Proofs.FrontendStages.Loop
