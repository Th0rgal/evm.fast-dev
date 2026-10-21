import InitECandidate.Proofs.FrontendStages.Loop.Translate219
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody235_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody235_1 : HolLoopProg 64 :=
.mark loopBody235_0

def loopBody235_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody235_3 : HolLoopProg 64 :=
.mark loopBody235_2

def loopBody235_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody235_5 : HolLoopProg 64 :=
.mark loopBody235_4

def loopBody235_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 2)

def loopBody235_7 : HolLoopProg 64 :=
.mark loopBody235_6

def loopBody235_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody235_9 : HolLoopProg 64 :=
.mark loopBody235_8

def loopBody235_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.tick

def loopBody235_11 : HolLoopProg 64 :=
.mark loopBody235_10

def loopBody235_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.lookup 0#5)

def loopBody235_13 : HolLoopProg 64 :=
.mark loopBody235_12

def loopBody235_14 : HolLoopProg 64 :=
.seq loopBody235_13 loopBody235_1

def loopBody235_15 : HolLoopProg 64 :=
.mark loopBody235_14

def loopBody235_16 : HolLoopProg 64 :=
.seq loopBody235_15 loopBody235_1

def loopBody235_17 : HolLoopProg 64 :=
.mark loopBody235_16

def loopBody235_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody235_19 : HolLoopProg 64 :=
.mark loopBody235_18

def loopBody235_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody235_21 : HolLoopProg 64 :=
.mark loopBody235_20

def loopBody235_22 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)) (some 76) ([7]) (some (7, loopBody235_21, loopBody235_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))

def loopBody235_23 : HolLoopProg 64 :=
.mark loopBody235_22

def loopBody235_24 : HolLoopProg 64 :=
.seq loopBody235_23 loopBody235_1

def loopBody235_25 : HolLoopProg 64 :=
.mark loopBody235_24

def loopBody235_26 : HolLoopProg 64 :=
.seq loopBody235_19 loopBody235_25

def loopBody235_27 : HolLoopProg 64 :=
.mark loopBody235_26

def loopBody235_28 : HolLoopProg 64 :=
.seq loopBody235_1 loopBody235_27

def loopBody235_29 : HolLoopProg 64 :=
.mark loopBody235_28

def loopBody235_30 : HolLoopProg 64 :=
.seq loopBody235_1 loopBody235_29

def loopBody235_31 : HolLoopProg 64 :=
.mark loopBody235_30

def loopBody235_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody235_33 : HolLoopProg 64 :=
.mark loopBody235_32

def loopBody235_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 6)

def loopBody235_35 : HolLoopProg 64 :=
.mark loopBody235_34

def loopBody235_36 : HolLoopProg 64 :=
.seq loopBody235_35 loopBody235_1

def loopBody235_37 : HolLoopProg 64 :=
.mark loopBody235_36

def loopBody235_38 : HolLoopProg 64 :=
.seq loopBody235_37 loopBody235_1

def loopBody235_39 : HolLoopProg 64 :=
.mark loopBody235_38

def loopBody235_40 : HolLoopProg 64 :=
.seq loopBody235_33 loopBody235_39

def loopBody235_41 : HolLoopProg 64 :=
.mark loopBody235_40

def loopBody235_42 : HolLoopProg 64 :=
.seq loopBody235_1 loopBody235_41

def loopBody235_43 : HolLoopProg 64 :=
.mark loopBody235_42

def loopBody235_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 5#64)

def loopBody235_45 : HolLoopProg 64 :=
.mark loopBody235_44

def loopBody235_46 : HolLoopProg 64 :=
.seq loopBody235_45 loopBody235_9

def loopBody235_47 : HolLoopProg 64 :=
.mark loopBody235_46

def loopBody235_48 : HolLoopProg 64 :=
.seq loopBody235_43 loopBody235_47

def loopBody235_49 : HolLoopProg 64 :=
.mark loopBody235_48

def loopBody235_50 : HolLoopProg 64 :=
.seq loopBody235_31 loopBody235_49

def loopBody235_51 : HolLoopProg 64 :=
.mark loopBody235_50

def loopBody235_52 : HolLoopProg 64 :=
.seq loopBody235_17 loopBody235_51

def loopBody235_53 : HolLoopProg 64 :=
.mark loopBody235_52

def loopBody235_54 : HolLoopProg 64 :=
.seq loopBody235_11 loopBody235_53

def loopBody235_55 : HolLoopProg 64 :=
.mark loopBody235_54

def loopBody235_56 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 5#64) loopBody235_9 loopBody235_55 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody235_57 : HolLoopProg 64 :=
.mark loopBody235_56

def loopBody235_58 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 298) ([6, 7, 8]) (some (6, loopBody235_57, loopBody235_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))

def loopBody235_59 : HolLoopProg 64 :=
.mark loopBody235_58

def loopBody235_60 : HolLoopProg 64 :=
.seq loopBody235_59 loopBody235_1

def loopBody235_61 : HolLoopProg 64 :=
.mark loopBody235_60

def loopBody235_62 : HolLoopProg 64 :=
.seq loopBody235_7 loopBody235_61

def loopBody235_63 : HolLoopProg 64 :=
.mark loopBody235_62

def loopBody235_64 : HolLoopProg 64 :=
.seq loopBody235_5 loopBody235_63

def loopBody235_65 : HolLoopProg 64 :=
.mark loopBody235_64

def loopBody235_66 : HolLoopProg 64 :=
.seq loopBody235_3 loopBody235_65

def loopBody235_67 : HolLoopProg 64 :=
.mark loopBody235_66

def loopBody235_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 5)

def loopBody235_69 : HolLoopProg 64 :=
.mark loopBody235_68

def loopBody235_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody235_71 : HolLoopProg 64 :=
.mark loopBody235_70

def loopBody235_72 : HolLoopProg 64 :=
.seq loopBody235_71 loopBody235_1

def loopBody235_73 : HolLoopProg 64 :=
.mark loopBody235_72

def loopBody235_74 : HolLoopProg 64 :=
.seq loopBody235_69 loopBody235_73

def loopBody235_75 : HolLoopProg 64 :=
.mark loopBody235_74

def loopBody235_76 : HolLoopProg 64 :=
.seq loopBody235_67 loopBody235_75

def loopBody235_77 : HolLoopProg 64 :=
.mark loopBody235_76

def loopBody235_78 : HolLoopProg 64 :=
.seq loopBody235_1 loopBody235_77

def loopBody235_79 : HolLoopProg 64 :=
.mark loopBody235_78

def loopBody235_80 : HolLoopProg 64 :=
.seq loopBody235_1 loopBody235_79

def loopBody235_81 : HolLoopProg 64 :=
.mark loopBody235_80

def loopBody235_82 : HolLoopProg 64 :=
.seq loopBody235_1 loopBody235_81

def loopBody235_83 : HolLoopProg 64 :=
.mark loopBody235_82

def loopBody235_84 : HolLoopProg 64 :=
.seq loopBody235_1 loopBody235_83

def loopBody235_85 : HolLoopProg 64 :=
.mark loopBody235_84

def output235 : Nat × List Nat × HolLoopProg 64 :=
  (299, [0, 1, 2, 3], loopBody235_85)
end InitECandidate.Proofs.FrontendStages.Loop
