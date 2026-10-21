import InitECandidate.Proofs.FrontendStages.Loop.Translate580
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody596_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody596_1 : HolLoopProg 64 :=
.mark loopBody596_0

def loopBody596_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 0)

def loopBody596_3 : HolLoopProg 64 :=
.mark loopBody596_2

def loopBody596_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 1)

def loopBody596_5 : HolLoopProg 64 :=
.mark loopBody596_4

def loopBody596_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 2)

def loopBody596_7 : HolLoopProg 64 :=
.mark loopBody596_6

def loopBody596_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 3)

def loopBody596_9 : HolLoopProg 64 :=
.mark loopBody596_8

def loopBody596_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 4332616871279656263#64)

def loopBody596_11 : HolLoopProg 64 :=
.mark loopBody596_10

def loopBody596_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 10917124144477883021#64)

def loopBody596_13 : HolLoopProg 64 :=
.mark loopBody596_12

def loopBody596_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 13281191951274694749#64)

def loopBody596_15 : HolLoopProg 64 :=
.mark loopBody596_14

def loopBody596_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 3486998266802970665#64)

def loopBody596_17 : HolLoopProg 64 :=
.mark loopBody596_16

def loopBody596_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody596_19 : HolLoopProg 64 :=
.mark loopBody596_18

def loopBody596_20 : HolLoopProg 64 :=
.call (some ([4, 5, 6, 7], Flapjack.Spt.ln)) (some 210) ([8, 9, 10, 11, 12, 13, 14, 15]) (some (8, loopBody596_19, loopBody596_1, (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody596_21 : HolLoopProg 64 :=
.mark loopBody596_20

def loopBody596_22 : HolLoopProg 64 :=
.seq loopBody596_21 loopBody596_1

def loopBody596_23 : HolLoopProg 64 :=
.mark loopBody596_22

def loopBody596_24 : HolLoopProg 64 :=
.seq loopBody596_17 loopBody596_23

def loopBody596_25 : HolLoopProg 64 :=
.mark loopBody596_24

def loopBody596_26 : HolLoopProg 64 :=
.seq loopBody596_15 loopBody596_25

def loopBody596_27 : HolLoopProg 64 :=
.mark loopBody596_26

def loopBody596_28 : HolLoopProg 64 :=
.seq loopBody596_13 loopBody596_27

def loopBody596_29 : HolLoopProg 64 :=
.mark loopBody596_28

def loopBody596_30 : HolLoopProg 64 :=
.seq loopBody596_11 loopBody596_29

def loopBody596_31 : HolLoopProg 64 :=
.mark loopBody596_30

def loopBody596_32 : HolLoopProg 64 :=
.seq loopBody596_9 loopBody596_31

def loopBody596_33 : HolLoopProg 64 :=
.mark loopBody596_32

def loopBody596_34 : HolLoopProg 64 :=
.seq loopBody596_7 loopBody596_33

def loopBody596_35 : HolLoopProg 64 :=
.mark loopBody596_34

def loopBody596_36 : HolLoopProg 64 :=
.seq loopBody596_5 loopBody596_35

def loopBody596_37 : HolLoopProg 64 :=
.mark loopBody596_36

def loopBody596_38 : HolLoopProg 64 :=
.seq loopBody596_3 loopBody596_37

def loopBody596_39 : HolLoopProg 64 :=
.mark loopBody596_38

def loopBody596_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 4)

def loopBody596_41 : HolLoopProg 64 :=
.mark loopBody596_40

def loopBody596_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 5)

def loopBody596_43 : HolLoopProg 64 :=
.mark loopBody596_42

def loopBody596_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 6)

def loopBody596_45 : HolLoopProg 64 :=
.mark loopBody596_44

def loopBody596_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 7)

def loopBody596_47 : HolLoopProg 64 :=
.mark loopBody596_46

def loopBody596_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 12812017116984455391#64)

def loopBody596_49 : HolLoopProg 64 :=
.mark loopBody596_48

def loopBody596_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 7129779742913871286#64)

def loopBody596_51 : HolLoopProg 64 :=
.mark loopBody596_50

def loopBody596_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 17257524443456604923#64)

def loopBody596_53 : HolLoopProg 64 :=
.mark loopBody596_52

def loopBody596_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 2377177743836652868#64)

def loopBody596_55 : HolLoopProg 64 :=
.mark loopBody596_54

def loopBody596_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 657) [8, 9, 10, 11, 12, 13, 14, 15] none

def loopBody596_57 : HolLoopProg 64 :=
.mark loopBody596_56

def loopBody596_58 : HolLoopProg 64 :=
.seq loopBody596_57 loopBody596_1

def loopBody596_59 : HolLoopProg 64 :=
.mark loopBody596_58

def loopBody596_60 : HolLoopProg 64 :=
.seq loopBody596_55 loopBody596_59

def loopBody596_61 : HolLoopProg 64 :=
.mark loopBody596_60

def loopBody596_62 : HolLoopProg 64 :=
.seq loopBody596_53 loopBody596_61

def loopBody596_63 : HolLoopProg 64 :=
.mark loopBody596_62

def loopBody596_64 : HolLoopProg 64 :=
.seq loopBody596_51 loopBody596_63

def loopBody596_65 : HolLoopProg 64 :=
.mark loopBody596_64

def loopBody596_66 : HolLoopProg 64 :=
.seq loopBody596_49 loopBody596_65

def loopBody596_67 : HolLoopProg 64 :=
.mark loopBody596_66

def loopBody596_68 : HolLoopProg 64 :=
.seq loopBody596_47 loopBody596_67

def loopBody596_69 : HolLoopProg 64 :=
.mark loopBody596_68

def loopBody596_70 : HolLoopProg 64 :=
.seq loopBody596_45 loopBody596_69

def loopBody596_71 : HolLoopProg 64 :=
.mark loopBody596_70

def loopBody596_72 : HolLoopProg 64 :=
.seq loopBody596_43 loopBody596_71

def loopBody596_73 : HolLoopProg 64 :=
.mark loopBody596_72

def loopBody596_74 : HolLoopProg 64 :=
.seq loopBody596_41 loopBody596_73

def loopBody596_75 : HolLoopProg 64 :=
.mark loopBody596_74

def loopBody596_76 : HolLoopProg 64 :=
.seq loopBody596_39 loopBody596_75

def loopBody596_77 : HolLoopProg 64 :=
.mark loopBody596_76

def loopBody596_78 : HolLoopProg 64 :=
.seq loopBody596_1 loopBody596_77

def loopBody596_79 : HolLoopProg 64 :=
.mark loopBody596_78

def loopBody596_80 : HolLoopProg 64 :=
.seq loopBody596_1 loopBody596_79

def loopBody596_81 : HolLoopProg 64 :=
.mark loopBody596_80

def loopBody596_82 : HolLoopProg 64 :=
.seq loopBody596_1 loopBody596_81

def loopBody596_83 : HolLoopProg 64 :=
.mark loopBody596_82

def loopBody596_84 : HolLoopProg 64 :=
.seq loopBody596_1 loopBody596_83

def loopBody596_85 : HolLoopProg 64 :=
.mark loopBody596_84

def loopBody596_86 : HolLoopProg 64 :=
.seq loopBody596_1 loopBody596_85

def loopBody596_87 : HolLoopProg 64 :=
.mark loopBody596_86

def loopBody596_88 : HolLoopProg 64 :=
.seq loopBody596_1 loopBody596_87

def loopBody596_89 : HolLoopProg 64 :=
.mark loopBody596_88

def loopBody596_90 : HolLoopProg 64 :=
.seq loopBody596_1 loopBody596_89

def loopBody596_91 : HolLoopProg 64 :=
.mark loopBody596_90

def loopBody596_92 : HolLoopProg 64 :=
.seq loopBody596_1 loopBody596_91

def loopBody596_93 : HolLoopProg 64 :=
.mark loopBody596_92

def output596 : Nat × List Nat × HolLoopProg 64 :=
  (660, [0, 1, 2, 3], loopBody596_93)
end InitECandidate.Proofs.FrontendStages.Loop
