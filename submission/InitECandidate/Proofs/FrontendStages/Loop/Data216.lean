import InitECandidate.Proofs.FrontendStages.Loop.Translate200
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody216_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 120#64]))

def loopBody216_1 : HolLoopProg 64 :=
.mark loopBody216_0

def loopBody216_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody216_3 : HolLoopProg 64 :=
.mark loopBody216_2

def loopBody216_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody216_5 : HolLoopProg 64 :=
.mark loopBody216_4

def loopBody216_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody216_7 : HolLoopProg 64 :=
.mark loopBody216_6

def loopBody216_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 2 (Flapjack.RegImm.reg 3) loopBody216_5 loopBody216_7 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)

def loopBody216_9 : HolLoopProg 64 :=
.mark loopBody216_8

def loopBody216_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody216_11 : HolLoopProg 64 :=
.mark loopBody216_10

def loopBody216_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody216_13 : HolLoopProg 64 :=
.mark loopBody216_12

def loopBody216_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody216_15 : HolLoopProg 64 :=
.mark loopBody216_14

def loopBody216_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody216_17 : HolLoopProg 64 :=
.mark loopBody216_16

def loopBody216_18 : HolLoopProg 64 :=
.seq loopBody216_15 loopBody216_17

def loopBody216_19 : HolLoopProg 64 :=
.mark loopBody216_18

def loopBody216_20 : HolLoopProg 64 :=
.seq loopBody216_13 loopBody216_19

def loopBody216_21 : HolLoopProg 64 :=
.mark loopBody216_20

def loopBody216_22 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.imm 0#64) loopBody216_21 loopBody216_17 (Flapjack.Spt.ln)

def loopBody216_23 : HolLoopProg 64 :=
.mark loopBody216_22

def loopBody216_24 : HolLoopProg 64 :=
.seq loopBody216_23 loopBody216_17

def loopBody216_25 : HolLoopProg 64 :=
.mark loopBody216_24

def loopBody216_26 : HolLoopProg 64 :=
.seq loopBody216_11 loopBody216_25

def loopBody216_27 : HolLoopProg 64 :=
.mark loopBody216_26

def loopBody216_28 : HolLoopProg 64 :=
.seq loopBody216_9 loopBody216_27

def loopBody216_29 : HolLoopProg 64 :=
.mark loopBody216_28

def loopBody216_30 : HolLoopProg 64 :=
.seq loopBody216_3 loopBody216_29

def loopBody216_31 : HolLoopProg 64 :=
.mark loopBody216_30

def loopBody216_32 : HolLoopProg 64 :=
.seq loopBody216_1 loopBody216_31

def loopBody216_33 : HolLoopProg 64 :=
.mark loopBody216_32

def loopBody216_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 8#64)

def loopBody216_35 : HolLoopProg 64 :=
.mark loopBody216_34

def loopBody216_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody216_37 : HolLoopProg 64 :=
.mark loopBody216_36

def loopBody216_38 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 68) ([2]) (some (2, loopBody216_37, loopBody216_17, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody216_39 : HolLoopProg 64 :=
.mark loopBody216_38

def loopBody216_40 : HolLoopProg 64 :=
.seq loopBody216_39 loopBody216_17

def loopBody216_41 : HolLoopProg 64 :=
.mark loopBody216_40

def loopBody216_42 : HolLoopProg 64 :=
.seq loopBody216_35 loopBody216_41

def loopBody216_43 : HolLoopProg 64 :=
.mark loopBody216_42

def loopBody216_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 120#64])

def loopBody216_45 : HolLoopProg 64 :=
.mark loopBody216_44

def loopBody216_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody216_47 : HolLoopProg 64 :=
.mark loopBody216_46

def loopBody216_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 3)

def loopBody216_49 : HolLoopProg 64 :=
.mark loopBody216_48

def loopBody216_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 2) 4

def loopBody216_51 : HolLoopProg 64 :=
.mark loopBody216_50

def loopBody216_52 : HolLoopProg 64 :=
.seq loopBody216_51 loopBody216_17

def loopBody216_53 : HolLoopProg 64 :=
.mark loopBody216_52

def loopBody216_54 : HolLoopProg 64 :=
.seq loopBody216_49 loopBody216_53

def loopBody216_55 : HolLoopProg 64 :=
.mark loopBody216_54

def loopBody216_56 : HolLoopProg 64 :=
.seq loopBody216_55 loopBody216_17

def loopBody216_57 : HolLoopProg 64 :=
.mark loopBody216_56

def loopBody216_58 : HolLoopProg 64 :=
.seq loopBody216_47 loopBody216_57

def loopBody216_59 : HolLoopProg 64 :=
.mark loopBody216_58

def loopBody216_60 : HolLoopProg 64 :=
.seq loopBody216_17 loopBody216_59

def loopBody216_61 : HolLoopProg 64 :=
.mark loopBody216_60

def loopBody216_62 : HolLoopProg 64 :=
.seq loopBody216_45 loopBody216_61

def loopBody216_63 : HolLoopProg 64 :=
.mark loopBody216_62

def loopBody216_64 : HolLoopProg 64 :=
.seq loopBody216_17 loopBody216_63

def loopBody216_65 : HolLoopProg 64 :=
.mark loopBody216_64

def loopBody216_66 : HolLoopProg 64 :=
.seq loopBody216_43 loopBody216_65

def loopBody216_67 : HolLoopProg 64 :=
.mark loopBody216_66

def loopBody216_68 : HolLoopProg 64 :=
.seq loopBody216_17 loopBody216_67

def loopBody216_69 : HolLoopProg 64 :=
.mark loopBody216_68

def loopBody216_70 : HolLoopProg 64 :=
.seq loopBody216_17 loopBody216_69

def loopBody216_71 : HolLoopProg 64 :=
.mark loopBody216_70

def loopBody216_72 : HolLoopProg 64 :=
.seq loopBody216_33 loopBody216_71

def loopBody216_73 : HolLoopProg 64 :=
.mark loopBody216_72

def loopBody216_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 8#64)

def loopBody216_75 : HolLoopProg 64 :=
.mark loopBody216_74

def loopBody216_76 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 78) ([2, 3]) (some (2, loopBody216_37, loopBody216_17, (Flapjack.Spt.ln)))

def loopBody216_77 : HolLoopProg 64 :=
.mark loopBody216_76

def loopBody216_78 : HolLoopProg 64 :=
.seq loopBody216_77 loopBody216_17

def loopBody216_79 : HolLoopProg 64 :=
.mark loopBody216_78

def loopBody216_80 : HolLoopProg 64 :=
.seq loopBody216_75 loopBody216_79

def loopBody216_81 : HolLoopProg 64 :=
.mark loopBody216_80

def loopBody216_82 : HolLoopProg 64 :=
.seq loopBody216_1 loopBody216_81

def loopBody216_83 : HolLoopProg 64 :=
.mark loopBody216_82

def loopBody216_84 : HolLoopProg 64 :=
.seq loopBody216_17 loopBody216_83

def loopBody216_85 : HolLoopProg 64 :=
.mark loopBody216_84

def loopBody216_86 : HolLoopProg 64 :=
.seq loopBody216_17 loopBody216_85

def loopBody216_87 : HolLoopProg 64 :=
.mark loopBody216_86

def loopBody216_88 : HolLoopProg 64 :=
.seq loopBody216_73 loopBody216_87

def loopBody216_89 : HolLoopProg 64 :=
.mark loopBody216_88

def loopBody216_90 : HolLoopProg 64 :=
.seq loopBody216_89 loopBody216_21

def loopBody216_91 : HolLoopProg 64 :=
.mark loopBody216_90

def output216 : Nat × List Nat × HolLoopProg 64 :=
  (280, [], loopBody216_91)
end InitECandidate.Proofs.FrontendStages.Loop
