import InitECandidate.Proofs.FrontendStages.Loop.Translate457
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody473_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 90#64)

def loopBody473_1 : HolLoopProg 64 :=
.mark loopBody473_0

def loopBody473_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody473_3 : HolLoopProg 64 :=
.mark loopBody473_2

def loopBody473_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody473_5 : HolLoopProg 64 :=
.mark loopBody473_4

def loopBody473_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody473_7 : HolLoopProg 64 :=
.mark loopBody473_6

def loopBody473_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notLower) 2 (Flapjack.RegImm.reg 3) loopBody473_5 loopBody473_7 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)

def loopBody473_9 : HolLoopProg 64 :=
.mark loopBody473_8

def loopBody473_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody473_11 : HolLoopProg 64 :=
.mark loopBody473_10

def loopBody473_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 128#64)

def loopBody473_13 : HolLoopProg 64 :=
.mark loopBody473_12

def loopBody473_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody473_15 : HolLoopProg 64 :=
.mark loopBody473_14

def loopBody473_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody473_17 : HolLoopProg 64 :=
.mark loopBody473_16

def loopBody473_18 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notLower) 5 (Flapjack.RegImm.reg 6) loopBody473_15 loopBody473_17 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody473_19 : HolLoopProg 64 :=
.mark loopBody473_18

def loopBody473_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody473_21 : HolLoopProg 64 :=
.mark loopBody473_20

def loopBody473_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.var 5])

def loopBody473_23 : HolLoopProg 64 :=
.mark loopBody473_22

def loopBody473_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 1#64)

def loopBody473_25 : HolLoopProg 64 :=
.mark loopBody473_24

def loopBody473_26 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.reg 9) loopBody473_25 loopBody473_21 (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit Flapjack.Spt.ln)

def loopBody473_27 : HolLoopProg 64 :=
.mark loopBody473_26

def loopBody473_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 8)

def loopBody473_29 : HolLoopProg 64 :=
.mark loopBody473_28

def loopBody473_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and
    [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 145#64],
      Flapjack.HolLoopExp.const 255#64])

def loopBody473_31 : HolLoopProg 64 :=
.mark loopBody473_30

def loopBody473_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody473_33 : HolLoopProg 64 :=
.mark loopBody473_32

def loopBody473_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody473_35 : HolLoopProg 64 :=
.mark loopBody473_34

def loopBody473_36 : HolLoopProg 64 :=
.seq loopBody473_33 loopBody473_35

def loopBody473_37 : HolLoopProg 64 :=
.mark loopBody473_36

def loopBody473_38 : HolLoopProg 64 :=
.seq loopBody473_31 loopBody473_37

def loopBody473_39 : HolLoopProg 64 :=
.mark loopBody473_38

def loopBody473_40 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody473_39 loopBody473_35 (Flapjack.Spt.ln)

def loopBody473_41 : HolLoopProg 64 :=
.mark loopBody473_40

def loopBody473_42 : HolLoopProg 64 :=
.seq loopBody473_41 loopBody473_35

def loopBody473_43 : HolLoopProg 64 :=
.mark loopBody473_42

def loopBody473_44 : HolLoopProg 64 :=
.seq loopBody473_29 loopBody473_43

def loopBody473_45 : HolLoopProg 64 :=
.mark loopBody473_44

def loopBody473_46 : HolLoopProg 64 :=
.seq loopBody473_27 loopBody473_45

def loopBody473_47 : HolLoopProg 64 :=
.mark loopBody473_46

def loopBody473_48 : HolLoopProg 64 :=
.seq loopBody473_23 loopBody473_47

def loopBody473_49 : HolLoopProg 64 :=
.mark loopBody473_48

def loopBody473_50 : HolLoopProg 64 :=
.seq loopBody473_21 loopBody473_49

def loopBody473_51 : HolLoopProg 64 :=
.mark loopBody473_50

def loopBody473_52 : HolLoopProg 64 :=
.seq loopBody473_19 loopBody473_51

def loopBody473_53 : HolLoopProg 64 :=
.mark loopBody473_52

def loopBody473_54 : HolLoopProg 64 :=
.seq loopBody473_13 loopBody473_53

def loopBody473_55 : HolLoopProg 64 :=
.mark loopBody473_54

def loopBody473_56 : HolLoopProg 64 :=
.seq loopBody473_11 loopBody473_55

def loopBody473_57 : HolLoopProg 64 :=
.mark loopBody473_56

def loopBody473_58 : HolLoopProg 64 :=
.seq loopBody473_9 loopBody473_57

def loopBody473_59 : HolLoopProg 64 :=
.mark loopBody473_58

def loopBody473_60 : HolLoopProg 64 :=
.seq loopBody473_3 loopBody473_59

def loopBody473_61 : HolLoopProg 64 :=
.mark loopBody473_60

def loopBody473_62 : HolLoopProg 64 :=
.seq loopBody473_1 loopBody473_61

def loopBody473_63 : HolLoopProg 64 :=
.mark loopBody473_62

def loopBody473_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 10#64)

def loopBody473_65 : HolLoopProg 64 :=
.mark loopBody473_64

def loopBody473_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 1)

def loopBody473_67 : HolLoopProg 64 :=
.mark loopBody473_66

def loopBody473_68 : HolLoopProg 64 :=
.seq loopBody473_67 loopBody473_35

def loopBody473_69 : HolLoopProg 64 :=
.mark loopBody473_68

def loopBody473_70 : HolLoopProg 64 :=
.seq loopBody473_69 loopBody473_35

def loopBody473_71 : HolLoopProg 64 :=
.mark loopBody473_70

def loopBody473_72 : HolLoopProg 64 :=
.seq loopBody473_65 loopBody473_71

def loopBody473_73 : HolLoopProg 64 :=
.mark loopBody473_72

def loopBody473_74 : HolLoopProg 64 :=
.seq loopBody473_35 loopBody473_73

def loopBody473_75 : HolLoopProg 64 :=
.mark loopBody473_74

def loopBody473_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 8#64)

def loopBody473_77 : HolLoopProg 64 :=
.mark loopBody473_76

def loopBody473_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 1

def loopBody473_79 : HolLoopProg 64 :=
.mark loopBody473_78

def loopBody473_80 : HolLoopProg 64 :=
.seq loopBody473_77 loopBody473_79

def loopBody473_81 : HolLoopProg 64 :=
.mark loopBody473_80

def loopBody473_82 : HolLoopProg 64 :=
.seq loopBody473_75 loopBody473_81

def loopBody473_83 : HolLoopProg 64 :=
.mark loopBody473_82

def loopBody473_84 : HolLoopProg 64 :=
.seq loopBody473_63 loopBody473_83

def loopBody473_85 : HolLoopProg 64 :=
.mark loopBody473_84

def loopBody473_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody473_87 : HolLoopProg 64 :=
.mark loopBody473_86

def loopBody473_88 : HolLoopProg 64 :=
.seq loopBody473_87 loopBody473_37

def loopBody473_89 : HolLoopProg 64 :=
.mark loopBody473_88

def loopBody473_90 : HolLoopProg 64 :=
.seq loopBody473_85 loopBody473_89

def loopBody473_91 : HolLoopProg 64 :=
.mark loopBody473_90

def output473 : Nat × List Nat × HolLoopProg 64 :=
  (537, [0], loopBody473_91)
end InitECandidate.Proofs.FrontendStages.Loop
