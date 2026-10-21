import InitECandidate.Proofs.FrontendStages.Loop.Translate350
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody366_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 176#64]),
        Flapjack.HolLoopExp.const 56#64]))

def loopBody366_1 : HolLoopProg 64 :=
.mark loopBody366_0

def loopBody366_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody366_3 : HolLoopProg 64 :=
.mark loopBody366_2

def loopBody366_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody366_5 : HolLoopProg 64 :=
.mark loopBody366_4

def loopBody366_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody366_7 : HolLoopProg 64 :=
.mark loopBody366_6

def loopBody366_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 2 (Flapjack.RegImm.reg 3) loopBody366_5 loopBody366_7 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)

def loopBody366_9 : HolLoopProg 64 :=
.mark loopBody366_8

def loopBody366_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody366_11 : HolLoopProg 64 :=
.mark loopBody366_10

def loopBody366_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody366_13 : HolLoopProg 64 :=
.mark loopBody366_12

def loopBody366_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 176#64]),
      Flapjack.HolLoopExp.const 56#64])

def loopBody366_15 : HolLoopProg 64 :=
.mark loopBody366_14

def loopBody366_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 2)

def loopBody366_17 : HolLoopProg 64 :=
.mark loopBody366_16

def loopBody366_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 1) 3

def loopBody366_19 : HolLoopProg 64 :=
.mark loopBody366_18

def loopBody366_20 : HolLoopProg 64 :=
.seq loopBody366_19 loopBody366_13

def loopBody366_21 : HolLoopProg 64 :=
.mark loopBody366_20

def loopBody366_22 : HolLoopProg 64 :=
.seq loopBody366_17 loopBody366_21

def loopBody366_23 : HolLoopProg 64 :=
.mark loopBody366_22

def loopBody366_24 : HolLoopProg 64 :=
.seq loopBody366_23 loopBody366_13

def loopBody366_25 : HolLoopProg 64 :=
.mark loopBody366_24

def loopBody366_26 : HolLoopProg 64 :=
.seq loopBody366_5 loopBody366_25

def loopBody366_27 : HolLoopProg 64 :=
.mark loopBody366_26

def loopBody366_28 : HolLoopProg 64 :=
.seq loopBody366_13 loopBody366_27

def loopBody366_29 : HolLoopProg 64 :=
.mark loopBody366_28

def loopBody366_30 : HolLoopProg 64 :=
.seq loopBody366_15 loopBody366_29

def loopBody366_31 : HolLoopProg 64 :=
.mark loopBody366_30

def loopBody366_32 : HolLoopProg 64 :=
.seq loopBody366_13 loopBody366_31

def loopBody366_33 : HolLoopProg 64 :=
.mark loopBody366_32

def loopBody366_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 176#64]),
      Flapjack.HolLoopExp.const 64#64])

def loopBody366_35 : HolLoopProg 64 :=
.mark loopBody366_34

def loopBody366_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody366_37 : HolLoopProg 64 :=
.mark loopBody366_36

def loopBody366_38 : HolLoopProg 64 :=
.seq loopBody366_37 loopBody366_25

def loopBody366_39 : HolLoopProg 64 :=
.mark loopBody366_38

def loopBody366_40 : HolLoopProg 64 :=
.seq loopBody366_13 loopBody366_39

def loopBody366_41 : HolLoopProg 64 :=
.mark loopBody366_40

def loopBody366_42 : HolLoopProg 64 :=
.seq loopBody366_35 loopBody366_41

def loopBody366_43 : HolLoopProg 64 :=
.mark loopBody366_42

def loopBody366_44 : HolLoopProg 64 :=
.seq loopBody366_13 loopBody366_43

def loopBody366_45 : HolLoopProg 64 :=
.mark loopBody366_44

def loopBody366_46 : HolLoopProg 64 :=
.seq loopBody366_33 loopBody366_45

def loopBody366_47 : HolLoopProg 64 :=
.mark loopBody366_46

def loopBody366_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 176#64]),
        Flapjack.HolLoopExp.const 64#64]))

def loopBody366_49 : HolLoopProg 64 :=
.mark loopBody366_48

def loopBody366_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody366_51 : HolLoopProg 64 :=
.mark loopBody366_50

def loopBody366_52 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 2 (Flapjack.RegImm.reg 3) loopBody366_5 loopBody366_7 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)

def loopBody366_53 : HolLoopProg 64 :=
.mark loopBody366_52

def loopBody366_54 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.imm 0#64) loopBody366_45 loopBody366_13 (Flapjack.Spt.ln)

def loopBody366_55 : HolLoopProg 64 :=
.mark loopBody366_54

def loopBody366_56 : HolLoopProg 64 :=
.seq loopBody366_55 loopBody366_13

def loopBody366_57 : HolLoopProg 64 :=
.mark loopBody366_56

def loopBody366_58 : HolLoopProg 64 :=
.seq loopBody366_11 loopBody366_57

def loopBody366_59 : HolLoopProg 64 :=
.mark loopBody366_58

def loopBody366_60 : HolLoopProg 64 :=
.seq loopBody366_53 loopBody366_59

def loopBody366_61 : HolLoopProg 64 :=
.mark loopBody366_60

def loopBody366_62 : HolLoopProg 64 :=
.seq loopBody366_51 loopBody366_61

def loopBody366_63 : HolLoopProg 64 :=
.mark loopBody366_62

def loopBody366_64 : HolLoopProg 64 :=
.seq loopBody366_49 loopBody366_63

def loopBody366_65 : HolLoopProg 64 :=
.mark loopBody366_64

def loopBody366_66 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.imm 0#64) loopBody366_47 loopBody366_65 (Flapjack.Spt.ln)

def loopBody366_67 : HolLoopProg 64 :=
.mark loopBody366_66

def loopBody366_68 : HolLoopProg 64 :=
.seq loopBody366_67 loopBody366_13

def loopBody366_69 : HolLoopProg 64 :=
.mark loopBody366_68

def loopBody366_70 : HolLoopProg 64 :=
.seq loopBody366_11 loopBody366_69

def loopBody366_71 : HolLoopProg 64 :=
.mark loopBody366_70

def loopBody366_72 : HolLoopProg 64 :=
.seq loopBody366_9 loopBody366_71

def loopBody366_73 : HolLoopProg 64 :=
.mark loopBody366_72

def loopBody366_74 : HolLoopProg 64 :=
.seq loopBody366_3 loopBody366_73

def loopBody366_75 : HolLoopProg 64 :=
.mark loopBody366_74

def loopBody366_76 : HolLoopProg 64 :=
.seq loopBody366_1 loopBody366_75

def loopBody366_77 : HolLoopProg 64 :=
.mark loopBody366_76

def loopBody366_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody366_79 : HolLoopProg 64 :=
.mark loopBody366_78

def loopBody366_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody366_81 : HolLoopProg 64 :=
.mark loopBody366_80

def loopBody366_82 : HolLoopProg 64 :=
.seq loopBody366_81 loopBody366_13

def loopBody366_83 : HolLoopProg 64 :=
.mark loopBody366_82

def loopBody366_84 : HolLoopProg 64 :=
.seq loopBody366_79 loopBody366_83

def loopBody366_85 : HolLoopProg 64 :=
.mark loopBody366_84

def loopBody366_86 : HolLoopProg 64 :=
.seq loopBody366_77 loopBody366_85

def loopBody366_87 : HolLoopProg 64 :=
.mark loopBody366_86

def output366 : Nat × List Nat × HolLoopProg 64 :=
  (430, [0], loopBody366_87)
end InitECandidate.Proofs.FrontendStages.Loop
