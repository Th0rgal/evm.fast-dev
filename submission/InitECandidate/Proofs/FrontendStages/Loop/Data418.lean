import InitECandidate.Proofs.FrontendStages.Loop.Translate402
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody418_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or
    [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.var 3])

def loopBody418_1 : HolLoopProg 64 :=
.mark loopBody418_0

def loopBody418_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody418_3 : HolLoopProg 64 :=
.mark loopBody418_2

def loopBody418_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody418_5 : HolLoopProg 64 :=
.mark loopBody418_4

def loopBody418_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody418_7 : HolLoopProg 64 :=
.mark loopBody418_6

def loopBody418_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.reg 6) loopBody418_5 loopBody418_7 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody418_9 : HolLoopProg 64 :=
.mark loopBody418_8

def loopBody418_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody418_11 : HolLoopProg 64 :=
.mark loopBody418_10

def loopBody418_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody418_13 : HolLoopProg 64 :=
.mark loopBody418_12

def loopBody418_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody418_15 : HolLoopProg 64 :=
.mark loopBody418_14

def loopBody418_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody418_17 : HolLoopProg 64 :=
.mark loopBody418_16

def loopBody418_18 : HolLoopProg 64 :=
.seq loopBody418_15 loopBody418_17

def loopBody418_19 : HolLoopProg 64 :=
.mark loopBody418_18

def loopBody418_20 : HolLoopProg 64 :=
.seq loopBody418_13 loopBody418_19

def loopBody418_21 : HolLoopProg 64 :=
.mark loopBody418_20

def loopBody418_22 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody418_21 loopBody418_17 (Flapjack.Spt.ls PUnit.unit)

def loopBody418_23 : HolLoopProg 64 :=
.mark loopBody418_22

def loopBody418_24 : HolLoopProg 64 :=
.seq loopBody418_23 loopBody418_17

def loopBody418_25 : HolLoopProg 64 :=
.mark loopBody418_24

def loopBody418_26 : HolLoopProg 64 :=
.seq loopBody418_11 loopBody418_25

def loopBody418_27 : HolLoopProg 64 :=
.mark loopBody418_26

def loopBody418_28 : HolLoopProg 64 :=
.seq loopBody418_9 loopBody418_27

def loopBody418_29 : HolLoopProg 64 :=
.mark loopBody418_28

def loopBody418_30 : HolLoopProg 64 :=
.seq loopBody418_3 loopBody418_29

def loopBody418_31 : HolLoopProg 64 :=
.mark loopBody418_30

def loopBody418_32 : HolLoopProg 64 :=
.seq loopBody418_1 loopBody418_31

def loopBody418_33 : HolLoopProg 64 :=
.mark loopBody418_32

def loopBody418_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody418_35 : HolLoopProg 64 :=
.mark loopBody418_34

def loopBody418_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody418_37 : HolLoopProg 64 :=
.mark loopBody418_36

def loopBody418_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 56#64]))

def loopBody418_39 : HolLoopProg 64 :=
.mark loopBody418_38

def loopBody418_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody418_41 : HolLoopProg 64 :=
.mark loopBody418_40

def loopBody418_42 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notLower) 6 (Flapjack.RegImm.reg 7) loopBody418_41 loopBody418_3 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)

def loopBody418_43 : HolLoopProg 64 :=
.mark loopBody418_42

def loopBody418_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody418_45 : HolLoopProg 64 :=
.mark loopBody418_44

def loopBody418_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody418_47 : HolLoopProg 64 :=
.mark loopBody418_46

def loopBody418_48 : HolLoopProg 64 :=
.seq loopBody418_47 loopBody418_17

def loopBody418_49 : HolLoopProg 64 :=
.mark loopBody418_48

def loopBody418_50 : HolLoopProg 64 :=
.seq loopBody418_7 loopBody418_49

def loopBody418_51 : HolLoopProg 64 :=
.mark loopBody418_50

def loopBody418_52 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody418_51 loopBody418_17 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)

def loopBody418_53 : HolLoopProg 64 :=
.mark loopBody418_52

def loopBody418_54 : HolLoopProg 64 :=
.seq loopBody418_53 loopBody418_17

def loopBody418_55 : HolLoopProg 64 :=
.mark loopBody418_54

def loopBody418_56 : HolLoopProg 64 :=
.seq loopBody418_45 loopBody418_55

def loopBody418_57 : HolLoopProg 64 :=
.mark loopBody418_56

def loopBody418_58 : HolLoopProg 64 :=
.seq loopBody418_43 loopBody418_57

def loopBody418_59 : HolLoopProg 64 :=
.mark loopBody418_58

def loopBody418_60 : HolLoopProg 64 :=
.seq loopBody418_39 loopBody418_59

def loopBody418_61 : HolLoopProg 64 :=
.mark loopBody418_60

def loopBody418_62 : HolLoopProg 64 :=
.seq loopBody418_37 loopBody418_61

def loopBody418_63 : HolLoopProg 64 :=
.mark loopBody418_62

def loopBody418_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 80#64]))

def loopBody418_65 : HolLoopProg 64 :=
.mark loopBody418_64

def loopBody418_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsr
        (Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.add
            [Flapjack.HolLoopExp.var 5,
              Flapjack.HolLoopExp.shift Flapjack.Shift.lsl
                (Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 4)
                  (Flapjack.HolLoopExp.const 6#64))
                (Flapjack.HolLoopExp.const 3#64)]))
        (Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 63#64]),
      Flapjack.HolLoopExp.const 1#64])

def loopBody418_67 : HolLoopProg 64 :=
.mark loopBody418_66

def loopBody418_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody418_69 : HolLoopProg 64 :=
.mark loopBody418_68

def loopBody418_70 : HolLoopProg 64 :=
.seq loopBody418_69 loopBody418_17

def loopBody418_71 : HolLoopProg 64 :=
.mark loopBody418_70

def loopBody418_72 : HolLoopProg 64 :=
.seq loopBody418_67 loopBody418_71

def loopBody418_73 : HolLoopProg 64 :=
.mark loopBody418_72

def loopBody418_74 : HolLoopProg 64 :=
.seq loopBody418_65 loopBody418_73

def loopBody418_75 : HolLoopProg 64 :=
.mark loopBody418_74

def loopBody418_76 : HolLoopProg 64 :=
.seq loopBody418_17 loopBody418_75

def loopBody418_77 : HolLoopProg 64 :=
.mark loopBody418_76

def loopBody418_78 : HolLoopProg 64 :=
.seq loopBody418_63 loopBody418_77

def loopBody418_79 : HolLoopProg 64 :=
.mark loopBody418_78

def loopBody418_80 : HolLoopProg 64 :=
.seq loopBody418_35 loopBody418_79

def loopBody418_81 : HolLoopProg 64 :=
.mark loopBody418_80

def loopBody418_82 : HolLoopProg 64 :=
.seq loopBody418_17 loopBody418_81

def loopBody418_83 : HolLoopProg 64 :=
.mark loopBody418_82

def loopBody418_84 : HolLoopProg 64 :=
.seq loopBody418_33 loopBody418_83

def loopBody418_85 : HolLoopProg 64 :=
.mark loopBody418_84

def output418 : Nat × List Nat × HolLoopProg 64 :=
  (482, [0, 1, 2, 3], loopBody418_85)
end InitECandidate.Proofs.FrontendStages.Loop
