import InitECandidate.Proofs.FrontendStages.Loop.Translate469
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody485_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody485_1 : HolLoopProg 64 :=
.mark loopBody485_0

def loopBody485_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 2#64)

def loopBody485_3 : HolLoopProg 64 :=
.mark loopBody485_2

def loopBody485_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody485_5 : HolLoopProg 64 :=
.mark loopBody485_4

def loopBody485_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 466) ([2]) (some (2, loopBody485_5, loopBody485_1, (Flapjack.Spt.ln)))

def loopBody485_7 : HolLoopProg 64 :=
.mark loopBody485_6

def loopBody485_8 : HolLoopProg 64 :=
.seq loopBody485_7 loopBody485_1

def loopBody485_9 : HolLoopProg 64 :=
.mark loopBody485_8

def loopBody485_10 : HolLoopProg 64 :=
.seq loopBody485_3 loopBody485_9

def loopBody485_11 : HolLoopProg 64 :=
.mark loopBody485_10

def loopBody485_12 : HolLoopProg 64 :=
.seq loopBody485_1 loopBody485_11

def loopBody485_13 : HolLoopProg 64 :=
.mark loopBody485_12

def loopBody485_14 : HolLoopProg 64 :=
.seq loopBody485_1 loopBody485_13

def loopBody485_15 : HolLoopProg 64 :=
.mark loopBody485_14

def loopBody485_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.add
            [Flapjack.HolLoopExp.load
                (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                  [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
              Flapjack.HolLoopExp.const 112#64]),
        Flapjack.HolLoopExp.const 32#64]))

def loopBody485_17 : HolLoopProg 64 :=
.mark loopBody485_16

def loopBody485_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody485_19 : HolLoopProg 64 :=
.mark loopBody485_18

def loopBody485_20 : HolLoopProg 64 :=
.call (some ([1, 2, 3, 4], Flapjack.Spt.ln)) (some 463) ([5]) (some (5, loopBody485_19, loopBody485_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody485_21 : HolLoopProg 64 :=
.mark loopBody485_20

def loopBody485_22 : HolLoopProg 64 :=
.seq loopBody485_21 loopBody485_1

def loopBody485_23 : HolLoopProg 64 :=
.mark loopBody485_22

def loopBody485_24 : HolLoopProg 64 :=
.seq loopBody485_17 loopBody485_23

def loopBody485_25 : HolLoopProg 64 :=
.mark loopBody485_24

def loopBody485_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody485_27 : HolLoopProg 64 :=
.mark loopBody485_26

def loopBody485_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody485_29 : HolLoopProg 64 :=
.mark loopBody485_28

def loopBody485_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody485_31 : HolLoopProg 64 :=
.mark loopBody485_30

def loopBody485_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 4)

def loopBody485_33 : HolLoopProg 64 :=
.mark loopBody485_32

def loopBody485_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody485_35 : HolLoopProg 64 :=
.mark loopBody485_34

def loopBody485_36 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.ln)) (some 472) ([6, 7, 8, 9]) (some (6, loopBody485_35, loopBody485_1, (Flapjack.Spt.ln)))

def loopBody485_37 : HolLoopProg 64 :=
.mark loopBody485_36

def loopBody485_38 : HolLoopProg 64 :=
.seq loopBody485_37 loopBody485_1

def loopBody485_39 : HolLoopProg 64 :=
.mark loopBody485_38

def loopBody485_40 : HolLoopProg 64 :=
.seq loopBody485_33 loopBody485_39

def loopBody485_41 : HolLoopProg 64 :=
.mark loopBody485_40

def loopBody485_42 : HolLoopProg 64 :=
.seq loopBody485_31 loopBody485_41

def loopBody485_43 : HolLoopProg 64 :=
.mark loopBody485_42

def loopBody485_44 : HolLoopProg 64 :=
.seq loopBody485_29 loopBody485_43

def loopBody485_45 : HolLoopProg 64 :=
.mark loopBody485_44

def loopBody485_46 : HolLoopProg 64 :=
.seq loopBody485_27 loopBody485_45

def loopBody485_47 : HolLoopProg 64 :=
.mark loopBody485_46

def loopBody485_48 : HolLoopProg 64 :=
.seq loopBody485_1 loopBody485_47

def loopBody485_49 : HolLoopProg 64 :=
.mark loopBody485_48

def loopBody485_50 : HolLoopProg 64 :=
.seq loopBody485_1 loopBody485_49

def loopBody485_51 : HolLoopProg 64 :=
.mark loopBody485_50

def loopBody485_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody485_53 : HolLoopProg 64 :=
.mark loopBody485_52

def loopBody485_54 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.ln)) (some 486) ([6]) (some (6, loopBody485_35, loopBody485_1, (Flapjack.Spt.ln)))

def loopBody485_55 : HolLoopProg 64 :=
.mark loopBody485_54

def loopBody485_56 : HolLoopProg 64 :=
.seq loopBody485_55 loopBody485_1

def loopBody485_57 : HolLoopProg 64 :=
.mark loopBody485_56

def loopBody485_58 : HolLoopProg 64 :=
.seq loopBody485_53 loopBody485_57

def loopBody485_59 : HolLoopProg 64 :=
.mark loopBody485_58

def loopBody485_60 : HolLoopProg 64 :=
.seq loopBody485_1 loopBody485_59

def loopBody485_61 : HolLoopProg 64 :=
.mark loopBody485_60

def loopBody485_62 : HolLoopProg 64 :=
.seq loopBody485_1 loopBody485_61

def loopBody485_63 : HolLoopProg 64 :=
.mark loopBody485_62

def loopBody485_64 : HolLoopProg 64 :=
.seq loopBody485_51 loopBody485_63

def loopBody485_65 : HolLoopProg 64 :=
.mark loopBody485_64

def loopBody485_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody485_67 : HolLoopProg 64 :=
.mark loopBody485_66

def loopBody485_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody485_69 : HolLoopProg 64 :=
.mark loopBody485_68

def loopBody485_70 : HolLoopProg 64 :=
.seq loopBody485_69 loopBody485_1

def loopBody485_71 : HolLoopProg 64 :=
.mark loopBody485_70

def loopBody485_72 : HolLoopProg 64 :=
.seq loopBody485_67 loopBody485_71

def loopBody485_73 : HolLoopProg 64 :=
.mark loopBody485_72

def loopBody485_74 : HolLoopProg 64 :=
.seq loopBody485_65 loopBody485_73

def loopBody485_75 : HolLoopProg 64 :=
.mark loopBody485_74

def loopBody485_76 : HolLoopProg 64 :=
.seq loopBody485_25 loopBody485_75

def loopBody485_77 : HolLoopProg 64 :=
.mark loopBody485_76

def loopBody485_78 : HolLoopProg 64 :=
.seq loopBody485_1 loopBody485_77

def loopBody485_79 : HolLoopProg 64 :=
.mark loopBody485_78

def loopBody485_80 : HolLoopProg 64 :=
.seq loopBody485_1 loopBody485_79

def loopBody485_81 : HolLoopProg 64 :=
.mark loopBody485_80

def loopBody485_82 : HolLoopProg 64 :=
.seq loopBody485_1 loopBody485_81

def loopBody485_83 : HolLoopProg 64 :=
.mark loopBody485_82

def loopBody485_84 : HolLoopProg 64 :=
.seq loopBody485_1 loopBody485_83

def loopBody485_85 : HolLoopProg 64 :=
.mark loopBody485_84

def loopBody485_86 : HolLoopProg 64 :=
.seq loopBody485_1 loopBody485_85

def loopBody485_87 : HolLoopProg 64 :=
.mark loopBody485_86

def loopBody485_88 : HolLoopProg 64 :=
.seq loopBody485_1 loopBody485_87

def loopBody485_89 : HolLoopProg 64 :=
.mark loopBody485_88

def loopBody485_90 : HolLoopProg 64 :=
.seq loopBody485_1 loopBody485_89

def loopBody485_91 : HolLoopProg 64 :=
.mark loopBody485_90

def loopBody485_92 : HolLoopProg 64 :=
.seq loopBody485_1 loopBody485_91

def loopBody485_93 : HolLoopProg 64 :=
.mark loopBody485_92

def loopBody485_94 : HolLoopProg 64 :=
.seq loopBody485_15 loopBody485_93

def loopBody485_95 : HolLoopProg 64 :=
.mark loopBody485_94

def output485 : Nat × List Nat × HolLoopProg 64 :=
  (549, [], loopBody485_95)
end InitECandidate.Proofs.FrontendStages.Loop
