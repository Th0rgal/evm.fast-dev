import InitECandidate.Proofs.FrontendStages.Loop.Translate472
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody488_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody488_1 : HolLoopProg 64 :=
.mark loopBody488_0

def loopBody488_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 2#64)

def loopBody488_3 : HolLoopProg 64 :=
.mark loopBody488_2

def loopBody488_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody488_5 : HolLoopProg 64 :=
.mark loopBody488_4

def loopBody488_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 466) ([2]) (some (2, loopBody488_5, loopBody488_1, (Flapjack.Spt.ln)))

def loopBody488_7 : HolLoopProg 64 :=
.mark loopBody488_6

def loopBody488_8 : HolLoopProg 64 :=
.seq loopBody488_7 loopBody488_1

def loopBody488_9 : HolLoopProg 64 :=
.mark loopBody488_8

def loopBody488_10 : HolLoopProg 64 :=
.seq loopBody488_3 loopBody488_9

def loopBody488_11 : HolLoopProg 64 :=
.mark loopBody488_10

def loopBody488_12 : HolLoopProg 64 :=
.seq loopBody488_1 loopBody488_11

def loopBody488_13 : HolLoopProg 64 :=
.mark loopBody488_12

def loopBody488_14 : HolLoopProg 64 :=
.seq loopBody488_1 loopBody488_13

def loopBody488_15 : HolLoopProg 64 :=
.mark loopBody488_14

def loopBody488_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.add
            [Flapjack.HolLoopExp.load
                (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                  [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
              Flapjack.HolLoopExp.const 112#64]),
        Flapjack.HolLoopExp.const 16#64]))

def loopBody488_17 : HolLoopProg 64 :=
.mark loopBody488_16

def loopBody488_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody488_19 : HolLoopProg 64 :=
.mark loopBody488_18

def loopBody488_20 : HolLoopProg 64 :=
.call (some ([1, 2, 3, 4], Flapjack.Spt.ln)) (some 463) ([5]) (some (5, loopBody488_19, loopBody488_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody488_21 : HolLoopProg 64 :=
.mark loopBody488_20

def loopBody488_22 : HolLoopProg 64 :=
.seq loopBody488_21 loopBody488_1

def loopBody488_23 : HolLoopProg 64 :=
.mark loopBody488_22

def loopBody488_24 : HolLoopProg 64 :=
.seq loopBody488_17 loopBody488_23

def loopBody488_25 : HolLoopProg 64 :=
.mark loopBody488_24

def loopBody488_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody488_27 : HolLoopProg 64 :=
.mark loopBody488_26

def loopBody488_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody488_29 : HolLoopProg 64 :=
.mark loopBody488_28

def loopBody488_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody488_31 : HolLoopProg 64 :=
.mark loopBody488_30

def loopBody488_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 4)

def loopBody488_33 : HolLoopProg 64 :=
.mark loopBody488_32

def loopBody488_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody488_35 : HolLoopProg 64 :=
.mark loopBody488_34

def loopBody488_36 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.ln)) (some 472) ([6, 7, 8, 9]) (some (6, loopBody488_35, loopBody488_1, (Flapjack.Spt.ln)))

def loopBody488_37 : HolLoopProg 64 :=
.mark loopBody488_36

def loopBody488_38 : HolLoopProg 64 :=
.seq loopBody488_37 loopBody488_1

def loopBody488_39 : HolLoopProg 64 :=
.mark loopBody488_38

def loopBody488_40 : HolLoopProg 64 :=
.seq loopBody488_33 loopBody488_39

def loopBody488_41 : HolLoopProg 64 :=
.mark loopBody488_40

def loopBody488_42 : HolLoopProg 64 :=
.seq loopBody488_31 loopBody488_41

def loopBody488_43 : HolLoopProg 64 :=
.mark loopBody488_42

def loopBody488_44 : HolLoopProg 64 :=
.seq loopBody488_29 loopBody488_43

def loopBody488_45 : HolLoopProg 64 :=
.mark loopBody488_44

def loopBody488_46 : HolLoopProg 64 :=
.seq loopBody488_27 loopBody488_45

def loopBody488_47 : HolLoopProg 64 :=
.mark loopBody488_46

def loopBody488_48 : HolLoopProg 64 :=
.seq loopBody488_1 loopBody488_47

def loopBody488_49 : HolLoopProg 64 :=
.mark loopBody488_48

def loopBody488_50 : HolLoopProg 64 :=
.seq loopBody488_1 loopBody488_49

def loopBody488_51 : HolLoopProg 64 :=
.mark loopBody488_50

def loopBody488_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody488_53 : HolLoopProg 64 :=
.mark loopBody488_52

def loopBody488_54 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.ln)) (some 486) ([6]) (some (6, loopBody488_35, loopBody488_1, (Flapjack.Spt.ln)))

def loopBody488_55 : HolLoopProg 64 :=
.mark loopBody488_54

def loopBody488_56 : HolLoopProg 64 :=
.seq loopBody488_55 loopBody488_1

def loopBody488_57 : HolLoopProg 64 :=
.mark loopBody488_56

def loopBody488_58 : HolLoopProg 64 :=
.seq loopBody488_53 loopBody488_57

def loopBody488_59 : HolLoopProg 64 :=
.mark loopBody488_58

def loopBody488_60 : HolLoopProg 64 :=
.seq loopBody488_1 loopBody488_59

def loopBody488_61 : HolLoopProg 64 :=
.mark loopBody488_60

def loopBody488_62 : HolLoopProg 64 :=
.seq loopBody488_1 loopBody488_61

def loopBody488_63 : HolLoopProg 64 :=
.mark loopBody488_62

def loopBody488_64 : HolLoopProg 64 :=
.seq loopBody488_51 loopBody488_63

def loopBody488_65 : HolLoopProg 64 :=
.mark loopBody488_64

def loopBody488_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody488_67 : HolLoopProg 64 :=
.mark loopBody488_66

def loopBody488_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody488_69 : HolLoopProg 64 :=
.mark loopBody488_68

def loopBody488_70 : HolLoopProg 64 :=
.seq loopBody488_69 loopBody488_1

def loopBody488_71 : HolLoopProg 64 :=
.mark loopBody488_70

def loopBody488_72 : HolLoopProg 64 :=
.seq loopBody488_67 loopBody488_71

def loopBody488_73 : HolLoopProg 64 :=
.mark loopBody488_72

def loopBody488_74 : HolLoopProg 64 :=
.seq loopBody488_65 loopBody488_73

def loopBody488_75 : HolLoopProg 64 :=
.mark loopBody488_74

def loopBody488_76 : HolLoopProg 64 :=
.seq loopBody488_25 loopBody488_75

def loopBody488_77 : HolLoopProg 64 :=
.mark loopBody488_76

def loopBody488_78 : HolLoopProg 64 :=
.seq loopBody488_1 loopBody488_77

def loopBody488_79 : HolLoopProg 64 :=
.mark loopBody488_78

def loopBody488_80 : HolLoopProg 64 :=
.seq loopBody488_1 loopBody488_79

def loopBody488_81 : HolLoopProg 64 :=
.mark loopBody488_80

def loopBody488_82 : HolLoopProg 64 :=
.seq loopBody488_1 loopBody488_81

def loopBody488_83 : HolLoopProg 64 :=
.mark loopBody488_82

def loopBody488_84 : HolLoopProg 64 :=
.seq loopBody488_1 loopBody488_83

def loopBody488_85 : HolLoopProg 64 :=
.mark loopBody488_84

def loopBody488_86 : HolLoopProg 64 :=
.seq loopBody488_1 loopBody488_85

def loopBody488_87 : HolLoopProg 64 :=
.mark loopBody488_86

def loopBody488_88 : HolLoopProg 64 :=
.seq loopBody488_1 loopBody488_87

def loopBody488_89 : HolLoopProg 64 :=
.mark loopBody488_88

def loopBody488_90 : HolLoopProg 64 :=
.seq loopBody488_1 loopBody488_89

def loopBody488_91 : HolLoopProg 64 :=
.mark loopBody488_90

def loopBody488_92 : HolLoopProg 64 :=
.seq loopBody488_1 loopBody488_91

def loopBody488_93 : HolLoopProg 64 :=
.mark loopBody488_92

def loopBody488_94 : HolLoopProg 64 :=
.seq loopBody488_15 loopBody488_93

def loopBody488_95 : HolLoopProg 64 :=
.mark loopBody488_94

def output488 : Nat × List Nat × HolLoopProg 64 :=
  (552, [], loopBody488_95)
end InitECandidate.Proofs.FrontendStages.Loop
