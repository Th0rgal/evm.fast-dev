import InitECandidate.Proofs.FrontendStages.Loop.Translate471
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody487_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody487_1 : HolLoopProg 64 :=
.mark loopBody487_0

def loopBody487_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 2#64)

def loopBody487_3 : HolLoopProg 64 :=
.mark loopBody487_2

def loopBody487_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody487_5 : HolLoopProg 64 :=
.mark loopBody487_4

def loopBody487_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 466) ([2]) (some (2, loopBody487_5, loopBody487_1, (Flapjack.Spt.ln)))

def loopBody487_7 : HolLoopProg 64 :=
.mark loopBody487_6

def loopBody487_8 : HolLoopProg 64 :=
.seq loopBody487_7 loopBody487_1

def loopBody487_9 : HolLoopProg 64 :=
.mark loopBody487_8

def loopBody487_10 : HolLoopProg 64 :=
.seq loopBody487_3 loopBody487_9

def loopBody487_11 : HolLoopProg 64 :=
.mark loopBody487_10

def loopBody487_12 : HolLoopProg 64 :=
.seq loopBody487_1 loopBody487_11

def loopBody487_13 : HolLoopProg 64 :=
.mark loopBody487_12

def loopBody487_14 : HolLoopProg 64 :=
.seq loopBody487_1 loopBody487_13

def loopBody487_15 : HolLoopProg 64 :=
.mark loopBody487_14

def loopBody487_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.add
            [Flapjack.HolLoopExp.load
                (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                  [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
              Flapjack.HolLoopExp.const 112#64]),
        Flapjack.HolLoopExp.const 8#64]))

def loopBody487_17 : HolLoopProg 64 :=
.mark loopBody487_16

def loopBody487_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 0#64]))

def loopBody487_19 : HolLoopProg 64 :=
.mark loopBody487_18

def loopBody487_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody487_21 : HolLoopProg 64 :=
.mark loopBody487_20

def loopBody487_22 : HolLoopProg 64 :=
.call (some ([2, 3, 4, 5], Flapjack.Spt.ln)) (some 463) ([6]) (some (6, loopBody487_21, loopBody487_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))

def loopBody487_23 : HolLoopProg 64 :=
.mark loopBody487_22

def loopBody487_24 : HolLoopProg 64 :=
.seq loopBody487_23 loopBody487_1

def loopBody487_25 : HolLoopProg 64 :=
.mark loopBody487_24

def loopBody487_26 : HolLoopProg 64 :=
.seq loopBody487_19 loopBody487_25

def loopBody487_27 : HolLoopProg 64 :=
.mark loopBody487_26

def loopBody487_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody487_29 : HolLoopProg 64 :=
.mark loopBody487_28

def loopBody487_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody487_31 : HolLoopProg 64 :=
.mark loopBody487_30

def loopBody487_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 4)

def loopBody487_33 : HolLoopProg 64 :=
.mark loopBody487_32

def loopBody487_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 5)

def loopBody487_35 : HolLoopProg 64 :=
.mark loopBody487_34

def loopBody487_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody487_37 : HolLoopProg 64 :=
.mark loopBody487_36

def loopBody487_38 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.ln)) (some 472) ([7, 8, 9, 10]) (some (7, loopBody487_37, loopBody487_1, (Flapjack.Spt.ln)))

def loopBody487_39 : HolLoopProg 64 :=
.mark loopBody487_38

def loopBody487_40 : HolLoopProg 64 :=
.seq loopBody487_39 loopBody487_1

def loopBody487_41 : HolLoopProg 64 :=
.mark loopBody487_40

def loopBody487_42 : HolLoopProg 64 :=
.seq loopBody487_35 loopBody487_41

def loopBody487_43 : HolLoopProg 64 :=
.mark loopBody487_42

def loopBody487_44 : HolLoopProg 64 :=
.seq loopBody487_33 loopBody487_43

def loopBody487_45 : HolLoopProg 64 :=
.mark loopBody487_44

def loopBody487_46 : HolLoopProg 64 :=
.seq loopBody487_31 loopBody487_45

def loopBody487_47 : HolLoopProg 64 :=
.mark loopBody487_46

def loopBody487_48 : HolLoopProg 64 :=
.seq loopBody487_29 loopBody487_47

def loopBody487_49 : HolLoopProg 64 :=
.mark loopBody487_48

def loopBody487_50 : HolLoopProg 64 :=
.seq loopBody487_1 loopBody487_49

def loopBody487_51 : HolLoopProg 64 :=
.mark loopBody487_50

def loopBody487_52 : HolLoopProg 64 :=
.seq loopBody487_1 loopBody487_51

def loopBody487_53 : HolLoopProg 64 :=
.mark loopBody487_52

def loopBody487_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody487_55 : HolLoopProg 64 :=
.mark loopBody487_54

def loopBody487_56 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.ln)) (some 486) ([7]) (some (7, loopBody487_37, loopBody487_1, (Flapjack.Spt.ln)))

def loopBody487_57 : HolLoopProg 64 :=
.mark loopBody487_56

def loopBody487_58 : HolLoopProg 64 :=
.seq loopBody487_57 loopBody487_1

def loopBody487_59 : HolLoopProg 64 :=
.mark loopBody487_58

def loopBody487_60 : HolLoopProg 64 :=
.seq loopBody487_55 loopBody487_59

def loopBody487_61 : HolLoopProg 64 :=
.mark loopBody487_60

def loopBody487_62 : HolLoopProg 64 :=
.seq loopBody487_1 loopBody487_61

def loopBody487_63 : HolLoopProg 64 :=
.mark loopBody487_62

def loopBody487_64 : HolLoopProg 64 :=
.seq loopBody487_1 loopBody487_63

def loopBody487_65 : HolLoopProg 64 :=
.mark loopBody487_64

def loopBody487_66 : HolLoopProg 64 :=
.seq loopBody487_53 loopBody487_65

def loopBody487_67 : HolLoopProg 64 :=
.mark loopBody487_66

def loopBody487_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody487_69 : HolLoopProg 64 :=
.mark loopBody487_68

def loopBody487_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody487_71 : HolLoopProg 64 :=
.mark loopBody487_70

def loopBody487_72 : HolLoopProg 64 :=
.seq loopBody487_71 loopBody487_1

def loopBody487_73 : HolLoopProg 64 :=
.mark loopBody487_72

def loopBody487_74 : HolLoopProg 64 :=
.seq loopBody487_69 loopBody487_73

def loopBody487_75 : HolLoopProg 64 :=
.mark loopBody487_74

def loopBody487_76 : HolLoopProg 64 :=
.seq loopBody487_67 loopBody487_75

def loopBody487_77 : HolLoopProg 64 :=
.mark loopBody487_76

def loopBody487_78 : HolLoopProg 64 :=
.seq loopBody487_27 loopBody487_77

def loopBody487_79 : HolLoopProg 64 :=
.mark loopBody487_78

def loopBody487_80 : HolLoopProg 64 :=
.seq loopBody487_1 loopBody487_79

def loopBody487_81 : HolLoopProg 64 :=
.mark loopBody487_80

def loopBody487_82 : HolLoopProg 64 :=
.seq loopBody487_1 loopBody487_81

def loopBody487_83 : HolLoopProg 64 :=
.mark loopBody487_82

def loopBody487_84 : HolLoopProg 64 :=
.seq loopBody487_1 loopBody487_83

def loopBody487_85 : HolLoopProg 64 :=
.mark loopBody487_84

def loopBody487_86 : HolLoopProg 64 :=
.seq loopBody487_1 loopBody487_85

def loopBody487_87 : HolLoopProg 64 :=
.mark loopBody487_86

def loopBody487_88 : HolLoopProg 64 :=
.seq loopBody487_1 loopBody487_87

def loopBody487_89 : HolLoopProg 64 :=
.mark loopBody487_88

def loopBody487_90 : HolLoopProg 64 :=
.seq loopBody487_1 loopBody487_89

def loopBody487_91 : HolLoopProg 64 :=
.mark loopBody487_90

def loopBody487_92 : HolLoopProg 64 :=
.seq loopBody487_1 loopBody487_91

def loopBody487_93 : HolLoopProg 64 :=
.mark loopBody487_92

def loopBody487_94 : HolLoopProg 64 :=
.seq loopBody487_1 loopBody487_93

def loopBody487_95 : HolLoopProg 64 :=
.mark loopBody487_94

def loopBody487_96 : HolLoopProg 64 :=
.seq loopBody487_17 loopBody487_95

def loopBody487_97 : HolLoopProg 64 :=
.mark loopBody487_96

def loopBody487_98 : HolLoopProg 64 :=
.seq loopBody487_1 loopBody487_97

def loopBody487_99 : HolLoopProg 64 :=
.mark loopBody487_98

def loopBody487_100 : HolLoopProg 64 :=
.seq loopBody487_15 loopBody487_99

def loopBody487_101 : HolLoopProg 64 :=
.mark loopBody487_100

def output487 : Nat × List Nat × HolLoopProg 64 :=
  (551, [], loopBody487_101)
end InitECandidate.Proofs.FrontendStages.Loop
