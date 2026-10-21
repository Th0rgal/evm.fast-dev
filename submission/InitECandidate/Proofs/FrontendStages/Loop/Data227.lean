import InitECandidate.Proofs.FrontendStages.Loop.Translate211
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody227_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody227_1 : HolLoopProg 64 :=
.mark loopBody227_0

def loopBody227_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 32#64)

def loopBody227_3 : HolLoopProg 64 :=
.mark loopBody227_2

def loopBody227_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody227_5 : HolLoopProg 64 :=
.mark loopBody227_4

def loopBody227_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ls PUnit.unit)) (some 68) ([2]) (some (2, loopBody227_5, loopBody227_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody227_7 : HolLoopProg 64 :=
.mark loopBody227_6

def loopBody227_8 : HolLoopProg 64 :=
.seq loopBody227_7 loopBody227_1

def loopBody227_9 : HolLoopProg 64 :=
.mark loopBody227_8

def loopBody227_10 : HolLoopProg 64 :=
.seq loopBody227_3 loopBody227_9

def loopBody227_11 : HolLoopProg 64 :=
.mark loopBody227_10

def loopBody227_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 0#64])

def loopBody227_13 : HolLoopProg 64 :=
.mark loopBody227_12

def loopBody227_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody227_15 : HolLoopProg 64 :=
.mark loopBody227_14

def loopBody227_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 3)

def loopBody227_17 : HolLoopProg 64 :=
.mark loopBody227_16

def loopBody227_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 2) 4

def loopBody227_19 : HolLoopProg 64 :=
.mark loopBody227_18

def loopBody227_20 : HolLoopProg 64 :=
.seq loopBody227_19 loopBody227_1

def loopBody227_21 : HolLoopProg 64 :=
.mark loopBody227_20

def loopBody227_22 : HolLoopProg 64 :=
.seq loopBody227_17 loopBody227_21

def loopBody227_23 : HolLoopProg 64 :=
.mark loopBody227_22

def loopBody227_24 : HolLoopProg 64 :=
.seq loopBody227_23 loopBody227_1

def loopBody227_25 : HolLoopProg 64 :=
.mark loopBody227_24

def loopBody227_26 : HolLoopProg 64 :=
.seq loopBody227_15 loopBody227_25

def loopBody227_27 : HolLoopProg 64 :=
.mark loopBody227_26

def loopBody227_28 : HolLoopProg 64 :=
.seq loopBody227_1 loopBody227_27

def loopBody227_29 : HolLoopProg 64 :=
.mark loopBody227_28

def loopBody227_30 : HolLoopProg 64 :=
.seq loopBody227_13 loopBody227_29

def loopBody227_31 : HolLoopProg 64 :=
.mark loopBody227_30

def loopBody227_32 : HolLoopProg 64 :=
.seq loopBody227_1 loopBody227_31

def loopBody227_33 : HolLoopProg 64 :=
.mark loopBody227_32

def loopBody227_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 8#64])

def loopBody227_35 : HolLoopProg 64 :=
.mark loopBody227_34

def loopBody227_36 : HolLoopProg 64 :=
.seq loopBody227_35 loopBody227_29

def loopBody227_37 : HolLoopProg 64 :=
.mark loopBody227_36

def loopBody227_38 : HolLoopProg 64 :=
.seq loopBody227_1 loopBody227_37

def loopBody227_39 : HolLoopProg 64 :=
.mark loopBody227_38

def loopBody227_40 : HolLoopProg 64 :=
.seq loopBody227_33 loopBody227_39

def loopBody227_41 : HolLoopProg 64 :=
.mark loopBody227_40

def loopBody227_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 16#64])

def loopBody227_43 : HolLoopProg 64 :=
.mark loopBody227_42

def loopBody227_44 : HolLoopProg 64 :=
.seq loopBody227_43 loopBody227_29

def loopBody227_45 : HolLoopProg 64 :=
.mark loopBody227_44

def loopBody227_46 : HolLoopProg 64 :=
.seq loopBody227_1 loopBody227_45

def loopBody227_47 : HolLoopProg 64 :=
.mark loopBody227_46

def loopBody227_48 : HolLoopProg 64 :=
.seq loopBody227_41 loopBody227_47

def loopBody227_49 : HolLoopProg 64 :=
.mark loopBody227_48

def loopBody227_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 24#64])

def loopBody227_51 : HolLoopProg 64 :=
.mark loopBody227_50

def loopBody227_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody227_53 : HolLoopProg 64 :=
.mark loopBody227_52

def loopBody227_54 : HolLoopProg 64 :=
.seq loopBody227_53 loopBody227_25

def loopBody227_55 : HolLoopProg 64 :=
.mark loopBody227_54

def loopBody227_56 : HolLoopProg 64 :=
.seq loopBody227_1 loopBody227_55

def loopBody227_57 : HolLoopProg 64 :=
.mark loopBody227_56

def loopBody227_58 : HolLoopProg 64 :=
.seq loopBody227_51 loopBody227_57

def loopBody227_59 : HolLoopProg 64 :=
.mark loopBody227_58

def loopBody227_60 : HolLoopProg 64 :=
.seq loopBody227_1 loopBody227_59

def loopBody227_61 : HolLoopProg 64 :=
.mark loopBody227_60

def loopBody227_62 : HolLoopProg 64 :=
.seq loopBody227_49 loopBody227_61

def loopBody227_63 : HolLoopProg 64 :=
.mark loopBody227_62

def loopBody227_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 1)

def loopBody227_65 : HolLoopProg 64 :=
.mark loopBody227_64

def loopBody227_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody227_67 : HolLoopProg 64 :=
.mark loopBody227_66

def loopBody227_68 : HolLoopProg 64 :=
.seq loopBody227_67 loopBody227_1

def loopBody227_69 : HolLoopProg 64 :=
.mark loopBody227_68

def loopBody227_70 : HolLoopProg 64 :=
.seq loopBody227_65 loopBody227_69

def loopBody227_71 : HolLoopProg 64 :=
.mark loopBody227_70

def loopBody227_72 : HolLoopProg 64 :=
.seq loopBody227_63 loopBody227_71

def loopBody227_73 : HolLoopProg 64 :=
.mark loopBody227_72

def loopBody227_74 : HolLoopProg 64 :=
.seq loopBody227_11 loopBody227_73

def loopBody227_75 : HolLoopProg 64 :=
.mark loopBody227_74

def loopBody227_76 : HolLoopProg 64 :=
.seq loopBody227_1 loopBody227_75

def loopBody227_77 : HolLoopProg 64 :=
.mark loopBody227_76

def loopBody227_78 : HolLoopProg 64 :=
.seq loopBody227_1 loopBody227_77

def loopBody227_79 : HolLoopProg 64 :=
.mark loopBody227_78

def output227 : Nat × List Nat × HolLoopProg 64 :=
  (291, [0], loopBody227_79)
end InitECandidate.Proofs.FrontendStages.Loop
