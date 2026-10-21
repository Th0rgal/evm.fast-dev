import InitECandidate.Proofs.FrontendStages.Loop.Translate786
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody802_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody802_1 : HolLoopProg 64 :=
.mark loopBody802_0

def loopBody802_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody802_3 : HolLoopProg 64 :=
.mark loopBody802_2

def loopBody802_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody802_5 : HolLoopProg 64 :=
.mark loopBody802_4

def loopBody802_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.tick

def loopBody802_7 : HolLoopProg 64 :=
.mark loopBody802_6

def loopBody802_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.lookup 0#5)

def loopBody802_9 : HolLoopProg 64 :=
.mark loopBody802_8

def loopBody802_10 : HolLoopProg 64 :=
.seq loopBody802_9 loopBody802_1

def loopBody802_11 : HolLoopProg 64 :=
.mark loopBody802_10

def loopBody802_12 : HolLoopProg 64 :=
.seq loopBody802_11 loopBody802_1

def loopBody802_13 : HolLoopProg 64 :=
.mark loopBody802_12

def loopBody802_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody802_15 : HolLoopProg 64 :=
.mark loopBody802_14

def loopBody802_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.shMem Flapjack.WordMemOp.store8 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.const 2688614400#64, Flapjack.HolLoopExp.const 70#64])

def loopBody802_17 : HolLoopProg 64 :=
.mark loopBody802_16

def loopBody802_18 : HolLoopProg 64 :=
.seq loopBody802_17 loopBody802_1

def loopBody802_19 : HolLoopProg 64 :=
.mark loopBody802_18

def loopBody802_20 : HolLoopProg 64 :=
.seq loopBody802_15 loopBody802_19

def loopBody802_21 : HolLoopProg 64 :=
.mark loopBody802_20

def loopBody802_22 : HolLoopProg 64 :=
.seq loopBody802_1 loopBody802_21

def loopBody802_23 : HolLoopProg 64 :=
.mark loopBody802_22

def loopBody802_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody802_25 : HolLoopProg 64 :=
.mark loopBody802_24

def loopBody802_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 3)

def loopBody802_27 : HolLoopProg 64 :=
.mark loopBody802_26

def loopBody802_28 : HolLoopProg 64 :=
.seq loopBody802_27 loopBody802_1

def loopBody802_29 : HolLoopProg 64 :=
.mark loopBody802_28

def loopBody802_30 : HolLoopProg 64 :=
.seq loopBody802_29 loopBody802_1

def loopBody802_31 : HolLoopProg 64 :=
.mark loopBody802_30

def loopBody802_32 : HolLoopProg 64 :=
.seq loopBody802_25 loopBody802_31

def loopBody802_33 : HolLoopProg 64 :=
.mark loopBody802_32

def loopBody802_34 : HolLoopProg 64 :=
.seq loopBody802_1 loopBody802_33

def loopBody802_35 : HolLoopProg 64 :=
.mark loopBody802_34

def loopBody802_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 9#64)

def loopBody802_37 : HolLoopProg 64 :=
.mark loopBody802_36

def loopBody802_38 : HolLoopProg 64 :=
.seq loopBody802_37 loopBody802_5

def loopBody802_39 : HolLoopProg 64 :=
.mark loopBody802_38

def loopBody802_40 : HolLoopProg 64 :=
.seq loopBody802_35 loopBody802_39

def loopBody802_41 : HolLoopProg 64 :=
.mark loopBody802_40

def loopBody802_42 : HolLoopProg 64 :=
.seq loopBody802_23 loopBody802_41

def loopBody802_43 : HolLoopProg 64 :=
.mark loopBody802_42

def loopBody802_44 : HolLoopProg 64 :=
.seq loopBody802_13 loopBody802_43

def loopBody802_45 : HolLoopProg 64 :=
.mark loopBody802_44

def loopBody802_46 : HolLoopProg 64 :=
.seq loopBody802_7 loopBody802_45

def loopBody802_47 : HolLoopProg 64 :=
.mark loopBody802_46

def loopBody802_48 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 3 (Flapjack.RegImm.imm 4#64) loopBody802_5 loopBody802_47 (Flapjack.Spt.ln)

def loopBody802_49 : HolLoopProg 64 :=
.mark loopBody802_48

def loopBody802_50 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 865) ([3]) (some (3, loopBody802_49, loopBody802_1, (Flapjack.Spt.ln)))

def loopBody802_51 : HolLoopProg 64 :=
.mark loopBody802_50

def loopBody802_52 : HolLoopProg 64 :=
.seq loopBody802_51 loopBody802_1

def loopBody802_53 : HolLoopProg 64 :=
.mark loopBody802_52

def loopBody802_54 : HolLoopProg 64 :=
.seq loopBody802_3 loopBody802_53

def loopBody802_55 : HolLoopProg 64 :=
.mark loopBody802_54

def loopBody802_56 : HolLoopProg 64 :=
.seq loopBody802_1 loopBody802_55

def loopBody802_57 : HolLoopProg 64 :=
.mark loopBody802_56

def loopBody802_58 : HolLoopProg 64 :=
.seq loopBody802_1 loopBody802_57

def loopBody802_59 : HolLoopProg 64 :=
.mark loopBody802_58

def loopBody802_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody802_61 : HolLoopProg 64 :=
.mark loopBody802_60

def loopBody802_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody802_63 : HolLoopProg 64 :=
.mark loopBody802_62

def loopBody802_64 : HolLoopProg 64 :=
.seq loopBody802_63 loopBody802_1

def loopBody802_65 : HolLoopProg 64 :=
.mark loopBody802_64

def loopBody802_66 : HolLoopProg 64 :=
.seq loopBody802_61 loopBody802_65

def loopBody802_67 : HolLoopProg 64 :=
.mark loopBody802_66

def loopBody802_68 : HolLoopProg 64 :=
.seq loopBody802_59 loopBody802_67

def loopBody802_69 : HolLoopProg 64 :=
.mark loopBody802_68

def loopBody802_70 : HolLoopProg 64 :=
.seq loopBody802_1 loopBody802_69

def loopBody802_71 : HolLoopProg 64 :=
.mark loopBody802_70

def loopBody802_72 : HolLoopProg 64 :=
.seq loopBody802_1 loopBody802_71

def loopBody802_73 : HolLoopProg 64 :=
.mark loopBody802_72

def output802 : Nat × List Nat × HolLoopProg 64 :=
  (866, [0], loopBody802_73)
end InitECandidate.Proofs.FrontendStages.Loop
