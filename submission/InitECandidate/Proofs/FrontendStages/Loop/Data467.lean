import InitECandidate.Proofs.FrontendStages.Loop.Translate451
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody467_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody467_1 : HolLoopProg 64 :=
.mark loopBody467_0

def loopBody467_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody467_3 : HolLoopProg 64 :=
.mark loopBody467_2

def loopBody467_4 : HolLoopProg 64 :=
.call (some ([1, 2, 3, 4], Flapjack.Spt.ln)) (some 471) ([]) (some (5, loopBody467_3, loopBody467_1, (Flapjack.Spt.ln)))

def loopBody467_5 : HolLoopProg 64 :=
.mark loopBody467_4

def loopBody467_6 : HolLoopProg 64 :=
.seq loopBody467_5 loopBody467_1

def loopBody467_7 : HolLoopProg 64 :=
.mark loopBody467_6

def loopBody467_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 2#64)

def loopBody467_9 : HolLoopProg 64 :=
.mark loopBody467_8

def loopBody467_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody467_11 : HolLoopProg 64 :=
.mark loopBody467_10

def loopBody467_12 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.ln)) (some 466) ([6]) (some (6, loopBody467_11, loopBody467_1, (Flapjack.Spt.ln)))

def loopBody467_13 : HolLoopProg 64 :=
.mark loopBody467_12

def loopBody467_14 : HolLoopProg 64 :=
.seq loopBody467_13 loopBody467_1

def loopBody467_15 : HolLoopProg 64 :=
.mark loopBody467_14

def loopBody467_16 : HolLoopProg 64 :=
.seq loopBody467_9 loopBody467_15

def loopBody467_17 : HolLoopProg 64 :=
.mark loopBody467_16

def loopBody467_18 : HolLoopProg 64 :=
.seq loopBody467_1 loopBody467_17

def loopBody467_19 : HolLoopProg 64 :=
.mark loopBody467_18

def loopBody467_20 : HolLoopProg 64 :=
.seq loopBody467_1 loopBody467_19

def loopBody467_21 : HolLoopProg 64 :=
.mark loopBody467_20

def loopBody467_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody467_23 : HolLoopProg 64 :=
.mark loopBody467_22

def loopBody467_24 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.ln)) (some 486) ([6]) (some (6, loopBody467_11, loopBody467_1, (Flapjack.Spt.ln)))

def loopBody467_25 : HolLoopProg 64 :=
.mark loopBody467_24

def loopBody467_26 : HolLoopProg 64 :=
.seq loopBody467_25 loopBody467_1

def loopBody467_27 : HolLoopProg 64 :=
.mark loopBody467_26

def loopBody467_28 : HolLoopProg 64 :=
.seq loopBody467_23 loopBody467_27

def loopBody467_29 : HolLoopProg 64 :=
.mark loopBody467_28

def loopBody467_30 : HolLoopProg 64 :=
.seq loopBody467_1 loopBody467_29

def loopBody467_31 : HolLoopProg 64 :=
.mark loopBody467_30

def loopBody467_32 : HolLoopProg 64 :=
.seq loopBody467_1 loopBody467_31

def loopBody467_33 : HolLoopProg 64 :=
.mark loopBody467_32

def loopBody467_34 : HolLoopProg 64 :=
.seq loopBody467_21 loopBody467_33

def loopBody467_35 : HolLoopProg 64 :=
.mark loopBody467_34

def loopBody467_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody467_37 : HolLoopProg 64 :=
.mark loopBody467_36

def loopBody467_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody467_39 : HolLoopProg 64 :=
.mark loopBody467_38

def loopBody467_40 : HolLoopProg 64 :=
.seq loopBody467_39 loopBody467_1

def loopBody467_41 : HolLoopProg 64 :=
.mark loopBody467_40

def loopBody467_42 : HolLoopProg 64 :=
.seq loopBody467_37 loopBody467_41

def loopBody467_43 : HolLoopProg 64 :=
.mark loopBody467_42

def loopBody467_44 : HolLoopProg 64 :=
.seq loopBody467_35 loopBody467_43

def loopBody467_45 : HolLoopProg 64 :=
.mark loopBody467_44

def loopBody467_46 : HolLoopProg 64 :=
.seq loopBody467_7 loopBody467_45

def loopBody467_47 : HolLoopProg 64 :=
.mark loopBody467_46

def loopBody467_48 : HolLoopProg 64 :=
.seq loopBody467_1 loopBody467_47

def loopBody467_49 : HolLoopProg 64 :=
.mark loopBody467_48

def loopBody467_50 : HolLoopProg 64 :=
.seq loopBody467_1 loopBody467_49

def loopBody467_51 : HolLoopProg 64 :=
.mark loopBody467_50

def loopBody467_52 : HolLoopProg 64 :=
.seq loopBody467_1 loopBody467_51

def loopBody467_53 : HolLoopProg 64 :=
.mark loopBody467_52

def loopBody467_54 : HolLoopProg 64 :=
.seq loopBody467_1 loopBody467_53

def loopBody467_55 : HolLoopProg 64 :=
.mark loopBody467_54

def loopBody467_56 : HolLoopProg 64 :=
.seq loopBody467_1 loopBody467_55

def loopBody467_57 : HolLoopProg 64 :=
.mark loopBody467_56

def loopBody467_58 : HolLoopProg 64 :=
.seq loopBody467_1 loopBody467_57

def loopBody467_59 : HolLoopProg 64 :=
.mark loopBody467_58

def loopBody467_60 : HolLoopProg 64 :=
.seq loopBody467_1 loopBody467_59

def loopBody467_61 : HolLoopProg 64 :=
.mark loopBody467_60

def loopBody467_62 : HolLoopProg 64 :=
.seq loopBody467_1 loopBody467_61

def loopBody467_63 : HolLoopProg 64 :=
.mark loopBody467_62

def output467 : Nat × List Nat × HolLoopProg 64 :=
  (531, [], loopBody467_63)
end InitECandidate.Proofs.FrontendStages.Loop
