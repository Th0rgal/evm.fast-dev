import InitECandidate.Proofs.FrontendStages.Loop.Translate196
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody212_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody212_1 : HolLoopProg 64 :=
.mark loopBody212_0

def loopBody212_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody212_3 : HolLoopProg 64 :=
.mark loopBody212_2

def loopBody212_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody212_5 : HolLoopProg 64 :=
.mark loopBody212_4

def loopBody212_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 11684671#64)

def loopBody212_7 : HolLoopProg 64 :=
.mark loopBody212_6

def loopBody212_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody212_9 : HolLoopProg 64 :=
.mark loopBody212_8

def loopBody212_10 : HolLoopProg 64 :=
.call (some ([1, 2, 3, 4], Flapjack.Spt.ln)) (some 275) ([5, 6, 7]) (some (5, loopBody212_9, loopBody212_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody212_11 : HolLoopProg 64 :=
.mark loopBody212_10

def loopBody212_12 : HolLoopProg 64 :=
.seq loopBody212_11 loopBody212_1

def loopBody212_13 : HolLoopProg 64 :=
.mark loopBody212_12

def loopBody212_14 : HolLoopProg 64 :=
.seq loopBody212_7 loopBody212_13

def loopBody212_15 : HolLoopProg 64 :=
.mark loopBody212_14

def loopBody212_16 : HolLoopProg 64 :=
.seq loopBody212_5 loopBody212_15

def loopBody212_17 : HolLoopProg 64 :=
.mark loopBody212_16

def loopBody212_18 : HolLoopProg 64 :=
.seq loopBody212_3 loopBody212_17

def loopBody212_19 : HolLoopProg 64 :=
.mark loopBody212_18

def loopBody212_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody212_21 : HolLoopProg 64 :=
.mark loopBody212_20

def loopBody212_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 2)

def loopBody212_23 : HolLoopProg 64 :=
.mark loopBody212_22

def loopBody212_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody212_25 : HolLoopProg 64 :=
.mark loopBody212_24

def loopBody212_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 4)

def loopBody212_27 : HolLoopProg 64 :=
.mark loopBody212_26

def loopBody212_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5, 6, 7, 8]

def loopBody212_29 : HolLoopProg 64 :=
.mark loopBody212_28

def loopBody212_30 : HolLoopProg 64 :=
.seq loopBody212_29 loopBody212_1

def loopBody212_31 : HolLoopProg 64 :=
.mark loopBody212_30

def loopBody212_32 : HolLoopProg 64 :=
.seq loopBody212_27 loopBody212_31

def loopBody212_33 : HolLoopProg 64 :=
.mark loopBody212_32

def loopBody212_34 : HolLoopProg 64 :=
.seq loopBody212_25 loopBody212_33

def loopBody212_35 : HolLoopProg 64 :=
.mark loopBody212_34

def loopBody212_36 : HolLoopProg 64 :=
.seq loopBody212_23 loopBody212_35

def loopBody212_37 : HolLoopProg 64 :=
.mark loopBody212_36

def loopBody212_38 : HolLoopProg 64 :=
.seq loopBody212_21 loopBody212_37

def loopBody212_39 : HolLoopProg 64 :=
.mark loopBody212_38

def loopBody212_40 : HolLoopProg 64 :=
.seq loopBody212_19 loopBody212_39

def loopBody212_41 : HolLoopProg 64 :=
.mark loopBody212_40

def loopBody212_42 : HolLoopProg 64 :=
.seq loopBody212_1 loopBody212_41

def loopBody212_43 : HolLoopProg 64 :=
.mark loopBody212_42

def loopBody212_44 : HolLoopProg 64 :=
.seq loopBody212_1 loopBody212_43

def loopBody212_45 : HolLoopProg 64 :=
.mark loopBody212_44

def loopBody212_46 : HolLoopProg 64 :=
.seq loopBody212_1 loopBody212_45

def loopBody212_47 : HolLoopProg 64 :=
.mark loopBody212_46

def loopBody212_48 : HolLoopProg 64 :=
.seq loopBody212_1 loopBody212_47

def loopBody212_49 : HolLoopProg 64 :=
.mark loopBody212_48

def loopBody212_50 : HolLoopProg 64 :=
.seq loopBody212_1 loopBody212_49

def loopBody212_51 : HolLoopProg 64 :=
.mark loopBody212_50

def loopBody212_52 : HolLoopProg 64 :=
.seq loopBody212_1 loopBody212_51

def loopBody212_53 : HolLoopProg 64 :=
.mark loopBody212_52

def loopBody212_54 : HolLoopProg 64 :=
.seq loopBody212_1 loopBody212_53

def loopBody212_55 : HolLoopProg 64 :=
.mark loopBody212_54

def loopBody212_56 : HolLoopProg 64 :=
.seq loopBody212_1 loopBody212_55

def loopBody212_57 : HolLoopProg 64 :=
.mark loopBody212_56

def output212 : Nat × List Nat × HolLoopProg 64 :=
  (276, [0], loopBody212_57)
end InitECandidate.Proofs.FrontendStages.Loop
