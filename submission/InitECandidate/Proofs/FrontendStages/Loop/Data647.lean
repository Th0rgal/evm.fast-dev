import InitECandidate.Proofs.FrontendStages.Loop.Translate631
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody647_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody647_1 : HolLoopProg 64 :=
.mark loopBody647_0

def loopBody647_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody647_3 : HolLoopProg 64 :=
.mark loopBody647_2

def loopBody647_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 2)

def loopBody647_5 : HolLoopProg 64 :=
.mark loopBody647_4

def loopBody647_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 3)

def loopBody647_7 : HolLoopProg 64 :=
.mark loopBody647_6

def loopBody647_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 4)

def loopBody647_9 : HolLoopProg 64 :=
.mark loopBody647_8

def loopBody647_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 5)

def loopBody647_11 : HolLoopProg 64 :=
.mark loopBody647_10

def loopBody647_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 0)

def loopBody647_13 : HolLoopProg 64 :=
.mark loopBody647_12

def loopBody647_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 1)

def loopBody647_15 : HolLoopProg 64 :=
.mark loopBody647_14

def loopBody647_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 2)

def loopBody647_17 : HolLoopProg 64 :=
.mark loopBody647_16

def loopBody647_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 3)

def loopBody647_19 : HolLoopProg 64 :=
.mark loopBody647_18

def loopBody647_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 4)

def loopBody647_21 : HolLoopProg 64 :=
.mark loopBody647_20

def loopBody647_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 5)

def loopBody647_23 : HolLoopProg 64 :=
.mark loopBody647_22

def loopBody647_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 710) [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] none

def loopBody647_25 : HolLoopProg 64 :=
.mark loopBody647_24

def loopBody647_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody647_27 : HolLoopProg 64 :=
.mark loopBody647_26

def loopBody647_28 : HolLoopProg 64 :=
.seq loopBody647_25 loopBody647_27

def loopBody647_29 : HolLoopProg 64 :=
.mark loopBody647_28

def loopBody647_30 : HolLoopProg 64 :=
.seq loopBody647_23 loopBody647_29

def loopBody647_31 : HolLoopProg 64 :=
.mark loopBody647_30

def loopBody647_32 : HolLoopProg 64 :=
.seq loopBody647_21 loopBody647_31

def loopBody647_33 : HolLoopProg 64 :=
.mark loopBody647_32

def loopBody647_34 : HolLoopProg 64 :=
.seq loopBody647_19 loopBody647_33

def loopBody647_35 : HolLoopProg 64 :=
.mark loopBody647_34

def loopBody647_36 : HolLoopProg 64 :=
.seq loopBody647_17 loopBody647_35

def loopBody647_37 : HolLoopProg 64 :=
.mark loopBody647_36

def loopBody647_38 : HolLoopProg 64 :=
.seq loopBody647_15 loopBody647_37

def loopBody647_39 : HolLoopProg 64 :=
.mark loopBody647_38

def loopBody647_40 : HolLoopProg 64 :=
.seq loopBody647_13 loopBody647_39

def loopBody647_41 : HolLoopProg 64 :=
.mark loopBody647_40

def loopBody647_42 : HolLoopProg 64 :=
.seq loopBody647_11 loopBody647_41

def loopBody647_43 : HolLoopProg 64 :=
.mark loopBody647_42

def loopBody647_44 : HolLoopProg 64 :=
.seq loopBody647_9 loopBody647_43

def loopBody647_45 : HolLoopProg 64 :=
.mark loopBody647_44

def loopBody647_46 : HolLoopProg 64 :=
.seq loopBody647_7 loopBody647_45

def loopBody647_47 : HolLoopProg 64 :=
.mark loopBody647_46

def loopBody647_48 : HolLoopProg 64 :=
.seq loopBody647_5 loopBody647_47

def loopBody647_49 : HolLoopProg 64 :=
.mark loopBody647_48

def loopBody647_50 : HolLoopProg 64 :=
.seq loopBody647_3 loopBody647_49

def loopBody647_51 : HolLoopProg 64 :=
.mark loopBody647_50

def loopBody647_52 : HolLoopProg 64 :=
.seq loopBody647_1 loopBody647_51

def loopBody647_53 : HolLoopProg 64 :=
.mark loopBody647_52

def output647 : Nat × List Nat × HolLoopProg 64 :=
  (711, [0, 1, 2, 3, 4, 5], loopBody647_53)
end InitECandidate.Proofs.FrontendStages.Loop
