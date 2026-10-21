import InitECandidate.Proofs.FrontendStages.Loop.Translate629
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody645_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody645_1 : HolLoopProg 64 :=
.mark loopBody645_0

def loopBody645_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody645_3 : HolLoopProg 64 :=
.mark loopBody645_2

def loopBody645_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 2)

def loopBody645_5 : HolLoopProg 64 :=
.mark loopBody645_4

def loopBody645_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 3)

def loopBody645_7 : HolLoopProg 64 :=
.mark loopBody645_6

def loopBody645_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 4)

def loopBody645_9 : HolLoopProg 64 :=
.mark loopBody645_8

def loopBody645_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 5)

def loopBody645_11 : HolLoopProg 64 :=
.mark loopBody645_10

def loopBody645_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 0)

def loopBody645_13 : HolLoopProg 64 :=
.mark loopBody645_12

def loopBody645_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 1)

def loopBody645_15 : HolLoopProg 64 :=
.mark loopBody645_14

def loopBody645_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 2)

def loopBody645_17 : HolLoopProg 64 :=
.mark loopBody645_16

def loopBody645_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 3)

def loopBody645_19 : HolLoopProg 64 :=
.mark loopBody645_18

def loopBody645_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 4)

def loopBody645_21 : HolLoopProg 64 :=
.mark loopBody645_20

def loopBody645_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 5)

def loopBody645_23 : HolLoopProg 64 :=
.mark loopBody645_22

def loopBody645_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 706) [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] none

def loopBody645_25 : HolLoopProg 64 :=
.mark loopBody645_24

def loopBody645_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody645_27 : HolLoopProg 64 :=
.mark loopBody645_26

def loopBody645_28 : HolLoopProg 64 :=
.seq loopBody645_25 loopBody645_27

def loopBody645_29 : HolLoopProg 64 :=
.mark loopBody645_28

def loopBody645_30 : HolLoopProg 64 :=
.seq loopBody645_23 loopBody645_29

def loopBody645_31 : HolLoopProg 64 :=
.mark loopBody645_30

def loopBody645_32 : HolLoopProg 64 :=
.seq loopBody645_21 loopBody645_31

def loopBody645_33 : HolLoopProg 64 :=
.mark loopBody645_32

def loopBody645_34 : HolLoopProg 64 :=
.seq loopBody645_19 loopBody645_33

def loopBody645_35 : HolLoopProg 64 :=
.mark loopBody645_34

def loopBody645_36 : HolLoopProg 64 :=
.seq loopBody645_17 loopBody645_35

def loopBody645_37 : HolLoopProg 64 :=
.mark loopBody645_36

def loopBody645_38 : HolLoopProg 64 :=
.seq loopBody645_15 loopBody645_37

def loopBody645_39 : HolLoopProg 64 :=
.mark loopBody645_38

def loopBody645_40 : HolLoopProg 64 :=
.seq loopBody645_13 loopBody645_39

def loopBody645_41 : HolLoopProg 64 :=
.mark loopBody645_40

def loopBody645_42 : HolLoopProg 64 :=
.seq loopBody645_11 loopBody645_41

def loopBody645_43 : HolLoopProg 64 :=
.mark loopBody645_42

def loopBody645_44 : HolLoopProg 64 :=
.seq loopBody645_9 loopBody645_43

def loopBody645_45 : HolLoopProg 64 :=
.mark loopBody645_44

def loopBody645_46 : HolLoopProg 64 :=
.seq loopBody645_7 loopBody645_45

def loopBody645_47 : HolLoopProg 64 :=
.mark loopBody645_46

def loopBody645_48 : HolLoopProg 64 :=
.seq loopBody645_5 loopBody645_47

def loopBody645_49 : HolLoopProg 64 :=
.mark loopBody645_48

def loopBody645_50 : HolLoopProg 64 :=
.seq loopBody645_3 loopBody645_49

def loopBody645_51 : HolLoopProg 64 :=
.mark loopBody645_50

def loopBody645_52 : HolLoopProg 64 :=
.seq loopBody645_1 loopBody645_51

def loopBody645_53 : HolLoopProg 64 :=
.mark loopBody645_52

def output645 : Nat × List Nat × HolLoopProg 64 :=
  (709, [0, 1, 2, 3, 4, 5], loopBody645_53)
end InitECandidate.Proofs.FrontendStages.Loop
