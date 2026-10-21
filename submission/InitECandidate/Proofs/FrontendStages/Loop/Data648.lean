import InitECandidate.Proofs.FrontendStages.Loop.Translate632
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody648_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody648_1 : HolLoopProg 64 :=
.mark loopBody648_0

def loopBody648_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody648_3 : HolLoopProg 64 :=
.mark loopBody648_2

def loopBody648_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 2)

def loopBody648_5 : HolLoopProg 64 :=
.mark loopBody648_4

def loopBody648_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 3)

def loopBody648_7 : HolLoopProg 64 :=
.mark loopBody648_6

def loopBody648_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 4)

def loopBody648_9 : HolLoopProg 64 :=
.mark loopBody648_8

def loopBody648_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 5)

def loopBody648_11 : HolLoopProg 64 :=
.mark loopBody648_10

def loopBody648_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 17644856173732828998#64)

def loopBody648_13 : HolLoopProg 64 :=
.mark loopBody648_12

def loopBody648_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 754043588434789617#64)

def loopBody648_15 : HolLoopProg 64 :=
.mark loopBody648_14

def loopBody648_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 10224657059481499349#64)

def loopBody648_17 : HolLoopProg 64 :=
.mark loopBody648_16

def loopBody648_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 7488229067341005760#64)

def loopBody648_19 : HolLoopProg 64 :=
.mark loopBody648_18

def loopBody648_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.const 11130996698012816685#64)

def loopBody648_21 : HolLoopProg 64 :=
.mark loopBody648_20

def loopBody648_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.const 1267921511277847466#64)

def loopBody648_23 : HolLoopProg 64 :=
.mark loopBody648_22

def loopBody648_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 710) [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] none

def loopBody648_25 : HolLoopProg 64 :=
.mark loopBody648_24

def loopBody648_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody648_27 : HolLoopProg 64 :=
.mark loopBody648_26

def loopBody648_28 : HolLoopProg 64 :=
.seq loopBody648_25 loopBody648_27

def loopBody648_29 : HolLoopProg 64 :=
.mark loopBody648_28

def loopBody648_30 : HolLoopProg 64 :=
.seq loopBody648_23 loopBody648_29

def loopBody648_31 : HolLoopProg 64 :=
.mark loopBody648_30

def loopBody648_32 : HolLoopProg 64 :=
.seq loopBody648_21 loopBody648_31

def loopBody648_33 : HolLoopProg 64 :=
.mark loopBody648_32

def loopBody648_34 : HolLoopProg 64 :=
.seq loopBody648_19 loopBody648_33

def loopBody648_35 : HolLoopProg 64 :=
.mark loopBody648_34

def loopBody648_36 : HolLoopProg 64 :=
.seq loopBody648_17 loopBody648_35

def loopBody648_37 : HolLoopProg 64 :=
.mark loopBody648_36

def loopBody648_38 : HolLoopProg 64 :=
.seq loopBody648_15 loopBody648_37

def loopBody648_39 : HolLoopProg 64 :=
.mark loopBody648_38

def loopBody648_40 : HolLoopProg 64 :=
.seq loopBody648_13 loopBody648_39

def loopBody648_41 : HolLoopProg 64 :=
.mark loopBody648_40

def loopBody648_42 : HolLoopProg 64 :=
.seq loopBody648_11 loopBody648_41

def loopBody648_43 : HolLoopProg 64 :=
.mark loopBody648_42

def loopBody648_44 : HolLoopProg 64 :=
.seq loopBody648_9 loopBody648_43

def loopBody648_45 : HolLoopProg 64 :=
.mark loopBody648_44

def loopBody648_46 : HolLoopProg 64 :=
.seq loopBody648_7 loopBody648_45

def loopBody648_47 : HolLoopProg 64 :=
.mark loopBody648_46

def loopBody648_48 : HolLoopProg 64 :=
.seq loopBody648_5 loopBody648_47

def loopBody648_49 : HolLoopProg 64 :=
.mark loopBody648_48

def loopBody648_50 : HolLoopProg 64 :=
.seq loopBody648_3 loopBody648_49

def loopBody648_51 : HolLoopProg 64 :=
.mark loopBody648_50

def loopBody648_52 : HolLoopProg 64 :=
.seq loopBody648_1 loopBody648_51

def loopBody648_53 : HolLoopProg 64 :=
.mark loopBody648_52

def output648 : Nat × List Nat × HolLoopProg 64 :=
  (712, [0, 1, 2, 3, 4, 5], loopBody648_53)
end InitECandidate.Proofs.FrontendStages.Loop
