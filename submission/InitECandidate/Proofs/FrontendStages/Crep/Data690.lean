import InitECandidate.Proofs.FrontendStages.Crep.Translate674
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody690_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "heap_mark" []

def crepBody690_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 288#64, Flapjack.CrepExp.const 5#64]]

def crepBody690_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp6_mul"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2]

def crepBody690_3 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody690_2

def crepBody690_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp6_mul"
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 288#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 288#64]]

def crepBody690_5 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody690_4

def crepBody690_6 : CrepProg (BitVec 64) :=
.seq crepBody690_3 crepBody690_5

def crepBody690_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp6_add"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 1,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 288#64]]

def crepBody690_8 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody690_7

def crepBody690_9 : CrepProg (BitVec 64) :=
.seq crepBody690_6 crepBody690_8

def crepBody690_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp6_add"
  [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 288#64]]

def crepBody690_11 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody690_10

def crepBody690_12 : CrepProg (BitVec 64) :=
.seq crepBody690_9 crepBody690_11

def crepBody690_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp6_mul"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9]

def crepBody690_14 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody690_13

def crepBody690_15 : CrepProg (BitVec 64) :=
.seq crepBody690_12 crepBody690_14

def crepBody690_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp6_sub"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 5]

def crepBody690_17 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody690_16

def crepBody690_18 : CrepProg (BitVec 64) :=
.seq crepBody690_15 crepBody690_17

def crepBody690_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp6_sub"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 288#64],
    Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 6]

def crepBody690_20 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody690_19

def crepBody690_21 : CrepProg (BitVec 64) :=
.seq crepBody690_18 crepBody690_20

def crepBody690_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp6_mul_v" [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 6]

def crepBody690_23 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody690_22

def crepBody690_24 : CrepProg (BitVec 64) :=
.seq crepBody690_21 crepBody690_23

def crepBody690_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp6_add"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6]

def crepBody690_26 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody690_25

def crepBody690_27 : CrepProg (BitVec 64) :=
.seq crepBody690_24 crepBody690_26

def crepBody690_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "heap_release" [Flapjack.CrepExp.var 3]

def crepBody690_29 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody690_28

def crepBody690_30 : CrepProg (BitVec 64) :=
.seq crepBody690_27 crepBody690_29

def crepBody690_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody690_32 : CrepProg (BitVec 64) :=
.seq crepBody690_30 crepBody690_31

def crepBody690_33 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 1152#64]) crepBody690_32

def crepBody690_34 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 864#64]) crepBody690_33

def crepBody690_35 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 576#64]) crepBody690_34

def crepBody690_36 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 288#64]) crepBody690_35

def crepBody690_37 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.var 4) crepBody690_36

def crepBody690_38 : CrepProg (BitVec 64) :=
.seq crepBody690_1 crepBody690_37

def crepBody690_39 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody690_38

def crepBody690_40 : CrepProg (BitVec 64) :=
.seq crepBody690_0 crepBody690_39

def crepBody690_41 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody690_40

def data690 : CrepProg (BitVec 64) := crepBody690_41
def output690 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 112#8, 49#8, 50#8, 95#8, 109#8, 117#8, 108#8], [0, 1, 2], crepProgToHOL data690)
end InitECandidate.Proofs.FrontendStages.Crep
