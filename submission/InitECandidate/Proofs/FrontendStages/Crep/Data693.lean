import InitECandidate.Proofs.FrontendStages.Crep.Translate677
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody693_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "heap_mark" []

def crepBody693_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 288#64, Flapjack.CrepExp.const 3#64]]

def crepBody693_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "fp6_mul"
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 1]

def crepBody693_3 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody693_2

def crepBody693_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "fp6_mul"
  [Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 288#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 288#64]]

def crepBody693_5 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody693_4

def crepBody693_6 : CrepProg (BitVec 64) :=
.seq crepBody693_3 crepBody693_5

def crepBody693_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "fp6_mul_v" [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 5]

def crepBody693_8 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody693_7

def crepBody693_9 : CrepProg (BitVec 64) :=
.seq crepBody693_6 crepBody693_8

def crepBody693_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "fp6_sub"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody693_11 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody693_10

def crepBody693_12 : CrepProg (BitVec 64) :=
.seq crepBody693_9 crepBody693_11

def crepBody693_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "fp6_inv" [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 6]

def crepBody693_14 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody693_13

def crepBody693_15 : CrepProg (BitVec 64) :=
.seq crepBody693_12 crepBody693_14

def crepBody693_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "fp6_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 6]

def crepBody693_17 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody693_16

def crepBody693_18 : CrepProg (BitVec 64) :=
.seq crepBody693_15 crepBody693_17

def crepBody693_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "fp6_mul"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 288#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 288#64],
    Flapjack.CrepExp.var 6]

def crepBody693_20 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody693_19

def crepBody693_21 : CrepProg (BitVec 64) :=
.seq crepBody693_18 crepBody693_20

def crepBody693_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "fp6_neg"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 288#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 288#64]]

def crepBody693_23 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody693_22

def crepBody693_24 : CrepProg (BitVec 64) :=
.seq crepBody693_21 crepBody693_23

def crepBody693_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody693_26 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody693_25

def crepBody693_27 : CrepProg (BitVec 64) :=
.seq crepBody693_24 crepBody693_26

def crepBody693_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody693_29 : CrepProg (BitVec 64) :=
.seq crepBody693_27 crepBody693_28

def crepBody693_30 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 576#64]) crepBody693_29

def crepBody693_31 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 288#64]) crepBody693_30

def crepBody693_32 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.var 3) crepBody693_31

def crepBody693_33 : CrepProg (BitVec 64) :=
.seq crepBody693_1 crepBody693_32

def crepBody693_34 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody693_33

def crepBody693_35 : CrepProg (BitVec 64) :=
.seq crepBody693_0 crepBody693_34

def crepBody693_36 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody693_35

def data693 : CrepProg (BitVec 64) := crepBody693_36
def output693 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 112#8, 49#8, 50#8, 95#8, 105#8, 110#8, 118#8], [0, 1], crepProgToHOL data693)
end InitECandidate.Proofs.FrontendStages.Crep
