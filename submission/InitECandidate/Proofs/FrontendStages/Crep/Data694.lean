import InitECandidate.Proofs.FrontendStages.Crep.Translate678
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody694_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "fp2_conj" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody694_1 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody694_0

def crepBody694_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "fp2_conj"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64]]

def crepBody694_3 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody694_2

def crepBody694_4 : CrepProg (BitVec 64) :=
.seq crepBody694_1 crepBody694_3

def crepBody694_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "fp2_mul"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
        Flapjack.CrepExp.const 960#64]]

def crepBody694_6 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody694_5

def crepBody694_7 : CrepProg (BitVec 64) :=
.seq crepBody694_4 crepBody694_6

def crepBody694_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "fp2_conj"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 192#64]]

def crepBody694_9 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody694_8

def crepBody694_10 : CrepProg (BitVec 64) :=
.seq crepBody694_7 crepBody694_9

def crepBody694_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "fp2_mul"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
        Flapjack.CrepExp.const 1152#64]]

def crepBody694_12 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody694_11

def crepBody694_13 : CrepProg (BitVec 64) :=
.seq crepBody694_10 crepBody694_12

def crepBody694_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "fp2_conj"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 288#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 288#64]]

def crepBody694_15 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody694_14

def crepBody694_16 : CrepProg (BitVec 64) :=
.seq crepBody694_13 crepBody694_15

def crepBody694_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "fp2_mul"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 288#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 288#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
        Flapjack.CrepExp.const 864#64]]

def crepBody694_18 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody694_17

def crepBody694_19 : CrepProg (BitVec 64) :=
.seq crepBody694_16 crepBody694_18

def crepBody694_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "fp2_conj"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 384#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 384#64]]

def crepBody694_21 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody694_20

def crepBody694_22 : CrepProg (BitVec 64) :=
.seq crepBody694_19 crepBody694_21

def crepBody694_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "fp2_mul"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 384#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 384#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
        Flapjack.CrepExp.const 1056#64]]

def crepBody694_24 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody694_23

def crepBody694_25 : CrepProg (BitVec 64) :=
.seq crepBody694_22 crepBody694_24

def crepBody694_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "fp2_conj"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 480#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 480#64]]

def crepBody694_27 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody694_26

def crepBody694_28 : CrepProg (BitVec 64) :=
.seq crepBody694_25 crepBody694_27

def crepBody694_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "fp2_mul"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 480#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 480#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
        Flapjack.CrepExp.const 1248#64]]

def crepBody694_30 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody694_29

def crepBody694_31 : CrepProg (BitVec 64) :=
.seq crepBody694_28 crepBody694_30

def crepBody694_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody694_33 : CrepProg (BitVec 64) :=
.seq crepBody694_31 crepBody694_32

def data694 : CrepProg (BitVec 64) := crepBody694_33
def output694 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 112#8, 49#8, 50#8, 95#8, 102#8, 114#8, 111#8, 98#8], [0, 1], crepProgToHOL data694)
end InitECandidate.Proofs.FrontendStages.Crep
