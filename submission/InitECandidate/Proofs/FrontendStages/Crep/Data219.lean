import InitECandidate.Proofs.FrontendStages.Crep.Translate203
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody219_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody219_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.var 3)

def crepBody219_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody219_3 : CrepProg (BitVec 64) :=
.seq crepBody219_1 crepBody219_2

def crepBody219_4 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.var 1) crepBody219_3

def crepBody219_5 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 128#64]) crepBody219_4

def crepBody219_6 : CrepProg (BitVec 64) :=
.seq crepBody219_0 crepBody219_5

def crepBody219_7 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody219_6

def crepBody219_8 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 136#64]) crepBody219_4

def crepBody219_9 : CrepProg (BitVec 64) :=
.seq crepBody219_0 crepBody219_8

def crepBody219_10 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody219_9

def crepBody219_11 : CrepProg (BitVec 64) :=
.seq crepBody219_7 crepBody219_10

def crepBody219_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "alloc" [Flapjack.CrepExp.const 64#64]

def crepBody219_13 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 144#64]) crepBody219_4

def crepBody219_14 : CrepProg (BitVec 64) :=
.seq crepBody219_12 crepBody219_13

def crepBody219_15 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody219_14

def crepBody219_16 : CrepProg (BitVec 64) :=
.seq crepBody219_11 crepBody219_15

def crepBody219_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "alloc" [Flapjack.CrepExp.const 40#64]

def crepBody219_18 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 152#64]) crepBody219_4

def crepBody219_19 : CrepProg (BitVec 64) :=
.seq crepBody219_17 crepBody219_18

def crepBody219_20 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody219_19

def crepBody219_21 : CrepProg (BitVec 64) :=
.seq crepBody219_16 crepBody219_20

def crepBody219_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "alloc" [Flapjack.CrepExp.const 16#64]

def crepBody219_23 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 160#64]) crepBody219_4

def crepBody219_24 : CrepProg (BitVec 64) :=
.seq crepBody219_22 crepBody219_23

def crepBody219_25 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody219_24

def crepBody219_26 : CrepProg (BitVec 64) :=
.seq crepBody219_21 crepBody219_25

def crepBody219_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 152#64]))
  (Flapjack.CrepExp.const 128#64)

def crepBody219_28 : CrepProg (BitVec 64) :=
.seq crepBody219_26 crepBody219_27

def crepBody219_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "keccak256"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 152#64]),
    Flapjack.CrepExp.const 1#64,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 128#64])]

def crepBody219_30 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody219_29

def crepBody219_31 : CrepProg (BitVec 64) :=
.seq crepBody219_28 crepBody219_30

def crepBody219_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "keccak256"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 152#64]),
    Flapjack.CrepExp.const 0#64,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 136#64])]

def crepBody219_33 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody219_32

def crepBody219_34 : CrepProg (BitVec 64) :=
.seq crepBody219_31 crepBody219_33

def crepBody219_35 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody219_36 : CrepProg (BitVec 64) :=
.seq crepBody219_34 crepBody219_35

def data219 : CrepProg (BitVec 64) := crepBody219_36
def output219 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [109#8, 112#8, 116#8, 95#8, 105#8, 110#8, 105#8, 116#8], [], crepProgToHOL data219)
end InitECandidate.Proofs.FrontendStages.Crep
