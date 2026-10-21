import InitECandidate.Proofs.FrontendStages.Crep.Translate749
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody765_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "words_of" [Flapjack.CrepExp.var 2]

def crepBody765_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "charge_gas"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.const 600#64,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 120#64, Flapjack.CrepExp.var 3]]]

def crepBody765_2 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody765_1

def crepBody765_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody765_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "memzero" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 12#64]

def crepBody765_5 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody765_4

def crepBody765_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "ripemd160"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 88#64]),
    Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 12#64]]

def crepBody765_7 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody765_6

def crepBody765_8 : CrepProg (BitVec 64) :=
.seq crepBody765_5 crepBody765_7

def crepBody765_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 6)

def crepBody765_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody765_11 : CrepProg (BitVec 64) :=
.seq crepBody765_9 crepBody765_10

def crepBody765_12 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 4) crepBody765_11

def crepBody765_13 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 120#64]) crepBody765_12

def crepBody765_14 : CrepProg (BitVec 64) :=
.seq crepBody765_8 crepBody765_13

def crepBody765_15 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 32#64) crepBody765_11

def crepBody765_16 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 128#64]) crepBody765_15

def crepBody765_17 : CrepProg (BitVec 64) :=
.seq crepBody765_14 crepBody765_16

def crepBody765_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody765_19 : CrepProg (BitVec 64) :=
.seq crepBody765_17 crepBody765_18

def crepBody765_20 : CrepProg (BitVec 64) :=
.seq crepBody765_3 crepBody765_19

def crepBody765_21 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody765_20

def crepBody765_22 : CrepProg (BitVec 64) :=
.seq crepBody765_2 crepBody765_21

def crepBody765_23 : CrepProg (BitVec 64) :=
.seq crepBody765_0 crepBody765_22

def crepBody765_24 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody765_23

def crepBody765_25 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64])) crepBody765_24

def crepBody765_26 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 112#64])) crepBody765_25

def data765 : CrepProg (BitVec 64) := crepBody765_26
def output765 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 114#8, 101#8, 95#8, 114#8, 105#8, 112#8, 101#8, 109#8, 100#8, 49#8, 54#8, 48#8], [], crepProgToHOL data765)
end InitECandidate.Proofs.FrontendStages.Crep
