import InitECandidate.Proofs.FrontendStages.Crep.Translate179
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody195_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "heap_mark" []

def crepBody195_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.const 32#64]]

def crepBody195_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "htr_bytes_vector"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64, Flapjack.CrepExp.var 3]

def crepBody195_3 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody195_2

def crepBody195_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 32#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64],
    Flapjack.CrepExp.const 32#64]

def crepBody195_5 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody195_4

def crepBody195_6 : CrepProg (BitVec 64) :=
.seq crepBody195_3 crepBody195_5

def crepBody195_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "htr_u64_at"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 80#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 64#64]]

def crepBody195_8 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody195_7

def crepBody195_9 : CrepProg (BitVec 64) :=
.seq crepBody195_6 crepBody195_8

def crepBody195_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "htr_bytes_vector"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 88#64],
    Flapjack.CrepExp.const 96#64,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 96#64]]

def crepBody195_11 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody195_10

def crepBody195_12 : CrepProg (BitVec 64) :=
.seq crepBody195_9 crepBody195_11

def crepBody195_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "merkleize"
  [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.var 1]

def crepBody195_14 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody195_13

def crepBody195_15 : CrepProg (BitVec 64) :=
.seq crepBody195_12 crepBody195_14

def crepBody195_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody195_17 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody195_16

def crepBody195_18 : CrepProg (BitVec 64) :=
.seq crepBody195_15 crepBody195_17

def crepBody195_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody195_20 : CrepProg (BitVec 64) :=
.seq crepBody195_18 crepBody195_19

def crepBody195_21 : CrepProg (BitVec 64) :=
.seq crepBody195_1 crepBody195_20

def crepBody195_22 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody195_21

def crepBody195_23 : CrepProg (BitVec 64) :=
.seq crepBody195_0 crepBody195_22

def crepBody195_24 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody195_23

def data195 : CrepProg (BitVec 64) := crepBody195_24
def output195 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [104#8, 116#8, 114#8, 95#8, 98#8, 100#8, 101#8, 112#8], [0, 1], crepProgToHOL data195)
end InitECandidate.Proofs.FrontendStages.Crep
