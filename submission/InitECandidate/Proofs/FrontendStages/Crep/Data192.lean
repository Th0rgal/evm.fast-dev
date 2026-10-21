import InitECandidate.Proofs.FrontendStages.Crep.Translate176
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody192_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "heap_mark" []

def crepBody192_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 5#64, Flapjack.CrepExp.const 32#64]]

def crepBody192_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "htr_bytes_vector"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64, Flapjack.CrepExp.var 3]

def crepBody192_3 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody192_2

def crepBody192_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 32#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64],
    Flapjack.CrepExp.const 32#64]

def crepBody192_5 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody192_4

def crepBody192_6 : CrepProg (BitVec 64) :=
.seq crepBody192_3 crepBody192_5

def crepBody192_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "htr_u64_at"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 80#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 64#64]]

def crepBody192_8 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody192_7

def crepBody192_9 : CrepProg (BitVec 64) :=
.seq crepBody192_6 crepBody192_8

def crepBody192_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "htr_bytes_vector"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 88#64],
    Flapjack.CrepExp.const 96#64,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 96#64]]

def crepBody192_11 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody192_10

def crepBody192_12 : CrepProg (BitVec 64) :=
.seq crepBody192_9 crepBody192_11

def crepBody192_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "htr_u64_at"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 184#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 128#64]]

def crepBody192_14 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody192_13

def crepBody192_15 : CrepProg (BitVec 64) :=
.seq crepBody192_12 crepBody192_14

def crepBody192_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "merkleize"
  [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 5#64, Flapjack.CrepExp.const 5#64, Flapjack.CrepExp.var 1]

def crepBody192_17 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody192_16

def crepBody192_18 : CrepProg (BitVec 64) :=
.seq crepBody192_15 crepBody192_17

def crepBody192_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody192_20 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody192_19

def crepBody192_21 : CrepProg (BitVec 64) :=
.seq crepBody192_18 crepBody192_20

def crepBody192_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody192_23 : CrepProg (BitVec 64) :=
.seq crepBody192_21 crepBody192_22

def crepBody192_24 : CrepProg (BitVec 64) :=
.seq crepBody192_1 crepBody192_23

def crepBody192_25 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody192_24

def crepBody192_26 : CrepProg (BitVec 64) :=
.seq crepBody192_0 crepBody192_25

def crepBody192_27 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody192_26

def data192 : CrepProg (BitVec 64) := crepBody192_27
def output192 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [104#8, 116#8, 114#8, 95#8, 100#8, 101#8, 112#8, 111#8, 115#8, 105#8, 116#8], [0, 1], crepProgToHOL data192)
end InitECandidate.Proofs.FrontendStages.Crep
