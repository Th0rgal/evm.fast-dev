import InitECandidate.Proofs.FrontendStages.Crep.Translate180
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody196_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "heap_mark" []

def crepBody196_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.const 32#64]]

def crepBody196_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "htr_bytes_vector"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 20#64, Flapjack.CrepExp.var 3]

def crepBody196_3 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody196_2

def crepBody196_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "htr_bytes_vector"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 20#64],
    Flapjack.CrepExp.const 48#64,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 32#64]]

def crepBody196_5 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody196_4

def crepBody196_6 : CrepProg (BitVec 64) :=
.seq crepBody196_3 crepBody196_5

def crepBody196_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "merkleize"
  [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 1]

def crepBody196_8 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody196_7

def crepBody196_9 : CrepProg (BitVec 64) :=
.seq crepBody196_6 crepBody196_8

def crepBody196_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody196_11 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody196_10

def crepBody196_12 : CrepProg (BitVec 64) :=
.seq crepBody196_9 crepBody196_11

def crepBody196_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody196_14 : CrepProg (BitVec 64) :=
.seq crepBody196_12 crepBody196_13

def crepBody196_15 : CrepProg (BitVec 64) :=
.seq crepBody196_1 crepBody196_14

def crepBody196_16 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody196_15

def crepBody196_17 : CrepProg (BitVec 64) :=
.seq crepBody196_0 crepBody196_16

def crepBody196_18 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody196_17

def data196 : CrepProg (BitVec 64) := crepBody196_18
def output196 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [104#8, 116#8, 114#8, 95#8, 98#8, 101#8, 120#8, 105#8, 116#8], [0, 1], crepProgToHOL data196)
end InitECandidate.Proofs.FrontendStages.Crep
