import InitECandidate.Proofs.FrontendStages.Crep.Translate178
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody194_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "heap_mark" []

def crepBody194_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 3#64, Flapjack.CrepExp.const 32#64]]

def crepBody194_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "htr_bytes_vector"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 20#64, Flapjack.CrepExp.var 3]

def crepBody194_3 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody194_2

def crepBody194_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "htr_bytes_vector"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 20#64],
    Flapjack.CrepExp.const 48#64,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 32#64]]

def crepBody194_5 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody194_4

def crepBody194_6 : CrepProg (BitVec 64) :=
.seq crepBody194_3 crepBody194_5

def crepBody194_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "htr_bytes_vector"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 68#64],
    Flapjack.CrepExp.const 48#64,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 64#64]]

def crepBody194_8 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody194_7

def crepBody194_9 : CrepProg (BitVec 64) :=
.seq crepBody194_6 crepBody194_8

def crepBody194_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "merkleize"
  [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 3#64, Flapjack.CrepExp.const 3#64, Flapjack.CrepExp.var 1]

def crepBody194_11 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody194_10

def crepBody194_12 : CrepProg (BitVec 64) :=
.seq crepBody194_9 crepBody194_11

def crepBody194_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody194_14 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody194_13

def crepBody194_15 : CrepProg (BitVec 64) :=
.seq crepBody194_12 crepBody194_14

def crepBody194_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody194_17 : CrepProg (BitVec 64) :=
.seq crepBody194_15 crepBody194_16

def crepBody194_18 : CrepProg (BitVec 64) :=
.seq crepBody194_1 crepBody194_17

def crepBody194_19 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody194_18

def crepBody194_20 : CrepProg (BitVec 64) :=
.seq crepBody194_0 crepBody194_19

def crepBody194_21 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody194_20

def data194 : CrepProg (BitVec 64) := crepBody194_21
def output194 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [104#8, 116#8, 114#8, 95#8, 99#8, 111#8, 110#8, 115#8], [0, 1], crepProgToHOL data194)
end InitECandidate.Proofs.FrontendStages.Crep
