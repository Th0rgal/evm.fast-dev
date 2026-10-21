import InitECandidate.Proofs.FrontendStages.Crep.Translate692
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody708_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "heap_mark" []

def crepBody708_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 96#64]

def crepBody708_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "g1_normalize" [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 0]

def crepBody708_3 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody708_2

def crepBody708_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "bls_fp_encode64" [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 1]

def crepBody708_5 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody708_4

def crepBody708_6 : CrepProg (BitVec 64) :=
.seq crepBody708_3 crepBody708_5

def crepBody708_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "bls_fp_encode64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 48#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 64#64]]

def crepBody708_8 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody708_7

def crepBody708_9 : CrepProg (BitVec 64) :=
.seq crepBody708_6 crepBody708_8

def crepBody708_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody708_11 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody708_10

def crepBody708_12 : CrepProg (BitVec 64) :=
.seq crepBody708_9 crepBody708_11

def crepBody708_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody708_14 : CrepProg (BitVec 64) :=
.seq crepBody708_12 crepBody708_13

def crepBody708_15 : CrepProg (BitVec 64) :=
.seq crepBody708_1 crepBody708_14

def crepBody708_16 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody708_15

def crepBody708_17 : CrepProg (BitVec 64) :=
.seq crepBody708_0 crepBody708_16

def crepBody708_18 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody708_17

def data708 : CrepProg (BitVec 64) := crepBody708_18
def output708 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [103#8, 49#8, 95#8, 101#8, 110#8, 99#8, 111#8, 100#8, 101#8], [0, 1], crepProgToHOL data708)
end InitECandidate.Proofs.FrontendStages.Crep
