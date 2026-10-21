import InitECandidate.Proofs.FrontendStages.Crep.Translate705
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody721_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "heap_mark" []

def crepBody721_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "alloc" [Flapjack.CrepExp.const 288#64]

def crepBody721_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "g2_mul"
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 0,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
        Flapjack.CrepExp.const 1344#64],
    Flapjack.CrepExp.const 4#64]

def crepBody721_3 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody721_2

def crepBody721_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "g2_is_inf" [Flapjack.CrepExp.var 2]

def crepBody721_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "heap_release" [Flapjack.CrepExp.var 1]

def crepBody721_6 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody721_5

def crepBody721_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 3]

def crepBody721_8 : CrepProg (BitVec 64) :=
.seq crepBody721_6 crepBody721_7

def crepBody721_9 : CrepProg (BitVec 64) :=
.seq crepBody721_4 crepBody721_8

def crepBody721_10 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody721_9

def crepBody721_11 : CrepProg (BitVec 64) :=
.seq crepBody721_3 crepBody721_10

def crepBody721_12 : CrepProg (BitVec 64) :=
.seq crepBody721_1 crepBody721_11

def crepBody721_13 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody721_12

def crepBody721_14 : CrepProg (BitVec 64) :=
.seq crepBody721_0 crepBody721_13

def crepBody721_15 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody721_14

def data721 : CrepProg (BitVec 64) := crepBody721_15
def output721 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [103#8, 50#8, 95#8, 115#8, 117#8, 98#8, 103#8, 114#8, 111#8, 117#8, 112#8, 95#8, 99#8, 104#8, 101#8, 99#8, 107#8], [0], crepProgToHOL data721)
end InitECandidate.Proofs.FrontendStages.Crep
