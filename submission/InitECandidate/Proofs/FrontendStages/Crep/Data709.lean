import InitECandidate.Proofs.FrontendStages.Crep.Translate693
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody709_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "heap_mark" []

def crepBody709_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "alloc" [Flapjack.CrepExp.const 144#64]

def crepBody709_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "g1_mul"
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 0,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
        Flapjack.CrepExp.const 1344#64],
    Flapjack.CrepExp.const 4#64]

def crepBody709_3 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody709_2

def crepBody709_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "g1_is_inf" [Flapjack.CrepExp.var 2]

def crepBody709_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "heap_release" [Flapjack.CrepExp.var 1]

def crepBody709_6 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody709_5

def crepBody709_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 3]

def crepBody709_8 : CrepProg (BitVec 64) :=
.seq crepBody709_6 crepBody709_7

def crepBody709_9 : CrepProg (BitVec 64) :=
.seq crepBody709_4 crepBody709_8

def crepBody709_10 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody709_9

def crepBody709_11 : CrepProg (BitVec 64) :=
.seq crepBody709_3 crepBody709_10

def crepBody709_12 : CrepProg (BitVec 64) :=
.seq crepBody709_1 crepBody709_11

def crepBody709_13 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody709_12

def crepBody709_14 : CrepProg (BitVec 64) :=
.seq crepBody709_0 crepBody709_13

def crepBody709_15 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody709_14

def data709 : CrepProg (BitVec 64) := crepBody709_15
def output709 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [103#8, 49#8, 95#8, 115#8, 117#8, 98#8, 103#8, 114#8, 111#8, 117#8, 112#8, 95#8, 99#8, 104#8, 101#8, 99#8, 107#8], [0], crepProgToHOL data709)
end InitECandidate.Proofs.FrontendStages.Crep
