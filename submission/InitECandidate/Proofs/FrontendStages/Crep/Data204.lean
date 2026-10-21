import InitECandidate.Proofs.FrontendStages.Crep.Translate188
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody204_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3, 4, 5, 6], none)) "rlp_item"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 0,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 16#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 0,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 16#64],
          Flapjack.CrepExp.const 8#64])]

def crepBody204_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 7)

def crepBody204_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody204_3 : CrepProg (BitVec 64) :=
.seq crepBody204_1 crepBody204_2

def crepBody204_4 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 6#64) crepBody204_3

def crepBody204_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 3#64

def crepBody204_6 : CrepProg (BitVec 64) :=
.seq crepBody204_4 crepBody204_5

def crepBody204_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 0#64)) crepBody204_6 crepBody204_2

def crepBody204_8 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 7#64) crepBody204_3

def crepBody204_9 : CrepProg (BitVec 64) :=
.seq crepBody204_8 crepBody204_5

def crepBody204_10 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 2)) crepBody204_9 crepBody204_2

def crepBody204_11 : CrepProg (BitVec 64) :=
.seq crepBody204_7 crepBody204_10

def crepBody204_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 4]

def crepBody204_13 : CrepProg (BitVec 64) :=
.seq crepBody204_11 crepBody204_12

def crepBody204_14 : CrepProg (BitVec 64) :=
.seq crepBody204_0 crepBody204_13

def crepBody204_15 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody204_14

def crepBody204_16 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody204_15

def crepBody204_17 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody204_16

def crepBody204_18 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody204_17

def data204 : CrepProg (BitVec 64) := crepBody204_18
def output204 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [104#8, 100#8, 114#8, 95#8, 98#8, 121#8, 116#8, 101#8, 115#8, 95#8, 102#8, 105#8, 101#8, 108#8, 100#8], [0, 1, 2], crepProgToHOL data204)
end InitECandidate.Proofs.FrontendStages.Crep
