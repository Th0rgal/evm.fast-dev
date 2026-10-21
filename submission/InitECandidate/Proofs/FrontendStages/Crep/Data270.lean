import InitECandidate.Proofs.FrontendStages.Crep.Translate254
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody270_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2, 3, 4, 5], none)) "rlp_item"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 0,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 16#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 0,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 16#64],
          Flapjack.CrepExp.const 8#64])]

def crepBody270_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 6)

def crepBody270_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody270_3 : CrepProg (BitVec 64) :=
.seq crepBody270_1 crepBody270_2

def crepBody270_4 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 15#64) crepBody270_3

def crepBody270_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 6#64

def crepBody270_6 : CrepProg (BitVec 64) :=
.seq crepBody270_4 crepBody270_5

def crepBody270_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody270_6 crepBody270_2

def crepBody270_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody270_9 : CrepProg (BitVec 64) :=
.seq crepBody270_7 crepBody270_8

def crepBody270_10 : CrepProg (BitVec 64) :=
.seq crepBody270_0 crepBody270_9

def crepBody270_11 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody270_10

def crepBody270_12 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody270_11

def crepBody270_13 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody270_12

def crepBody270_14 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody270_13

def data270 : CrepProg (BitVec 64) := crepBody270_14
def output270 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [116#8, 120#8, 95#8, 98#8, 121#8, 116#8, 101#8, 115#8, 95#8, 105#8, 116#8, 101#8, 109#8], [0, 1], crepProgToHOL data270)
end InitECandidate.Proofs.FrontendStages.Crep
