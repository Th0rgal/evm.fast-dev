import InitECandidate.Proofs.FrontendStages.Crep.Translate189
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody205_0 : CrepProg (BitVec 64) :=
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

def crepBody205_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 6)

def crepBody205_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody205_3 : CrepProg (BitVec 64) :=
.seq crepBody205_1 crepBody205_2

def crepBody205_4 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 8#64) crepBody205_3

def crepBody205_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 3#64

def crepBody205_6 : CrepProg (BitVec 64) :=
.seq crepBody205_4 crepBody205_5

def crepBody205_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody205_6 crepBody205_2

def crepBody205_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody205_9 : CrepProg (BitVec 64) :=
.seq crepBody205_7 crepBody205_8

def crepBody205_10 : CrepProg (BitVec 64) :=
.seq crepBody205_0 crepBody205_9

def crepBody205_11 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody205_10

def crepBody205_12 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody205_11

def crepBody205_13 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody205_12

def crepBody205_14 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody205_13

def data205 : CrepProg (BitVec 64) := crepBody205_14
def output205 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [104#8, 100#8, 114#8, 95#8, 114#8, 97#8, 119#8, 95#8, 102#8, 105#8, 101#8, 108#8, 100#8], [0, 1], crepProgToHOL data205)
end InitECandidate.Proofs.FrontendStages.Crep
