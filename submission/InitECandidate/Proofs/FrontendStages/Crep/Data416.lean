import InitECandidate.Proofs.FrontendStages.Crep.Translate400
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody416_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2])

def crepBody416_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody416_2 : CrepProg (BitVec 64) :=
.seq crepBody416_0 crepBody416_1

def crepBody416_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.var 3)

def crepBody416_4 : CrepProg (BitVec 64) :=
.seq crepBody416_3 crepBody416_1

def crepBody416_5 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 5)) crepBody416_4 crepBody416_1

def crepBody416_6 : CrepProg (BitVec 64) :=
.seq crepBody416_2 crepBody416_5

def crepBody416_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "memcpy"
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 2],
    Flapjack.CrepExp.var 5]

def crepBody416_8 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody416_7

def crepBody416_9 : CrepProg (BitVec 64) :=
.seq crepBody416_6 crepBody416_8

def crepBody416_10 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.var 1)) crepBody416_9 crepBody416_1

def crepBody416_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "memzero"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5],
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 5]]

def crepBody416_12 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody416_11

def crepBody416_13 : CrepProg (BitVec 64) :=
.seq crepBody416_10 crepBody416_12

def crepBody416_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody416_15 : CrepProg (BitVec 64) :=
.seq crepBody416_13 crepBody416_14

def crepBody416_16 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody416_15

def data416 : CrepProg (BitVec 64) := crepBody416_16
def output416 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [98#8, 117#8, 102#8, 102#8, 101#8, 114#8, 95#8, 114#8, 101#8, 97#8, 100#8], [0, 1, 2, 3, 4], crepProgToHOL data416)
end InitECandidate.Proofs.FrontendStages.Crep
