import InitECandidate.Proofs.FrontendStages.Crep.Translate241
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody257_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.var 1,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 16#64])]

def crepBody257_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody257_2 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 0#64)) crepBody257_0 crepBody257_1

def crepBody257_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "mpt_fail" [Flapjack.CrepExp.const 2#64]

def crepBody257_4 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody257_3

def crepBody257_5 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody257_4 crepBody257_1

def crepBody257_6 : CrepProg (BitVec 64) :=
.seq crepBody257_2 crepBody257_5

def crepBody257_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "_node_rlp_fill" [Flapjack.CrepExp.var 0]

def crepBody257_8 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody257_7

def crepBody257_9 : CrepProg (BitVec 64) :=
.seq crepBody257_6 crepBody257_8

def crepBody257_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 16#64])]

def crepBody257_11 : CrepProg (BitVec 64) :=
.seq crepBody257_9 crepBody257_10

def crepBody257_12 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64])) crepBody257_11

def data257 : CrepProg (BitVec 64) := crepBody257_12
def output257 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [110#8, 111#8, 100#8, 101#8, 95#8, 114#8, 108#8, 112#8], [0], crepProgToHOL data257)
end InitECandidate.Proofs.FrontendStages.Crep
