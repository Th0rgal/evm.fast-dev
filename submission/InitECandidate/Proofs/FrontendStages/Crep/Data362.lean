import InitECandidate.Proofs.FrontendStages.Crep.Translate346
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody362_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "get_account" [Flapjack.CrepExp.var 0]

def crepBody362_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "acct_copy" [Flapjack.CrepExp.var 1]

def crepBody362_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.var 3)

def crepBody362_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody362_4 : CrepProg (BitVec 64) :=
.seq crepBody362_2 crepBody362_3

def crepBody362_5 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 0#64]),
    Flapjack.CrepExp.const 1#64]) crepBody362_4

def crepBody362_6 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 0#64]) crepBody362_5

def crepBody362_7 : CrepProg (BitVec 64) :=
.seq crepBody362_1 crepBody362_6

def crepBody362_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "modify_state_commit" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody362_9 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody362_8

def crepBody362_10 : CrepProg (BitVec 64) :=
.seq crepBody362_7 crepBody362_9

def crepBody362_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody362_12 : CrepProg (BitVec 64) :=
.seq crepBody362_10 crepBody362_11

def crepBody362_13 : CrepProg (BitVec 64) :=
.seq crepBody362_0 crepBody362_12

def crepBody362_14 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody362_13

def data362 : CrepProg (BitVec 64) := crepBody362_14
def output362 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [105#8, 110#8, 99#8, 114#8, 101#8, 109#8, 101#8, 110#8, 116#8, 95#8, 110#8, 111#8, 110#8, 99#8, 101#8], [0], crepProgToHOL data362)
end InitECandidate.Proofs.FrontendStages.Crep
