import InitECandidate.Proofs.FrontendStages.Crep.Translate363
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody379_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2], none)) "htab_get"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]),
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.var 0]

def crepBody379_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 2]

def crepBody379_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody379_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 0#64)) crepBody379_1 crepBody379_2

def crepBody379_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "record_pre_state_read" [Flapjack.CrepExp.var 0]

def crepBody379_5 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody379_4

def crepBody379_6 : CrepProg (BitVec 64) :=
.seq crepBody379_3 crepBody379_5

def crepBody379_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "ws_get_account_optional" [Flapjack.CrepExp.var 0]

def crepBody379_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 3]

def crepBody379_9 : CrepProg (BitVec 64) :=
.seq crepBody379_7 crepBody379_8

def crepBody379_10 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody379_9

def crepBody379_11 : CrepProg (BitVec 64) :=
.seq crepBody379_6 crepBody379_10

def crepBody379_12 : CrepProg (BitVec 64) :=
.seq crepBody379_0 crepBody379_11

def crepBody379_13 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody379_12

def crepBody379_14 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody379_13

def data379 : CrepProg (BitVec 64) := crepBody379_14
def output379 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [103#8, 101#8, 116#8, 95#8, 112#8, 114#8, 101#8, 95#8, 116#8, 120#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8,
    116#8], [0], crepProgToHOL data379)
end InitECandidate.Proofs.FrontendStages.Crep
