import InitECandidate.Proofs.FrontendStages.Crep.Translate516
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody532_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "state_restore"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 288#64]),
          Flapjack.CrepExp.const 24#64])]

def crepBody532_1 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody532_0

def crepBody532_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody532_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
        Flapjack.CrepExp.const 160#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody532_1 crepBody532_2

def crepBody532_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody532_5 : CrepProg (BitVec 64) :=
.seq crepBody532_3 crepBody532_4

def data532 : CrepProg (BitVec 64) := crepBody532_5
def output532 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [102#8, 114#8, 97#8, 109#8, 101#8, 95#8, 101#8, 112#8, 105#8, 108#8, 111#8, 103#8, 117#8, 101#8], [], crepProgToHOL data532)
end InitECandidate.Proofs.FrontendStages.Crep
