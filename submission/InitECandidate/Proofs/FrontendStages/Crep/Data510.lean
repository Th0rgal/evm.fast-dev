import InitECandidate.Proofs.FrontendStages.Crep.Translate494
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody510_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "charge_gas" [Flapjack.CrepExp.const 2#64]

def crepBody510_1 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody510_0

def crepBody510_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "block_env" []

def crepBody510_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "stack_push_word"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 80#64])]

def crepBody510_4 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody510_3

def crepBody510_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody510_6 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody510_5

def crepBody510_7 : CrepProg (BitVec 64) :=
.seq crepBody510_4 crepBody510_6

def crepBody510_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody510_9 : CrepProg (BitVec 64) :=
.seq crepBody510_7 crepBody510_8

def crepBody510_10 : CrepProg (BitVec 64) :=
.seq crepBody510_2 crepBody510_9

def crepBody510_11 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody510_10

def crepBody510_12 : CrepProg (BitVec 64) :=
.seq crepBody510_1 crepBody510_11

def data510 : CrepProg (BitVec 64) := crepBody510_12
def output510 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [111#8, 112#8, 95#8, 116#8, 105#8, 109#8, 101#8, 115#8, 116#8, 97#8, 109#8, 112#8], [], crepProgToHOL data510)
end InitECandidate.Proofs.FrontendStages.Crep
