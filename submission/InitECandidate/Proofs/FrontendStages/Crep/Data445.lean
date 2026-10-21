import InitECandidate.Proofs.FrontendStages.Crep.Translate429
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody445_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3, 4], none)) "stack_pop" []

def crepBody445_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "charge_gas" [Flapjack.CrepExp.const 3#64]

def crepBody445_2 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody445_1

def crepBody445_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "u256_is_zero"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody445_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "stack_push_bool" [Flapjack.CrepExp.var 5]

def crepBody445_5 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody445_4

def crepBody445_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody445_7 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody445_6

def crepBody445_8 : CrepProg (BitVec 64) :=
.seq crepBody445_5 crepBody445_7

def crepBody445_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody445_10 : CrepProg (BitVec 64) :=
.seq crepBody445_8 crepBody445_9

def crepBody445_11 : CrepProg (BitVec 64) :=
.seq crepBody445_3 crepBody445_10

def crepBody445_12 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody445_11

def crepBody445_13 : CrepProg (BitVec 64) :=
.seq crepBody445_2 crepBody445_12

def crepBody445_14 : CrepProg (BitVec 64) :=
.seq crepBody445_0 crepBody445_13

def crepBody445_15 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody445_14

def crepBody445_16 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody445_15

def crepBody445_17 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody445_16

def crepBody445_18 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody445_17

def data445 : CrepProg (BitVec 64) := crepBody445_18
def output445 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 105#8, 115#8, 122#8, 101#8, 114#8, 111#8], [], crepProgToHOL data445)
end InitECandidate.Proofs.FrontendStages.Crep
