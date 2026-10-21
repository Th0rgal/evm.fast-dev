import InitECandidate.Proofs.FrontendStages.Crep.Translate482
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody498_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3, 4], none)) "stack_pop" []

def crepBody498_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "to_address_masked"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody498_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "access_gas_cost" [Flapjack.CrepExp.var 5]

def crepBody498_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "charge_gas"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 100#64]]

def crepBody498_4 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody498_3

def crepBody498_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "warm_after_charge" [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6]

def crepBody498_6 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody498_5

def crepBody498_7 : CrepProg (BitVec 64) :=
.seq crepBody498_4 crepBody498_6

def crepBody498_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7, 8], none)) "ext_code_of" [Flapjack.CrepExp.var 5]

def crepBody498_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "stack_push_word" [Flapjack.CrepExp.var 8]

def crepBody498_10 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody498_9

def crepBody498_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody498_12 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody498_11

def crepBody498_13 : CrepProg (BitVec 64) :=
.seq crepBody498_10 crepBody498_12

def crepBody498_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody498_15 : CrepProg (BitVec 64) :=
.seq crepBody498_13 crepBody498_14

def crepBody498_16 : CrepProg (BitVec 64) :=
.seq crepBody498_8 crepBody498_15

def crepBody498_17 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody498_16

def crepBody498_18 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody498_17

def crepBody498_19 : CrepProg (BitVec 64) :=
.seq crepBody498_7 crepBody498_18

def crepBody498_20 : CrepProg (BitVec 64) :=
.seq crepBody498_2 crepBody498_19

def crepBody498_21 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody498_20

def crepBody498_22 : CrepProg (BitVec 64) :=
.seq crepBody498_1 crepBody498_21

def crepBody498_23 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody498_22

def crepBody498_24 : CrepProg (BitVec 64) :=
.seq crepBody498_0 crepBody498_23

def crepBody498_25 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody498_24

def crepBody498_26 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody498_25

def crepBody498_27 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody498_26

def crepBody498_28 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody498_27

def data498 : CrepProg (BitVec 64) := crepBody498_28
def output498 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [111#8, 112#8, 95#8, 101#8, 120#8, 116#8, 99#8, 111#8, 100#8, 101#8, 115#8, 105#8, 122#8, 101#8], [], crepProgToHOL data498)
end InitECandidate.Proofs.FrontendStages.Crep
