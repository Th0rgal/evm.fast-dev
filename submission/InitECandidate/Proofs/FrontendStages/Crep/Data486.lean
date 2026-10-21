import InitECandidate.Proofs.FrontendStages.Crep.Translate470
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody486_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3, 4], none)) "stack_pop" []

def crepBody486_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "to_address_masked"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody486_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "access_gas_cost" [Flapjack.CrepExp.var 5]

def crepBody486_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "charge_gas" [Flapjack.CrepExp.var 6]

def crepBody486_4 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody486_3

def crepBody486_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "warm_after_charge" [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6]

def crepBody486_6 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody486_5

def crepBody486_7 : CrepProg (BitVec 64) :=
.seq crepBody486_4 crepBody486_6

def crepBody486_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "get_account" [Flapjack.CrepExp.var 5]

def crepBody486_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "stack_push"
  [Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 24#64])]

def crepBody486_10 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody486_9

def crepBody486_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody486_12 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody486_11

def crepBody486_13 : CrepProg (BitVec 64) :=
.seq crepBody486_10 crepBody486_12

def crepBody486_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody486_15 : CrepProg (BitVec 64) :=
.seq crepBody486_13 crepBody486_14

def crepBody486_16 : CrepProg (BitVec 64) :=
.seq crepBody486_8 crepBody486_15

def crepBody486_17 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody486_16

def crepBody486_18 : CrepProg (BitVec 64) :=
.seq crepBody486_7 crepBody486_17

def crepBody486_19 : CrepProg (BitVec 64) :=
.seq crepBody486_2 crepBody486_18

def crepBody486_20 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody486_19

def crepBody486_21 : CrepProg (BitVec 64) :=
.seq crepBody486_1 crepBody486_20

def crepBody486_22 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody486_21

def crepBody486_23 : CrepProg (BitVec 64) :=
.seq crepBody486_0 crepBody486_22

def crepBody486_24 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody486_23

def crepBody486_25 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody486_24

def crepBody486_26 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody486_25

def crepBody486_27 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody486_26

def data486 : CrepProg (BitVec 64) := crepBody486_27
def output486 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 98#8, 97#8, 108#8, 97#8, 110#8, 99#8, 101#8], [], crepProgToHOL data486)
end InitECandidate.Proofs.FrontendStages.Crep
