import InitECandidate.Proofs.FrontendStages.Crep.Translate472
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody488_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "charge_gas" [Flapjack.CrepExp.const 2#64]

def crepBody488_1 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody488_0

def crepBody488_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3, 4], none)) "address_to_u256"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.load
                  (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
                Flapjack.CrepExp.const 112#64]),
          Flapjack.CrepExp.const 16#64])]

def crepBody488_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "stack_push"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody488_4 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody488_3

def crepBody488_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody488_6 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody488_5

def crepBody488_7 : CrepProg (BitVec 64) :=
.seq crepBody488_4 crepBody488_6

def crepBody488_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody488_9 : CrepProg (BitVec 64) :=
.seq crepBody488_7 crepBody488_8

def crepBody488_10 : CrepProg (BitVec 64) :=
.seq crepBody488_2 crepBody488_9

def crepBody488_11 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody488_10

def crepBody488_12 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody488_11

def crepBody488_13 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody488_12

def crepBody488_14 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody488_13

def crepBody488_15 : CrepProg (BitVec 64) :=
.seq crepBody488_1 crepBody488_14

def data488 : CrepProg (BitVec 64) := crepBody488_15
def output488 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 99#8, 97#8, 108#8, 108#8, 101#8, 114#8], [], crepProgToHOL data488)
end InitECandidate.Proofs.FrontendStages.Crep
