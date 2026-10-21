import InitECandidate.Proofs.FrontendStages.Crep.Translate467
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody483_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3, 4], none)) "stack_pop" []

def crepBody483_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "charge_gas" [Flapjack.CrepExp.const 100#64]

def crepBody483_2 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody483_1

def crepBody483_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "u256_to_be32"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.var 5]

def crepBody483_4 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody483_3

def crepBody483_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7, 8, 9, 10], none)) "get_transient_storage"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 5]

def crepBody483_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "stack_push"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10]

def crepBody483_7 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody483_6

def crepBody483_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody483_9 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody483_8

def crepBody483_10 : CrepProg (BitVec 64) :=
.seq crepBody483_7 crepBody483_9

def crepBody483_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody483_12 : CrepProg (BitVec 64) :=
.seq crepBody483_10 crepBody483_11

def crepBody483_13 : CrepProg (BitVec 64) :=
.seq crepBody483_5 crepBody483_12

def crepBody483_14 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody483_13

def crepBody483_15 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody483_14

def crepBody483_16 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody483_15

def crepBody483_17 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody483_16

def crepBody483_18 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.load
              (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
            Flapjack.CrepExp.const 112#64]),
      Flapjack.CrepExp.const 32#64])) crepBody483_17

def crepBody483_19 : CrepProg (BitVec 64) :=
.seq crepBody483_4 crepBody483_18

def crepBody483_20 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 280#64])) crepBody483_19

def crepBody483_21 : CrepProg (BitVec 64) :=
.seq crepBody483_2 crepBody483_20

def crepBody483_22 : CrepProg (BitVec 64) :=
.seq crepBody483_0 crepBody483_21

def crepBody483_23 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody483_22

def crepBody483_24 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody483_23

def crepBody483_25 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody483_24

def crepBody483_26 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody483_25

def data483 : CrepProg (BitVec 64) := crepBody483_26
def output483 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 116#8, 108#8, 111#8, 97#8, 100#8], [], crepProgToHOL data483)
end InitECandidate.Proofs.FrontendStages.Crep
