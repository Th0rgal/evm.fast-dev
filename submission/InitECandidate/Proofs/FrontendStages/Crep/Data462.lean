import InitECandidate.Proofs.FrontendStages.Crep.Translate446
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody462_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3, 4], none)) "stack_pop" []

def crepBody462_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6, 7, 8], none)) "stack_pop" []

def crepBody462_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "charge_with_memory"
  [Flapjack.CrepExp.const 3#64, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3,
    Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 32#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64,
    Flapjack.CrepExp.const 0#64]

def crepBody462_3 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody462_2

def crepBody462_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "sat_word"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody462_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "u256_to_be32"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.load
                (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
              Flapjack.CrepExp.const 24#64]),
        Flapjack.CrepExp.var 9]]

def crepBody462_6 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody462_5

def crepBody462_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody462_8 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody462_7

def crepBody462_9 : CrepProg (BitVec 64) :=
.seq crepBody462_6 crepBody462_8

def crepBody462_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody462_11 : CrepProg (BitVec 64) :=
.seq crepBody462_9 crepBody462_10

def crepBody462_12 : CrepProg (BitVec 64) :=
.seq crepBody462_4 crepBody462_11

def crepBody462_13 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody462_12

def crepBody462_14 : CrepProg (BitVec 64) :=
.seq crepBody462_3 crepBody462_13

def crepBody462_15 : CrepProg (BitVec 64) :=
.seq crepBody462_1 crepBody462_14

def crepBody462_16 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody462_15

def crepBody462_17 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody462_16

def crepBody462_18 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody462_17

def crepBody462_19 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody462_18

def crepBody462_20 : CrepProg (BitVec 64) :=
.seq crepBody462_0 crepBody462_19

def crepBody462_21 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody462_20

def crepBody462_22 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody462_21

def crepBody462_23 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody462_22

def crepBody462_24 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody462_23

def data462 : CrepProg (BitVec 64) := crepBody462_24
def output462 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 109#8, 115#8, 116#8, 111#8, 114#8, 101#8], [], crepProgToHOL data462)
end InitECandidate.Proofs.FrontendStages.Crep
