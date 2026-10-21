import InitECandidate.Proofs.FrontendStages.Crep.Translate447
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody463_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3, 4], none)) "stack_pop" []

def crepBody463_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6, 7, 8], none)) "stack_pop" []

def crepBody463_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "charge_with_memory"
  [Flapjack.CrepExp.const 3#64, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3,
    Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64,
    Flapjack.CrepExp.const 0#64]

def crepBody463_3 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody463_2

def crepBody463_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "sat_word"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody463_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.load
              (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
            Flapjack.CrepExp.const 24#64]),
      Flapjack.CrepExp.var 9])
  (Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 255#64])

def crepBody463_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody463_7 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody463_6

def crepBody463_8 : CrepProg (BitVec 64) :=
.seq crepBody463_5 crepBody463_7

def crepBody463_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody463_10 : CrepProg (BitVec 64) :=
.seq crepBody463_8 crepBody463_9

def crepBody463_11 : CrepProg (BitVec 64) :=
.seq crepBody463_4 crepBody463_10

def crepBody463_12 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody463_11

def crepBody463_13 : CrepProg (BitVec 64) :=
.seq crepBody463_3 crepBody463_12

def crepBody463_14 : CrepProg (BitVec 64) :=
.seq crepBody463_1 crepBody463_13

def crepBody463_15 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody463_14

def crepBody463_16 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody463_15

def crepBody463_17 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody463_16

def crepBody463_18 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody463_17

def crepBody463_19 : CrepProg (BitVec 64) :=
.seq crepBody463_0 crepBody463_18

def crepBody463_20 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody463_19

def crepBody463_21 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody463_20

def crepBody463_22 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody463_21

def crepBody463_23 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody463_22

def data463 : CrepProg (BitVec 64) := crepBody463_23
def output463 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 109#8, 115#8, 116#8, 111#8, 114#8, 101#8, 56#8], [], crepProgToHOL data463)
end InitECandidate.Proofs.FrontendStages.Crep
