import InitECandidate.Proofs.FrontendStages.Crep.Translate468
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody484_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "require_not_static" []

def crepBody484_1 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody484_0

def crepBody484_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3, 4], none)) "stack_pop" []

def crepBody484_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6, 7, 8], none)) "stack_pop" []

def crepBody484_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "charge_gas" [Flapjack.CrepExp.const 100#64]

def crepBody484_5 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody484_4

def crepBody484_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "u256_to_be32"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.var 9]

def crepBody484_7 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody484_6

def crepBody484_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "set_transient_storage"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody484_9 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody484_8

def crepBody484_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody484_11 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody484_10

def crepBody484_12 : CrepProg (BitVec 64) :=
.seq crepBody484_9 crepBody484_11

def crepBody484_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody484_14 : CrepProg (BitVec 64) :=
.seq crepBody484_12 crepBody484_13

def crepBody484_15 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.load
              (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
            Flapjack.CrepExp.const 112#64]),
      Flapjack.CrepExp.const 32#64])) crepBody484_14

def crepBody484_16 : CrepProg (BitVec 64) :=
.seq crepBody484_7 crepBody484_15

def crepBody484_17 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 280#64])) crepBody484_16

def crepBody484_18 : CrepProg (BitVec 64) :=
.seq crepBody484_5 crepBody484_17

def crepBody484_19 : CrepProg (BitVec 64) :=
.seq crepBody484_3 crepBody484_18

def crepBody484_20 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody484_19

def crepBody484_21 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody484_20

def crepBody484_22 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody484_21

def crepBody484_23 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody484_22

def crepBody484_24 : CrepProg (BitVec 64) :=
.seq crepBody484_2 crepBody484_23

def crepBody484_25 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody484_24

def crepBody484_26 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody484_25

def crepBody484_27 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody484_26

def crepBody484_28 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody484_27

def crepBody484_29 : CrepProg (BitVec 64) :=
.seq crepBody484_1 crepBody484_28

def data484 : CrepProg (BitVec 64) := crepBody484_29
def output484 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 116#8, 115#8, 116#8, 111#8, 114#8, 101#8], [], crepProgToHOL data484)
end InitECandidate.Proofs.FrontendStages.Crep
