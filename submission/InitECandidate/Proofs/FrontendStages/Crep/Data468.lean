import InitECandidate.Proofs.FrontendStages.Crep.Translate452
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody468_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "charge_gas" [Flapjack.CrepExp.const 2#64]

def crepBody468_1 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody468_0

def crepBody468_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "charge_gas" [Flapjack.CrepExp.const 3#64]

def crepBody468_3 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody468_2

def crepBody468_4 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 0#64)) crepBody468_1 crepBody468_3

def crepBody468_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "heap_mark" []

def crepBody468_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody468_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "buffer_read"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
          Flapjack.CrepExp.const 48#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
          Flapjack.CrepExp.const 56#64]),
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.load
                (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
              Flapjack.CrepExp.const 0#64]),
        Flapjack.CrepExp.const 1#64],
    Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 2]

def crepBody468_8 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody468_7

def crepBody468_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3, 4, 5, 6], none)) "u256_from_be" [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 0]

def crepBody468_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "heap_release" [Flapjack.CrepExp.var 1]

def crepBody468_11 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody468_10

def crepBody468_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "stack_push"
  [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6]

def crepBody468_13 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody468_12

def crepBody468_14 : CrepProg (BitVec 64) :=
.seq crepBody468_11 crepBody468_13

def crepBody468_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "pc_add"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.var 0]]

def crepBody468_16 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody468_15

def crepBody468_17 : CrepProg (BitVec 64) :=
.seq crepBody468_14 crepBody468_16

def crepBody468_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody468_19 : CrepProg (BitVec 64) :=
.seq crepBody468_17 crepBody468_18

def crepBody468_20 : CrepProg (BitVec 64) :=
.seq crepBody468_9 crepBody468_19

def crepBody468_21 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody468_20

def crepBody468_22 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody468_21

def crepBody468_23 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody468_22

def crepBody468_24 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody468_23

def crepBody468_25 : CrepProg (BitVec 64) :=
.seq crepBody468_8 crepBody468_24

def crepBody468_26 : CrepProg (BitVec 64) :=
.seq crepBody468_6 crepBody468_25

def crepBody468_27 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody468_26

def crepBody468_28 : CrepProg (BitVec 64) :=
.seq crepBody468_5 crepBody468_27

def crepBody468_29 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody468_28

def crepBody468_30 : CrepProg (BitVec 64) :=
.seq crepBody468_4 crepBody468_29

def data468 : CrepProg (BitVec 64) := crepBody468_30
def output468 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 112#8, 117#8, 115#8, 104#8], [0], crepProgToHOL data468)
end InitECandidate.Proofs.FrontendStages.Crep
