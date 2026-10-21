import InitECandidate.Proofs.FrontendStages.Crep.Translate502
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody518_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3, 4], none)) "stack_pop" []

def crepBody518_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6, 7, 8], none)) "stack_pop" []

def crepBody518_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9, 10], none)) "extend_memory_cost1"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody518_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "charge_gas" [Flapjack.CrepExp.var 9]

def crepBody518_4 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody518_3

def crepBody518_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "extend_memory" [Flapjack.CrepExp.var 10]

def crepBody518_6 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody518_5

def crepBody518_7 : CrepProg (BitVec 64) :=
.seq crepBody518_4 crepBody518_6

def crepBody518_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "sat_word"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody518_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "sat_word"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody518_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.var 14)

def crepBody518_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody518_12 : CrepProg (BitVec 64) :=
.seq crepBody518_10 crepBody518_11

def crepBody518_13 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
          Flapjack.CrepExp.const 24#64]),
    Flapjack.CrepExp.var 12]) crepBody518_12

def crepBody518_14 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 120#64]) crepBody518_13

def crepBody518_15 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.var 11) crepBody518_12

def crepBody518_16 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 128#64]) crepBody518_15

def crepBody518_17 : CrepProg (BitVec 64) :=
.seq crepBody518_14 crepBody518_16

def crepBody518_18 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody518_12

def crepBody518_19 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 104#64]) crepBody518_18

def crepBody518_20 : CrepProg (BitVec 64) :=
.seq crepBody518_17 crepBody518_19

def crepBody518_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody518_22 : CrepProg (BitVec 64) :=
.seq crepBody518_20 crepBody518_21

def crepBody518_23 : CrepProg (BitVec 64) :=
.seq crepBody518_9 crepBody518_22

def crepBody518_24 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody518_23

def crepBody518_25 : CrepProg (BitVec 64) :=
.seq crepBody518_8 crepBody518_24

def crepBody518_26 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody518_25

def crepBody518_27 : CrepProg (BitVec 64) :=
.seq crepBody518_7 crepBody518_26

def crepBody518_28 : CrepProg (BitVec 64) :=
.seq crepBody518_2 crepBody518_27

def crepBody518_29 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody518_28

def crepBody518_30 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody518_29

def crepBody518_31 : CrepProg (BitVec 64) :=
.seq crepBody518_1 crepBody518_30

def crepBody518_32 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody518_31

def crepBody518_33 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody518_32

def crepBody518_34 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody518_33

def crepBody518_35 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody518_34

def crepBody518_36 : CrepProg (BitVec 64) :=
.seq crepBody518_0 crepBody518_35

def crepBody518_37 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody518_36

def crepBody518_38 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody518_37

def crepBody518_39 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody518_38

def crepBody518_40 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody518_39

def data518 : CrepProg (BitVec 64) := crepBody518_40
def output518 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 114#8, 101#8, 116#8, 117#8, 114#8, 110#8], [], crepProgToHOL data518)
end InitECandidate.Proofs.FrontendStages.Crep
