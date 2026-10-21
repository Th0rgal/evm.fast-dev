import InitECandidate.Proofs.FrontendStages.Crep.Translate503
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody519_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3, 4], none)) "stack_pop" []

def crepBody519_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6, 7, 8], none)) "stack_pop" []

def crepBody519_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9, 10], none)) "extend_memory_cost1"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody519_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "charge_gas" [Flapjack.CrepExp.var 9]

def crepBody519_4 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody519_3

def crepBody519_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "extend_memory" [Flapjack.CrepExp.var 10]

def crepBody519_6 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody519_5

def crepBody519_7 : CrepProg (BitVec 64) :=
.seq crepBody519_4 crepBody519_6

def crepBody519_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "sat_word"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody519_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "sat_word"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody519_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.var 14)

def crepBody519_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody519_12 : CrepProg (BitVec 64) :=
.seq crepBody519_10 crepBody519_11

def crepBody519_13 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
          Flapjack.CrepExp.const 24#64]),
    Flapjack.CrepExp.var 12]) crepBody519_12

def crepBody519_14 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 120#64]) crepBody519_13

def crepBody519_15 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.var 11) crepBody519_12

def crepBody519_16 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 128#64]) crepBody519_15

def crepBody519_17 : CrepProg (BitVec 64) :=
.seq crepBody519_14 crepBody519_16

def crepBody519_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 13)

def crepBody519_19 : CrepProg (BitVec 64) :=
.seq crepBody519_18 crepBody519_11

def crepBody519_20 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 1#64) crepBody519_19

def crepBody519_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 8#64

def crepBody519_22 : CrepProg (BitVec 64) :=
.seq crepBody519_20 crepBody519_21

def crepBody519_23 : CrepProg (BitVec 64) :=
.seq crepBody519_17 crepBody519_22

def crepBody519_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody519_25 : CrepProg (BitVec 64) :=
.seq crepBody519_23 crepBody519_24

def crepBody519_26 : CrepProg (BitVec 64) :=
.seq crepBody519_9 crepBody519_25

def crepBody519_27 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody519_26

def crepBody519_28 : CrepProg (BitVec 64) :=
.seq crepBody519_8 crepBody519_27

def crepBody519_29 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody519_28

def crepBody519_30 : CrepProg (BitVec 64) :=
.seq crepBody519_7 crepBody519_29

def crepBody519_31 : CrepProg (BitVec 64) :=
.seq crepBody519_2 crepBody519_30

def crepBody519_32 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody519_31

def crepBody519_33 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody519_32

def crepBody519_34 : CrepProg (BitVec 64) :=
.seq crepBody519_1 crepBody519_33

def crepBody519_35 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody519_34

def crepBody519_36 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody519_35

def crepBody519_37 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody519_36

def crepBody519_38 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody519_37

def crepBody519_39 : CrepProg (BitVec 64) :=
.seq crepBody519_0 crepBody519_38

def crepBody519_40 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody519_39

def crepBody519_41 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody519_40

def crepBody519_42 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody519_41

def crepBody519_43 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody519_42

def data519 : CrepProg (BitVec 64) := crepBody519_43
def output519 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 114#8, 101#8, 118#8, 101#8, 114#8, 116#8], [], crepProgToHOL data519)
end InitECandidate.Proofs.FrontendStages.Crep
