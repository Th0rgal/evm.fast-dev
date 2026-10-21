import InitECandidate.Proofs.FrontendStages.Crep.Translate442
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody458_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3, 4], none)) "stack_pop" []

def crepBody458_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6, 7, 8], none)) "stack_pop" []

def crepBody458_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "charge_gas" [Flapjack.CrepExp.const 10#64]

def crepBody458_3 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody458_2

def crepBody458_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "u256_is_zero"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody458_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody458_6 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody458_5

def crepBody458_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody458_8 : CrepProg (BitVec 64) :=
.seq crepBody458_6 crepBody458_7

def crepBody458_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody458_10 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.const 0#64)) crepBody458_8 crepBody458_9

def crepBody458_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "is_valid_jumpdest"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody458_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 11)

def crepBody458_13 : CrepProg (BitVec 64) :=
.seq crepBody458_12 crepBody458_9

def crepBody458_14 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 6#64) crepBody458_13

def crepBody458_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 8#64

def crepBody458_16 : CrepProg (BitVec 64) :=
.seq crepBody458_14 crepBody458_15

def crepBody458_17 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 0#64)) crepBody458_16 crepBody458_9

def crepBody458_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.var 12)

def crepBody458_19 : CrepProg (BitVec 64) :=
.seq crepBody458_18 crepBody458_9

def crepBody458_20 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.var 1) crepBody458_19

def crepBody458_21 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 0#64]) crepBody458_20

def crepBody458_22 : CrepProg (BitVec 64) :=
.seq crepBody458_17 crepBody458_21

def crepBody458_23 : CrepProg (BitVec 64) :=
.seq crepBody458_22 crepBody458_7

def crepBody458_24 : CrepProg (BitVec 64) :=
.seq crepBody458_11 crepBody458_23

def crepBody458_25 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody458_24

def crepBody458_26 : CrepProg (BitVec 64) :=
.seq crepBody458_10 crepBody458_25

def crepBody458_27 : CrepProg (BitVec 64) :=
.seq crepBody458_4 crepBody458_26

def crepBody458_28 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody458_27

def crepBody458_29 : CrepProg (BitVec 64) :=
.seq crepBody458_3 crepBody458_28

def crepBody458_30 : CrepProg (BitVec 64) :=
.seq crepBody458_1 crepBody458_29

def crepBody458_31 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody458_30

def crepBody458_32 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody458_31

def crepBody458_33 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody458_32

def crepBody458_34 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody458_33

def crepBody458_35 : CrepProg (BitVec 64) :=
.seq crepBody458_0 crepBody458_34

def crepBody458_36 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody458_35

def crepBody458_37 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody458_36

def crepBody458_38 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody458_37

def crepBody458_39 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody458_38

def data458 : CrepProg (BitVec 64) := crepBody458_39
def output458 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 106#8, 117#8, 109#8, 112#8, 105#8], [], crepProgToHOL data458)
end InitECandidate.Proofs.FrontendStages.Crep
