import InitECandidate.Proofs.FrontendStages.Crep.Translate441
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody457_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3, 4], none)) "stack_pop" []

def crepBody457_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "charge_gas" [Flapjack.CrepExp.const 8#64]

def crepBody457_2 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody457_1

def crepBody457_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "is_valid_jumpdest"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody457_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 6)

def crepBody457_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody457_6 : CrepProg (BitVec 64) :=
.seq crepBody457_4 crepBody457_5

def crepBody457_7 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 6#64) crepBody457_6

def crepBody457_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 8#64

def crepBody457_9 : CrepProg (BitVec 64) :=
.seq crepBody457_7 crepBody457_8

def crepBody457_10 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64)) crepBody457_9 crepBody457_5

def crepBody457_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 7)

def crepBody457_12 : CrepProg (BitVec 64) :=
.seq crepBody457_11 crepBody457_5

def crepBody457_13 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 1) crepBody457_12

def crepBody457_14 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 0#64]) crepBody457_13

def crepBody457_15 : CrepProg (BitVec 64) :=
.seq crepBody457_10 crepBody457_14

def crepBody457_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody457_17 : CrepProg (BitVec 64) :=
.seq crepBody457_15 crepBody457_16

def crepBody457_18 : CrepProg (BitVec 64) :=
.seq crepBody457_3 crepBody457_17

def crepBody457_19 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody457_18

def crepBody457_20 : CrepProg (BitVec 64) :=
.seq crepBody457_2 crepBody457_19

def crepBody457_21 : CrepProg (BitVec 64) :=
.seq crepBody457_0 crepBody457_20

def crepBody457_22 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody457_21

def crepBody457_23 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody457_22

def crepBody457_24 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody457_23

def crepBody457_25 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody457_24

def data457 : CrepProg (BitVec 64) := crepBody457_25
def output457 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 106#8, 117#8, 109#8, 112#8], [], crepProgToHOL data457)
end InitECandidate.Proofs.FrontendStages.Crep
