import InitECandidate.Proofs.FrontendStages.Crep.Translate777
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody793_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "state_fresh_tx" []

def crepBody793_1 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody793_0

def crepBody793_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2], none)) "ext_code_of" [Flapjack.CrepExp.var 0]

def crepBody793_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 3)

def crepBody793_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody793_5 : CrepProg (BitVec 64) :=
.seq crepBody793_3 crepBody793_4

def crepBody793_6 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 70#64) crepBody793_5

def crepBody793_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 4#64

def crepBody793_8 : CrepProg (BitVec 64) :=
.seq crepBody793_6 crepBody793_7

def crepBody793_9 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody793_8 crepBody793_4

def crepBody793_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 8#64]

def crepBody793_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "process_unchecked_system_transaction"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 0#64]

def crepBody793_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 5)

def crepBody793_13 : CrepProg (BitVec 64) :=
.seq crepBody793_12 crepBody793_4

def crepBody793_14 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 71#64) crepBody793_13

def crepBody793_15 : CrepProg (BitVec 64) :=
.seq crepBody793_14 crepBody793_7

def crepBody793_16 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 32#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody793_15 crepBody793_4

def crepBody793_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 4]

def crepBody793_18 : CrepProg (BitVec 64) :=
.seq crepBody793_16 crepBody793_17

def crepBody793_19 : CrepProg (BitVec 64) :=
.seq crepBody793_11 crepBody793_18

def crepBody793_20 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody793_19

def crepBody793_21 : CrepProg (BitVec 64) :=
.seq crepBody793_10 crepBody793_20

def crepBody793_22 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody793_21

def crepBody793_23 : CrepProg (BitVec 64) :=
.seq crepBody793_9 crepBody793_22

def crepBody793_24 : CrepProg (BitVec 64) :=
.seq crepBody793_2 crepBody793_23

def crepBody793_25 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody793_24

def crepBody793_26 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody793_25

def crepBody793_27 : CrepProg (BitVec 64) :=
.seq crepBody793_1 crepBody793_26

def data793 : CrepProg (BitVec 64) := crepBody793_27
def output793 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 114#8, 111#8, 99#8, 101#8, 115#8, 115#8, 95#8, 99#8, 104#8, 101#8, 99#8, 107#8, 101#8, 100#8, 95#8, 115#8,
    121#8, 115#8, 116#8, 101#8, 109#8, 95#8, 116#8, 114#8, 97#8, 110#8, 115#8, 97#8, 99#8, 116#8, 105#8, 111#8, 110#8], [0], crepProgToHOL data793)
end InitECandidate.Proofs.FrontendStages.Crep
