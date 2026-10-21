import InitECandidate.Proofs.FrontendStages.Crep.Translate424
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody440_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3, 4], none)) "stack_pop" []

def crepBody440_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6, 7, 8], none)) "stack_pop" []

def crepBody440_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "charge_gas" [Flapjack.CrepExp.const 3#64]

def crepBody440_3 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody440_2

def crepBody440_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "u256_lt"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody440_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "stack_push_bool" [Flapjack.CrepExp.var 9]

def crepBody440_6 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody440_5

def crepBody440_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody440_8 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody440_7

def crepBody440_9 : CrepProg (BitVec 64) :=
.seq crepBody440_6 crepBody440_8

def crepBody440_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody440_11 : CrepProg (BitVec 64) :=
.seq crepBody440_9 crepBody440_10

def crepBody440_12 : CrepProg (BitVec 64) :=
.seq crepBody440_4 crepBody440_11

def crepBody440_13 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody440_12

def crepBody440_14 : CrepProg (BitVec 64) :=
.seq crepBody440_3 crepBody440_13

def crepBody440_15 : CrepProg (BitVec 64) :=
.seq crepBody440_1 crepBody440_14

def crepBody440_16 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody440_15

def crepBody440_17 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody440_16

def crepBody440_18 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody440_17

def crepBody440_19 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody440_18

def crepBody440_20 : CrepProg (BitVec 64) :=
.seq crepBody440_0 crepBody440_19

def crepBody440_21 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody440_20

def crepBody440_22 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody440_21

def crepBody440_23 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody440_22

def crepBody440_24 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody440_23

def data440 : CrepProg (BitVec 64) := crepBody440_24
def output440 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 108#8, 116#8], [], crepProgToHOL data440)
end InitECandidate.Proofs.FrontendStages.Crep
