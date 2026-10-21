import InitECandidate.Proofs.FrontendStages.Crep.Translate340
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody356_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "destroy_storage" [Flapjack.CrepExp.var 0]

def crepBody356_1 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody356_0

def crepBody356_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "get_account" [Flapjack.CrepExp.var 0]

def crepBody356_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "acct_copy" [Flapjack.CrepExp.var 1]

def crepBody356_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.var 3)

def crepBody356_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody356_6 : CrepProg (BitVec 64) :=
.seq crepBody356_4 crepBody356_5

def crepBody356_7 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody356_6

def crepBody356_8 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 0#64]) crepBody356_7

def crepBody356_9 : CrepProg (BitVec 64) :=
.seq crepBody356_3 crepBody356_8

def crepBody356_10 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 136#64])) crepBody356_6

def crepBody356_11 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64]) crepBody356_10

def crepBody356_12 : CrepProg (BitVec 64) :=
.seq crepBody356_9 crepBody356_11

def crepBody356_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "modify_state_commit" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody356_14 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody356_13

def crepBody356_15 : CrepProg (BitVec 64) :=
.seq crepBody356_12 crepBody356_14

def crepBody356_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody356_17 : CrepProg (BitVec 64) :=
.seq crepBody356_15 crepBody356_16

def crepBody356_18 : CrepProg (BitVec 64) :=
.seq crepBody356_2 crepBody356_17

def crepBody356_19 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody356_18

def crepBody356_20 : CrepProg (BitVec 64) :=
.seq crepBody356_1 crepBody356_19

def data356 : CrepProg (BitVec 64) := crepBody356_20
def output356 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [99#8, 108#8, 101#8, 97#8, 114#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8, 95#8, 112#8, 114#8, 101#8,
    115#8, 101#8, 114#8, 118#8, 105#8, 110#8, 103#8, 95#8, 98#8, 97#8, 108#8, 97#8, 110#8, 99#8, 101#8], [0], crepProgToHOL data356)
end InitECandidate.Proofs.FrontendStages.Crep
