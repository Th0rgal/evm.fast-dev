import InitECandidate.Proofs.FrontendStages.Crep.Translate345
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody361_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "get_account" [Flapjack.CrepExp.var 0]

def crepBody361_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "acct_copy" [Flapjack.CrepExp.var 5]

def crepBody361_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 7)

def crepBody361_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 8)

def crepBody361_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 9)

def crepBody361_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 10)

def crepBody361_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody361_7 : CrepProg (BitVec 64) :=
.seq crepBody361_5 crepBody361_6

def crepBody361_8 : CrepProg (BitVec 64) :=
.seq crepBody361_4 crepBody361_7

def crepBody361_9 : CrepProg (BitVec 64) :=
.seq crepBody361_3 crepBody361_8

def crepBody361_10 : CrepProg (BitVec 64) :=
.seq crepBody361_2 crepBody361_9

def crepBody361_11 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 4) crepBody361_10

def crepBody361_12 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 3) crepBody361_11

def crepBody361_13 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 2) crepBody361_12

def crepBody361_14 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 1) crepBody361_13

def crepBody361_15 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 8#64]) crepBody361_14

def crepBody361_16 : CrepProg (BitVec 64) :=
.seq crepBody361_1 crepBody361_15

def crepBody361_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "modify_state_commit" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 5]

def crepBody361_18 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody361_17

def crepBody361_19 : CrepProg (BitVec 64) :=
.seq crepBody361_16 crepBody361_18

def crepBody361_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody361_21 : CrepProg (BitVec 64) :=
.seq crepBody361_19 crepBody361_20

def crepBody361_22 : CrepProg (BitVec 64) :=
.seq crepBody361_0 crepBody361_21

def crepBody361_23 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody361_22

def data361 : CrepProg (BitVec 64) := crepBody361_23
def output361 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [115#8, 101#8, 116#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8, 95#8, 98#8, 97#8, 108#8, 97#8, 110#8, 99#8,
    101#8], [0, 1, 2, 3, 4], crepProgToHOL data361)
end InitECandidate.Proofs.FrontendStages.Crep
