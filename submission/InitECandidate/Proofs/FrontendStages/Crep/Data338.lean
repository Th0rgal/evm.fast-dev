import InitECandidate.Proofs.FrontendStages.Crep.Translate322
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody338_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "htab_set"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 1#64]

def crepBody338_1 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody338_0

def crepBody338_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2], none)) "htab_get"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.var 0]

def crepBody338_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 2]

def crepBody338_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody338_5 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 0#64)) crepBody338_3 crepBody338_4

def crepBody338_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "get_pre_state_account_optional" [Flapjack.CrepExp.var 0]

def crepBody338_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 3]

def crepBody338_8 : CrepProg (BitVec 64) :=
.seq crepBody338_6 crepBody338_7

def crepBody338_9 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody338_8

def crepBody338_10 : CrepProg (BitVec 64) :=
.seq crepBody338_5 crepBody338_9

def crepBody338_11 : CrepProg (BitVec 64) :=
.seq crepBody338_2 crepBody338_10

def crepBody338_12 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody338_11

def crepBody338_13 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody338_12

def crepBody338_14 : CrepProg (BitVec 64) :=
.seq crepBody338_1 crepBody338_13

def data338 : CrepProg (BitVec 64) := crepBody338_14
def output338 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [103#8, 101#8, 116#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8, 95#8, 111#8, 112#8, 116#8, 105#8, 111#8,
    110#8, 97#8, 108#8], [0], crepProgToHOL data338)
end InitECandidate.Proofs.FrontendStages.Crep
