import InitECandidate.Proofs.FrontendStages.Crep.Translate171
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody187_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4, 5], none)) "ssz_split_var_list"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2]

def crepBody187_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "ssz_fail" [Flapjack.CrepExp.const 70#64]

def crepBody187_2 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody187_1

def crepBody187_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody187_4 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 3)
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 4,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 16#64],
        Flapjack.CrepExp.const 8#64]))) crepBody187_2 crepBody187_3

def crepBody187_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6 (Flapjack.CrepExp.var 7)

def crepBody187_6 : CrepProg (BitVec 64) :=
.seq crepBody187_5 crepBody187_3

def crepBody187_7 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 1#64]) crepBody187_6

def crepBody187_8 : CrepProg (BitVec 64) :=
.seq crepBody187_4 crepBody187_7

def crepBody187_9 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 5)) crepBody187_8

def crepBody187_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody187_11 : CrepProg (BitVec 64) :=
.seq crepBody187_9 crepBody187_10

def crepBody187_12 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody187_11

def crepBody187_13 : CrepProg (BitVec 64) :=
.seq crepBody187_0 crepBody187_12

def crepBody187_14 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody187_13

def crepBody187_15 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody187_14

def data187 : CrepProg (BitVec 64) := crepBody187_15
def output187 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 98#8, 121#8, 116#8, 101#8, 115#8, 95#8, 108#8, 105#8, 115#8, 116#8], [0, 1, 2, 3], crepProgToHOL data187)
end InitECandidate.Proofs.FrontendStages.Crep
