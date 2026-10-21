import InitECandidate.Proofs.FrontendStages.Crep.Translate756
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody772_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "rlp_list_header_len" [Flapjack.CrepExp.var 2]

def crepBody772_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 9#64],
    Flapjack.CrepExp.var 2]

def crepBody772_2 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody772_1

def crepBody772_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "rlp_encode_list_header" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 2]

def crepBody772_4 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody772_3

def crepBody772_5 : CrepProg (BitVec 64) :=
.seq crepBody772_2 crepBody772_4

def crepBody772_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 2]]

def crepBody772_7 : CrepProg (BitVec 64) :=
.seq crepBody772_5 crepBody772_6

def crepBody772_8 : CrepProg (BitVec 64) :=
.seq crepBody772_0 crepBody772_7

def crepBody772_9 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody772_8

def crepBody772_10 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.sub
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 9#64]]) crepBody772_9

def data772 : CrepProg (BitVec 64) := crepBody772_10
def output772 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [114#8, 108#8, 112#8, 95#8, 102#8, 105#8, 110#8, 105#8, 115#8, 104#8, 95#8, 108#8, 105#8, 115#8, 116#8], [0, 1], crepProgToHOL data772)
end InitECandidate.Proofs.FrontendStages.Crep
