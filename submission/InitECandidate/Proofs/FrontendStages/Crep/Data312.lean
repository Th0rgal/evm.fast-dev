import InitECandidate.Proofs.FrontendStages.Crep.Translate296
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody312_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "heap_mark" []

def crepBody312_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody312_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "keccak256"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 1#64],
    Flapjack.CrepExp.const 64#64, Flapjack.CrepExp.var 3]

def crepBody312_3 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody312_2

def crepBody312_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "memcpy"
  [Flapjack.CrepExp.var 1,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 12#64],
    Flapjack.CrepExp.const 20#64]

def crepBody312_5 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody312_4

def crepBody312_6 : CrepProg (BitVec 64) :=
.seq crepBody312_3 crepBody312_5

def crepBody312_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody312_8 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody312_7

def crepBody312_9 : CrepProg (BitVec 64) :=
.seq crepBody312_6 crepBody312_8

def crepBody312_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody312_11 : CrepProg (BitVec 64) :=
.seq crepBody312_9 crepBody312_10

def crepBody312_12 : CrepProg (BitVec 64) :=
.seq crepBody312_1 crepBody312_11

def crepBody312_13 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody312_12

def crepBody312_14 : CrepProg (BitVec 64) :=
.seq crepBody312_0 crepBody312_13

def crepBody312_15 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody312_14

def data312 : CrepProg (BitVec 64) := crepBody312_15
def output312 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [115#8, 101#8, 110#8, 100#8, 101#8, 114#8, 95#8, 97#8, 100#8, 100#8, 114#8, 101#8, 115#8, 115#8, 95#8, 102#8, 114#8,
    111#8, 109#8, 95#8, 112#8, 117#8, 98#8, 108#8, 105#8, 99#8, 95#8, 107#8, 101#8, 121#8], [0, 1], crepProgToHOL data312)
end InitECandidate.Proofs.FrontendStages.Crep
