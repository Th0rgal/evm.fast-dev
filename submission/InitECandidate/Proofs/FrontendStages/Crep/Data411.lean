import InitECandidate.Proofs.FrontendStages.Crep.Translate395
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody411_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "words_of" [Flapjack.CrepExp.var 0]

def crepBody411_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2, 3], none)) "mul64x64" [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 1]

def crepBody411_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 18446744073709551615#64]

def crepBody411_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody411_4 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 0#64)) crepBody411_2 crepBody411_3

def crepBody411_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "add_sat"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 3#64],
    Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 9#64)]

def crepBody411_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 4]

def crepBody411_7 : CrepProg (BitVec 64) :=
.seq crepBody411_5 crepBody411_6

def crepBody411_8 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody411_7

def crepBody411_9 : CrepProg (BitVec 64) :=
.seq crepBody411_4 crepBody411_8

def crepBody411_10 : CrepProg (BitVec 64) :=
.seq crepBody411_1 crepBody411_9

def crepBody411_11 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody411_10

def crepBody411_12 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody411_11

def crepBody411_13 : CrepProg (BitVec 64) :=
.seq crepBody411_0 crepBody411_12

def crepBody411_14 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody411_13

def data411 : CrepProg (BitVec 64) := crepBody411_14
def output411 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [109#8, 101#8, 109#8, 111#8, 114#8, 121#8, 95#8, 103#8, 97#8, 115#8, 95#8, 99#8, 111#8, 115#8, 116#8], [0], crepProgToHOL data411)
end InitECandidate.Proofs.FrontendStages.Crep
