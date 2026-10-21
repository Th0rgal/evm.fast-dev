import InitECandidate.Proofs.FrontendStages.Crep.Translate642
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody658_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "st_be64" [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 5]

def crepBody658_1 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody658_0

def crepBody658_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "st_be64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 8#64], Flapjack.CrepExp.var 4]

def crepBody658_3 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody658_2

def crepBody658_4 : CrepProg (BitVec 64) :=
.seq crepBody658_1 crepBody658_3

def crepBody658_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "st_be64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 16#64],
    Flapjack.CrepExp.var 3]

def crepBody658_6 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody658_5

def crepBody658_7 : CrepProg (BitVec 64) :=
.seq crepBody658_4 crepBody658_6

def crepBody658_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "st_be64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 24#64],
    Flapjack.CrepExp.var 2]

def crepBody658_9 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody658_8

def crepBody658_10 : CrepProg (BitVec 64) :=
.seq crepBody658_7 crepBody658_9

def crepBody658_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "st_be64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 32#64],
    Flapjack.CrepExp.var 1]

def crepBody658_12 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody658_11

def crepBody658_13 : CrepProg (BitVec 64) :=
.seq crepBody658_10 crepBody658_12

def crepBody658_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "st_be64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 40#64],
    Flapjack.CrepExp.var 0]

def crepBody658_15 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody658_14

def crepBody658_16 : CrepProg (BitVec 64) :=
.seq crepBody658_13 crepBody658_15

def crepBody658_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody658_18 : CrepProg (BitVec 64) :=
.seq crepBody658_16 crepBody658_17

def data658 : CrepProg (BitVec 64) := crepBody658_18
def output658 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [98#8, 108#8, 115#8, 95#8, 102#8, 112#8, 95#8, 116#8, 111#8, 95#8, 98#8, 101#8, 52#8, 56#8], [0, 1, 2, 3, 4, 5, 6], crepProgToHOL data658)
end InitECandidate.Proofs.FrontendStages.Crep
