import InitECandidate.Proofs.FrontendStages.Crep.Translate564
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody580_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.var 2)

def crepBody580_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 3)

def crepBody580_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 4)

def crepBody580_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 5)

def crepBody580_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody580_5 : CrepProg (BitVec 64) :=
.seq crepBody580_3 crepBody580_4

def crepBody580_6 : CrepProg (BitVec 64) :=
.seq crepBody580_2 crepBody580_5

def crepBody580_7 : CrepProg (BitVec 64) :=
.seq crepBody580_1 crepBody580_6

def crepBody580_8 : CrepProg (BitVec 64) :=
.seq crepBody580_0 crepBody580_7

def crepBody580_9 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody580_8

def crepBody580_10 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody580_9

def crepBody580_11 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody580_10

def crepBody580_12 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 1#64) crepBody580_11

def crepBody580_13 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.var 0) crepBody580_12

def crepBody580_14 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64]) crepBody580_12

def crepBody580_15 : CrepProg (BitVec 64) :=
.seq crepBody580_13 crepBody580_14

def crepBody580_16 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody580_11

def crepBody580_17 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 64#64]) crepBody580_16

def crepBody580_18 : CrepProg (BitVec 64) :=
.seq crepBody580_15 crepBody580_17

def crepBody580_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody580_20 : CrepProg (BitVec 64) :=
.seq crepBody580_18 crepBody580_19

def data580 : CrepProg (BitVec 64) := crepBody580_20
def output580 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 50#8, 53#8, 54#8, 95#8, 115#8, 101#8, 116#8, 95#8, 105#8, 110#8, 102#8, 105#8, 110#8, 105#8, 116#8, 121#8], [0], crepProgToHOL data580)
end InitECandidate.Proofs.FrontendStages.Crep
