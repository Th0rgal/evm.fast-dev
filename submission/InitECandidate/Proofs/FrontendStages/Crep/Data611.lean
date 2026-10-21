import InitECandidate.Proofs.FrontendStages.Crep.Translate595
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody611_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "memzero"
  [Flapjack.CrepExp.var 1,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64]]

def crepBody611_1 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody611_0

def crepBody611_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.var 3)

def crepBody611_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 4)

def crepBody611_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 5)

def crepBody611_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 6)

def crepBody611_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody611_7 : CrepProg (BitVec 64) :=
.seq crepBody611_5 crepBody611_6

def crepBody611_8 : CrepProg (BitVec 64) :=
.seq crepBody611_4 crepBody611_7

def crepBody611_9 : CrepProg (BitVec 64) :=
.seq crepBody611_3 crepBody611_8

def crepBody611_10 : CrepProg (BitVec 64) :=
.seq crepBody611_2 crepBody611_9

def crepBody611_11 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 1011752739694698287#64) crepBody611_10

def crepBody611_12 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 7381016538464732716#64) crepBody611_11

def crepBody611_13 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 754611498739239741#64) crepBody611_12

def crepBody611_14 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 15230403791020821917#64) crepBody611_13

def crepBody611_15 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.var 1) crepBody611_14

def crepBody611_16 : CrepProg (BitVec 64) :=
.seq crepBody611_1 crepBody611_15

def crepBody611_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody611_18 : CrepProg (BitVec 64) :=
.seq crepBody611_16 crepBody611_17

def data611 : CrepProg (BitVec 64) := crepBody611_18
def output611 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 101#8, 95#8, 115#8, 101#8, 116#8, 95#8, 111#8, 110#8, 101#8], [0, 1], crepProgToHOL data611)
end InitECandidate.Proofs.FrontendStages.Crep
