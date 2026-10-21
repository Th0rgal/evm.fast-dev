import InitECandidate.Proofs.FrontendStages.Crep.Translate773
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody789_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6, 7, 8, 9, 10, 11, 12], none)) "u256_mul_full"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64,
    Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody789_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 13 (Flapjack.CrepExp.const 1#64)

def crepBody789_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody789_3 : CrepProg (BitVec 64) :=
.seq crepBody789_1 crepBody789_2

def crepBody789_4 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12])
  (Flapjack.CrepExp.const 0#64)) crepBody789_3 crepBody789_2

def crepBody789_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7,
    Flapjack.CrepExp.var 8]

def crepBody789_6 : CrepProg (BitVec 64) :=
.seq crepBody789_4 crepBody789_5

def crepBody789_7 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody789_6

def crepBody789_8 : CrepProg (BitVec 64) :=
.seq crepBody789_0 crepBody789_7

def crepBody789_9 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody789_8

def crepBody789_10 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody789_9

def crepBody789_11 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody789_10

def crepBody789_12 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody789_11

def crepBody789_13 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody789_12

def crepBody789_14 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody789_13

def crepBody789_15 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody789_14

def crepBody789_16 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody789_15

def data789 : CrepProg (BitVec 64) := crepBody789_16
def output789 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 101#8, 101#8, 95#8, 109#8, 117#8, 108#8], [0, 1, 2, 3, 4], crepProgToHOL data789)
end InitECandidate.Proofs.FrontendStages.Crep
