import InitECandidate.Proofs.FrontendStages.Crep.Translate361
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody377_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "bal_ensure_account" [Flapjack.CrepExp.var 0]

def crepBody377_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "lst_upsert_idx"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.const 24#64, Flapjack.CrepExp.var 1]

def crepBody377_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 7)

def crepBody377_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody377_4 : CrepProg (BitVec 64) :=
.seq crepBody377_2 crepBody377_3

def crepBody377_5 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 2) crepBody377_4

def crepBody377_6 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 8#64]) crepBody377_5

def crepBody377_7 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 3) crepBody377_4

def crepBody377_8 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 16#64]) crepBody377_7

def crepBody377_9 : CrepProg (BitVec 64) :=
.seq crepBody377_6 crepBody377_8

def crepBody377_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody377_11 : CrepProg (BitVec 64) :=
.seq crepBody377_9 crepBody377_10

def crepBody377_12 : CrepProg (BitVec 64) :=
.seq crepBody377_1 crepBody377_11

def crepBody377_13 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody377_12

def crepBody377_14 : CrepProg (BitVec 64) :=
.seq crepBody377_0 crepBody377_13

def crepBody377_15 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody377_14

def data377 : CrepProg (BitVec 64) := crepBody377_15
def output377 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [97#8, 100#8, 100#8, 95#8, 99#8, 111#8, 100#8, 101#8, 95#8, 99#8, 104#8, 97#8, 110#8, 103#8, 101#8], [0, 1, 2, 3], crepProgToHOL data377)
end InitECandidate.Proofs.FrontendStages.Crep
