import InitECandidate.Proofs.FrontendStages.Crep.Translate359
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody375_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "bal_ensure_account" [Flapjack.CrepExp.var 0]

def crepBody375_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "lst_upsert_idx"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.const 40#64, Flapjack.CrepExp.var 1]

def crepBody375_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.var 9)

def crepBody375_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 10)

def crepBody375_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 11)

def crepBody375_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 12)

def crepBody375_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody375_7 : CrepProg (BitVec 64) :=
.seq crepBody375_5 crepBody375_6

def crepBody375_8 : CrepProg (BitVec 64) :=
.seq crepBody375_4 crepBody375_7

def crepBody375_9 : CrepProg (BitVec 64) :=
.seq crepBody375_3 crepBody375_8

def crepBody375_10 : CrepProg (BitVec 64) :=
.seq crepBody375_2 crepBody375_9

def crepBody375_11 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.var 5) crepBody375_10

def crepBody375_12 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 4) crepBody375_11

def crepBody375_13 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 3) crepBody375_12

def crepBody375_14 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 2) crepBody375_13

def crepBody375_15 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64]) crepBody375_14

def crepBody375_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody375_17 : CrepProg (BitVec 64) :=
.seq crepBody375_15 crepBody375_16

def crepBody375_18 : CrepProg (BitVec 64) :=
.seq crepBody375_1 crepBody375_17

def crepBody375_19 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody375_18

def crepBody375_20 : CrepProg (BitVec 64) :=
.seq crepBody375_0 crepBody375_19

def crepBody375_21 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody375_20

def data375 : CrepProg (BitVec 64) := crepBody375_21
def output375 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [97#8, 100#8, 100#8, 95#8, 98#8, 97#8, 108#8, 97#8, 110#8, 99#8, 101#8, 95#8, 99#8, 104#8, 97#8, 110#8, 103#8, 101#8], [0, 1, 2, 3, 4, 5], crepProgToHOL data375)
end InitECandidate.Proofs.FrontendStages.Crep
