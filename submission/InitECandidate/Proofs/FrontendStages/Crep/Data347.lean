import InitECandidate.Proofs.FrontendStages.Crep.Translate331
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody347_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "get_account" [Flapjack.CrepExp.var 0]

def crepBody347_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody347_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody347_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 0#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody347_1 crepBody347_2

def crepBody347_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "memeq"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 136#64]),
    Flapjack.CrepExp.const 32#64]

def crepBody347_5 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody347_1 crepBody347_2

def crepBody347_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "account_has_storage" [Flapjack.CrepExp.var 0]

def crepBody347_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 0#64)) crepBody347_1 crepBody347_2

def crepBody347_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1#64]

def crepBody347_9 : CrepProg (BitVec 64) :=
.seq crepBody347_7 crepBody347_8

def crepBody347_10 : CrepProg (BitVec 64) :=
.seq crepBody347_6 crepBody347_9

def crepBody347_11 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody347_10

def crepBody347_12 : CrepProg (BitVec 64) :=
.seq crepBody347_5 crepBody347_11

def crepBody347_13 : CrepProg (BitVec 64) :=
.seq crepBody347_4 crepBody347_12

def crepBody347_14 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody347_13

def crepBody347_15 : CrepProg (BitVec 64) :=
.seq crepBody347_3 crepBody347_14

def crepBody347_16 : CrepProg (BitVec 64) :=
.seq crepBody347_0 crepBody347_15

def crepBody347_17 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody347_16

def data347 : CrepProg (BitVec 64) := crepBody347_17
def output347 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8, 95#8, 100#8, 101#8, 112#8, 108#8, 111#8, 121#8, 97#8, 98#8, 108#8,
    101#8], [0], crepProgToHOL data347)
end InitECandidate.Proofs.FrontendStages.Crep
