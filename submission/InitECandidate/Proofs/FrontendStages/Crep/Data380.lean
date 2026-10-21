import InitECandidate.Proofs.FrontendStages.Crep.Translate364
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody380_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2, 3], none)) "stor_lookup"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]),
          Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody380_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.load (Flapjack.CrepExp.var 3),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 24#64])]

def crepBody380_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody380_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody380_1 crepBody380_2

def crepBody380_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "record_pre_state_read" [Flapjack.CrepExp.var 0]

def crepBody380_5 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody380_4

def crepBody380_6 : CrepProg (BitVec 64) :=
.seq crepBody380_3 crepBody380_5

def crepBody380_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4, 5, 6, 7], none)) "ws_get_storage" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody380_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7]

def crepBody380_9 : CrepProg (BitVec 64) :=
.seq crepBody380_7 crepBody380_8

def crepBody380_10 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody380_9

def crepBody380_11 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody380_10

def crepBody380_12 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody380_11

def crepBody380_13 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody380_12

def crepBody380_14 : CrepProg (BitVec 64) :=
.seq crepBody380_6 crepBody380_13

def crepBody380_15 : CrepProg (BitVec 64) :=
.seq crepBody380_0 crepBody380_14

def crepBody380_16 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody380_15

def crepBody380_17 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody380_16

def data380 : CrepProg (BitVec 64) := crepBody380_17
def output380 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [103#8, 101#8, 116#8, 95#8, 112#8, 114#8, 101#8, 95#8, 116#8, 120#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8,
    101#8], [0, 1], crepProgToHOL data380)
end InitECandidate.Proofs.FrontendStages.Crep
