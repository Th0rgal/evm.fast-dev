import InitECandidate.Proofs.FrontendStages.Crep.Translate327
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody343_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "htab_has"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
          Flapjack.CrepExp.const 56#64]),
    Flapjack.CrepExp.var 0]

def crepBody343_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64]

def crepBody343_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody343_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody343_1 crepBody343_2

def crepBody343_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3, 4], none)) "stor_lookup"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]),
          Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody343_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.load (Flapjack.CrepExp.var 4),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 24#64])]

def crepBody343_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 0#64)) crepBody343_5 crepBody343_2

def crepBody343_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "record_pre_state_read" [Flapjack.CrepExp.var 0]

def crepBody343_8 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody343_7

def crepBody343_9 : CrepProg (BitVec 64) :=
.seq crepBody343_6 crepBody343_8

def crepBody343_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6, 7, 8], none)) "ws_get_storage" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody343_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody343_12 : CrepProg (BitVec 64) :=
.seq crepBody343_10 crepBody343_11

def crepBody343_13 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody343_12

def crepBody343_14 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody343_13

def crepBody343_15 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody343_14

def crepBody343_16 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody343_15

def crepBody343_17 : CrepProg (BitVec 64) :=
.seq crepBody343_9 crepBody343_16

def crepBody343_18 : CrepProg (BitVec 64) :=
.seq crepBody343_4 crepBody343_17

def crepBody343_19 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody343_18

def crepBody343_20 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody343_19

def crepBody343_21 : CrepProg (BitVec 64) :=
.seq crepBody343_3 crepBody343_20

def crepBody343_22 : CrepProg (BitVec 64) :=
.seq crepBody343_0 crepBody343_21

def crepBody343_23 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody343_22

def data343 : CrepProg (BitVec 64) := crepBody343_23
def output343 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [103#8, 101#8, 116#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8, 95#8, 111#8, 114#8, 105#8, 103#8, 105#8,
    110#8, 97#8, 108#8], [0, 1], crepProgToHOL data343)
end InitECandidate.Proofs.FrontendStages.Crep
