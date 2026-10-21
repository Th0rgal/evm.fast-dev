import InitECandidate.Proofs.FrontendStages.Crep.Translate326
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody342_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "sk_make" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody342_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "htab_set"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
          Flapjack.CrepExp.const 24#64]),
    Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 1#64]

def crepBody342_2 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody342_1

def crepBody342_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3, 4], none)) "stor_lookup"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
          Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody342_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.load (Flapjack.CrepExp.var 4),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 24#64])]

def crepBody342_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody342_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 0#64)) crepBody342_4 crepBody342_5

def crepBody342_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3, 4], none)) "stor_lookup"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]),
          Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody342_8 : CrepProg (BitVec 64) :=
.seq crepBody342_6 crepBody342_7

def crepBody342_9 : CrepProg (BitVec 64) :=
.seq crepBody342_8 crepBody342_6

def crepBody342_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "record_pre_state_read" [Flapjack.CrepExp.var 0]

def crepBody342_11 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody342_10

def crepBody342_12 : CrepProg (BitVec 64) :=
.seq crepBody342_9 crepBody342_11

def crepBody342_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6, 7, 8], none)) "ws_get_storage" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody342_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody342_15 : CrepProg (BitVec 64) :=
.seq crepBody342_13 crepBody342_14

def crepBody342_16 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody342_15

def crepBody342_17 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody342_16

def crepBody342_18 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody342_17

def crepBody342_19 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody342_18

def crepBody342_20 : CrepProg (BitVec 64) :=
.seq crepBody342_12 crepBody342_19

def crepBody342_21 : CrepProg (BitVec 64) :=
.seq crepBody342_3 crepBody342_20

def crepBody342_22 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody342_21

def crepBody342_23 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody342_22

def crepBody342_24 : CrepProg (BitVec 64) :=
.seq crepBody342_2 crepBody342_23

def crepBody342_25 : CrepProg (BitVec 64) :=
.seq crepBody342_0 crepBody342_24

def crepBody342_26 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody342_25

def data342 : CrepProg (BitVec 64) := crepBody342_26
def output342 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [103#8, 101#8, 116#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8], [0, 1], crepProgToHOL data342)
end InitECandidate.Proofs.FrontendStages.Crep
