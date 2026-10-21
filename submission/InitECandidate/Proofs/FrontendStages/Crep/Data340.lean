import InitECandidate.Proofs.FrontendStages.Crep.Translate324
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody340_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "memeq"
  [Flapjack.CrepExp.var 0,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 136#64]),
    Flapjack.CrepExp.const 32#64]

def crepBody340_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64]

def crepBody340_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody340_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody340_1 crepBody340_2

def crepBody340_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3, 4], none)) "htab_get"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
          Flapjack.CrepExp.const 48#64]),
    Flapjack.CrepExp.var 0]

def crepBody340_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.load (Flapjack.CrepExp.var 4),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 8#64])]

def crepBody340_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 0#64)) crepBody340_5 crepBody340_2

def crepBody340_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3, 4], none)) "htab_get"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]),
          Flapjack.CrepExp.const 48#64]),
    Flapjack.CrepExp.var 0]

def crepBody340_8 : CrepProg (BitVec 64) :=
.seq crepBody340_6 crepBody340_7

def crepBody340_9 : CrepProg (BitVec 64) :=
.seq crepBody340_8 crepBody340_6

def crepBody340_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "sk_make" [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 0]

def crepBody340_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "htab_set"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
          Flapjack.CrepExp.const 40#64]),
    Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 1#64]

def crepBody340_12 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody340_11

def crepBody340_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6, 7], none)) "ws_get_code" [Flapjack.CrepExp.var 0]

def crepBody340_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7]

def crepBody340_15 : CrepProg (BitVec 64) :=
.seq crepBody340_13 crepBody340_14

def crepBody340_16 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody340_15

def crepBody340_17 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody340_16

def crepBody340_18 : CrepProg (BitVec 64) :=
.seq crepBody340_12 crepBody340_17

def crepBody340_19 : CrepProg (BitVec 64) :=
.seq crepBody340_10 crepBody340_18

def crepBody340_20 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody340_19

def crepBody340_21 : CrepProg (BitVec 64) :=
.seq crepBody340_9 crepBody340_20

def crepBody340_22 : CrepProg (BitVec 64) :=
.seq crepBody340_4 crepBody340_21

def crepBody340_23 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody340_22

def crepBody340_24 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody340_23

def crepBody340_25 : CrepProg (BitVec 64) :=
.seq crepBody340_3 crepBody340_24

def crepBody340_26 : CrepProg (BitVec 64) :=
.seq crepBody340_0 crepBody340_25

def crepBody340_27 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody340_26

def data340 : CrepProg (BitVec 64) := crepBody340_27
def output340 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [103#8, 101#8, 116#8, 95#8, 99#8, 111#8, 100#8, 101#8], [0, 1], crepProgToHOL data340)
end InitECandidate.Proofs.FrontendStages.Crep
