import InitECandidate.Proofs.FrontendStages.Crep.Translate209
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody225_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 2 (Flapjack.CrepExp.var 3)

def crepBody225_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody225_2 : CrepProg (BitVec 64) :=
.seq crepBody225_0 crepBody225_1

def crepBody225_3 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 2#64]) crepBody225_2

def crepBody225_4 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 2)
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 1],
      Flapjack.CrepExp.const 2#64])) crepBody225_3

def crepBody225_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "htab_new" [Flapjack.CrepExp.const 32#64, Flapjack.CrepExp.var 2]

def crepBody225_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "keccak256"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 0,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 16#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 0,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 16#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 152#64])]

def crepBody225_7 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody225_6

def crepBody225_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "htab_set"
  [Flapjack.CrepExp.var 3,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 152#64]),
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 0,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 16#64]]]

def crepBody225_9 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody225_8

def crepBody225_10 : CrepProg (BitVec 64) :=
.seq crepBody225_7 crepBody225_9

def crepBody225_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.var 5)

def crepBody225_12 : CrepProg (BitVec 64) :=
.seq crepBody225_11 crepBody225_1

def crepBody225_13 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 1#64]) crepBody225_12

def crepBody225_14 : CrepProg (BitVec 64) :=
.seq crepBody225_10 crepBody225_13

def crepBody225_15 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.var 1)) crepBody225_14

def crepBody225_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 3]

def crepBody225_17 : CrepProg (BitVec 64) :=
.seq crepBody225_15 crepBody225_16

def crepBody225_18 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody225_17

def crepBody225_19 : CrepProg (BitVec 64) :=
.seq crepBody225_5 crepBody225_18

def crepBody225_20 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody225_19

def crepBody225_21 : CrepProg (BitVec 64) :=
.seq crepBody225_4 crepBody225_20

def crepBody225_22 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 4#64) crepBody225_21

def data225 : CrepProg (BitVec 64) := crepBody225_22
def output225 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [110#8, 111#8, 100#8, 101#8, 100#8, 98#8, 95#8, 98#8, 117#8, 105#8, 108#8, 100#8], [0, 1], crepProgToHOL data225)
end InitECandidate.Proofs.FrontendStages.Crep
