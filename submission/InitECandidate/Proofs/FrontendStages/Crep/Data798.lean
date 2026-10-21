import InitECandidate.Proofs.FrontendStages.Crep.Translate782
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody798_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 8#64]]

def crepBody798_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 0)

def crepBody798_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64], Flapjack.CrepExp.var 1,
    Flapjack.CrepExp.var 2]

def crepBody798_3 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody798_2

def crepBody798_4 : CrepProg (BitVec 64) :=
.seq crepBody798_1 crepBody798_3

def crepBody798_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 6)

def crepBody798_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody798_7 : CrepProg (BitVec 64) :=
.seq crepBody798_5 crepBody798_6

def crepBody798_8 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 3) crepBody798_7

def crepBody798_9 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 416#64]),
          Flapjack.CrepExp.const 56#64]),
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 16#64]]) crepBody798_8

def crepBody798_10 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 1#64]) crepBody798_7

def crepBody798_11 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 416#64]),
          Flapjack.CrepExp.const 56#64]),
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 16#64],
    Flapjack.CrepExp.const 8#64]) crepBody798_10

def crepBody798_12 : CrepProg (BitVec 64) :=
.seq crepBody798_9 crepBody798_11

def crepBody798_13 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 1#64]) crepBody798_7

def crepBody798_14 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 416#64]),
    Flapjack.CrepExp.const 64#64]) crepBody798_13

def crepBody798_15 : CrepProg (BitVec 64) :=
.seq crepBody798_12 crepBody798_14

def crepBody798_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody798_17 : CrepProg (BitVec 64) :=
.seq crepBody798_15 crepBody798_16

def crepBody798_18 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 416#64]),
      Flapjack.CrepExp.const 64#64])) crepBody798_17

def crepBody798_19 : CrepProg (BitVec 64) :=
.seq crepBody798_4 crepBody798_18

def crepBody798_20 : CrepProg (BitVec 64) :=
.seq crepBody798_0 crepBody798_19

def crepBody798_21 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody798_20

def data798 : CrepProg (BitVec 64) := crepBody798_21
def output798 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [114#8, 101#8, 113#8, 117#8, 101#8, 115#8, 116#8, 115#8, 95#8, 97#8, 112#8, 112#8, 101#8, 110#8, 100#8], [0, 1, 2], crepProgToHOL data798)
end InitECandidate.Proofs.FrontendStages.Crep
