import InitECandidate.Proofs.FrontendStages.Crep.Translate763
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody779_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "heap_mark" []

def crepBody779_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64],
        Flapjack.CrepExp.const 8#64]]

def crepBody779_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "sha256"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 0,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 16#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 0,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 16#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 4,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 32#64]]]

def crepBody779_3 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody779_2

def crepBody779_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.var 6)

def crepBody779_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody779_6 : CrepProg (BitVec 64) :=
.seq crepBody779_4 crepBody779_5

def crepBody779_7 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 1#64]) crepBody779_6

def crepBody779_8 : CrepProg (BitVec 64) :=
.seq crepBody779_3 crepBody779_7

def crepBody779_9 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 1)) crepBody779_8

def crepBody779_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "sha256"
  [Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64],
    Flapjack.CrepExp.var 2]

def crepBody779_11 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody779_10

def crepBody779_12 : CrepProg (BitVec 64) :=
.seq crepBody779_9 crepBody779_11

def crepBody779_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "heap_release" [Flapjack.CrepExp.var 3]

def crepBody779_14 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody779_13

def crepBody779_15 : CrepProg (BitVec 64) :=
.seq crepBody779_12 crepBody779_14

def crepBody779_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody779_17 : CrepProg (BitVec 64) :=
.seq crepBody779_15 crepBody779_16

def crepBody779_18 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody779_17

def crepBody779_19 : CrepProg (BitVec 64) :=
.seq crepBody779_1 crepBody779_18

def crepBody779_20 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody779_19

def crepBody779_21 : CrepProg (BitVec 64) :=
.seq crepBody779_0 crepBody779_20

def crepBody779_22 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody779_21

def data779 : CrepProg (BitVec 64) := crepBody779_22
def output779 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [99#8, 111#8, 109#8, 112#8, 117#8, 116#8, 101#8, 95#8, 114#8, 101#8, 113#8, 117#8, 101#8, 115#8, 116#8, 115#8, 95#8,
    104#8, 97#8, 115#8, 104#8], [0, 1, 2], crepProgToHOL data779)
end InitECandidate.Proofs.FrontendStages.Crep
