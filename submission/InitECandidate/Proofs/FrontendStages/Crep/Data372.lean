import InitECandidate.Proofs.FrontendStages.Crep.Translate356
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody372_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 4,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 1]]]

def crepBody372_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody372_2 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 4,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 1]]))
  (Flapjack.CrepExp.var 2)) crepBody372_0 crepBody372_1

def crepBody372_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.var 6)

def crepBody372_4 : CrepProg (BitVec 64) :=
.seq crepBody372_3 crepBody372_1

def crepBody372_5 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 1#64]) crepBody372_4

def crepBody372_6 : CrepProg (BitVec 64) :=
.seq crepBody372_2 crepBody372_5

def crepBody372_7 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 3)) crepBody372_6

def crepBody372_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "lst_push" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody372_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.var 8)

def crepBody372_10 : CrepProg (BitVec 64) :=
.seq crepBody372_9 crepBody372_1

def crepBody372_11 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 2) crepBody372_10

def crepBody372_12 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 6) crepBody372_11

def crepBody372_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 6]

def crepBody372_14 : CrepProg (BitVec 64) :=
.seq crepBody372_12 crepBody372_13

def crepBody372_15 : CrepProg (BitVec 64) :=
.seq crepBody372_8 crepBody372_14

def crepBody372_16 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody372_15

def crepBody372_17 : CrepProg (BitVec 64) :=
.seq crepBody372_7 crepBody372_16

def crepBody372_18 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody372_17

def crepBody372_19 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64])) crepBody372_18

def crepBody372_20 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64])) crepBody372_19

def data372 : CrepProg (BitVec 64) := crepBody372_20
def output372 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [108#8, 115#8, 116#8, 95#8, 117#8, 112#8, 115#8, 101#8, 114#8, 116#8, 95#8, 105#8, 100#8, 120#8], [0, 1, 2], crepProgToHOL data372)
end InitECandidate.Proofs.FrontendStages.Crep
