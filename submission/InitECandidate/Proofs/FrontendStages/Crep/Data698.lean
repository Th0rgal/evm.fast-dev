import InitECandidate.Proofs.FrontendStages.Crep.Translate682
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody698_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.var 2)

def crepBody698_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 3)

def crepBody698_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 4)

def crepBody698_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 5)

def crepBody698_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64])
  (Flapjack.CrepExp.var 6)

def crepBody698_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 40#64])
  (Flapjack.CrepExp.var 7)

def crepBody698_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody698_7 : CrepProg (BitVec 64) :=
.seq crepBody698_5 crepBody698_6

def crepBody698_8 : CrepProg (BitVec 64) :=
.seq crepBody698_4 crepBody698_7

def crepBody698_9 : CrepProg (BitVec 64) :=
.seq crepBody698_3 crepBody698_8

def crepBody698_10 : CrepProg (BitVec 64) :=
.seq crepBody698_2 crepBody698_9

def crepBody698_11 : CrepProg (BitVec 64) :=
.seq crepBody698_1 crepBody698_10

def crepBody698_12 : CrepProg (BitVec 64) :=
.seq crepBody698_0 crepBody698_11

def crepBody698_13 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 1582556514881692819#64) crepBody698_12

def crepBody698_14 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 6631298214892334189#64) crepBody698_13

def crepBody698_15 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 8632934651105793861#64) crepBody698_14

def crepBody698_16 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 6865905132761471162#64) crepBody698_15

def crepBody698_17 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 17002214543764226050#64) crepBody698_16

def crepBody698_18 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 8505329371266088957#64) crepBody698_17

def crepBody698_19 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.var 0) crepBody698_18

def crepBody698_20 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64]) crepBody698_18

def crepBody698_21 : CrepProg (BitVec 64) :=
.seq crepBody698_19 crepBody698_20

def crepBody698_22 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody698_12

def crepBody698_23 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody698_22

def crepBody698_24 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody698_23

def crepBody698_25 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody698_24

def crepBody698_26 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody698_25

def crepBody698_27 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody698_26

def crepBody698_28 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 96#64]) crepBody698_27

def crepBody698_29 : CrepProg (BitVec 64) :=
.seq crepBody698_21 crepBody698_28

def crepBody698_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody698_31 : CrepProg (BitVec 64) :=
.seq crepBody698_29 crepBody698_30

def data698 : CrepProg (BitVec 64) := crepBody698_31
def output698 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [103#8, 49#8, 95#8, 115#8, 101#8, 116#8, 95#8, 105#8, 110#8, 102#8], [0], crepProgToHOL data698)
end InitECandidate.Proofs.FrontendStages.Crep
