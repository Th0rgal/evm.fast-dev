import InitECandidate.Proofs.FrontendStages.Crep.Translate647
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody663_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.var 2)

def crepBody663_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 3)

def crepBody663_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 4)

def crepBody663_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 5)

def crepBody663_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64])
  (Flapjack.CrepExp.var 6)

def crepBody663_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 40#64])
  (Flapjack.CrepExp.var 7)

def crepBody663_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody663_7 : CrepProg (BitVec 64) :=
.seq crepBody663_5 crepBody663_6

def crepBody663_8 : CrepProg (BitVec 64) :=
.seq crepBody663_4 crepBody663_7

def crepBody663_9 : CrepProg (BitVec 64) :=
.seq crepBody663_3 crepBody663_8

def crepBody663_10 : CrepProg (BitVec 64) :=
.seq crepBody663_2 crepBody663_9

def crepBody663_11 : CrepProg (BitVec 64) :=
.seq crepBody663_1 crepBody663_10

def crepBody663_12 : CrepProg (BitVec 64) :=
.seq crepBody663_0 crepBody663_11

def crepBody663_13 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 1582556514881692819#64) crepBody663_12

def crepBody663_14 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 6631298214892334189#64) crepBody663_13

def crepBody663_15 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 8632934651105793861#64) crepBody663_14

def crepBody663_16 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 6865905132761471162#64) crepBody663_15

def crepBody663_17 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 17002214543764226050#64) crepBody663_16

def crepBody663_18 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 8505329371266088957#64) crepBody663_17

def crepBody663_19 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.var 0) crepBody663_18

def crepBody663_20 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody663_12

def crepBody663_21 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody663_20

def crepBody663_22 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody663_21

def crepBody663_23 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody663_22

def crepBody663_24 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody663_23

def crepBody663_25 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody663_24

def crepBody663_26 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64]) crepBody663_25

def crepBody663_27 : CrepProg (BitVec 64) :=
.seq crepBody663_19 crepBody663_26

def crepBody663_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody663_29 : CrepProg (BitVec 64) :=
.seq crepBody663_27 crepBody663_28

def data663 : CrepProg (BitVec 64) := crepBody663_29
def output663 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 112#8, 50#8, 95#8, 115#8, 101#8, 116#8, 95#8, 111#8, 110#8, 101#8], [0], crepProgToHOL data663)
end InitECandidate.Proofs.FrontendStages.Crep
