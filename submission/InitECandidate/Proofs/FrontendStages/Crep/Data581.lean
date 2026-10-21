import InitECandidate.Proofs.FrontendStages.Crep.Translate565
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody581_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.var 10)

def crepBody581_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 11)

def crepBody581_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 12)

def crepBody581_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 13)

def crepBody581_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody581_5 : CrepProg (BitVec 64) :=
.seq crepBody581_3 crepBody581_4

def crepBody581_6 : CrepProg (BitVec 64) :=
.seq crepBody581_2 crepBody581_5

def crepBody581_7 : CrepProg (BitVec 64) :=
.seq crepBody581_1 crepBody581_6

def crepBody581_8 : CrepProg (BitVec 64) :=
.seq crepBody581_0 crepBody581_7

def crepBody581_9 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.var 4) crepBody581_8

def crepBody581_10 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.var 3) crepBody581_9

def crepBody581_11 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 2) crepBody581_10

def crepBody581_12 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 1) crepBody581_11

def crepBody581_13 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 0) crepBody581_12

def crepBody581_14 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.var 8) crepBody581_8

def crepBody581_15 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.var 7) crepBody581_14

def crepBody581_16 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 6) crepBody581_15

def crepBody581_17 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 5) crepBody581_16

def crepBody581_18 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64]) crepBody581_17

def crepBody581_19 : CrepProg (BitVec 64) :=
.seq crepBody581_13 crepBody581_18

def crepBody581_20 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody581_8

def crepBody581_21 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody581_20

def crepBody581_22 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody581_21

def crepBody581_23 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 1#64) crepBody581_22

def crepBody581_24 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 64#64]) crepBody581_23

def crepBody581_25 : CrepProg (BitVec 64) :=
.seq crepBody581_19 crepBody581_24

def crepBody581_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody581_27 : CrepProg (BitVec 64) :=
.seq crepBody581_25 crepBody581_26

def data581 : CrepProg (BitVec 64) := crepBody581_27
def output581 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 50#8, 53#8, 54#8, 95#8, 115#8, 101#8, 116#8, 95#8, 97#8, 102#8, 102#8, 105#8, 110#8, 101#8], [0, 1, 2, 3, 4, 5, 6, 7, 8], crepProgToHOL data581)
end InitECandidate.Proofs.FrontendStages.Crep
