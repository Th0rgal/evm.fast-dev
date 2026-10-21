import InitECandidate.Proofs.FrontendStages.Crep.Translate212
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody228_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc" [Flapjack.CrepExp.const 64#64]

def crepBody228_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 6)

def crepBody228_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody228_3 : CrepProg (BitVec 64) :=
.seq crepBody228_1 crepBody228_2

def crepBody228_4 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 1#64) crepBody228_3

def crepBody228_5 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 0#64]) crepBody228_4

def crepBody228_6 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody228_3

def crepBody228_7 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 8#64]) crepBody228_6

def crepBody228_8 : CrepProg (BitVec 64) :=
.seq crepBody228_5 crepBody228_7

def crepBody228_9 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 16#64]) crepBody228_6

def crepBody228_10 : CrepProg (BitVec 64) :=
.seq crepBody228_8 crepBody228_9

def crepBody228_11 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 24#64]) crepBody228_6

def crepBody228_12 : CrepProg (BitVec 64) :=
.seq crepBody228_10 crepBody228_11

def crepBody228_13 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 0) crepBody228_3

def crepBody228_14 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 32#64]) crepBody228_13

def crepBody228_15 : CrepProg (BitVec 64) :=
.seq crepBody228_12 crepBody228_14

def crepBody228_16 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 1) crepBody228_3

def crepBody228_17 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 40#64]) crepBody228_16

def crepBody228_18 : CrepProg (BitVec 64) :=
.seq crepBody228_15 crepBody228_17

def crepBody228_19 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 2) crepBody228_3

def crepBody228_20 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 48#64]) crepBody228_19

def crepBody228_21 : CrepProg (BitVec 64) :=
.seq crepBody228_18 crepBody228_20

def crepBody228_22 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 3) crepBody228_3

def crepBody228_23 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 56#64]) crepBody228_22

def crepBody228_24 : CrepProg (BitVec 64) :=
.seq crepBody228_21 crepBody228_23

def crepBody228_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 4]

def crepBody228_26 : CrepProg (BitVec 64) :=
.seq crepBody228_24 crepBody228_25

def crepBody228_27 : CrepProg (BitVec 64) :=
.seq crepBody228_0 crepBody228_26

def crepBody228_28 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody228_27

def data228 : CrepProg (BitVec 64) := crepBody228_28
def output228 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [110#8, 111#8, 100#8, 101#8, 95#8, 110#8, 101#8, 119#8, 95#8, 108#8, 101#8, 97#8, 102#8], [0, 1, 2, 3], crepProgToHOL data228)
end InitECandidate.Proofs.FrontendStages.Crep
