import InitECandidate.Proofs.FrontendStages.Crep.Translate213
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody229_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 56#64]

def crepBody229_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.var 5)

def crepBody229_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody229_3 : CrepProg (BitVec 64) :=
.seq crepBody229_1 crepBody229_2

def crepBody229_4 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 2#64) crepBody229_3

def crepBody229_5 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 0#64]) crepBody229_4

def crepBody229_6 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody229_3

def crepBody229_7 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 8#64]) crepBody229_6

def crepBody229_8 : CrepProg (BitVec 64) :=
.seq crepBody229_5 crepBody229_7

def crepBody229_9 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 16#64]) crepBody229_6

def crepBody229_10 : CrepProg (BitVec 64) :=
.seq crepBody229_8 crepBody229_9

def crepBody229_11 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 24#64]) crepBody229_6

def crepBody229_12 : CrepProg (BitVec 64) :=
.seq crepBody229_10 crepBody229_11

def crepBody229_13 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.var 0) crepBody229_3

def crepBody229_14 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 32#64]) crepBody229_13

def crepBody229_15 : CrepProg (BitVec 64) :=
.seq crepBody229_12 crepBody229_14

def crepBody229_16 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.var 1) crepBody229_3

def crepBody229_17 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 40#64]) crepBody229_16

def crepBody229_18 : CrepProg (BitVec 64) :=
.seq crepBody229_15 crepBody229_17

def crepBody229_19 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.var 2) crepBody229_3

def crepBody229_20 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 48#64]) crepBody229_19

def crepBody229_21 : CrepProg (BitVec 64) :=
.seq crepBody229_18 crepBody229_20

def crepBody229_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 3]

def crepBody229_23 : CrepProg (BitVec 64) :=
.seq crepBody229_21 crepBody229_22

def crepBody229_24 : CrepProg (BitVec 64) :=
.seq crepBody229_0 crepBody229_23

def crepBody229_25 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody229_24

def data229 : CrepProg (BitVec 64) := crepBody229_25
def output229 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [110#8, 111#8, 100#8, 101#8, 95#8, 110#8, 101#8, 119#8, 95#8, 101#8, 120#8, 116#8], [0, 1, 2], crepProgToHOL data229)
end InitECandidate.Proofs.FrontendStages.Crep
