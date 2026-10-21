import InitECandidate.Proofs.FrontendStages.Crep.Translate309
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody325_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "alloc" [Flapjack.CrepExp.const 56#64]

def crepBody325_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.var 8)

def crepBody325_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody325_3 : CrepProg (BitVec 64) :=
.seq crepBody325_1 crepBody325_2

def crepBody325_4 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 0) crepBody325_3

def crepBody325_5 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 0#64]) crepBody325_4

def crepBody325_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 9)

def crepBody325_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 10)

def crepBody325_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 11)

def crepBody325_9 : CrepProg (BitVec 64) :=
.seq crepBody325_8 crepBody325_2

def crepBody325_10 : CrepProg (BitVec 64) :=
.seq crepBody325_7 crepBody325_9

def crepBody325_11 : CrepProg (BitVec 64) :=
.seq crepBody325_6 crepBody325_10

def crepBody325_12 : CrepProg (BitVec 64) :=
.seq crepBody325_1 crepBody325_11

def crepBody325_13 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 4) crepBody325_12

def crepBody325_14 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 3) crepBody325_13

def crepBody325_15 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 2) crepBody325_14

def crepBody325_16 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 1) crepBody325_15

def crepBody325_17 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 8#64]) crepBody325_16

def crepBody325_18 : CrepProg (BitVec 64) :=
.seq crepBody325_5 crepBody325_17

def crepBody325_19 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 128#64])) crepBody325_3

def crepBody325_20 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 40#64]) crepBody325_19

def crepBody325_21 : CrepProg (BitVec 64) :=
.seq crepBody325_18 crepBody325_20

def crepBody325_22 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 5) crepBody325_3

def crepBody325_23 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 48#64]) crepBody325_22

def crepBody325_24 : CrepProg (BitVec 64) :=
.seq crepBody325_21 crepBody325_23

def crepBody325_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 6]

def crepBody325_26 : CrepProg (BitVec 64) :=
.seq crepBody325_24 crepBody325_25

def crepBody325_27 : CrepProg (BitVec 64) :=
.seq crepBody325_0 crepBody325_26

def crepBody325_28 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody325_27

def data325 : CrepProg (BitVec 64) := crepBody325_28
def output325 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [97#8, 99#8, 99#8, 116#8, 95#8, 110#8, 101#8, 119#8], [0, 1, 2, 3, 4, 5], crepProgToHOL data325)
end InitECandidate.Proofs.FrontendStages.Crep
