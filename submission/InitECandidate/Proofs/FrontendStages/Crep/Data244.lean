import InitECandidate.Proofs.FrontendStages.Crep.Translate228
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody244_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "node_new_branch" []

def crepBody244_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.var 10)

def crepBody244_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody244_3 : CrepProg (BitVec 64) :=
.seq crepBody244_1 crepBody244_2

def crepBody244_4 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 2) crepBody244_3

def crepBody244_5 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 160#64]) crepBody244_4

def crepBody244_6 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 3) crepBody244_3

def crepBody244_7 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 168#64]) crepBody244_6

def crepBody244_8 : CrepProg (BitVec 64) :=
.seq crepBody244_5 crepBody244_7

def crepBody244_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "node_new_leaf"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 1#64],
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 1#64],
    Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]

def crepBody244_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.var 11)

def crepBody244_11 : CrepProg (BitVec 64) :=
.seq crepBody244_10 crepBody244_2

def crepBody244_12 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 9) crepBody244_11

def crepBody244_13 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 32#64,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.loadByte (Flapjack.CrepExp.var 0), Flapjack.CrepExp.const 8#64]]) crepBody244_12

def crepBody244_14 : CrepProg (BitVec 64) :=
.seq crepBody244_9 crepBody244_13

def crepBody244_15 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody244_14

def crepBody244_16 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 0#64)) crepBody244_8 crepBody244_15

def crepBody244_17 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 6) crepBody244_3

def crepBody244_18 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 160#64]) crepBody244_17

def crepBody244_19 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 7) crepBody244_3

def crepBody244_20 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 168#64]) crepBody244_19

def crepBody244_21 : CrepProg (BitVec 64) :=
.seq crepBody244_18 crepBody244_20

def crepBody244_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "node_new_leaf"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 1#64],
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 1#64],
    Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7]

def crepBody244_23 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 32#64,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.loadByte (Flapjack.CrepExp.var 4), Flapjack.CrepExp.const 8#64]]) crepBody244_12

def crepBody244_24 : CrepProg (BitVec 64) :=
.seq crepBody244_22 crepBody244_23

def crepBody244_25 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody244_24

def crepBody244_26 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64)) crepBody244_21 crepBody244_25

def crepBody244_27 : CrepProg (BitVec 64) :=
.seq crepBody244_16 crepBody244_26

def crepBody244_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 8]

def crepBody244_29 : CrepProg (BitVec 64) :=
.seq crepBody244_27 crepBody244_28

def crepBody244_30 : CrepProg (BitVec 64) :=
.seq crepBody244_0 crepBody244_29

def crepBody244_31 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody244_30

def data244 : CrepProg (BitVec 64) := crepBody244_31
def output244 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [95#8, 99#8, 114#8, 101#8, 97#8, 116#8, 101#8, 95#8, 98#8, 114#8, 97#8, 110#8, 99#8, 104#8, 95#8, 102#8, 114#8, 111#8,
    109#8, 95#8, 116#8, 119#8, 111#8, 95#8, 108#8, 101#8, 97#8, 118#8, 101#8, 115#8], [0, 1, 2, 3, 4, 5, 6, 7], crepProgToHOL data244)
end InitECandidate.Proofs.FrontendStages.Crep
