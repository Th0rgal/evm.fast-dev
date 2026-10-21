import InitECandidate.Proofs.FrontendStages.Crep.Translate307
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody323_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.var 2)

def crepBody323_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody323_2 : CrepProg (BitVec 64) :=
.seq crepBody323_0 crepBody323_1

def crepBody323_3 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.sub
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.const 1#64]) crepBody323_2

def crepBody323_4 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 16#64]) crepBody323_3

def crepBody323_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "htab_set"
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 24#64])]

def crepBody323_6 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody323_5

def crepBody323_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "htab_del" [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]

def crepBody323_8 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody323_7

def crepBody323_9 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 16#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody323_6 crepBody323_8

def crepBody323_10 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 8#64])) crepBody323_9

def crepBody323_11 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.var 1)) crepBody323_10

def crepBody323_12 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 200#64]),
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 16#64]),
        Flapjack.CrepExp.const 32#64]]) crepBody323_11

def crepBody323_13 : CrepProg (BitVec 64) :=
.seq crepBody323_4 crepBody323_12

def crepBody323_14 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 0)
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 16#64]))) crepBody323_13

def crepBody323_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody323_16 : CrepProg (BitVec 64) :=
.seq crepBody323_14 crepBody323_15

def data323 : CrepProg (BitVec 64) := crepBody323_16
def output323 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [115#8, 116#8, 97#8, 116#8, 101#8, 95#8, 114#8, 101#8, 115#8, 116#8, 111#8, 114#8, 101#8], [0], crepProgToHOL data323)
end InitECandidate.Proofs.FrontendStages.Crep
