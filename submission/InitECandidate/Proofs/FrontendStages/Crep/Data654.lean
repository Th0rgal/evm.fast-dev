import InitECandidate.Proofs.FrontendStages.Crep.Translate638
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody654_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 15 (Flapjack.CrepExp.var 16)

def crepBody654_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody654_2 : CrepProg (BitVec 64) :=
.seq crepBody654_0 crepBody654_1

def crepBody654_3 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 1#64]) crepBody654_2

def crepBody654_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8, 9, 10, 11, 12, 13], none)) "bls_fp_mul"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11,
    Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9,
    Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13]

def crepBody654_5 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 14) (Flapjack.CrepExp.const 1#64)) crepBody654_4 crepBody654_1

def crepBody654_6 : CrepProg (BitVec 64) :=
.seq crepBody654_3 crepBody654_5

def crepBody654_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8, 9, 10, 11, 12, 13], none)) "bls_fp_mul"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11,
    Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1,
    Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody654_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 14 (Flapjack.CrepExp.const 1#64)

def crepBody654_9 : CrepProg (BitVec 64) :=
.seq crepBody654_8 crepBody654_1

def crepBody654_10 : CrepProg (BitVec 64) :=
.seq crepBody654_7 crepBody654_9

def crepBody654_11 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 16) (Flapjack.CrepExp.const 1#64)) crepBody654_10 crepBody654_1

def crepBody654_12 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.shift Flapjack.Shift.lsr
      (Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 6,
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
              [Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 15) (Flapjack.CrepExp.const 6#64),
                Flapjack.CrepExp.const 8#64]]))
      (Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 63#64]),
    Flapjack.CrepExp.const 1#64]) crepBody654_11

def crepBody654_13 : CrepProg (BitVec 64) :=
.seq crepBody654_6 crepBody654_12

def crepBody654_14 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 0#64) (Flapjack.CrepExp.var 15)) crepBody654_13

def crepBody654_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11,
    Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13]

def crepBody654_16 : CrepProg (BitVec 64) :=
.seq crepBody654_14 crepBody654_15

def crepBody654_17 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 64#64]) crepBody654_16

def crepBody654_18 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody654_17

def crepBody654_19 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 1582556514881692819#64) crepBody654_18

def crepBody654_20 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 6631298214892334189#64) crepBody654_19

def crepBody654_21 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 8632934651105793861#64) crepBody654_20

def crepBody654_22 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 6865905132761471162#64) crepBody654_21

def crepBody654_23 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 17002214543764226050#64) crepBody654_22

def crepBody654_24 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 8505329371266088957#64) crepBody654_23

def data654 : CrepProg (BitVec 64) := crepBody654_24
def output654 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [98#8, 108#8, 115#8, 95#8, 102#8, 112#8, 95#8, 112#8, 111#8, 119#8], [0, 1, 2, 3, 4, 5, 6, 7], crepProgToHOL data654)
end InitECandidate.Proofs.FrontendStages.Crep
