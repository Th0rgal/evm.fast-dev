import InitECandidate.Proofs.FrontendStages.Crep.Translate608
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody624_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "fe_set_one" [Flapjack.CrepExp.const 12#64, Flapjack.CrepExp.var 0]

def crepBody624_1 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody624_0

def crepBody624_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.var 6)

def crepBody624_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody624_4 : CrepProg (BitVec 64) :=
.seq crepBody624_2 crepBody624_3

def crepBody624_5 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 1#64]) crepBody624_4

def crepBody624_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "fq12_sqr" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 0]

def crepBody624_7 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody624_6

def crepBody624_8 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 1#64)) crepBody624_7 crepBody624_3

def crepBody624_9 : CrepProg (BitVec 64) :=
.seq crepBody624_5 crepBody624_8

def crepBody624_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "fq12_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody624_11 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody624_10

def crepBody624_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.const 1#64)

def crepBody624_13 : CrepProg (BitVec 64) :=
.seq crepBody624_12 crepBody624_3

def crepBody624_14 : CrepProg (BitVec 64) :=
.seq crepBody624_11 crepBody624_13

def crepBody624_15 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 1#64)) crepBody624_14 crepBody624_3

def crepBody624_16 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.shift Flapjack.Shift.lsr
      (Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 2,
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
              [Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 6#64),
                Flapjack.CrepExp.const 8#64]]))
      (Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 63#64]),
    Flapjack.CrepExp.const 1#64]) crepBody624_15

def crepBody624_17 : CrepProg (BitVec 64) :=
.seq crepBody624_9 crepBody624_16

def crepBody624_18 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 0#64) (Flapjack.CrepExp.var 5)) crepBody624_17

def crepBody624_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody624_20 : CrepProg (BitVec 64) :=
.seq crepBody624_18 crepBody624_19

def crepBody624_21 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 64#64]) crepBody624_20

def crepBody624_22 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody624_21

def crepBody624_23 : CrepProg (BitVec 64) :=
.seq crepBody624_1 crepBody624_22

def data624 : CrepProg (BitVec 64) := crepBody624_23
def output624 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [102#8, 113#8, 49#8, 50#8, 95#8, 112#8, 111#8, 119#8, 95#8, 119#8, 111#8, 114#8, 100#8, 115#8], [0, 1, 2, 3], crepProgToHOL data624)
end InitECandidate.Proofs.FrontendStages.Crep
