import InitECandidate.Proofs.FrontendStages.Crep.Translate251
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody267_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3, 4, 5, 6], none)) "rlp_item"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 0,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 16#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 0,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 16#64],
          Flapjack.CrepExp.const 8#64])]

def crepBody267_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 7)

def crepBody267_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody267_3 : CrepProg (BitVec 64) :=
.seq crepBody267_1 crepBody267_2

def crepBody267_4 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 10#64) crepBody267_3

def crepBody267_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 6#64

def crepBody267_6 : CrepProg (BitVec 64) :=
.seq crepBody267_4 crepBody267_5

def crepBody267_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 0#64)) crepBody267_6 crepBody267_2

def crepBody267_8 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 11#64) crepBody267_3

def crepBody267_9 : CrepProg (BitVec 64) :=
.seq crepBody267_8 crepBody267_5

def crepBody267_10 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.loadByte (Flapjack.CrepExp.var 4))
  (Flapjack.CrepExp.const 0#64)) crepBody267_9 crepBody267_2

def crepBody267_11 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 0#64) (Flapjack.CrepExp.var 5)) crepBody267_10 crepBody267_2

def crepBody267_12 : CrepProg (BitVec 64) :=
.seq crepBody267_7 crepBody267_11

def crepBody267_13 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 12#64) crepBody267_3

def crepBody267_14 : CrepProg (BitVec 64) :=
.seq crepBody267_13 crepBody267_5

def crepBody267_15 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.var 5)) crepBody267_14 crepBody267_2

def crepBody267_16 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody267_15 crepBody267_2

def crepBody267_17 : CrepProg (BitVec 64) :=
.seq crepBody267_12 crepBody267_16

def crepBody267_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody267_19 : CrepProg (BitVec 64) :=
.seq crepBody267_17 crepBody267_18

def crepBody267_20 : CrepProg (BitVec 64) :=
.seq crepBody267_0 crepBody267_19

def crepBody267_21 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody267_20

def crepBody267_22 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody267_21

def crepBody267_23 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody267_22

def crepBody267_24 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody267_23

def data267 : CrepProg (BitVec 64) := crepBody267_24
def output267 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [116#8, 120#8, 95#8, 115#8, 99#8, 97#8, 108#8, 97#8, 114#8, 95#8, 105#8, 116#8, 101#8, 109#8], [0, 1, 2], crepProgToHOL data267)
end InitECandidate.Proofs.FrontendStages.Crep
