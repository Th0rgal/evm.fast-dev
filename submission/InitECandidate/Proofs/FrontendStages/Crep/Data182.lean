import InitECandidate.Proofs.FrontendStages.Crep.Translate166
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody182_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody182_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody182_2 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 0#64)) crepBody182_0 crepBody182_1

def crepBody182_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "ssz_fail" [Flapjack.CrepExp.const 10#64]

def crepBody182_4 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody182_3

def crepBody182_5 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 2),
      Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 5)])) crepBody182_4 crepBody182_1

def crepBody182_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "ssz_fail" [Flapjack.CrepExp.const 11#64]

def crepBody182_7 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody182_6

def crepBody182_8 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 5)
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.sub
      [Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0,
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 8#64]],
        Flapjack.CrepExp.const 8#64]))) crepBody182_7 crepBody182_1

def crepBody182_9 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.const 0#64) (Flapjack.CrepExp.var 4)) crepBody182_8 crepBody182_1

def crepBody182_10 : CrepProg (BitVec 64) :=
.seq crepBody182_5 crepBody182_9

def crepBody182_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.var 6)

def crepBody182_12 : CrepProg (BitVec 64) :=
.seq crepBody182_11 crepBody182_1

def crepBody182_13 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 1#64]) crepBody182_12

def crepBody182_14 : CrepProg (BitVec 64) :=
.seq crepBody182_10 crepBody182_13

def crepBody182_15 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 0,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 8#64]])) crepBody182_14

def crepBody182_16 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.var 1)) crepBody182_15

def crepBody182_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "ssz_fail" [Flapjack.CrepExp.const 12#64]

def crepBody182_18 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody182_17

def crepBody182_19 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.load (Flapjack.CrepExp.var 0)) (Flapjack.CrepExp.var 2)) crepBody182_18 crepBody182_1

def crepBody182_20 : CrepProg (BitVec 64) :=
.seq crepBody182_16 crepBody182_19

def crepBody182_21 : CrepProg (BitVec 64) :=
.seq crepBody182_20 crepBody182_0

def crepBody182_22 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody182_21

def crepBody182_23 : CrepProg (BitVec 64) :=
.seq crepBody182_2 crepBody182_22

def data182 : CrepProg (BitVec 64) := crepBody182_23
def output182 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [115#8, 115#8, 122#8, 95#8, 99#8, 104#8, 101#8, 99#8, 107#8, 95#8, 111#8, 102#8, 102#8, 115#8, 101#8, 116#8, 115#8], [0, 1, 2, 3], crepProgToHOL data182)
end InitECandidate.Proofs.FrontendStages.Crep
