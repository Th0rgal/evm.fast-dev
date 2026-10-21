import InitECandidate.Proofs.FrontendStages.Crep.Translate703
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody719_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "bls_fp_decode64" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody719_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody719_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody719_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody719_1 crepBody719_2

def crepBody719_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "bls_fp_decode64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 64#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64]]

def crepBody719_5 : CrepProg (BitVec 64) :=
.seq crepBody719_3 crepBody719_4

def crepBody719_6 : CrepProg (BitVec 64) :=
.seq crepBody719_5 crepBody719_3

def crepBody719_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "bls_fp_decode64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 128#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64]]

def crepBody719_8 : CrepProg (BitVec 64) :=
.seq crepBody719_6 crepBody719_7

def crepBody719_9 : CrepProg (BitVec 64) :=
.seq crepBody719_8 crepBody719_3

def crepBody719_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "bls_fp_decode64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64, Flapjack.CrepExp.const 48#64]]

def crepBody719_11 : CrepProg (BitVec 64) :=
.seq crepBody719_9 crepBody719_10

def crepBody719_12 : CrepProg (BitVec 64) :=
.seq crepBody719_11 crepBody719_3

def crepBody719_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "fp2_is_zero" [Flapjack.CrepExp.var 1]

def crepBody719_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "fp2_is_zero"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64]]

def crepBody719_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "fp2_set_zero"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 192#64]]

def crepBody719_16 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody719_15

def crepBody719_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1#64]

def crepBody719_18 : CrepProg (BitVec 64) :=
.seq crepBody719_16 crepBody719_17

def crepBody719_19 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 1#64)),
    Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 1#64))]) crepBody719_18 crepBody719_2

def crepBody719_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "fp2_set_one"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 192#64]]

def crepBody719_21 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody719_20

def crepBody719_22 : CrepProg (BitVec 64) :=
.seq crepBody719_19 crepBody719_21

def crepBody719_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call none "g2_on_curve"
  [Flapjack.CrepExp.var 1,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64]]

def crepBody719_24 : CrepProg (BitVec 64) :=
.seq crepBody719_22 crepBody719_23

def crepBody719_25 : CrepProg (BitVec 64) :=
.seq crepBody719_14 crepBody719_24

def crepBody719_26 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody719_25

def crepBody719_27 : CrepProg (BitVec 64) :=
.seq crepBody719_13 crepBody719_26

def crepBody719_28 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody719_27

def crepBody719_29 : CrepProg (BitVec 64) :=
.seq crepBody719_12 crepBody719_28

def crepBody719_30 : CrepProg (BitVec 64) :=
.seq crepBody719_0 crepBody719_29

def crepBody719_31 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody719_30

def data719 : CrepProg (BitVec 64) := crepBody719_31
def output719 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [103#8, 50#8, 95#8, 100#8, 101#8, 99#8, 111#8, 100#8, 101#8], [0, 1], crepProgToHOL data719)
end InitECandidate.Proofs.FrontendStages.Crep
