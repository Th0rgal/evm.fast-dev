import InitECandidate.Proofs.FrontendStages.Crep.Translate229
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody245_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "memeq"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 6]

def crepBody245_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.var 9)

def crepBody245_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody245_3 : CrepProg (BitVec 64) :=
.seq crepBody245_1 crepBody245_2

def crepBody245_4 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 3) crepBody245_3

def crepBody245_5 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64]) crepBody245_4

def crepBody245_6 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 4) crepBody245_3

def crepBody245_7 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 56#64]) crepBody245_6

def crepBody245_8 : CrepProg (BitVec 64) :=
.seq crepBody245_5 crepBody245_7

def crepBody245_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 0]

def crepBody245_10 : CrepProg (BitVec 64) :=
.seq crepBody245_8 crepBody245_9

def crepBody245_11 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 0#64)) crepBody245_10 crepBody245_2

def crepBody245_12 : CrepProg (BitVec 64) :=
.seq crepBody245_0 crepBody245_11

def crepBody245_13 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody245_12

def crepBody245_14 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 2)) crepBody245_13 crepBody245_2

def crepBody245_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "common_prefix_length"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2]

def crepBody245_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "_create_branch_from_two_leaves"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 7],
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7],
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 56#64]),
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 7],
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 7], Flapjack.CrepExp.var 3,
    Flapjack.CrepExp.var 4]

def crepBody245_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call none "node_new_ext" [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody245_18 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 0#64) (Flapjack.CrepExp.var 7)) crepBody245_17 crepBody245_2

def crepBody245_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 8]

def crepBody245_20 : CrepProg (BitVec 64) :=
.seq crepBody245_18 crepBody245_19

def crepBody245_21 : CrepProg (BitVec 64) :=
.seq crepBody245_16 crepBody245_20

def crepBody245_22 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody245_21

def crepBody245_23 : CrepProg (BitVec 64) :=
.seq crepBody245_15 crepBody245_22

def crepBody245_24 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody245_23

def crepBody245_25 : CrepProg (BitVec 64) :=
.seq crepBody245_14 crepBody245_24

def crepBody245_26 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 40#64])) crepBody245_25

def crepBody245_27 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64])) crepBody245_26

def data245 : CrepProg (BitVec 64) := crepBody245_27
def output245 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [95#8, 105#8, 110#8, 115#8, 101#8, 114#8, 116#8, 95#8, 105#8, 110#8, 116#8, 111#8, 95#8, 108#8, 101#8, 97#8, 102#8], [0, 1, 2, 3, 4], crepProgToHOL data245)
end InitECandidate.Proofs.FrontendStages.Crep
