import InitECandidate.Proofs.FrontendStages.Crep.Translate512
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody528_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "frame_new" [Flapjack.CrepExp.var 0]

def crepBody528_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "scratch_alloc" [Flapjack.CrepExp.const 104#64]

def crepBody528_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "memzero" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 104#64]

def crepBody528_3 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody528_2

def crepBody528_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 6)

def crepBody528_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody528_6 : CrepProg (BitVec 64) :=
.seq crepBody528_4 crepBody528_5

def crepBody528_7 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 2) crepBody528_6

def crepBody528_8 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 0#64]) crepBody528_7

def crepBody528_9 : CrepProg (BitVec 64) :=
.seq crepBody528_3 crepBody528_8

def crepBody528_10 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 288#64])) crepBody528_6

def crepBody528_11 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 8#64]) crepBody528_10

def crepBody528_12 : CrepProg (BitVec 64) :=
.seq crepBody528_9 crepBody528_11

def crepBody528_13 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 1) crepBody528_6

def crepBody528_14 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 16#64]) crepBody528_13

def crepBody528_15 : CrepProg (BitVec 64) :=
.seq crepBody528_12 crepBody528_14

def crepBody528_16 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 0) crepBody528_6

def crepBody528_17 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 40#64]) crepBody528_16

def crepBody528_18 : CrepProg (BitVec 64) :=
.seq crepBody528_15 crepBody528_17

def crepBody528_19 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 3) crepBody528_6

def crepBody528_20 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]) crepBody528_19

def crepBody528_21 : CrepProg (BitVec 64) :=
.seq crepBody528_18 crepBody528_20

def crepBody528_22 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 4) crepBody528_6

def crepBody528_23 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 288#64]) crepBody528_22

def crepBody528_24 : CrepProg (BitVec 64) :=
.seq crepBody528_21 crepBody528_23

def crepBody528_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 3]

def crepBody528_26 : CrepProg (BitVec 64) :=
.seq crepBody528_24 crepBody528_25

def crepBody528_27 : CrepProg (BitVec 64) :=
.seq crepBody528_1 crepBody528_26

def crepBody528_28 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody528_27

def crepBody528_29 : CrepProg (BitVec 64) :=
.seq crepBody528_0 crepBody528_28

def crepBody528_30 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody528_29

def crepBody528_31 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64])) crepBody528_30

def data528 : CrepProg (BitVec 64) := crepBody528_31
def output528 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 114#8, 97#8, 109#8, 101#8, 95#8, 111#8, 112#8, 101#8, 110#8], [0, 1], crepProgToHOL data528)
end InitECandidate.Proofs.FrontendStages.Crep
