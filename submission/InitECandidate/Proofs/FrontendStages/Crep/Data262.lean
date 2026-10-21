import InitECandidate.Proofs.FrontendStages.Crep.Translate246
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody262_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 1]

def crepBody262_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody262_2 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 0#64)) crepBody262_0 crepBody262_1

def crepBody262_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2, 3], none)) "node_rlp" [Flapjack.CrepExp.var 0]

def crepBody262_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody262_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "keccak256"
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody262_6 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody262_5

def crepBody262_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 6)

def crepBody262_8 : CrepProg (BitVec 64) :=
.seq crepBody262_7 crepBody262_1

def crepBody262_9 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 4) crepBody262_8

def crepBody262_10 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 24#64]) crepBody262_9

def crepBody262_11 : CrepProg (BitVec 64) :=
.seq crepBody262_6 crepBody262_10

def crepBody262_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 4]

def crepBody262_13 : CrepProg (BitVec 64) :=
.seq crepBody262_11 crepBody262_12

def crepBody262_14 : CrepProg (BitVec 64) :=
.seq crepBody262_4 crepBody262_13

def crepBody262_15 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody262_14

def crepBody262_16 : CrepProg (BitVec 64) :=
.seq crepBody262_3 crepBody262_15

def crepBody262_17 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody262_16

def crepBody262_18 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody262_17

def crepBody262_19 : CrepProg (BitVec 64) :=
.seq crepBody262_2 crepBody262_18

def crepBody262_20 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 24#64])) crepBody262_19

def data262 : CrepProg (BitVec 64) := crepBody262_20
def output262 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [110#8, 111#8, 100#8, 101#8, 95#8, 104#8, 97#8, 115#8, 104#8], [0], crepProgToHOL data262)
end InitECandidate.Proofs.FrontendStages.Crep
