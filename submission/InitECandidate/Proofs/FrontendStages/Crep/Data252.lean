import InitECandidate.Proofs.FrontendStages.Crep.Translate236
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody252_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6], none)) "mpt_nibble_key"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2]

def crepBody252_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "_mpt_delete_node"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 0#64]

def crepBody252_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "_mpt_insert_node"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 0#64,
    Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody252_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 0#64),
      Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 0#64)])) crepBody252_1 crepBody252_2

def crepBody252_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.var 9)

def crepBody252_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody252_6 : CrepProg (BitVec 64) :=
.seq crepBody252_4 crepBody252_5

def crepBody252_7 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 7) crepBody252_6

def crepBody252_8 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64]) crepBody252_7

def crepBody252_9 : CrepProg (BitVec 64) :=
.seq crepBody252_3 crepBody252_8

def crepBody252_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody252_11 : CrepProg (BitVec 64) :=
.seq crepBody252_9 crepBody252_10

def crepBody252_12 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64])) crepBody252_11

def crepBody252_13 : CrepProg (BitVec 64) :=
.seq crepBody252_0 crepBody252_12

def crepBody252_14 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody252_13

def crepBody252_15 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody252_14

def data252 : CrepProg (BitVec 64) := crepBody252_15
def output252 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [109#8, 112#8, 116#8, 95#8, 115#8, 101#8, 116#8], [0, 1, 2, 3, 4], crepProgToHOL data252)
end InitECandidate.Proofs.FrontendStages.Crep
