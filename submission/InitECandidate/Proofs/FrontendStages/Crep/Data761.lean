import InitECandidate.Proofs.FrontendStages.Crep.Translate745
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody761_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "is_zero_bytes" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 18#64]

def crepBody761_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody761_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody761_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 0#64)) crepBody761_1 crepBody761_2

def crepBody761_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 18#64]

def crepBody761_5 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 0#64)) crepBody761_4 crepBody761_2

def crepBody761_6 : CrepProg (BitVec 64) :=
.seq crepBody761_5 crepBody761_1

def crepBody761_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 1#64)) crepBody761_6 crepBody761_2

def crepBody761_8 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody761_1 crepBody761_2

def crepBody761_9 : CrepProg (BitVec 64) :=
.seq crepBody761_7 crepBody761_8

def crepBody761_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 3]

def crepBody761_11 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 1#64)),
    Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.const 17#64) (Flapjack.CrepExp.var 3))]) crepBody761_10 crepBody761_2

def crepBody761_12 : CrepProg (BitVec 64) :=
.seq crepBody761_9 crepBody761_11

def crepBody761_13 : CrepProg (BitVec 64) :=
.seq crepBody761_12 crepBody761_1

def crepBody761_14 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.loadByte
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 19#64])) crepBody761_13

def crepBody761_15 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.loadByte
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 18#64])) crepBody761_14

def crepBody761_16 : CrepProg (BitVec 64) :=
.seq crepBody761_3 crepBody761_15

def crepBody761_17 : CrepProg (BitVec 64) :=
.seq crepBody761_0 crepBody761_16

def crepBody761_18 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody761_17

def data761 : CrepProg (BitVec 64) := crepBody761_18
def output761 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 114#8, 101#8, 99#8, 111#8, 109#8, 112#8, 105#8, 108#8, 101#8, 95#8, 105#8, 110#8, 100#8, 101#8, 120#8], [0], crepProgToHOL data761)
end InitECandidate.Proofs.FrontendStages.Crep
