import InitECandidate.Proofs.FrontendStages.Crep.Translate274
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody290_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "u256_byte_length"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]

def crepBody290_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1#64]

def crepBody290_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody290_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 0#64)) crepBody290_1 crepBody290_2

def crepBody290_4 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 128#64)) crepBody290_1 crepBody290_2

def crepBody290_5 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 1#64)) crepBody290_4 crepBody290_2

def crepBody290_6 : CrepProg (BitVec 64) :=
.seq crepBody290_3 crepBody290_5

def crepBody290_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.var 4]]

def crepBody290_8 : CrepProg (BitVec 64) :=
.seq crepBody290_6 crepBody290_7

def crepBody290_9 : CrepProg (BitVec 64) :=
.seq crepBody290_0 crepBody290_8

def crepBody290_10 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody290_9

def data290 : CrepProg (BitVec 64) := crepBody290_10
def output290 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [116#8, 120#8, 95#8, 117#8, 50#8, 53#8, 54#8, 95#8, 101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 100#8, 95#8, 108#8,
    101#8, 110#8], [0, 1, 2, 3], crepProgToHOL data290)
end InitECandidate.Proofs.FrontendStages.Crep
