import InitECandidate.Proofs.FrontendStages.Crep.Translate247
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody263_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "memcpy"
  [Flapjack.CrepExp.var 1,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 128#64]),
    Flapjack.CrepExp.const 32#64]

def crepBody263_1 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody263_0

def crepBody263_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody263_3 : CrepProg (BitVec 64) :=
.seq crepBody263_1 crepBody263_2

def crepBody263_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody263_5 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody263_3 crepBody263_4

def crepBody263_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "node_hash" [Flapjack.CrepExp.var 2]

def crepBody263_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "memcpy"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 32#64]

def crepBody263_8 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody263_7

def crepBody263_9 : CrepProg (BitVec 64) :=
.seq crepBody263_8 crepBody263_2

def crepBody263_10 : CrepProg (BitVec 64) :=
.seq crepBody263_6 crepBody263_9

def crepBody263_11 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody263_10

def crepBody263_12 : CrepProg (BitVec 64) :=
.seq crepBody263_5 crepBody263_11

def crepBody263_13 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64])) crepBody263_12

def data263 : CrepProg (BitVec 64) := crepBody263_13
def output263 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [109#8, 112#8, 116#8, 95#8, 114#8, 111#8, 111#8, 116#8], [0, 1], crepProgToHOL data263)
end InitECandidate.Proofs.FrontendStages.Crep
