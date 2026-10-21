import InitECandidate.Proofs.FrontendStages.Crep.Translate767
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody783_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "st_be32" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody783_1 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody783_0

def crepBody783_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "st_be64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 4#64], Flapjack.CrepExp.var 2]

def crepBody783_3 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody783_2

def crepBody783_4 : CrepProg (BitVec 64) :=
.seq crepBody783_1 crepBody783_3

def crepBody783_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "st_be64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 12#64],
    Flapjack.CrepExp.var 3]

def crepBody783_6 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody783_5

def crepBody783_7 : CrepProg (BitVec 64) :=
.seq crepBody783_4 crepBody783_6

def crepBody783_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody783_9 : CrepProg (BitVec 64) :=
.seq crepBody783_7 crepBody783_8

def data783 : CrepProg (BitVec 64) := crepBody783_9
def output783 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [97#8, 100#8, 100#8, 114#8, 95#8, 102#8, 114#8, 111#8, 109#8, 95#8, 119#8, 111#8, 114#8, 100#8, 115#8], [0, 1, 2, 3], crepProgToHOL data783)
end InitECandidate.Proofs.FrontendStages.Crep
