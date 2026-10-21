import InitECandidate.Proofs.FrontendStages.Crep.Translate382
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody398_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "st_be32" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 2]

def crepBody398_1 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody398_0

def crepBody398_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "st_be64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 4#64], Flapjack.CrepExp.var 1]

def crepBody398_3 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody398_2

def crepBody398_4 : CrepProg (BitVec 64) :=
.seq crepBody398_1 crepBody398_3

def crepBody398_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "st_be64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 12#64],
    Flapjack.CrepExp.var 0]

def crepBody398_6 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody398_5

def crepBody398_7 : CrepProg (BitVec 64) :=
.seq crepBody398_4 crepBody398_6

def crepBody398_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 4]

def crepBody398_9 : CrepProg (BitVec 64) :=
.seq crepBody398_7 crepBody398_8

def crepBody398_10 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 240#64]) crepBody398_9

def data398 : CrepProg (BitVec 64) := crepBody398_10
def output398 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [116#8, 111#8, 95#8, 97#8, 100#8, 100#8, 114#8, 101#8, 115#8, 115#8, 95#8, 109#8, 97#8, 115#8, 107#8, 101#8, 100#8], [0, 1, 2, 3], crepProgToHOL data398)
end InitECandidate.Proofs.FrontendStages.Crep
