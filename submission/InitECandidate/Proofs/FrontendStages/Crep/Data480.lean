import InitECandidate.Proofs.FrontendStages.Crep.Translate464
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody480_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "sk_make" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody480_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "htab_set"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
          Flapjack.CrepExp.const 176#64]),
    Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 1#64]

def crepBody480_2 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody480_1

def crepBody480_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody480_4 : CrepProg (BitVec 64) :=
.seq crepBody480_2 crepBody480_3

def crepBody480_5 : CrepProg (BitVec 64) :=
.seq crepBody480_0 crepBody480_4

def crepBody480_6 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody480_5

def data480 : CrepProg (BitVec 64) := crepBody480_6
def output480 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [119#8, 97#8, 114#8, 109#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8, 95#8, 107#8, 101#8, 121#8], [0, 1], crepProgToHOL data480)
end InitECandidate.Proofs.FrontendStages.Crep
