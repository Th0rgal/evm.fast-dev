import InitECandidate.Proofs.FrontendStages.Crep.Translate210
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody226_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2, 3], none)) "htab_get" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody226_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64]

def crepBody226_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody226_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody226_1 crepBody226_2

def crepBody226_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.load (Flapjack.CrepExp.var 3),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 8#64])]

def crepBody226_5 : CrepProg (BitVec 64) :=
.seq crepBody226_3 crepBody226_4

def crepBody226_6 : CrepProg (BitVec 64) :=
.seq crepBody226_0 crepBody226_5

def crepBody226_7 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody226_6

def crepBody226_8 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody226_7

def data226 : CrepProg (BitVec 64) := crepBody226_8
def output226 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [110#8, 111#8, 100#8, 101#8, 100#8, 98#8, 95#8, 108#8, 111#8, 111#8, 107#8, 117#8, 112#8], [0, 1], crepProgToHOL data226)
end InitECandidate.Proofs.FrontendStages.Crep
