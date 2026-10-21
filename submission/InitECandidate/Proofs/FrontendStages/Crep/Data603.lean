import InitECandidate.Proofs.FrontendStages.Crep.Translate587
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody603_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "fq12_sqr" [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2]

def crepBody603_1 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody603_0

def crepBody603_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody603_3 : CrepProg (BitVec 64) :=
.seq crepBody603_1 crepBody603_2

def crepBody603_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody603_5 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 12#64)) crepBody603_3 crepBody603_4

def crepBody603_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 2]

def crepBody603_7 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody603_6

def crepBody603_8 : CrepProg (BitVec 64) :=
.seq crepBody603_5 crepBody603_7

def crepBody603_9 : CrepProg (BitVec 64) :=
.seq crepBody603_8 crepBody603_2

def data603 : CrepProg (BitVec 64) := crepBody603_9
def output603 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 101#8, 95#8, 115#8, 113#8, 114#8], [0, 1, 2], crepProgToHOL data603)
end InitECandidate.Proofs.FrontendStages.Crep
