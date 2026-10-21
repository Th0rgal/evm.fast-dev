import InitECandidate.Proofs.FrontendStages.Crep.Translate242
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody258_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 2 (Flapjack.CrepExp.loadByte (Flapjack.CrepExp.var 0))

def crepBody258_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody258_2 : CrepProg (BitVec 64) :=
.seq crepBody258_0 crepBody258_1

def crepBody258_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 0#64) (Flapjack.CrepExp.var 1)) crepBody258_2 crepBody258_1

def crepBody258_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call none "rlp_bytes_encoded_len" [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 1]

def crepBody258_5 : CrepProg (BitVec 64) :=
.seq crepBody258_3 crepBody258_4

def crepBody258_6 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody258_5

def data258 : CrepProg (BitVec 64) := crepBody258_6
def output258 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [114#8, 108#8, 112#8, 95#8, 118#8, 97#8, 108#8, 117#8, 101#8, 95#8, 101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 100#8,
    95#8, 108#8, 101#8, 110#8], [0, 1], crepProgToHOL data258)
end InitECandidate.Proofs.FrontendStages.Crep
