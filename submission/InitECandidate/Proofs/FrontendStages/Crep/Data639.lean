import InitECandidate.Proofs.FrontendStages.Crep.Translate623
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody639_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1#64]

def crepBody639_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody639_2 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 11)) crepBody639_0 crepBody639_1

def crepBody639_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody639_4 : CrepProg (BitVec 64) :=
.seq crepBody639_2 crepBody639_3

def crepBody639_5 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 11)) crepBody639_4 crepBody639_1

def crepBody639_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.var 10)) crepBody639_0 crepBody639_1

def crepBody639_7 : CrepProg (BitVec 64) :=
.seq crepBody639_6 crepBody639_3

def crepBody639_8 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.var 10)) crepBody639_7 crepBody639_1

def crepBody639_9 : CrepProg (BitVec 64) :=
.seq crepBody639_5 crepBody639_8

def crepBody639_10 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 9)) crepBody639_0 crepBody639_1

def crepBody639_11 : CrepProg (BitVec 64) :=
.seq crepBody639_10 crepBody639_3

def crepBody639_12 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 9)) crepBody639_11 crepBody639_1

def crepBody639_13 : CrepProg (BitVec 64) :=
.seq crepBody639_9 crepBody639_12

def crepBody639_14 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.var 8)) crepBody639_0 crepBody639_1

def crepBody639_15 : CrepProg (BitVec 64) :=
.seq crepBody639_14 crepBody639_3

def crepBody639_16 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.var 8)) crepBody639_15 crepBody639_1

def crepBody639_17 : CrepProg (BitVec 64) :=
.seq crepBody639_13 crepBody639_16

def crepBody639_18 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.var 7)) crepBody639_0 crepBody639_1

def crepBody639_19 : CrepProg (BitVec 64) :=
.seq crepBody639_18 crepBody639_3

def crepBody639_20 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.var 7)) crepBody639_19 crepBody639_1

def crepBody639_21 : CrepProg (BitVec 64) :=
.seq crepBody639_17 crepBody639_20

def crepBody639_22 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.var 6)) crepBody639_0 crepBody639_1

def crepBody639_23 : CrepProg (BitVec 64) :=
.seq crepBody639_21 crepBody639_22

def crepBody639_24 : CrepProg (BitVec 64) :=
.seq crepBody639_23 crepBody639_3

def data639 : CrepProg (BitVec 64) := crepBody639_24
def output639 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [98#8, 108#8, 115#8, 95#8, 102#8, 112#8, 95#8, 108#8, 116#8, 95#8, 114#8, 97#8, 119#8], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], crepProgToHOL data639)
end InitECandidate.Proofs.FrontendStages.Crep
