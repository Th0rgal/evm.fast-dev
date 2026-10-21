import InitECandidate.Proofs.FrontendStages.Crep.Translate235
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody251_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "scratch_mark" []

def crepBody251_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.loadGlob 0#5)

def crepBody251_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody251_3 : CrepProg (BitVec 64) :=
.seq crepBody251_1 crepBody251_2

def crepBody251_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "scratch_release" [Flapjack.CrepExp.var 4]

def crepBody251_5 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody251_4

def crepBody251_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 7)

def crepBody251_7 : CrepProg (BitVec 64) :=
.seq crepBody251_6 crepBody251_2

def crepBody251_8 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 5) crepBody251_7

def crepBody251_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 5#64

def crepBody251_10 : CrepProg (BitVec 64) :=
.seq crepBody251_8 crepBody251_9

def crepBody251_11 : CrepProg (BitVec 64) :=
.seq crepBody251_5 crepBody251_10

def crepBody251_12 : CrepProg (BitVec 64) :=
.seq crepBody251_3 crepBody251_11

def crepBody251_13 : CrepProg (BitVec 64) :=
.call (some (([6]), some ((5#64), crepBody251_12))) ("_mpt_delete_node_body") ([Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3])

def crepBody251_14 : CrepProg (BitVec 64) :=
.seq crepBody251_13 crepBody251_5

def crepBody251_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 6]

def crepBody251_16 : CrepProg (BitVec 64) :=
.seq crepBody251_14 crepBody251_15

def crepBody251_17 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody251_16

def crepBody251_18 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody251_17

def crepBody251_19 : CrepProg (BitVec 64) :=
.seq crepBody251_0 crepBody251_18

def crepBody251_20 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody251_19

def data251 : CrepProg (BitVec 64) := crepBody251_20
def output251 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [95#8, 109#8, 112#8, 116#8, 95#8, 100#8, 101#8, 108#8, 101#8, 116#8, 101#8, 95#8, 110#8, 111#8, 100#8, 101#8], [0, 1, 2, 3], crepProgToHOL data251)
end InitECandidate.Proofs.FrontendStages.Crep
