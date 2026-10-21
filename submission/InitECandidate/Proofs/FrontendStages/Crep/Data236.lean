import InitECandidate.Proofs.FrontendStages.Crep.Translate220
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody236_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "scratch_mark" []

def crepBody236_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.loadGlob 0#5)

def crepBody236_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody236_3 : CrepProg (BitVec 64) :=
.seq crepBody236_1 crepBody236_2

def crepBody236_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "scratch_release" [Flapjack.CrepExp.var 3]

def crepBody236_5 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody236_4

def crepBody236_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 6)

def crepBody236_7 : CrepProg (BitVec 64) :=
.seq crepBody236_6 crepBody236_2

def crepBody236_8 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 4) crepBody236_7

def crepBody236_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 1#64

def crepBody236_10 : CrepProg (BitVec 64) :=
.seq crepBody236_8 crepBody236_9

def crepBody236_11 : CrepProg (BitVec 64) :=
.seq crepBody236_5 crepBody236_10

def crepBody236_12 : CrepProg (BitVec 64) :=
.seq crepBody236_3 crepBody236_11

def crepBody236_13 : CrepProg (BitVec 64) :=
.call (some (([5]), some ((1#64), crepBody236_12))) ("_decode_witness_node_mpt") ([Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3])

def crepBody236_14 : CrepProg (BitVec 64) :=
.seq crepBody236_13 crepBody236_5

def crepBody236_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 5]

def crepBody236_16 : CrepProg (BitVec 64) :=
.seq crepBody236_14 crepBody236_15

def crepBody236_17 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody236_16

def crepBody236_18 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody236_17

def crepBody236_19 : CrepProg (BitVec 64) :=
.seq crepBody236_0 crepBody236_18

def crepBody236_20 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody236_19

def data236 : CrepProg (BitVec 64) := crepBody236_20
def output236 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [95#8, 100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 119#8, 105#8, 116#8, 110#8, 101#8, 115#8, 115#8, 95#8, 110#8,
    111#8, 100#8, 101#8], [0, 1, 2], crepProgToHOL data236)
end InitECandidate.Proofs.FrontendStages.Crep
