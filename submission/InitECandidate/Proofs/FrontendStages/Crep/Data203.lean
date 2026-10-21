import InitECandidate.Proofs.FrontendStages.Crep.Translate187
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody203_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3, 4], none)) "hdr_uint_field"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2]

def crepBody203_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 5)

def crepBody203_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody203_3 : CrepProg (BitVec 64) :=
.seq crepBody203_1 crepBody203_2

def crepBody203_4 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 5#64) crepBody203_3

def crepBody203_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 3#64

def crepBody203_6 : CrepProg (BitVec 64) :=
.seq crepBody203_4 crepBody203_5

def crepBody203_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 32#64) (Flapjack.CrepExp.var 4)) crepBody203_6 crepBody203_2

def crepBody203_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6, 7, 8], none)) "u256_from_be" [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody203_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody203_10 : CrepProg (BitVec 64) :=
.seq crepBody203_8 crepBody203_9

def crepBody203_11 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody203_10

def crepBody203_12 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody203_11

def crepBody203_13 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody203_12

def crepBody203_14 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody203_13

def crepBody203_15 : CrepProg (BitVec 64) :=
.seq crepBody203_7 crepBody203_14

def crepBody203_16 : CrepProg (BitVec 64) :=
.seq crepBody203_0 crepBody203_15

def crepBody203_17 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody203_16

def crepBody203_18 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody203_17

def data203 : CrepProg (BitVec 64) := crepBody203_18
def output203 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [104#8, 100#8, 114#8, 95#8, 117#8, 50#8, 53#8, 54#8, 95#8, 102#8, 105#8, 101#8, 108#8, 100#8], [0, 1, 2], crepProgToHOL data203)
end InitECandidate.Proofs.FrontendStages.Crep
