import InitECandidate.Proofs.FrontendStages.Crep.Translate669
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody685_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "heap_mark" []

def crepBody685_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 96#64]

def crepBody685_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "fp2_mul_xi"
  [Flapjack.CrepExp.var 3,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 192#64]]

def crepBody685_3 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody685_2

def crepBody685_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "fp2_copy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64]]

def crepBody685_5 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody685_4

def crepBody685_6 : CrepProg (BitVec 64) :=
.seq crepBody685_3 crepBody685_5

def crepBody685_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "fp2_copy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.var 1]

def crepBody685_8 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody685_7

def crepBody685_9 : CrepProg (BitVec 64) :=
.seq crepBody685_6 crepBody685_8

def crepBody685_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "fp2_copy" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3]

def crepBody685_11 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody685_10

def crepBody685_12 : CrepProg (BitVec 64) :=
.seq crepBody685_9 crepBody685_11

def crepBody685_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody685_14 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody685_13

def crepBody685_15 : CrepProg (BitVec 64) :=
.seq crepBody685_12 crepBody685_14

def crepBody685_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody685_17 : CrepProg (BitVec 64) :=
.seq crepBody685_15 crepBody685_16

def crepBody685_18 : CrepProg (BitVec 64) :=
.seq crepBody685_1 crepBody685_17

def crepBody685_19 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody685_18

def crepBody685_20 : CrepProg (BitVec 64) :=
.seq crepBody685_0 crepBody685_19

def crepBody685_21 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody685_20

def data685 : CrepProg (BitVec 64) := crepBody685_21
def output685 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 112#8, 54#8, 95#8, 109#8, 117#8, 108#8, 95#8, 118#8], [0, 1], crepProgToHOL data685)
end InitECandidate.Proofs.FrontendStages.Crep
