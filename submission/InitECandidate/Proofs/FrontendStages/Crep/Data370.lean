import InitECandidate.Proofs.FrontendStages.Crep.Translate354
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody370_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "htab_new" [Flapjack.CrepExp.const 20#64, Flapjack.CrepExp.const 64#64]

def crepBody370_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.var 3)

def crepBody370_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody370_3 : CrepProg (BitVec 64) :=
.seq crepBody370_1 crepBody370_2

def crepBody370_4 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.var 1) crepBody370_3

def crepBody370_5 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 216#64]) crepBody370_4

def crepBody370_6 : CrepProg (BitVec 64) :=
.seq crepBody370_0 crepBody370_5

def crepBody370_7 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody370_6

def crepBody370_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "htab_new" [Flapjack.CrepExp.const 28#64, Flapjack.CrepExp.const 64#64]

def crepBody370_9 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 232#64]) crepBody370_4

def crepBody370_10 : CrepProg (BitVec 64) :=
.seq crepBody370_8 crepBody370_9

def crepBody370_11 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody370_10

def crepBody370_12 : CrepProg (BitVec 64) :=
.seq crepBody370_7 crepBody370_11

def crepBody370_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "htab_new" [Flapjack.CrepExp.const 60#64, Flapjack.CrepExp.const 64#64]

def crepBody370_14 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 240#64]) crepBody370_4

def crepBody370_15 : CrepProg (BitVec 64) :=
.seq crepBody370_13 crepBody370_14

def crepBody370_16 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody370_15

def crepBody370_17 : CrepProg (BitVec 64) :=
.seq crepBody370_12 crepBody370_16

def crepBody370_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "alloc" [Flapjack.CrepExp.const 64#64]

def crepBody370_19 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 248#64]) crepBody370_4

def crepBody370_20 : CrepProg (BitVec 64) :=
.seq crepBody370_18 crepBody370_19

def crepBody370_21 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody370_20

def crepBody370_22 : CrepProg (BitVec 64) :=
.seq crepBody370_17 crepBody370_21

def crepBody370_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.var 2)

def crepBody370_24 : CrepProg (BitVec 64) :=
.seq crepBody370_23 crepBody370_2

def crepBody370_25 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody370_24

def crepBody370_26 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 224#64]) crepBody370_25

def crepBody370_27 : CrepProg (BitVec 64) :=
.seq crepBody370_22 crepBody370_26

def crepBody370_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody370_29 : CrepProg (BitVec 64) :=
.seq crepBody370_27 crepBody370_28

def data370 : CrepProg (BitVec 64) := crepBody370_29
def output370 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [98#8, 97#8, 108#8, 95#8, 105#8, 110#8, 105#8, 116#8], [], crepProgToHOL data370)
end InitECandidate.Proofs.FrontendStages.Crep
