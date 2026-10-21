import InitECandidate.Proofs.FrontendStages.Crep.Translate701
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody717_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "heap_mark" []

def crepBody717_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 96#64]

def crepBody717_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "g2_is_inf" [Flapjack.CrepExp.var 1]

def crepBody717_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "memzero" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 192#64]

def crepBody717_4 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody717_3

def crepBody717_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody717_6 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody717_5

def crepBody717_7 : CrepProg (BitVec 64) :=
.seq crepBody717_4 crepBody717_6

def crepBody717_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody717_9 : CrepProg (BitVec 64) :=
.seq crepBody717_7 crepBody717_8

def crepBody717_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody717_11 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 1#64)) crepBody717_9 crepBody717_10

def crepBody717_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "fp2_inv"
  [Flapjack.CrepExp.var 3,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 192#64]]

def crepBody717_13 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody717_12

def crepBody717_14 : CrepProg (BitVec 64) :=
.seq crepBody717_11 crepBody717_13

def crepBody717_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "fp2_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 3]

def crepBody717_16 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody717_15

def crepBody717_17 : CrepProg (BitVec 64) :=
.seq crepBody717_14 crepBody717_16

def crepBody717_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "fp2_mul"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.var 3]

def crepBody717_19 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody717_18

def crepBody717_20 : CrepProg (BitVec 64) :=
.seq crepBody717_17 crepBody717_19

def crepBody717_21 : CrepProg (BitVec 64) :=
.seq crepBody717_20 crepBody717_6

def crepBody717_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1#64]

def crepBody717_23 : CrepProg (BitVec 64) :=
.seq crepBody717_21 crepBody717_22

def crepBody717_24 : CrepProg (BitVec 64) :=
.seq crepBody717_2 crepBody717_23

def crepBody717_25 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody717_24

def crepBody717_26 : CrepProg (BitVec 64) :=
.seq crepBody717_1 crepBody717_25

def crepBody717_27 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody717_26

def crepBody717_28 : CrepProg (BitVec 64) :=
.seq crepBody717_0 crepBody717_27

def crepBody717_29 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody717_28

def data717 : CrepProg (BitVec 64) := crepBody717_29
def output717 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [103#8, 50#8, 95#8, 110#8, 111#8, 114#8, 109#8, 97#8, 108#8, 105#8, 122#8, 101#8], [0, 1], crepProgToHOL data717)
end InitECandidate.Proofs.FrontendStages.Crep
