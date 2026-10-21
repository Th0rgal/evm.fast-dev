import InitECandidate.Proofs.FrontendStages.Crep.Translate702
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody718_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "heap_mark" []

def crepBody718_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 96#64]

def crepBody718_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc" [Flapjack.CrepExp.const 96#64]

def crepBody718_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "fp2_sqr" [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 1]

def crepBody718_4 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody718_3

def crepBody718_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "fp2_sqr" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 0]

def crepBody718_6 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody718_5

def crepBody718_7 : CrepProg (BitVec 64) :=
.seq crepBody718_4 crepBody718_6

def crepBody718_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "fp2_mul"
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 0]

def crepBody718_9 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody718_8

def crepBody718_10 : CrepProg (BitVec 64) :=
.seq crepBody718_7 crepBody718_9

def crepBody718_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "fp2_add"
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
        Flapjack.CrepExp.const 288#64]]

def crepBody718_12 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody718_11

def crepBody718_13 : CrepProg (BitVec 64) :=
.seq crepBody718_10 crepBody718_12

def crepBody718_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "fp2_eq" [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody718_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody718_16 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody718_15

def crepBody718_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 5]

def crepBody718_18 : CrepProg (BitVec 64) :=
.seq crepBody718_16 crepBody718_17

def crepBody718_19 : CrepProg (BitVec 64) :=
.seq crepBody718_14 crepBody718_18

def crepBody718_20 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody718_19

def crepBody718_21 : CrepProg (BitVec 64) :=
.seq crepBody718_13 crepBody718_20

def crepBody718_22 : CrepProg (BitVec 64) :=
.seq crepBody718_2 crepBody718_21

def crepBody718_23 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody718_22

def crepBody718_24 : CrepProg (BitVec 64) :=
.seq crepBody718_1 crepBody718_23

def crepBody718_25 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody718_24

def crepBody718_26 : CrepProg (BitVec 64) :=
.seq crepBody718_0 crepBody718_25

def crepBody718_27 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody718_26

def data718 : CrepProg (BitVec 64) := crepBody718_27
def output718 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [103#8, 50#8, 95#8, 111#8, 110#8, 95#8, 99#8, 117#8, 114#8, 118#8, 101#8], [0, 1], crepProgToHOL data718)
end InitECandidate.Proofs.FrontendStages.Crep
