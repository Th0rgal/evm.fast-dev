import InitECandidate.Proofs.FrontendStages.Crep.Translate728
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody744_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "heap_mark" []

def crepBody744_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 288#64]

def crepBody744_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc" [Flapjack.CrepExp.const 288#64]

def crepBody744_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "g2_decode" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3]

def crepBody744_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "g2_decode"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 256#64],
    Flapjack.CrepExp.var 4]

def crepBody744_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody744_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 1#64)) crepBody744_4 crepBody744_5

def crepBody744_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody744_8 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody744_7

def crepBody744_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1#64]

def crepBody744_10 : CrepProg (BitVec 64) :=
.seq crepBody744_8 crepBody744_9

def crepBody744_11 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64)) crepBody744_10 crepBody744_5

def crepBody744_12 : CrepProg (BitVec 64) :=
.seq crepBody744_6 crepBody744_11

def crepBody744_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "g2_add"
  [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody744_14 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody744_13

def crepBody744_15 : CrepProg (BitVec 64) :=
.seq crepBody744_12 crepBody744_14

def crepBody744_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "g2_encode" [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 1]

def crepBody744_17 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody744_16

def crepBody744_18 : CrepProg (BitVec 64) :=
.seq crepBody744_15 crepBody744_17

def crepBody744_19 : CrepProg (BitVec 64) :=
.seq crepBody744_18 crepBody744_8

def crepBody744_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody744_21 : CrepProg (BitVec 64) :=
.seq crepBody744_19 crepBody744_20

def crepBody744_22 : CrepProg (BitVec 64) :=
.seq crepBody744_3 crepBody744_21

def crepBody744_23 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody744_22

def crepBody744_24 : CrepProg (BitVec 64) :=
.seq crepBody744_2 crepBody744_23

def crepBody744_25 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody744_24

def crepBody744_26 : CrepProg (BitVec 64) :=
.seq crepBody744_1 crepBody744_25

def crepBody744_27 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody744_26

def crepBody744_28 : CrepProg (BitVec 64) :=
.seq crepBody744_0 crepBody744_27

def crepBody744_29 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody744_28

def data744 : CrepProg (BitVec 64) := crepBody744_29
def output744 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [98#8, 108#8, 115#8, 95#8, 103#8, 50#8, 95#8, 97#8, 100#8, 100#8, 95#8, 101#8, 120#8, 101#8, 99#8], [0, 1], crepProgToHOL data744)
end InitECandidate.Proofs.FrontendStages.Crep
