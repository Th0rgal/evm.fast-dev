import InitECandidate.Proofs.FrontendStages.Crep.Translate726
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody742_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "heap_mark" []

def crepBody742_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 144#64]

def crepBody742_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc" [Flapjack.CrepExp.const 144#64]

def crepBody742_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "g1_decode" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3]

def crepBody742_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "g1_decode"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 128#64],
    Flapjack.CrepExp.var 4]

def crepBody742_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody742_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 1#64)) crepBody742_4 crepBody742_5

def crepBody742_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody742_8 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody742_7

def crepBody742_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1#64]

def crepBody742_10 : CrepProg (BitVec 64) :=
.seq crepBody742_8 crepBody742_9

def crepBody742_11 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64)) crepBody742_10 crepBody742_5

def crepBody742_12 : CrepProg (BitVec 64) :=
.seq crepBody742_6 crepBody742_11

def crepBody742_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "g1_add"
  [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody742_14 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody742_13

def crepBody742_15 : CrepProg (BitVec 64) :=
.seq crepBody742_12 crepBody742_14

def crepBody742_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "g1_encode" [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 1]

def crepBody742_17 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody742_16

def crepBody742_18 : CrepProg (BitVec 64) :=
.seq crepBody742_15 crepBody742_17

def crepBody742_19 : CrepProg (BitVec 64) :=
.seq crepBody742_18 crepBody742_8

def crepBody742_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody742_21 : CrepProg (BitVec 64) :=
.seq crepBody742_19 crepBody742_20

def crepBody742_22 : CrepProg (BitVec 64) :=
.seq crepBody742_3 crepBody742_21

def crepBody742_23 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody742_22

def crepBody742_24 : CrepProg (BitVec 64) :=
.seq crepBody742_2 crepBody742_23

def crepBody742_25 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody742_24

def crepBody742_26 : CrepProg (BitVec 64) :=
.seq crepBody742_1 crepBody742_25

def crepBody742_27 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody742_26

def crepBody742_28 : CrepProg (BitVec 64) :=
.seq crepBody742_0 crepBody742_27

def crepBody742_29 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody742_28

def data742 : CrepProg (BitVec 64) := crepBody742_29
def output742 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [98#8, 108#8, 115#8, 95#8, 103#8, 49#8, 95#8, 97#8, 100#8, 100#8, 95#8, 101#8, 120#8, 101#8, 99#8], [0, 1], crepProgToHOL data742)
end InitECandidate.Proofs.FrontendStages.Crep
