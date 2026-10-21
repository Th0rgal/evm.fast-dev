import InitECandidate.Proofs.FrontendStages.Crep.Translate704
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody720_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "heap_mark" []

def crepBody720_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 192#64]

def crepBody720_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "g2_normalize" [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 0]

def crepBody720_3 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody720_2

def crepBody720_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "bls_fp_encode64" [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 1]

def crepBody720_5 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody720_4

def crepBody720_6 : CrepProg (BitVec 64) :=
.seq crepBody720_3 crepBody720_5

def crepBody720_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "bls_fp_encode64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 48#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 64#64]]

def crepBody720_8 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody720_7

def crepBody720_9 : CrepProg (BitVec 64) :=
.seq crepBody720_6 crepBody720_8

def crepBody720_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "bls_fp_encode64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 128#64]]

def crepBody720_11 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody720_10

def crepBody720_12 : CrepProg (BitVec 64) :=
.seq crepBody720_9 crepBody720_11

def crepBody720_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "bls_fp_encode64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 144#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 192#64]]

def crepBody720_14 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody720_13

def crepBody720_15 : CrepProg (BitVec 64) :=
.seq crepBody720_12 crepBody720_14

def crepBody720_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody720_17 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody720_16

def crepBody720_18 : CrepProg (BitVec 64) :=
.seq crepBody720_15 crepBody720_17

def crepBody720_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody720_20 : CrepProg (BitVec 64) :=
.seq crepBody720_18 crepBody720_19

def crepBody720_21 : CrepProg (BitVec 64) :=
.seq crepBody720_1 crepBody720_20

def crepBody720_22 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody720_21

def crepBody720_23 : CrepProg (BitVec 64) :=
.seq crepBody720_0 crepBody720_22

def crepBody720_24 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody720_23

def data720 : CrepProg (BitVec 64) := crepBody720_24
def output720 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [103#8, 50#8, 95#8, 101#8, 110#8, 99#8, 111#8, 100#8, 101#8], [0, 1], crepProgToHOL data720)
end InitECandidate.Proofs.FrontendStages.Crep
