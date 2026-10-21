import InitECandidate.Proofs.FrontendStages.Crep.Translate731
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody747_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "heap_mark" []

def crepBody747_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 48#64]

def crepBody747_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc" [Flapjack.CrepExp.const 144#64]

def crepBody747_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "bls_fp_decode64" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3]

def crepBody747_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody747_5 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody747_4

def crepBody747_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1#64]

def crepBody747_7 : CrepProg (BitVec 64) :=
.seq crepBody747_5 crepBody747_6

def crepBody747_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody747_9 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64)) crepBody747_7 crepBody747_8

def crepBody747_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "map_fp_to_g1"
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8,
    Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11]

def crepBody747_11 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody747_10

def crepBody747_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "g1_encode" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 1]

def crepBody747_13 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody747_12

def crepBody747_14 : CrepProg (BitVec 64) :=
.seq crepBody747_11 crepBody747_13

def crepBody747_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody747_16 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody747_15

def crepBody747_17 : CrepProg (BitVec 64) :=
.seq crepBody747_14 crepBody747_16

def crepBody747_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody747_19 : CrepProg (BitVec 64) :=
.seq crepBody747_17 crepBody747_18

def crepBody747_20 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 40#64])) crepBody747_19

def crepBody747_21 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 32#64])) crepBody747_20

def crepBody747_22 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 24#64])) crepBody747_21

def crepBody747_23 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 16#64])) crepBody747_22

def crepBody747_24 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 8#64])) crepBody747_23

def crepBody747_25 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load (Flapjack.CrepExp.var 3)) crepBody747_24

def crepBody747_26 : CrepProg (BitVec 64) :=
.seq crepBody747_9 crepBody747_25

def crepBody747_27 : CrepProg (BitVec 64) :=
.seq crepBody747_3 crepBody747_26

def crepBody747_28 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody747_27

def crepBody747_29 : CrepProg (BitVec 64) :=
.seq crepBody747_2 crepBody747_28

def crepBody747_30 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody747_29

def crepBody747_31 : CrepProg (BitVec 64) :=
.seq crepBody747_1 crepBody747_30

def crepBody747_32 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody747_31

def crepBody747_33 : CrepProg (BitVec 64) :=
.seq crepBody747_0 crepBody747_32

def crepBody747_34 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody747_33

def data747 : CrepProg (BitVec 64) := crepBody747_34
def output747 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [98#8, 108#8, 115#8, 95#8, 109#8, 97#8, 112#8, 95#8, 102#8, 112#8, 95#8, 116#8, 111#8, 95#8, 103#8, 49#8, 95#8, 101#8,
    120#8, 101#8, 99#8], [0, 1], crepProgToHOL data747)
end InitECandidate.Proofs.FrontendStages.Crep
