import InitECandidate.Proofs.FrontendStages.Crep.Translate618
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody634_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "charge_gas" [Flapjack.CrepExp.const 6000#64]

def crepBody634_1 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody634_0

def crepBody634_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "alloc" [Flapjack.CrepExp.const 64#64]

def crepBody634_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "heap_mark" []

def crepBody634_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc" [Flapjack.CrepExp.const 96#64]

def crepBody634_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "buffer_read"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 88#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64]),
    Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 96#64, Flapjack.CrepExp.var 4]

def crepBody634_6 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody634_5

def crepBody634_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "bn254_g1_mul" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 2]

def crepBody634_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "heap_release" [Flapjack.CrepExp.var 3]

def crepBody634_9 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody634_8

def crepBody634_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 6)

def crepBody634_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody634_12 : CrepProg (BitVec 64) :=
.seq crepBody634_10 crepBody634_11

def crepBody634_13 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 4#64) crepBody634_12

def crepBody634_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 8#64

def crepBody634_15 : CrepProg (BitVec 64) :=
.seq crepBody634_13 crepBody634_14

def crepBody634_16 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64)) crepBody634_15 crepBody634_11

def crepBody634_17 : CrepProg (BitVec 64) :=
.seq crepBody634_9 crepBody634_16

def crepBody634_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 7)

def crepBody634_19 : CrepProg (BitVec 64) :=
.seq crepBody634_18 crepBody634_11

def crepBody634_20 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 2) crepBody634_19

def crepBody634_21 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 120#64]) crepBody634_20

def crepBody634_22 : CrepProg (BitVec 64) :=
.seq crepBody634_17 crepBody634_21

def crepBody634_23 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 64#64) crepBody634_19

def crepBody634_24 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 128#64]) crepBody634_23

def crepBody634_25 : CrepProg (BitVec 64) :=
.seq crepBody634_22 crepBody634_24

def crepBody634_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody634_27 : CrepProg (BitVec 64) :=
.seq crepBody634_25 crepBody634_26

def crepBody634_28 : CrepProg (BitVec 64) :=
.seq crepBody634_7 crepBody634_27

def crepBody634_29 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody634_28

def crepBody634_30 : CrepProg (BitVec 64) :=
.seq crepBody634_6 crepBody634_29

def crepBody634_31 : CrepProg (BitVec 64) :=
.seq crepBody634_4 crepBody634_30

def crepBody634_32 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody634_31

def crepBody634_33 : CrepProg (BitVec 64) :=
.seq crepBody634_3 crepBody634_32

def crepBody634_34 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody634_33

def crepBody634_35 : CrepProg (BitVec 64) :=
.seq crepBody634_2 crepBody634_34

def crepBody634_36 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody634_35

def crepBody634_37 : CrepProg (BitVec 64) :=
.seq crepBody634_1 crepBody634_36

def crepBody634_38 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 112#64])) crepBody634_37

def data634 : CrepProg (BitVec 64) := crepBody634_38
def output634 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 114#8, 101#8, 95#8, 97#8, 108#8, 116#8, 95#8, 98#8, 110#8, 49#8, 50#8, 56#8, 95#8, 109#8, 117#8, 108#8], [], crepProgToHOL data634)
end InitECandidate.Proofs.FrontendStages.Crep
