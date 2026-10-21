import InitECandidate.Proofs.FrontendStages.Crep.Translate617
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody633_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "charge_gas" [Flapjack.CrepExp.const 150#64]

def crepBody633_1 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody633_0

def crepBody633_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "alloc" [Flapjack.CrepExp.const 64#64]

def crepBody633_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "heap_mark" []

def crepBody633_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc" [Flapjack.CrepExp.const 128#64]

def crepBody633_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "buffer_read"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 88#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64]),
    Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 128#64, Flapjack.CrepExp.var 4]

def crepBody633_6 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody633_5

def crepBody633_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "bn254_g1_add" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 2]

def crepBody633_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "heap_release" [Flapjack.CrepExp.var 3]

def crepBody633_9 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody633_8

def crepBody633_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 6)

def crepBody633_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody633_12 : CrepProg (BitVec 64) :=
.seq crepBody633_10 crepBody633_11

def crepBody633_13 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 4#64) crepBody633_12

def crepBody633_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 8#64

def crepBody633_15 : CrepProg (BitVec 64) :=
.seq crepBody633_13 crepBody633_14

def crepBody633_16 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64)) crepBody633_15 crepBody633_11

def crepBody633_17 : CrepProg (BitVec 64) :=
.seq crepBody633_9 crepBody633_16

def crepBody633_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 7)

def crepBody633_19 : CrepProg (BitVec 64) :=
.seq crepBody633_18 crepBody633_11

def crepBody633_20 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 2) crepBody633_19

def crepBody633_21 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 120#64]) crepBody633_20

def crepBody633_22 : CrepProg (BitVec 64) :=
.seq crepBody633_17 crepBody633_21

def crepBody633_23 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 64#64) crepBody633_19

def crepBody633_24 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 128#64]) crepBody633_23

def crepBody633_25 : CrepProg (BitVec 64) :=
.seq crepBody633_22 crepBody633_24

def crepBody633_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody633_27 : CrepProg (BitVec 64) :=
.seq crepBody633_25 crepBody633_26

def crepBody633_28 : CrepProg (BitVec 64) :=
.seq crepBody633_7 crepBody633_27

def crepBody633_29 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody633_28

def crepBody633_30 : CrepProg (BitVec 64) :=
.seq crepBody633_6 crepBody633_29

def crepBody633_31 : CrepProg (BitVec 64) :=
.seq crepBody633_4 crepBody633_30

def crepBody633_32 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody633_31

def crepBody633_33 : CrepProg (BitVec 64) :=
.seq crepBody633_3 crepBody633_32

def crepBody633_34 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody633_33

def crepBody633_35 : CrepProg (BitVec 64) :=
.seq crepBody633_2 crepBody633_34

def crepBody633_36 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody633_35

def crepBody633_37 : CrepProg (BitVec 64) :=
.seq crepBody633_1 crepBody633_36

def crepBody633_38 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 112#64])) crepBody633_37

def data633 : CrepProg (BitVec 64) := crepBody633_38
def output633 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 114#8, 101#8, 95#8, 97#8, 108#8, 116#8, 95#8, 98#8, 110#8, 49#8, 50#8, 56#8, 95#8, 97#8, 100#8, 100#8], [], crepProgToHOL data633)
end InitECandidate.Proofs.FrontendStages.Crep
