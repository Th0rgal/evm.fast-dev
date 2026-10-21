import InitECandidate.Proofs.FrontendStages.Crep.Translate739
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody755_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 3)

def crepBody755_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody755_2 : CrepProg (BitVec 64) :=
.seq crepBody755_0 crepBody755_1

def crepBody755_3 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 10#64) crepBody755_2

def crepBody755_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 8#64

def crepBody755_5 : CrepProg (BitVec 64) :=
.seq crepBody755_3 crepBody755_4

def crepBody755_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 512#64)) crepBody755_5 crepBody755_1

def crepBody755_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "charge_gas" [Flapjack.CrepExp.const 600#64]

def crepBody755_8 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody755_7

def crepBody755_9 : CrepProg (BitVec 64) :=
.seq crepBody755_6 crepBody755_8

def crepBody755_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 256#64]

def crepBody755_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "bls_g2_add_exec"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 88#64]),
    Flapjack.CrepExp.var 3]

def crepBody755_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 5)

def crepBody755_13 : CrepProg (BitVec 64) :=
.seq crepBody755_12 crepBody755_1

def crepBody755_14 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 10#64) crepBody755_13

def crepBody755_15 : CrepProg (BitVec 64) :=
.seq crepBody755_14 crepBody755_4

def crepBody755_16 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 0#64)) crepBody755_15 crepBody755_1

def crepBody755_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 6)

def crepBody755_18 : CrepProg (BitVec 64) :=
.seq crepBody755_17 crepBody755_1

def crepBody755_19 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 3) crepBody755_18

def crepBody755_20 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 120#64]) crepBody755_19

def crepBody755_21 : CrepProg (BitVec 64) :=
.seq crepBody755_16 crepBody755_20

def crepBody755_22 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 256#64) crepBody755_18

def crepBody755_23 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 128#64]) crepBody755_22

def crepBody755_24 : CrepProg (BitVec 64) :=
.seq crepBody755_21 crepBody755_23

def crepBody755_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody755_26 : CrepProg (BitVec 64) :=
.seq crepBody755_24 crepBody755_25

def crepBody755_27 : CrepProg (BitVec 64) :=
.seq crepBody755_11 crepBody755_26

def crepBody755_28 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody755_27

def crepBody755_29 : CrepProg (BitVec 64) :=
.seq crepBody755_10 crepBody755_28

def crepBody755_30 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody755_29

def crepBody755_31 : CrepProg (BitVec 64) :=
.seq crepBody755_9 crepBody755_30

def crepBody755_32 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64])) crepBody755_31

def crepBody755_33 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 112#64])) crepBody755_32

def data755 : CrepProg (BitVec 64) := crepBody755_33
def output755 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 114#8, 101#8, 95#8, 98#8, 108#8, 115#8, 95#8, 103#8, 50#8, 95#8, 97#8, 100#8, 100#8], [], crepProgToHOL data755)
end InitECandidate.Proofs.FrontendStages.Crep
