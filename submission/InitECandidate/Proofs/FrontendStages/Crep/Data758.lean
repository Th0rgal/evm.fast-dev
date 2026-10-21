import InitECandidate.Proofs.FrontendStages.Crep.Translate742
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody758_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 3)

def crepBody758_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody758_2 : CrepProg (BitVec 64) :=
.seq crepBody758_0 crepBody758_1

def crepBody758_3 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 10#64) crepBody758_2

def crepBody758_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 8#64

def crepBody758_5 : CrepProg (BitVec 64) :=
.seq crepBody758_3 crepBody758_4

def crepBody758_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 64#64)) crepBody758_5 crepBody758_1

def crepBody758_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "charge_gas" [Flapjack.CrepExp.const 5500#64]

def crepBody758_8 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody758_7

def crepBody758_9 : CrepProg (BitVec 64) :=
.seq crepBody758_6 crepBody758_8

def crepBody758_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 128#64]

def crepBody758_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "bls_map_fp_to_g1_exec"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 88#64]),
    Flapjack.CrepExp.var 3]

def crepBody758_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 5)

def crepBody758_13 : CrepProg (BitVec 64) :=
.seq crepBody758_12 crepBody758_1

def crepBody758_14 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 10#64) crepBody758_13

def crepBody758_15 : CrepProg (BitVec 64) :=
.seq crepBody758_14 crepBody758_4

def crepBody758_16 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 0#64)) crepBody758_15 crepBody758_1

def crepBody758_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 6)

def crepBody758_18 : CrepProg (BitVec 64) :=
.seq crepBody758_17 crepBody758_1

def crepBody758_19 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 3) crepBody758_18

def crepBody758_20 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 120#64]) crepBody758_19

def crepBody758_21 : CrepProg (BitVec 64) :=
.seq crepBody758_16 crepBody758_20

def crepBody758_22 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 128#64) crepBody758_18

def crepBody758_23 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 128#64]) crepBody758_22

def crepBody758_24 : CrepProg (BitVec 64) :=
.seq crepBody758_21 crepBody758_23

def crepBody758_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody758_26 : CrepProg (BitVec 64) :=
.seq crepBody758_24 crepBody758_25

def crepBody758_27 : CrepProg (BitVec 64) :=
.seq crepBody758_11 crepBody758_26

def crepBody758_28 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody758_27

def crepBody758_29 : CrepProg (BitVec 64) :=
.seq crepBody758_10 crepBody758_28

def crepBody758_30 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody758_29

def crepBody758_31 : CrepProg (BitVec 64) :=
.seq crepBody758_9 crepBody758_30

def crepBody758_32 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64])) crepBody758_31

def crepBody758_33 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 112#64])) crepBody758_32

def data758 : CrepProg (BitVec 64) := crepBody758_33
def output758 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 114#8, 101#8, 95#8, 98#8, 108#8, 115#8, 95#8, 109#8, 97#8, 112#8, 95#8, 102#8, 112#8, 95#8, 116#8, 111#8,
    95#8, 103#8, 49#8], [], crepProgToHOL data758)
end InitECandidate.Proofs.FrontendStages.Crep
