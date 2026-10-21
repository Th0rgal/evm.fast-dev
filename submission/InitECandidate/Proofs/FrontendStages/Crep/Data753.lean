import InitECandidate.Proofs.FrontendStages.Crep.Translate737
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody753_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 3)

def crepBody753_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody753_2 : CrepProg (BitVec 64) :=
.seq crepBody753_0 crepBody753_1

def crepBody753_3 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 10#64) crepBody753_2

def crepBody753_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 8#64

def crepBody753_5 : CrepProg (BitVec 64) :=
.seq crepBody753_3 crepBody753_4

def crepBody753_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 256#64)) crepBody753_5 crepBody753_1

def crepBody753_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "charge_gas" [Flapjack.CrepExp.const 375#64]

def crepBody753_8 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody753_7

def crepBody753_9 : CrepProg (BitVec 64) :=
.seq crepBody753_6 crepBody753_8

def crepBody753_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 128#64]

def crepBody753_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "bls_g1_add_exec"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 88#64]),
    Flapjack.CrepExp.var 3]

def crepBody753_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 5)

def crepBody753_13 : CrepProg (BitVec 64) :=
.seq crepBody753_12 crepBody753_1

def crepBody753_14 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 10#64) crepBody753_13

def crepBody753_15 : CrepProg (BitVec 64) :=
.seq crepBody753_14 crepBody753_4

def crepBody753_16 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 0#64)) crepBody753_15 crepBody753_1

def crepBody753_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 6)

def crepBody753_18 : CrepProg (BitVec 64) :=
.seq crepBody753_17 crepBody753_1

def crepBody753_19 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 3) crepBody753_18

def crepBody753_20 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 120#64]) crepBody753_19

def crepBody753_21 : CrepProg (BitVec 64) :=
.seq crepBody753_16 crepBody753_20

def crepBody753_22 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 128#64) crepBody753_18

def crepBody753_23 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 128#64]) crepBody753_22

def crepBody753_24 : CrepProg (BitVec 64) :=
.seq crepBody753_21 crepBody753_23

def crepBody753_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody753_26 : CrepProg (BitVec 64) :=
.seq crepBody753_24 crepBody753_25

def crepBody753_27 : CrepProg (BitVec 64) :=
.seq crepBody753_11 crepBody753_26

def crepBody753_28 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody753_27

def crepBody753_29 : CrepProg (BitVec 64) :=
.seq crepBody753_10 crepBody753_28

def crepBody753_30 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody753_29

def crepBody753_31 : CrepProg (BitVec 64) :=
.seq crepBody753_9 crepBody753_30

def crepBody753_32 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64])) crepBody753_31

def crepBody753_33 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 112#64])) crepBody753_32

def data753 : CrepProg (BitVec 64) := crepBody753_33
def output753 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 114#8, 101#8, 95#8, 98#8, 108#8, 115#8, 95#8, 103#8, 49#8, 95#8, 97#8, 100#8, 100#8], [], crepProgToHOL data753)
end InitECandidate.Proofs.FrontendStages.Crep
