import InitECandidate.Proofs.FrontendStages.Crep.Translate744
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody760_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 3)

def crepBody760_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody760_2 : CrepProg (BitVec 64) :=
.seq crepBody760_0 crepBody760_1

def crepBody760_3 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 13#64) crepBody760_2

def crepBody760_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 8#64

def crepBody760_5 : CrepProg (BitVec 64) :=
.seq crepBody760_3 crepBody760_4

def crepBody760_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 192#64)) crepBody760_5 crepBody760_1

def crepBody760_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "charge_gas" [Flapjack.CrepExp.const 50000#64]

def crepBody760_8 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody760_7

def crepBody760_9 : CrepProg (BitVec 64) :=
.seq crepBody760_6 crepBody760_8

def crepBody760_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 64#64]

def crepBody760_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "kzg_point_evaluation_exec"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 88#64]),
    Flapjack.CrepExp.var 3]

def crepBody760_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 5)

def crepBody760_13 : CrepProg (BitVec 64) :=
.seq crepBody760_12 crepBody760_1

def crepBody760_14 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 13#64) crepBody760_13

def crepBody760_15 : CrepProg (BitVec 64) :=
.seq crepBody760_14 crepBody760_4

def crepBody760_16 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 0#64)) crepBody760_15 crepBody760_1

def crepBody760_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 6)

def crepBody760_18 : CrepProg (BitVec 64) :=
.seq crepBody760_17 crepBody760_1

def crepBody760_19 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 3) crepBody760_18

def crepBody760_20 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 120#64]) crepBody760_19

def crepBody760_21 : CrepProg (BitVec 64) :=
.seq crepBody760_16 crepBody760_20

def crepBody760_22 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 64#64) crepBody760_18

def crepBody760_23 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 128#64]) crepBody760_22

def crepBody760_24 : CrepProg (BitVec 64) :=
.seq crepBody760_21 crepBody760_23

def crepBody760_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody760_26 : CrepProg (BitVec 64) :=
.seq crepBody760_24 crepBody760_25

def crepBody760_27 : CrepProg (BitVec 64) :=
.seq crepBody760_11 crepBody760_26

def crepBody760_28 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody760_27

def crepBody760_29 : CrepProg (BitVec 64) :=
.seq crepBody760_10 crepBody760_28

def crepBody760_30 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody760_29

def crepBody760_31 : CrepProg (BitVec 64) :=
.seq crepBody760_9 crepBody760_30

def crepBody760_32 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64])) crepBody760_31

def crepBody760_33 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 112#64])) crepBody760_32

def data760 : CrepProg (BitVec 64) := crepBody760_33
def output760 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 114#8, 101#8, 95#8, 107#8, 122#8, 103#8, 95#8, 112#8, 111#8, 105#8, 110#8, 116#8, 95#8, 101#8, 118#8, 97#8,
    108#8, 117#8, 97#8, 116#8, 105#8, 111#8, 110#8], [], crepProgToHOL data760)
end InitECandidate.Proofs.FrontendStages.Crep
