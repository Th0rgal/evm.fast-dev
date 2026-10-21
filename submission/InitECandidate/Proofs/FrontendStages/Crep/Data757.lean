import InitECandidate.Proofs.FrontendStages.Crep.Translate741
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody757_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 3)

def crepBody757_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody757_2 : CrepProg (BitVec 64) :=
.seq crepBody757_0 crepBody757_1

def crepBody757_3 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 10#64) crepBody757_2

def crepBody757_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 8#64

def crepBody757_5 : CrepProg (BitVec 64) :=
.seq crepBody757_3 crepBody757_4

def crepBody757_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody757_5 crepBody757_1

def crepBody757_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3, 4], none)) "udivmod" [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 384#64]

def crepBody757_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 5)

def crepBody757_9 : CrepProg (BitVec 64) :=
.seq crepBody757_8 crepBody757_1

def crepBody757_10 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 10#64) crepBody757_9

def crepBody757_11 : CrepProg (BitVec 64) :=
.seq crepBody757_10 crepBody757_4

def crepBody757_12 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 0#64)) crepBody757_11 crepBody757_1

def crepBody757_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "charge_gas"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 32600#64, Flapjack.CrepExp.var 5],
        Flapjack.CrepExp.const 37700#64]]

def crepBody757_14 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody757_13

def crepBody757_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody757_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "bls_pairing_exec"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 88#64]),
    Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6]

def crepBody757_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 8)

def crepBody757_18 : CrepProg (BitVec 64) :=
.seq crepBody757_17 crepBody757_1

def crepBody757_19 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 10#64) crepBody757_18

def crepBody757_20 : CrepProg (BitVec 64) :=
.seq crepBody757_19 crepBody757_4

def crepBody757_21 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 0#64)) crepBody757_20 crepBody757_1

def crepBody757_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.var 9)

def crepBody757_23 : CrepProg (BitVec 64) :=
.seq crepBody757_22 crepBody757_1

def crepBody757_24 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 6) crepBody757_23

def crepBody757_25 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 120#64]) crepBody757_24

def crepBody757_26 : CrepProg (BitVec 64) :=
.seq crepBody757_21 crepBody757_25

def crepBody757_27 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 32#64) crepBody757_23

def crepBody757_28 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 128#64]) crepBody757_27

def crepBody757_29 : CrepProg (BitVec 64) :=
.seq crepBody757_26 crepBody757_28

def crepBody757_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody757_31 : CrepProg (BitVec 64) :=
.seq crepBody757_29 crepBody757_30

def crepBody757_32 : CrepProg (BitVec 64) :=
.seq crepBody757_16 crepBody757_31

def crepBody757_33 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody757_32

def crepBody757_34 : CrepProg (BitVec 64) :=
.seq crepBody757_15 crepBody757_33

def crepBody757_35 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody757_34

def crepBody757_36 : CrepProg (BitVec 64) :=
.seq crepBody757_14 crepBody757_35

def crepBody757_37 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.var 3) crepBody757_36

def crepBody757_38 : CrepProg (BitVec 64) :=
.seq crepBody757_12 crepBody757_37

def crepBody757_39 : CrepProg (BitVec 64) :=
.seq crepBody757_7 crepBody757_38

def crepBody757_40 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody757_39

def crepBody757_41 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody757_40

def crepBody757_42 : CrepProg (BitVec 64) :=
.seq crepBody757_6 crepBody757_41

def crepBody757_43 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64])) crepBody757_42

def crepBody757_44 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 112#64])) crepBody757_43

def data757 : CrepProg (BitVec 64) := crepBody757_44
def output757 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 114#8, 101#8, 95#8, 98#8, 108#8, 115#8, 95#8, 112#8, 97#8, 105#8, 114#8, 105#8, 110#8, 103#8], [], crepProgToHOL data757)
end InitECandidate.Proofs.FrontendStages.Crep
