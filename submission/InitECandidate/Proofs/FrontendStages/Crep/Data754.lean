import InitECandidate.Proofs.FrontendStages.Crep.Translate738
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody754_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 3)

def crepBody754_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody754_2 : CrepProg (BitVec 64) :=
.seq crepBody754_0 crepBody754_1

def crepBody754_3 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 10#64) crepBody754_2

def crepBody754_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 8#64

def crepBody754_5 : CrepProg (BitVec 64) :=
.seq crepBody754_3 crepBody754_4

def crepBody754_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody754_5 crepBody754_1

def crepBody754_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3, 4], none)) "udivmod" [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 160#64]

def crepBody754_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 5)

def crepBody754_9 : CrepProg (BitVec 64) :=
.seq crepBody754_8 crepBody754_1

def crepBody754_10 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 10#64) crepBody754_9

def crepBody754_11 : CrepProg (BitVec 64) :=
.seq crepBody754_10 crepBody754_4

def crepBody754_12 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 0#64)) crepBody754_11 crepBody754_1

def crepBody754_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "bls_g1_msm_discount" [Flapjack.CrepExp.var 5]

def crepBody754_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7, 8], none)) "udivmod"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 12000#64],
        Flapjack.CrepExp.var 6],
    Flapjack.CrepExp.const 1000#64]

def crepBody754_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "charge_gas" [Flapjack.CrepExp.var 7]

def crepBody754_16 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody754_15

def crepBody754_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "alloc" [Flapjack.CrepExp.const 128#64]

def crepBody754_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "bls_g1_msm_exec"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 88#64]),
    Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 9]

def crepBody754_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 11)

def crepBody754_20 : CrepProg (BitVec 64) :=
.seq crepBody754_19 crepBody754_1

def crepBody754_21 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 10#64) crepBody754_20

def crepBody754_22 : CrepProg (BitVec 64) :=
.seq crepBody754_21 crepBody754_4

def crepBody754_23 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 0#64)) crepBody754_22 crepBody754_1

def crepBody754_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.var 12)

def crepBody754_25 : CrepProg (BitVec 64) :=
.seq crepBody754_24 crepBody754_1

def crepBody754_26 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.var 9) crepBody754_25

def crepBody754_27 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 120#64]) crepBody754_26

def crepBody754_28 : CrepProg (BitVec 64) :=
.seq crepBody754_23 crepBody754_27

def crepBody754_29 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 128#64) crepBody754_25

def crepBody754_30 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 128#64]) crepBody754_29

def crepBody754_31 : CrepProg (BitVec 64) :=
.seq crepBody754_28 crepBody754_30

def crepBody754_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody754_33 : CrepProg (BitVec 64) :=
.seq crepBody754_31 crepBody754_32

def crepBody754_34 : CrepProg (BitVec 64) :=
.seq crepBody754_18 crepBody754_33

def crepBody754_35 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody754_34

def crepBody754_36 : CrepProg (BitVec 64) :=
.seq crepBody754_17 crepBody754_35

def crepBody754_37 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody754_36

def crepBody754_38 : CrepProg (BitVec 64) :=
.seq crepBody754_16 crepBody754_37

def crepBody754_39 : CrepProg (BitVec 64) :=
.seq crepBody754_14 crepBody754_38

def crepBody754_40 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody754_39

def crepBody754_41 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody754_40

def crepBody754_42 : CrepProg (BitVec 64) :=
.seq crepBody754_13 crepBody754_41

def crepBody754_43 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody754_42

def crepBody754_44 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.var 3) crepBody754_43

def crepBody754_45 : CrepProg (BitVec 64) :=
.seq crepBody754_12 crepBody754_44

def crepBody754_46 : CrepProg (BitVec 64) :=
.seq crepBody754_7 crepBody754_45

def crepBody754_47 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody754_46

def crepBody754_48 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody754_47

def crepBody754_49 : CrepProg (BitVec 64) :=
.seq crepBody754_6 crepBody754_48

def crepBody754_50 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64])) crepBody754_49

def crepBody754_51 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 112#64])) crepBody754_50

def data754 : CrepProg (BitVec 64) := crepBody754_51
def output754 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 114#8, 101#8, 95#8, 98#8, 108#8, 115#8, 95#8, 103#8, 49#8, 95#8, 109#8, 115#8, 109#8], [], crepProgToHOL data754)
end InitECandidate.Proofs.FrontendStages.Crep
