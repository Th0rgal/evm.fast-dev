import InitECandidate.Proofs.FrontendStages.Crep.Translate740
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody756_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 3)

def crepBody756_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody756_2 : CrepProg (BitVec 64) :=
.seq crepBody756_0 crepBody756_1

def crepBody756_3 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 10#64) crepBody756_2

def crepBody756_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 8#64

def crepBody756_5 : CrepProg (BitVec 64) :=
.seq crepBody756_3 crepBody756_4

def crepBody756_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody756_5 crepBody756_1

def crepBody756_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3, 4], none)) "udivmod" [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 288#64]

def crepBody756_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 5)

def crepBody756_9 : CrepProg (BitVec 64) :=
.seq crepBody756_8 crepBody756_1

def crepBody756_10 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 10#64) crepBody756_9

def crepBody756_11 : CrepProg (BitVec 64) :=
.seq crepBody756_10 crepBody756_4

def crepBody756_12 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 0#64)) crepBody756_11 crepBody756_1

def crepBody756_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "bls_g2_msm_discount" [Flapjack.CrepExp.var 5]

def crepBody756_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7, 8], none)) "udivmod"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 22500#64],
        Flapjack.CrepExp.var 6],
    Flapjack.CrepExp.const 1000#64]

def crepBody756_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "charge_gas" [Flapjack.CrepExp.var 7]

def crepBody756_16 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody756_15

def crepBody756_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "alloc" [Flapjack.CrepExp.const 256#64]

def crepBody756_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "bls_g2_msm_exec"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 88#64]),
    Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 9]

def crepBody756_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 11)

def crepBody756_20 : CrepProg (BitVec 64) :=
.seq crepBody756_19 crepBody756_1

def crepBody756_21 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 10#64) crepBody756_20

def crepBody756_22 : CrepProg (BitVec 64) :=
.seq crepBody756_21 crepBody756_4

def crepBody756_23 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 0#64)) crepBody756_22 crepBody756_1

def crepBody756_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.var 12)

def crepBody756_25 : CrepProg (BitVec 64) :=
.seq crepBody756_24 crepBody756_1

def crepBody756_26 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.var 9) crepBody756_25

def crepBody756_27 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 120#64]) crepBody756_26

def crepBody756_28 : CrepProg (BitVec 64) :=
.seq crepBody756_23 crepBody756_27

def crepBody756_29 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 256#64) crepBody756_25

def crepBody756_30 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 128#64]) crepBody756_29

def crepBody756_31 : CrepProg (BitVec 64) :=
.seq crepBody756_28 crepBody756_30

def crepBody756_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody756_33 : CrepProg (BitVec 64) :=
.seq crepBody756_31 crepBody756_32

def crepBody756_34 : CrepProg (BitVec 64) :=
.seq crepBody756_18 crepBody756_33

def crepBody756_35 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody756_34

def crepBody756_36 : CrepProg (BitVec 64) :=
.seq crepBody756_17 crepBody756_35

def crepBody756_37 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody756_36

def crepBody756_38 : CrepProg (BitVec 64) :=
.seq crepBody756_16 crepBody756_37

def crepBody756_39 : CrepProg (BitVec 64) :=
.seq crepBody756_14 crepBody756_38

def crepBody756_40 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody756_39

def crepBody756_41 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody756_40

def crepBody756_42 : CrepProg (BitVec 64) :=
.seq crepBody756_13 crepBody756_41

def crepBody756_43 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody756_42

def crepBody756_44 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.var 3) crepBody756_43

def crepBody756_45 : CrepProg (BitVec 64) :=
.seq crepBody756_12 crepBody756_44

def crepBody756_46 : CrepProg (BitVec 64) :=
.seq crepBody756_7 crepBody756_45

def crepBody756_47 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody756_46

def crepBody756_48 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody756_47

def crepBody756_49 : CrepProg (BitVec 64) :=
.seq crepBody756_6 crepBody756_48

def crepBody756_50 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64])) crepBody756_49

def crepBody756_51 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 112#64])) crepBody756_50

def data756 : CrepProg (BitVec 64) := crepBody756_51
def output756 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 114#8, 101#8, 95#8, 98#8, 108#8, 115#8, 95#8, 103#8, 50#8, 95#8, 109#8, 115#8, 109#8], [], crepProgToHOL data756)
end InitECandidate.Proofs.FrontendStages.Crep
