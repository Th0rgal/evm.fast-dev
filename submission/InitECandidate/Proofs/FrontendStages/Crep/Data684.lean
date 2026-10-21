import InitECandidate.Proofs.FrontendStages.Crep.Translate668
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody684_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "heap_mark" []

def crepBody684_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 96#64, Flapjack.CrepExp.const 10#64]]

def crepBody684_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "fp2_mul"
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2]

def crepBody684_3 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody684_2

def crepBody684_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "fp2_mul"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.var 1,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 96#64]]

def crepBody684_5 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody684_4

def crepBody684_6 : CrepProg (BitVec 64) :=
.seq crepBody684_3 crepBody684_5

def crepBody684_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "fp2_mul"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.var 1,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 192#64]]

def crepBody684_8 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody684_7

def crepBody684_9 : CrepProg (BitVec 64) :=
.seq crepBody684_6 crepBody684_8

def crepBody684_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "fp2_mul"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 288#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.var 2]

def crepBody684_11 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody684_10

def crepBody684_12 : CrepProg (BitVec 64) :=
.seq crepBody684_9 crepBody684_11

def crepBody684_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "fp2_mul"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 384#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 96#64]]

def crepBody684_14 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody684_13

def crepBody684_15 : CrepProg (BitVec 64) :=
.seq crepBody684_12 crepBody684_14

def crepBody684_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "fp2_mul"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 480#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 192#64]]

def crepBody684_17 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody684_16

def crepBody684_18 : CrepProg (BitVec 64) :=
.seq crepBody684_15 crepBody684_17

def crepBody684_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "fp2_mul"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 576#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.var 2]

def crepBody684_20 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody684_19

def crepBody684_21 : CrepProg (BitVec 64) :=
.seq crepBody684_18 crepBody684_20

def crepBody684_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "fp2_mul"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 672#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 96#64]]

def crepBody684_23 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody684_22

def crepBody684_24 : CrepProg (BitVec 64) :=
.seq crepBody684_21 crepBody684_23

def crepBody684_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "fp2_mul"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 768#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 192#64]]

def crepBody684_26 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody684_25

def crepBody684_27 : CrepProg (BitVec 64) :=
.seq crepBody684_24 crepBody684_26

def crepBody684_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "fp2_add"
  [Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 480#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 672#64]]

def crepBody684_29 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody684_28

def crepBody684_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "fp2_mul_xi" [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 5]

def crepBody684_31 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody684_30

def crepBody684_32 : CrepProg (BitVec 64) :=
.seq crepBody684_29 crepBody684_31

def crepBody684_33 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "fp2_add"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody684_34 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody684_33

def crepBody684_35 : CrepProg (BitVec 64) :=
.seq crepBody684_32 crepBody684_34

def crepBody684_36 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "fp2_mul_xi"
  [Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 768#64]]

def crepBody684_37 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody684_36

def crepBody684_38 : CrepProg (BitVec 64) :=
.seq crepBody684_35 crepBody684_37

def crepBody684_39 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "fp2_add"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 96#64]]

def crepBody684_40 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody684_39

def crepBody684_41 : CrepProg (BitVec 64) :=
.seq crepBody684_38 crepBody684_40

def crepBody684_42 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "fp2_add"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 288#64]]

def crepBody684_43 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody684_42

def crepBody684_44 : CrepProg (BitVec 64) :=
.seq crepBody684_41 crepBody684_43

def crepBody684_45 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "fp2_add"
  [Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 384#64]]

def crepBody684_46 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody684_45

def crepBody684_47 : CrepProg (BitVec 64) :=
.seq crepBody684_44 crepBody684_46

def crepBody684_48 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "fp2_add"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 576#64]]

def crepBody684_49 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody684_48

def crepBody684_50 : CrepProg (BitVec 64) :=
.seq crepBody684_47 crepBody684_49

def crepBody684_51 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "heap_release" [Flapjack.CrepExp.var 3]

def crepBody684_52 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody684_51

def crepBody684_53 : CrepProg (BitVec 64) :=
.seq crepBody684_50 crepBody684_52

def crepBody684_54 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody684_55 : CrepProg (BitVec 64) :=
.seq crepBody684_53 crepBody684_54

def crepBody684_56 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 864#64]) crepBody684_55

def crepBody684_57 : CrepProg (BitVec 64) :=
.seq crepBody684_27 crepBody684_56

def crepBody684_58 : CrepProg (BitVec 64) :=
.seq crepBody684_1 crepBody684_57

def crepBody684_59 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody684_58

def crepBody684_60 : CrepProg (BitVec 64) :=
.seq crepBody684_0 crepBody684_59

def crepBody684_61 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody684_60

def data684 : CrepProg (BitVec 64) := crepBody684_61
def output684 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 112#8, 54#8, 95#8, 109#8, 117#8, 108#8], [0, 1, 2], crepProgToHOL data684)
end InitECandidate.Proofs.FrontendStages.Crep
