import InitECandidate.Proofs.FrontendStages.Crep.Translate719
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody735_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "heap_mark" []

def crepBody735_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 96#64, Flapjack.CrepExp.const 3#64]]

def crepBody735_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 96#64, Flapjack.CrepExp.const 4#64]]

def crepBody735_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "fp2_copy" [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 7]

def crepBody735_4 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody735_3

def crepBody735_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "fp2_sqr"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.var 7]

def crepBody735_6 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody735_5

def crepBody735_7 : CrepProg (BitVec 64) :=
.seq crepBody735_4 crepBody735_6

def crepBody735_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "fp2_mul"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.var 7]

def crepBody735_9 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody735_8

def crepBody735_10 : CrepProg (BitVec 64) :=
.seq crepBody735_7 crepBody735_9

def crepBody735_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "iso_horner_fp2"
  [Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
        Flapjack.CrepExp.const 5600#64],
    Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 3]

def crepBody735_12 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody735_11

def crepBody735_13 : CrepProg (BitVec 64) :=
.seq crepBody735_10 crepBody735_12

def crepBody735_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "iso_horner_fp2"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
        Flapjack.CrepExp.const 5984#64],
    Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 3]

def crepBody735_15 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody735_14

def crepBody735_16 : CrepProg (BitVec 64) :=
.seq crepBody735_13 crepBody735_15

def crepBody735_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "iso_horner_fp2"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
        Flapjack.CrepExp.const 6368#64],
    Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 3]

def crepBody735_18 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody735_17

def crepBody735_19 : CrepProg (BitVec 64) :=
.seq crepBody735_16 crepBody735_18

def crepBody735_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "iso_horner_fp2"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 288#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
        Flapjack.CrepExp.const 6752#64],
    Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 3]

def crepBody735_21 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody735_20

def crepBody735_22 : CrepProg (BitVec 64) :=
.seq crepBody735_19 crepBody735_21

def crepBody735_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "fp2_mul"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.var 6]

def crepBody735_24 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody735_23

def crepBody735_25 : CrepProg (BitVec 64) :=
.seq crepBody735_22 crepBody735_24

def crepBody735_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "fp2_mul"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 288#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 288#64],
    Flapjack.CrepExp.var 7]

def crepBody735_27 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody735_26

def crepBody735_28 : CrepProg (BitVec 64) :=
.seq crepBody735_25 crepBody735_27

def crepBody735_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "fp2_mul"
  [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 288#64]]

def crepBody735_30 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody735_29

def crepBody735_31 : CrepProg (BitVec 64) :=
.seq crepBody735_28 crepBody735_30

def crepBody735_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "fp2_mul"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 192#64]]

def crepBody735_33 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody735_32

def crepBody735_34 : CrepProg (BitVec 64) :=
.seq crepBody735_31 crepBody735_33

def crepBody735_35 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "fp2_mul"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 288#64]]

def crepBody735_36 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody735_35

def crepBody735_37 : CrepProg (BitVec 64) :=
.seq crepBody735_34 crepBody735_36

def crepBody735_38 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "g2_copy" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3]

def crepBody735_39 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody735_38

def crepBody735_40 : CrepProg (BitVec 64) :=
.seq crepBody735_37 crepBody735_39

def crepBody735_41 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody735_42 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody735_41

def crepBody735_43 : CrepProg (BitVec 64) :=
.seq crepBody735_40 crepBody735_42

def crepBody735_44 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody735_45 : CrepProg (BitVec 64) :=
.seq crepBody735_43 crepBody735_44

def crepBody735_46 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 192#64]) crepBody735_45

def crepBody735_47 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64]) crepBody735_46

def crepBody735_48 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.var 1) crepBody735_47

def crepBody735_49 : CrepProg (BitVec 64) :=
.seq crepBody735_2 crepBody735_48

def crepBody735_50 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody735_49

def crepBody735_51 : CrepProg (BitVec 64) :=
.seq crepBody735_1 crepBody735_50

def crepBody735_52 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody735_51

def crepBody735_53 : CrepProg (BitVec 64) :=
.seq crepBody735_0 crepBody735_52

def crepBody735_54 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody735_53

def data735 : CrepProg (BitVec 64) := crepBody735_54
def output735 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [105#8, 115#8, 111#8, 95#8, 109#8, 97#8, 112#8, 95#8, 103#8, 50#8], [0, 1], crepProgToHOL data735)
end InitECandidate.Proofs.FrontendStages.Crep
