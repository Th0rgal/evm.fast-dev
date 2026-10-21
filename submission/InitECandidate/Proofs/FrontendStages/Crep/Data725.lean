import InitECandidate.Proofs.FrontendStages.Crep.Translate709
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody725_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "heap_mark" []

def crepBody725_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "alloc" [Flapjack.CrepExp.const 288#64]

def crepBody725_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 96#64, Flapjack.CrepExp.const 3#64]]

def crepBody725_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "fp2_copy" [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 13]

def crepBody725_4 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody725_3

def crepBody725_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "fp2_copy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 96#64]]

def crepBody725_6 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody725_5

def crepBody725_7 : CrepProg (BitVec 64) :=
.seq crepBody725_4 crepBody725_6

def crepBody725_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "fp2_set_one"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 192#64]]

def crepBody725_9 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody725_8

def crepBody725_10 : CrepProg (BitVec 64) :=
.seq crepBody725_7 crepBody725_9

def crepBody725_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "fp12_set_one" [Flapjack.CrepExp.var 0]

def crepBody725_12 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody725_11

def crepBody725_13 : CrepProg (BitVec 64) :=
.seq crepBody725_10 crepBody725_12

def crepBody725_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 18 (Flapjack.CrepExp.var 19)

def crepBody725_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody725_16 : CrepProg (BitVec 64) :=
.seq crepBody725_14 crepBody725_15

def crepBody725_17 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 1#64]) crepBody725_16

def crepBody725_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "fp12_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 0]

def crepBody725_19 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody725_18

def crepBody725_20 : CrepProg (BitVec 64) :=
.seq crepBody725_17 crepBody725_19

def crepBody725_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "pair_doubling_step" [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16]

def crepBody725_22 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody725_21

def crepBody725_23 : CrepProg (BitVec 64) :=
.seq crepBody725_20 crepBody725_22

def crepBody725_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "pair_ell"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10,
    Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12]

def crepBody725_25 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody725_24

def crepBody725_26 : CrepProg (BitVec 64) :=
.seq crepBody725_23 crepBody725_25

def crepBody725_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "pair_addition_step"
  [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 13,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.var 16]

def crepBody725_28 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody725_27

def crepBody725_29 : CrepProg (BitVec 64) :=
.seq crepBody725_28 crepBody725_25

def crepBody725_30 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.op Flapjack.BinOp.and
    [Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 17) (Flapjack.CrepExp.var 18),
      Flapjack.CrepExp.const 1#64])
  (Flapjack.CrepExp.const 1#64)) crepBody725_29 crepBody725_15

def crepBody725_31 : CrepProg (BitVec 64) :=
.seq crepBody725_26 crepBody725_30

def crepBody725_32 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 0#64) (Flapjack.CrepExp.var 18)) crepBody725_31

def crepBody725_33 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "fp12_conj" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 0]

def crepBody725_34 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody725_33

def crepBody725_35 : CrepProg (BitVec 64) :=
.seq crepBody725_32 crepBody725_34

def crepBody725_36 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "heap_release" [Flapjack.CrepExp.var 14]

def crepBody725_37 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody725_36

def crepBody725_38 : CrepProg (BitVec 64) :=
.seq crepBody725_35 crepBody725_37

def crepBody725_39 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody725_40 : CrepProg (BitVec 64) :=
.seq crepBody725_38 crepBody725_39

def crepBody725_41 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 63#64) crepBody725_40

def crepBody725_42 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
      Flapjack.CrepExp.const 1376#64])) crepBody725_41

def crepBody725_43 : CrepProg (BitVec 64) :=
.seq crepBody725_13 crepBody725_42

def crepBody725_44 : CrepProg (BitVec 64) :=
.seq crepBody725_2 crepBody725_43

def crepBody725_45 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody725_44

def crepBody725_46 : CrepProg (BitVec 64) :=
.seq crepBody725_1 crepBody725_45

def crepBody725_47 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody725_46

def crepBody725_48 : CrepProg (BitVec 64) :=
.seq crepBody725_0 crepBody725_47

def crepBody725_49 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody725_48

def data725 : CrepProg (BitVec 64) := crepBody725_49
def output725 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 97#8, 105#8, 114#8, 95#8, 109#8, 105#8, 108#8, 108#8, 101#8, 114#8, 95#8, 108#8, 111#8, 111#8, 112#8], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13], crepProgToHOL data725)
end InitECandidate.Proofs.FrontendStages.Crep
