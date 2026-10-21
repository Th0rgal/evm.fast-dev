import InitECandidate.Proofs.FrontendStages.Crep.Translate181
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody197_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "heap_mark" []

def crepBody197_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "alloc"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 32#64],
        Flapjack.CrepExp.const 32#64]]

def crepBody197_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "htr_deposit"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 1,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 3]],
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 6,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 32#64]]]

def crepBody197_3 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody197_2

def crepBody197_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody197_5 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 0#64)) crepBody197_3 crepBody197_4

def crepBody197_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "htr_wdreq"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 1,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 3]],
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 6,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 32#64]]]

def crepBody197_7 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody197_6

def crepBody197_8 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 1#64)) crepBody197_7 crepBody197_4

def crepBody197_9 : CrepProg (BitVec 64) :=
.seq crepBody197_5 crepBody197_8

def crepBody197_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "htr_cons"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 1,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 3]],
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 6,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 32#64]]]

def crepBody197_11 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody197_10

def crepBody197_12 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 2#64)) crepBody197_11 crepBody197_4

def crepBody197_13 : CrepProg (BitVec 64) :=
.seq crepBody197_9 crepBody197_12

def crepBody197_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "htr_bdep"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 1,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 3]],
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 6,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 32#64]]]

def crepBody197_15 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody197_14

def crepBody197_16 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 3#64)) crepBody197_15 crepBody197_4

def crepBody197_17 : CrepProg (BitVec 64) :=
.seq crepBody197_13 crepBody197_16

def crepBody197_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "htr_bexit"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 1,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 3]],
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 6,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 32#64]]]

def crepBody197_19 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody197_18

def crepBody197_20 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 4#64)) crepBody197_19 crepBody197_4

def crepBody197_21 : CrepProg (BitVec 64) :=
.seq crepBody197_17 crepBody197_20

def crepBody197_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.var 8)

def crepBody197_23 : CrepProg (BitVec 64) :=
.seq crepBody197_22 crepBody197_4

def crepBody197_24 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 1#64]) crepBody197_23

def crepBody197_25 : CrepProg (BitVec 64) :=
.seq crepBody197_21 crepBody197_24

def crepBody197_26 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.var 2)) crepBody197_25

def crepBody197_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "htr_plist_chunks"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 4]

def crepBody197_28 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody197_27

def crepBody197_29 : CrepProg (BitVec 64) :=
.seq crepBody197_26 crepBody197_28

def crepBody197_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "heap_release" [Flapjack.CrepExp.var 5]

def crepBody197_31 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody197_30

def crepBody197_32 : CrepProg (BitVec 64) :=
.seq crepBody197_29 crepBody197_31

def crepBody197_33 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody197_34 : CrepProg (BitVec 64) :=
.seq crepBody197_32 crepBody197_33

def crepBody197_35 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody197_34

def crepBody197_36 : CrepProg (BitVec 64) :=
.seq crepBody197_1 crepBody197_35

def crepBody197_37 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody197_36

def crepBody197_38 : CrepProg (BitVec 64) :=
.seq crepBody197_0 crepBody197_37

def crepBody197_39 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody197_38

def data197 : CrepProg (BitVec 64) := crepBody197_39
def output197 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [104#8, 116#8, 114#8, 95#8, 114#8, 101#8, 113#8, 117#8, 101#8, 115#8, 116#8, 95#8, 108#8, 105#8, 115#8, 116#8], [0, 1, 2, 3, 4], crepProgToHOL data197)
end InitECandidate.Proofs.FrontendStages.Crep
