import InitECandidate.Proofs.FrontendStages.Crep.Translate718
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody734_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "heap_mark" []

def crepBody734_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "alloc" [Flapjack.CrepExp.const 96#64]

def crepBody734_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "alloc" [Flapjack.CrepExp.const 96#64]

def crepBody734_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "fp2_copy"
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 1,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
          [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 1#64],
            Flapjack.CrepExp.const 96#64]]]

def crepBody734_4 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody734_3

def crepBody734_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp2_mul"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 3]

def crepBody734_6 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody734_5

def crepBody734_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp2_mul"
  [Flapjack.CrepExp.var 7,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 4,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 96#64]],
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 1,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
          [Flapjack.CrepExp.op Flapjack.BinOp.sub
              [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 2#64],
                Flapjack.CrepExp.var 8],
            Flapjack.CrepExp.const 96#64]]]

def crepBody734_8 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody734_7

def crepBody734_9 : CrepProg (BitVec 64) :=
.seq crepBody734_6 crepBody734_8

def crepBody734_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp2_add"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7]

def crepBody734_11 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody734_10

def crepBody734_12 : CrepProg (BitVec 64) :=
.seq crepBody734_9 crepBody734_11

def crepBody734_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.var 9)

def crepBody734_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody734_15 : CrepProg (BitVec 64) :=
.seq crepBody734_13 crepBody734_14

def crepBody734_16 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 1#64]) crepBody734_15

def crepBody734_17 : CrepProg (BitVec 64) :=
.seq crepBody734_12 crepBody734_16

def crepBody734_18 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 8)
  (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 1#64])) crepBody734_17

def crepBody734_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp2_copy" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 6]

def crepBody734_20 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody734_19

def crepBody734_21 : CrepProg (BitVec 64) :=
.seq crepBody734_18 crepBody734_20

def crepBody734_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "heap_release" [Flapjack.CrepExp.var 5]

def crepBody734_23 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody734_22

def crepBody734_24 : CrepProg (BitVec 64) :=
.seq crepBody734_21 crepBody734_23

def crepBody734_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody734_26 : CrepProg (BitVec 64) :=
.seq crepBody734_24 crepBody734_25

def crepBody734_27 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody734_26

def crepBody734_28 : CrepProg (BitVec 64) :=
.seq crepBody734_4 crepBody734_27

def crepBody734_29 : CrepProg (BitVec 64) :=
.seq crepBody734_2 crepBody734_28

def crepBody734_30 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody734_29

def crepBody734_31 : CrepProg (BitVec 64) :=
.seq crepBody734_1 crepBody734_30

def crepBody734_32 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody734_31

def crepBody734_33 : CrepProg (BitVec 64) :=
.seq crepBody734_0 crepBody734_32

def crepBody734_34 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody734_33

def data734 : CrepProg (BitVec 64) := crepBody734_34
def output734 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [105#8, 115#8, 111#8, 95#8, 104#8, 111#8, 114#8, 110#8, 101#8, 114#8, 95#8, 102#8, 112#8, 50#8], [0, 1, 2, 3, 4], crepProgToHOL data734)
end InitECandidate.Proofs.FrontendStages.Crep
