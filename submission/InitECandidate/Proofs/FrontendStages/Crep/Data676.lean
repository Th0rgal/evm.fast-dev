import InitECandidate.Proofs.FrontendStages.Crep.Translate660
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody676_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "heap_mark" []

def crepBody676_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "alloc" [Flapjack.CrepExp.const 96#64]

def crepBody676_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "alloc" [Flapjack.CrepExp.const 96#64]

def crepBody676_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "fp2_copy" [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 1]

def crepBody676_4 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody676_3

def crepBody676_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "fp2_set_one" [Flapjack.CrepExp.var 6]

def crepBody676_6 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody676_5

def crepBody676_7 : CrepProg (BitVec 64) :=
.seq crepBody676_4 crepBody676_6

def crepBody676_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.var 9)

def crepBody676_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody676_10 : CrepProg (BitVec 64) :=
.seq crepBody676_8 crepBody676_9

def crepBody676_11 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 1#64]) crepBody676_10

def crepBody676_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp2_sqr" [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 6]

def crepBody676_13 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody676_12

def crepBody676_14 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 1#64)) crepBody676_13 crepBody676_9

def crepBody676_15 : CrepProg (BitVec 64) :=
.seq crepBody676_11 crepBody676_14

def crepBody676_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp2_mul"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 5]

def crepBody676_17 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody676_16

def crepBody676_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.const 1#64)

def crepBody676_19 : CrepProg (BitVec 64) :=
.seq crepBody676_18 crepBody676_9

def crepBody676_20 : CrepProg (BitVec 64) :=
.seq crepBody676_17 crepBody676_19

def crepBody676_21 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.const 1#64)) crepBody676_20 crepBody676_9

def crepBody676_22 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.shift Flapjack.Shift.lsr
      (Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 2,
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
              [Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.const 6#64),
                Flapjack.CrepExp.const 8#64]]))
      (Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 63#64]),
    Flapjack.CrepExp.const 1#64]) crepBody676_21

def crepBody676_23 : CrepProg (BitVec 64) :=
.seq crepBody676_15 crepBody676_22

def crepBody676_24 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 0#64) (Flapjack.CrepExp.var 8)) crepBody676_23

def crepBody676_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp2_copy" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 6]

def crepBody676_26 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody676_25

def crepBody676_27 : CrepProg (BitVec 64) :=
.seq crepBody676_24 crepBody676_26

def crepBody676_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "heap_release" [Flapjack.CrepExp.var 4]

def crepBody676_29 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody676_28

def crepBody676_30 : CrepProg (BitVec 64) :=
.seq crepBody676_27 crepBody676_29

def crepBody676_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody676_32 : CrepProg (BitVec 64) :=
.seq crepBody676_30 crepBody676_31

def crepBody676_33 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 64#64]) crepBody676_32

def crepBody676_34 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody676_33

def crepBody676_35 : CrepProg (BitVec 64) :=
.seq crepBody676_7 crepBody676_34

def crepBody676_36 : CrepProg (BitVec 64) :=
.seq crepBody676_2 crepBody676_35

def crepBody676_37 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody676_36

def crepBody676_38 : CrepProg (BitVec 64) :=
.seq crepBody676_1 crepBody676_37

def crepBody676_39 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody676_38

def crepBody676_40 : CrepProg (BitVec 64) :=
.seq crepBody676_0 crepBody676_39

def crepBody676_41 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody676_40

def data676 : CrepProg (BitVec 64) := crepBody676_41
def output676 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 112#8, 50#8, 95#8, 112#8, 111#8, 119#8], [0, 1, 2, 3], crepProgToHOL data676)
end InitECandidate.Proofs.FrontendStages.Crep
