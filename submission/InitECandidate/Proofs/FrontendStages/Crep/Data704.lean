import InitECandidate.Proofs.FrontendStages.Crep.Translate688
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody704_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "heap_mark" []

def crepBody704_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "alloc" [Flapjack.CrepExp.const 144#64]

def crepBody704_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "alloc" [Flapjack.CrepExp.const 144#64]

def crepBody704_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "g1_copy" [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 1]

def crepBody704_4 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody704_3

def crepBody704_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "g1_set_inf" [Flapjack.CrepExp.var 5]

def crepBody704_6 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody704_5

def crepBody704_7 : CrepProg (BitVec 64) :=
.seq crepBody704_4 crepBody704_6

def crepBody704_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.var 9)

def crepBody704_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody704_10 : CrepProg (BitVec 64) :=
.seq crepBody704_8 crepBody704_9

def crepBody704_11 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 1#64]) crepBody704_10

def crepBody704_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "g1_double" [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 5]

def crepBody704_13 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody704_12

def crepBody704_14 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.const 1#64)) crepBody704_13 crepBody704_9

def crepBody704_15 : CrepProg (BitVec 64) :=
.seq crepBody704_11 crepBody704_14

def crepBody704_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "g1_add"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6]

def crepBody704_17 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody704_16

def crepBody704_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.const 1#64)

def crepBody704_19 : CrepProg (BitVec 64) :=
.seq crepBody704_18 crepBody704_9

def crepBody704_20 : CrepProg (BitVec 64) :=
.seq crepBody704_17 crepBody704_19

def crepBody704_21 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.const 1#64)) crepBody704_20 crepBody704_9

def crepBody704_22 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.shift Flapjack.Shift.lsr
      (Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 2,
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
              [Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 6#64),
                Flapjack.CrepExp.const 8#64]]))
      (Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 63#64]),
    Flapjack.CrepExp.const 1#64]) crepBody704_21

def crepBody704_23 : CrepProg (BitVec 64) :=
.seq crepBody704_15 crepBody704_22

def crepBody704_24 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 0#64) (Flapjack.CrepExp.var 7)) crepBody704_23

def crepBody704_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "g1_copy" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 5]

def crepBody704_26 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody704_25

def crepBody704_27 : CrepProg (BitVec 64) :=
.seq crepBody704_24 crepBody704_26

def crepBody704_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "heap_release" [Flapjack.CrepExp.var 4]

def crepBody704_29 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody704_28

def crepBody704_30 : CrepProg (BitVec 64) :=
.seq crepBody704_27 crepBody704_29

def crepBody704_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody704_32 : CrepProg (BitVec 64) :=
.seq crepBody704_30 crepBody704_31

def crepBody704_33 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody704_32

def crepBody704_34 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 64#64]) crepBody704_33

def crepBody704_35 : CrepProg (BitVec 64) :=
.seq crepBody704_7 crepBody704_34

def crepBody704_36 : CrepProg (BitVec 64) :=
.seq crepBody704_2 crepBody704_35

def crepBody704_37 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody704_36

def crepBody704_38 : CrepProg (BitVec 64) :=
.seq crepBody704_1 crepBody704_37

def crepBody704_39 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody704_38

def crepBody704_40 : CrepProg (BitVec 64) :=
.seq crepBody704_0 crepBody704_39

def crepBody704_41 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody704_40

def data704 : CrepProg (BitVec 64) := crepBody704_41
def output704 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [103#8, 49#8, 95#8, 109#8, 117#8, 108#8], [0, 1, 2, 3], crepProgToHOL data704)
end InitECandidate.Proofs.FrontendStages.Crep
