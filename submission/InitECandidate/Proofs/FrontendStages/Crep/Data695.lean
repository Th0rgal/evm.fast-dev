import InitECandidate.Proofs.FrontendStages.Crep.Translate679
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody695_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "heap_mark" []

def crepBody695_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 576#64]

def crepBody695_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc" [Flapjack.CrepExp.const 576#64]

def crepBody695_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "fp12_copy" [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 1]

def crepBody695_4 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody695_3

def crepBody695_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "fp12_set_one" [Flapjack.CrepExp.var 4]

def crepBody695_6 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody695_5

def crepBody695_7 : CrepProg (BitVec 64) :=
.seq crepBody695_4 crepBody695_6

def crepBody695_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.var 8)

def crepBody695_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody695_10 : CrepProg (BitVec 64) :=
.seq crepBody695_8 crepBody695_9

def crepBody695_11 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 1#64]) crepBody695_10

def crepBody695_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "fp12_mul"
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 4]

def crepBody695_13 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody695_12

def crepBody695_14 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 1#64)) crepBody695_13 crepBody695_9

def crepBody695_15 : CrepProg (BitVec 64) :=
.seq crepBody695_11 crepBody695_14

def crepBody695_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "fp12_mul"
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 3]

def crepBody695_17 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody695_16

def crepBody695_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6 (Flapjack.CrepExp.const 1#64)

def crepBody695_19 : CrepProg (BitVec 64) :=
.seq crepBody695_18 crepBody695_9

def crepBody695_20 : CrepProg (BitVec 64) :=
.seq crepBody695_17 crepBody695_19

def crepBody695_21 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.op Flapjack.BinOp.and
    [Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 7),
      Flapjack.CrepExp.const 1#64])
  (Flapjack.CrepExp.const 1#64)) crepBody695_20 crepBody695_9

def crepBody695_22 : CrepProg (BitVec 64) :=
.seq crepBody695_15 crepBody695_21

def crepBody695_23 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 0#64) (Flapjack.CrepExp.var 7)) crepBody695_22

def crepBody695_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "fp12_copy" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 4]

def crepBody695_25 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody695_24

def crepBody695_26 : CrepProg (BitVec 64) :=
.seq crepBody695_23 crepBody695_25

def crepBody695_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody695_28 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody695_27

def crepBody695_29 : CrepProg (BitVec 64) :=
.seq crepBody695_26 crepBody695_28

def crepBody695_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody695_31 : CrepProg (BitVec 64) :=
.seq crepBody695_29 crepBody695_30

def crepBody695_32 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 64#64) crepBody695_31

def crepBody695_33 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody695_32

def crepBody695_34 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
      Flapjack.CrepExp.const 1376#64])) crepBody695_33

def crepBody695_35 : CrepProg (BitVec 64) :=
.seq crepBody695_7 crepBody695_34

def crepBody695_36 : CrepProg (BitVec 64) :=
.seq crepBody695_2 crepBody695_35

def crepBody695_37 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody695_36

def crepBody695_38 : CrepProg (BitVec 64) :=
.seq crepBody695_1 crepBody695_37

def crepBody695_39 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody695_38

def crepBody695_40 : CrepProg (BitVec 64) :=
.seq crepBody695_0 crepBody695_39

def crepBody695_41 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody695_40

def data695 : CrepProg (BitVec 64) := crepBody695_41
def output695 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [102#8, 112#8, 49#8, 50#8, 95#8, 112#8, 111#8, 119#8, 95#8, 97#8, 98#8, 115#8, 120#8], [0, 1], crepProgToHOL data695)
end InitECandidate.Proofs.FrontendStages.Crep
