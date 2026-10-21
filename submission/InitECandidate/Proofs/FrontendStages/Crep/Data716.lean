import InitECandidate.Proofs.FrontendStages.Crep.Translate700
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody716_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "heap_mark" []

def crepBody716_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "alloc" [Flapjack.CrepExp.const 288#64]

def crepBody716_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "g2_set_inf" [Flapjack.CrepExp.var 5]

def crepBody716_3 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody716_2

def crepBody716_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6 (Flapjack.CrepExp.var 8)

def crepBody716_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody716_6 : CrepProg (BitVec 64) :=
.seq crepBody716_4 crepBody716_5

def crepBody716_7 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 1#64]) crepBody716_6

def crepBody716_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "g2_double" [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 5]

def crepBody716_9 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody716_8

def crepBody716_10 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 1#64)) crepBody716_9 crepBody716_5

def crepBody716_11 : CrepProg (BitVec 64) :=
.seq crepBody716_7 crepBody716_10

def crepBody716_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "g2_add"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 1]

def crepBody716_13 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody716_12

def crepBody716_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.const 1#64)

def crepBody716_15 : CrepProg (BitVec 64) :=
.seq crepBody716_14 crepBody716_5

def crepBody716_16 : CrepProg (BitVec 64) :=
.seq crepBody716_13 crepBody716_15

def crepBody716_17 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.const 1#64)) crepBody716_16 crepBody716_5

def crepBody716_18 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.shift Flapjack.Shift.lsr
      (Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 2,
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
              [Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 6#64),
                Flapjack.CrepExp.const 8#64]]))
      (Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 63#64]),
    Flapjack.CrepExp.const 1#64]) crepBody716_17

def crepBody716_19 : CrepProg (BitVec 64) :=
.seq crepBody716_11 crepBody716_18

def crepBody716_20 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 0#64) (Flapjack.CrepExp.var 6)) crepBody716_19

def crepBody716_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "g2_copy" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 5]

def crepBody716_22 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody716_21

def crepBody716_23 : CrepProg (BitVec 64) :=
.seq crepBody716_20 crepBody716_22

def crepBody716_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "heap_release" [Flapjack.CrepExp.var 4]

def crepBody716_25 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody716_24

def crepBody716_26 : CrepProg (BitVec 64) :=
.seq crepBody716_23 crepBody716_25

def crepBody716_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody716_28 : CrepProg (BitVec 64) :=
.seq crepBody716_26 crepBody716_27

def crepBody716_29 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody716_28

def crepBody716_30 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 64#64]) crepBody716_29

def crepBody716_31 : CrepProg (BitVec 64) :=
.seq crepBody716_3 crepBody716_30

def crepBody716_32 : CrepProg (BitVec 64) :=
.seq crepBody716_1 crepBody716_31

def crepBody716_33 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody716_32

def crepBody716_34 : CrepProg (BitVec 64) :=
.seq crepBody716_0 crepBody716_33

def crepBody716_35 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody716_34

def data716 : CrepProg (BitVec 64) := crepBody716_35
def output716 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [103#8, 50#8, 95#8, 109#8, 117#8, 108#8], [0, 1, 2, 3], crepProgToHOL data716)
end InitECandidate.Proofs.FrontendStages.Crep
