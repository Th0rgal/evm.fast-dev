import InitECandidate.Proofs.FrontendStages.Crep.Translate610
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody626_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "bn254_init" []

def crepBody626_1 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody626_0

def crepBody626_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "ecp_is_inf" [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 1]

def crepBody626_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "ecp_is_inf" [Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.var 2]

def crepBody626_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "fe_set_one" [Flapjack.CrepExp.const 12#64, Flapjack.CrepExp.var 0]

def crepBody626_5 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody626_4

def crepBody626_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody626_7 : CrepProg (BitVec 64) :=
.seq crepBody626_5 crepBody626_6

def crepBody626_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody626_9 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.op Flapjack.BinOp.or [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]) (Flapjack.CrepExp.const 1#64)) crepBody626_7 crepBody626_8

def crepBody626_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "heap_mark" []

def crepBody626_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "alloc" [Flapjack.CrepExp.const 1152#64]

def crepBody626_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "alloc" [Flapjack.CrepExp.const 1152#64]

def crepBody626_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "alloc" [Flapjack.CrepExp.const 384#64]

def crepBody626_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "alloc" [Flapjack.CrepExp.const 384#64]

def crepBody626_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fq12_twist" [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 1]

def crepBody626_16 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody626_15

def crepBody626_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fq12_cast" [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 2]

def crepBody626_18 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody626_17

def crepBody626_19 : CrepProg (BitVec 64) :=
.seq crepBody626_16 crepBody626_18

def crepBody626_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "bn254_miller_raw"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7]

def crepBody626_21 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody626_20

def crepBody626_22 : CrepProg (BitVec 64) :=
.seq crepBody626_19 crepBody626_21

def crepBody626_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fq12_inv" [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 9]

def crepBody626_24 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody626_23

def crepBody626_25 : CrepProg (BitVec 64) :=
.seq crepBody626_22 crepBody626_24

def crepBody626_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fq12_mul"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9]

def crepBody626_27 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody626_26

def crepBody626_28 : CrepProg (BitVec 64) :=
.seq crepBody626_25 crepBody626_27

def crepBody626_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fq12_pow_words"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 8,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 384#64]),
    Flapjack.CrepExp.const 44#64]

def crepBody626_30 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody626_29

def crepBody626_31 : CrepProg (BitVec 64) :=
.seq crepBody626_28 crepBody626_30

def crepBody626_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "heap_release" [Flapjack.CrepExp.var 5]

def crepBody626_33 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody626_32

def crepBody626_34 : CrepProg (BitVec 64) :=
.seq crepBody626_31 crepBody626_33

def crepBody626_35 : CrepProg (BitVec 64) :=
.seq crepBody626_34 crepBody626_6

def crepBody626_36 : CrepProg (BitVec 64) :=
.seq crepBody626_14 crepBody626_35

def crepBody626_37 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody626_36

def crepBody626_38 : CrepProg (BitVec 64) :=
.seq crepBody626_13 crepBody626_37

def crepBody626_39 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody626_38

def crepBody626_40 : CrepProg (BitVec 64) :=
.seq crepBody626_12 crepBody626_39

def crepBody626_41 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody626_40

def crepBody626_42 : CrepProg (BitVec 64) :=
.seq crepBody626_11 crepBody626_41

def crepBody626_43 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody626_42

def crepBody626_44 : CrepProg (BitVec 64) :=
.seq crepBody626_10 crepBody626_43

def crepBody626_45 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody626_44

def crepBody626_46 : CrepProg (BitVec 64) :=
.seq crepBody626_9 crepBody626_45

def crepBody626_47 : CrepProg (BitVec 64) :=
.seq crepBody626_3 crepBody626_46

def crepBody626_48 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody626_47

def crepBody626_49 : CrepProg (BitVec 64) :=
.seq crepBody626_2 crepBody626_48

def crepBody626_50 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody626_49

def crepBody626_51 : CrepProg (BitVec 64) :=
.seq crepBody626_1 crepBody626_50

def data626 : CrepProg (BitVec 64) := crepBody626_51
def output626 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [98#8, 110#8, 50#8, 53#8, 52#8, 95#8, 112#8, 97#8, 105#8, 114#8, 105#8, 110#8, 103#8], [0, 1, 2], crepProgToHOL data626)
end InitECandidate.Proofs.FrontendStages.Crep
