import InitECandidate.Proofs.FrontendStages.Crep.Translate730
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody746_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "heap_mark" []

def crepBody746_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc" [Flapjack.CrepExp.const 144#64]

def crepBody746_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "alloc" [Flapjack.CrepExp.const 288#64]

def crepBody746_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "alloc" [Flapjack.CrepExp.const 576#64]

def crepBody746_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "fp12_set_one" [Flapjack.CrepExp.var 6]

def crepBody746_5 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody746_4

def crepBody746_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "g1_decode" [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 4]

def crepBody746_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "heap_release" [Flapjack.CrepExp.var 3]

def crepBody746_8 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody746_7

def crepBody746_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1#64]

def crepBody746_10 : CrepProg (BitVec 64) :=
.seq crepBody746_8 crepBody746_9

def crepBody746_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody746_12 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.const 0#64)) crepBody746_10 crepBody746_11

def crepBody746_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "g1_subgroup_check" [Flapjack.CrepExp.var 4]

def crepBody746_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "heap_release" [Flapjack.CrepExp.var 3]

def crepBody746_15 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody746_14

def crepBody746_16 : CrepProg (BitVec 64) :=
.seq crepBody746_15 crepBody746_9

def crepBody746_17 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 0#64)) crepBody746_16 crepBody746_11

def crepBody746_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "g2_decode"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 128#64],
    Flapjack.CrepExp.var 5]

def crepBody746_19 : CrepProg (BitVec 64) :=
.seq crepBody746_17 crepBody746_18

def crepBody746_20 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.const 0#64)) crepBody746_16 crepBody746_11

def crepBody746_21 : CrepProg (BitVec 64) :=
.seq crepBody746_19 crepBody746_20

def crepBody746_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "g2_subgroup_check" [Flapjack.CrepExp.var 5]

def crepBody746_23 : CrepProg (BitVec 64) :=
.seq crepBody746_21 crepBody746_22

def crepBody746_24 : CrepProg (BitVec 64) :=
.seq crepBody746_23 crepBody746_17

def crepBody746_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "pair_accumulate"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody746_26 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody746_25

def crepBody746_27 : CrepProg (BitVec 64) :=
.seq crepBody746_24 crepBody746_26

def crepBody746_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.var 11)

def crepBody746_29 : CrepProg (BitVec 64) :=
.seq crepBody746_28 crepBody746_11

def crepBody746_30 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 1#64]) crepBody746_29

def crepBody746_31 : CrepProg (BitVec 64) :=
.seq crepBody746_27 crepBody746_30

def crepBody746_32 : CrepProg (BitVec 64) :=
.seq crepBody746_13 crepBody746_31

def crepBody746_33 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody746_32

def crepBody746_34 : CrepProg (BitVec 64) :=
.seq crepBody746_12 crepBody746_33

def crepBody746_35 : CrepProg (BitVec 64) :=
.seq crepBody746_6 crepBody746_34

def crepBody746_36 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody746_35

def crepBody746_37 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 0,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 384#64]]) crepBody746_36

def crepBody746_38 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.var 1)) crepBody746_37

def crepBody746_39 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "fp12_final_exp" [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 6]

def crepBody746_40 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody746_39

def crepBody746_41 : CrepProg (BitVec 64) :=
.seq crepBody746_38 crepBody746_40

def crepBody746_42 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "fp12_is_one" [Flapjack.CrepExp.var 6]

def crepBody746_43 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "memzero" [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 32#64]

def crepBody746_44 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody746_43

def crepBody746_45 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 31#64])
  (Flapjack.CrepExp.var 8)

def crepBody746_46 : CrepProg (BitVec 64) :=
.seq crepBody746_44 crepBody746_45

def crepBody746_47 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "heap_release" [Flapjack.CrepExp.var 3]

def crepBody746_48 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody746_47

def crepBody746_49 : CrepProg (BitVec 64) :=
.seq crepBody746_46 crepBody746_48

def crepBody746_50 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody746_51 : CrepProg (BitVec 64) :=
.seq crepBody746_49 crepBody746_50

def crepBody746_52 : CrepProg (BitVec 64) :=
.seq crepBody746_42 crepBody746_51

def crepBody746_53 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody746_52

def crepBody746_54 : CrepProg (BitVec 64) :=
.seq crepBody746_41 crepBody746_53

def crepBody746_55 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody746_54

def crepBody746_56 : CrepProg (BitVec 64) :=
.seq crepBody746_5 crepBody746_55

def crepBody746_57 : CrepProg (BitVec 64) :=
.seq crepBody746_3 crepBody746_56

def crepBody746_58 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody746_57

def crepBody746_59 : CrepProg (BitVec 64) :=
.seq crepBody746_2 crepBody746_58

def crepBody746_60 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody746_59

def crepBody746_61 : CrepProg (BitVec 64) :=
.seq crepBody746_1 crepBody746_60

def crepBody746_62 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody746_61

def crepBody746_63 : CrepProg (BitVec 64) :=
.seq crepBody746_0 crepBody746_62

def crepBody746_64 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody746_63

def data746 : CrepProg (BitVec 64) := crepBody746_64
def output746 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [98#8, 108#8, 115#8, 95#8, 112#8, 97#8, 105#8, 114#8, 105#8, 110#8, 103#8, 95#8, 101#8, 120#8, 101#8, 99#8], [0, 1, 2], crepProgToHOL data746)
end InitECandidate.Proofs.FrontendStages.Crep
