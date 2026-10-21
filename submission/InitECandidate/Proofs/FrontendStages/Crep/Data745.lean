import InitECandidate.Proofs.FrontendStages.Crep.Translate729
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody745_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "heap_mark" []

def crepBody745_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc" [Flapjack.CrepExp.const 288#64]

def crepBody745_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "alloc" [Flapjack.CrepExp.const 288#64]

def crepBody745_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody745_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "g2_decode" [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 5]

def crepBody745_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "heap_release" [Flapjack.CrepExp.var 3]

def crepBody745_6 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody745_5

def crepBody745_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1#64]

def crepBody745_8 : CrepProg (BitVec 64) :=
.seq crepBody745_6 crepBody745_7

def crepBody745_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody745_10 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.const 0#64)) crepBody745_8 crepBody745_9

def crepBody745_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "g2_subgroup_check" [Flapjack.CrepExp.var 5]

def crepBody745_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "heap_release" [Flapjack.CrepExp.var 3]

def crepBody745_13 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody745_12

def crepBody745_14 : CrepProg (BitVec 64) :=
.seq crepBody745_13 crepBody745_7

def crepBody745_15 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 0#64)) crepBody745_14 crepBody745_9

def crepBody745_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11, 12, 13, 14], none)) "u256_from_be"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 256#64],
    Flapjack.CrepExp.const 32#64]

def crepBody745_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 15) (Flapjack.CrepExp.var 16)

def crepBody745_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 17)

def crepBody745_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 18)

def crepBody745_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 19)

def crepBody745_21 : CrepProg (BitVec 64) :=
.seq crepBody745_20 crepBody745_9

def crepBody745_22 : CrepProg (BitVec 64) :=
.seq crepBody745_19 crepBody745_21

def crepBody745_23 : CrepProg (BitVec 64) :=
.seq crepBody745_18 crepBody745_22

def crepBody745_24 : CrepProg (BitVec 64) :=
.seq crepBody745_17 crepBody745_23

def crepBody745_25 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.var 14) crepBody745_24

def crepBody745_26 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.var 13) crepBody745_25

def crepBody745_27 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.var 12) crepBody745_26

def crepBody745_28 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.var 11) crepBody745_27

def crepBody745_29 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.var 6) crepBody745_28

def crepBody745_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "g2_mul"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 4#64]

def crepBody745_31 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody745_30

def crepBody745_32 : CrepProg (BitVec 64) :=
.seq crepBody745_29 crepBody745_31

def crepBody745_33 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "g2_copy" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody745_34 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody745_33

def crepBody745_35 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "g2_add"
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody745_36 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody745_35

def crepBody745_37 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 0#64)) crepBody745_34 crepBody745_36

def crepBody745_38 : CrepProg (BitVec 64) :=
.seq crepBody745_32 crepBody745_37

def crepBody745_39 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.var 15)

def crepBody745_40 : CrepProg (BitVec 64) :=
.seq crepBody745_39 crepBody745_9

def crepBody745_41 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 1#64]) crepBody745_40

def crepBody745_42 : CrepProg (BitVec 64) :=
.seq crepBody745_38 crepBody745_41

def crepBody745_43 : CrepProg (BitVec 64) :=
.seq crepBody745_16 crepBody745_42

def crepBody745_44 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody745_43

def crepBody745_45 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody745_44

def crepBody745_46 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody745_45

def crepBody745_47 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody745_46

def crepBody745_48 : CrepProg (BitVec 64) :=
.seq crepBody745_15 crepBody745_47

def crepBody745_49 : CrepProg (BitVec 64) :=
.seq crepBody745_11 crepBody745_48

def crepBody745_50 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody745_49

def crepBody745_51 : CrepProg (BitVec 64) :=
.seq crepBody745_10 crepBody745_50

def crepBody745_52 : CrepProg (BitVec 64) :=
.seq crepBody745_4 crepBody745_51

def crepBody745_53 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody745_52

def crepBody745_54 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 0,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 288#64]]) crepBody745_53

def crepBody745_55 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.var 1)) crepBody745_54

def crepBody745_56 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "g2_encode" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 2]

def crepBody745_57 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody745_56

def crepBody745_58 : CrepProg (BitVec 64) :=
.seq crepBody745_55 crepBody745_57

def crepBody745_59 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "heap_release" [Flapjack.CrepExp.var 3]

def crepBody745_60 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody745_59

def crepBody745_61 : CrepProg (BitVec 64) :=
.seq crepBody745_58 crepBody745_60

def crepBody745_62 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody745_63 : CrepProg (BitVec 64) :=
.seq crepBody745_61 crepBody745_62

def crepBody745_64 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody745_63

def crepBody745_65 : CrepProg (BitVec 64) :=
.seq crepBody745_3 crepBody745_64

def crepBody745_66 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody745_65

def crepBody745_67 : CrepProg (BitVec 64) :=
.seq crepBody745_2 crepBody745_66

def crepBody745_68 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody745_67

def crepBody745_69 : CrepProg (BitVec 64) :=
.seq crepBody745_1 crepBody745_68

def crepBody745_70 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody745_69

def crepBody745_71 : CrepProg (BitVec 64) :=
.seq crepBody745_0 crepBody745_70

def crepBody745_72 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody745_71

def data745 : CrepProg (BitVec 64) := crepBody745_72
def output745 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [98#8, 108#8, 115#8, 95#8, 103#8, 50#8, 95#8, 109#8, 115#8, 109#8, 95#8, 101#8, 120#8, 101#8, 99#8], [0, 1, 2], crepProgToHOL data745)
end InitECandidate.Proofs.FrontendStages.Crep
