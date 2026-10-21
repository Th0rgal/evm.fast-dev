import InitECandidate.Proofs.FrontendStages.Crep.Translate240
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody256_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "scratch_mark" []

def crepBody256_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "scratch_alloc" [Flapjack.CrepExp.const 48#64]

def crepBody256_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 4)

def crepBody256_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody256_4 : CrepProg (BitVec 64) :=
.seq crepBody256_2 crepBody256_3

def crepBody256_5 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody256_4

def crepBody256_6 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 0#64]) crepBody256_5

def crepBody256_7 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.var 0) crepBody256_4

def crepBody256_8 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 8#64]) crepBody256_7

def crepBody256_9 : CrepProg (BitVec 64) :=
.seq crepBody256_6 crepBody256_8

def crepBody256_10 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 16#64]) crepBody256_5

def crepBody256_11 : CrepProg (BitVec 64) :=
.seq crepBody256_9 crepBody256_10

def crepBody256_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "_node_rlp_begin" [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 0]

def crepBody256_13 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody256_12

def crepBody256_14 : CrepProg (BitVec 64) :=
.seq crepBody256_11 crepBody256_13

def crepBody256_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.var 9)

def crepBody256_16 : CrepProg (BitVec 64) :=
.seq crepBody256_15 crepBody256_3

def crepBody256_17 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 1#64) crepBody256_16

def crepBody256_18 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 16#64]) crepBody256_17

def crepBody256_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 48#64]))

def crepBody256_20 : CrepProg (BitVec 64) :=
.seq crepBody256_19 crepBody256_3

def crepBody256_21 : CrepProg (BitVec 64) :=
.seq crepBody256_18 crepBody256_20

def crepBody256_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "_node_needs_rlp" [Flapjack.CrepExp.var 6]

def crepBody256_23 : CrepProg (BitVec 64) :=
.seq crepBody256_21 crepBody256_22

def crepBody256_24 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 16#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody256_23 crepBody256_3

def crepBody256_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 32#64,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 8#64]]))

def crepBody256_26 : CrepProg (BitVec 64) :=
.seq crepBody256_25 crepBody256_3

def crepBody256_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.var 9)

def crepBody256_28 : CrepProg (BitVec 64) :=
.seq crepBody256_27 crepBody256_3

def crepBody256_29 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 1#64]) crepBody256_28

def crepBody256_30 : CrepProg (BitVec 64) :=
.seq crepBody256_26 crepBody256_29

def crepBody256_31 : CrepProg (BitVec 64) :=
.seq crepBody256_30 crepBody256_22

def crepBody256_32 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.const 16#64)),
    Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 0#64))]) crepBody256_31

def crepBody256_33 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.var 10)

def crepBody256_34 : CrepProg (BitVec 64) :=
.seq crepBody256_33 crepBody256_3

def crepBody256_35 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 8) crepBody256_34

def crepBody256_36 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 16#64]) crepBody256_35

def crepBody256_37 : CrepProg (BitVec 64) :=
.seq crepBody256_32 crepBody256_36

def crepBody256_38 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 16#64])) crepBody256_37

def crepBody256_39 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 3#64)) crepBody256_38 crepBody256_3

def crepBody256_40 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 2#64)) crepBody256_24 crepBody256_39

def crepBody256_41 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "scratch_alloc" [Flapjack.CrepExp.const 48#64]

def crepBody256_42 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 3) crepBody256_34

def crepBody256_43 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 0#64]) crepBody256_42

def crepBody256_44 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 6) crepBody256_34

def crepBody256_45 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 8#64]) crepBody256_44

def crepBody256_46 : CrepProg (BitVec 64) :=
.seq crepBody256_43 crepBody256_45

def crepBody256_47 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody256_34

def crepBody256_48 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 16#64]) crepBody256_47

def crepBody256_49 : CrepProg (BitVec 64) :=
.seq crepBody256_46 crepBody256_48

def crepBody256_50 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "_node_rlp_begin" [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 6]

def crepBody256_51 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody256_50

def crepBody256_52 : CrepProg (BitVec 64) :=
.seq crepBody256_49 crepBody256_51

def crepBody256_53 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 8)

def crepBody256_54 : CrepProg (BitVec 64) :=
.seq crepBody256_53 crepBody256_3

def crepBody256_55 : CrepProg (BitVec 64) :=
.seq crepBody256_52 crepBody256_54

def crepBody256_56 : CrepProg (BitVec 64) :=
.seq crepBody256_41 crepBody256_55

def crepBody256_57 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody256_56

def crepBody256_58 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "_node_rlp_finish" [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody256_59 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody256_58

def crepBody256_60 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 0#64])) crepBody256_54

def crepBody256_61 : CrepProg (BitVec 64) :=
.seq crepBody256_59 crepBody256_60

def crepBody256_62 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 0#64)) crepBody256_57 crepBody256_61

def crepBody256_63 : CrepProg (BitVec 64) :=
.seq crepBody256_40 crepBody256_62

def crepBody256_64 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody256_63

def crepBody256_65 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody256_64

def crepBody256_66 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 0#64])) crepBody256_65

def crepBody256_67 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 8#64])) crepBody256_66

def crepBody256_68 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 0#64)) crepBody256_67

def crepBody256_69 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "scratch_release" [Flapjack.CrepExp.var 1]

def crepBody256_70 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody256_69

def crepBody256_71 : CrepProg (BitVec 64) :=
.seq crepBody256_68 crepBody256_70

def crepBody256_72 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody256_73 : CrepProg (BitVec 64) :=
.seq crepBody256_71 crepBody256_72

def crepBody256_74 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.var 2) crepBody256_73

def crepBody256_75 : CrepProg (BitVec 64) :=
.seq crepBody256_14 crepBody256_74

def crepBody256_76 : CrepProg (BitVec 64) :=
.seq crepBody256_1 crepBody256_75

def crepBody256_77 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody256_76

def crepBody256_78 : CrepProg (BitVec 64) :=
.seq crepBody256_0 crepBody256_77

def crepBody256_79 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody256_78

def data256 : CrepProg (BitVec 64) := crepBody256_79
def output256 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [95#8, 110#8, 111#8, 100#8, 101#8, 95#8, 114#8, 108#8, 112#8, 95#8, 102#8, 105#8, 108#8, 108#8], [0], crepProgToHOL data256)
end InitECandidate.Proofs.FrontendStages.Crep
