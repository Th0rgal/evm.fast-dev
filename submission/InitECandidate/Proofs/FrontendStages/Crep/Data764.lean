import InitECandidate.Proofs.FrontendStages.Crep.Translate748
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody764_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "charge_gas" [Flapjack.CrepExp.const 3000#64]

def crepBody764_1 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody764_0

def crepBody764_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody764_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 8#64]

def crepBody764_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "heap_mark" []

def crepBody764_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "alloc" [Flapjack.CrepExp.const 128#64]

def crepBody764_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "buffer_read"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 88#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64]),
    Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 128#64, Flapjack.CrepExp.var 5]

def crepBody764_7 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody764_6

def crepBody764_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6, 7, 8, 9], none)) "u256_from_be"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 32#64],
    Flapjack.CrepExp.const 32#64]

def crepBody764_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10, 11, 12, 13], none)) "u256_from_be"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 64#64],
    Flapjack.CrepExp.const 32#64]

def crepBody764_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14, 15, 16, 17], none)) "u256_from_be"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.const 32#64]

def crepBody764_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "u256_fits_word"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9]

def crepBody764_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "heap_release" [Flapjack.CrepExp.var 4]

def crepBody764_13 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody764_12

def crepBody764_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 19) (Flapjack.CrepExp.var 20)

def crepBody764_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody764_16 : CrepProg (BitVec 64) :=
.seq crepBody764_14 crepBody764_15

def crepBody764_17 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 3) crepBody764_16

def crepBody764_18 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 120#64]) crepBody764_17

def crepBody764_19 : CrepProg (BitVec 64) :=
.seq crepBody764_13 crepBody764_18

def crepBody764_20 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody764_16

def crepBody764_21 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 128#64]) crepBody764_20

def crepBody764_22 : CrepProg (BitVec 64) :=
.seq crepBody764_19 crepBody764_21

def crepBody764_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody764_24 : CrepProg (BitVec 64) :=
.seq crepBody764_22 crepBody764_23

def crepBody764_25 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 18) (Flapjack.CrepExp.const 0#64)) crepBody764_24 crepBody764_15

def crepBody764_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "secp256k1_ecrecover"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11,
    Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15,
    Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 12#64]]

def crepBody764_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "heap_release" [Flapjack.CrepExp.var 4]

def crepBody764_28 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody764_27

def crepBody764_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 20) (Flapjack.CrepExp.var 21)

def crepBody764_30 : CrepProg (BitVec 64) :=
.seq crepBody764_29 crepBody764_15

def crepBody764_31 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.var 3) crepBody764_30

def crepBody764_32 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 120#64]) crepBody764_31

def crepBody764_33 : CrepProg (BitVec 64) :=
.seq crepBody764_28 crepBody764_32

def crepBody764_34 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody764_30

def crepBody764_35 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 128#64]) crepBody764_34

def crepBody764_36 : CrepProg (BitVec 64) :=
.seq crepBody764_33 crepBody764_35

def crepBody764_37 : CrepProg (BitVec 64) :=
.seq crepBody764_36 crepBody764_23

def crepBody764_38 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 19) (Flapjack.CrepExp.const 0#64)) crepBody764_37 crepBody764_15

def crepBody764_39 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "memzero" [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 12#64]

def crepBody764_40 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody764_39

def crepBody764_41 : CrepProg (BitVec 64) :=
.seq crepBody764_38 crepBody764_40

def crepBody764_42 : CrepProg (BitVec 64) :=
.seq crepBody764_41 crepBody764_28

def crepBody764_43 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.var 2) crepBody764_30

def crepBody764_44 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 120#64]) crepBody764_43

def crepBody764_45 : CrepProg (BitVec 64) :=
.seq crepBody764_42 crepBody764_44

def crepBody764_46 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 32#64) crepBody764_30

def crepBody764_47 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 128#64]) crepBody764_46

def crepBody764_48 : CrepProg (BitVec 64) :=
.seq crepBody764_45 crepBody764_47

def crepBody764_49 : CrepProg (BitVec 64) :=
.seq crepBody764_48 crepBody764_23

def crepBody764_50 : CrepProg (BitVec 64) :=
.seq crepBody764_26 crepBody764_49

def crepBody764_51 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody764_50

def crepBody764_52 : CrepProg (BitVec 64) :=
.seq crepBody764_25 crepBody764_51

def crepBody764_53 : CrepProg (BitVec 64) :=
.seq crepBody764_11 crepBody764_52

def crepBody764_54 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody764_53

def crepBody764_55 : CrepProg (BitVec 64) :=
.seq crepBody764_10 crepBody764_54

def crepBody764_56 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody764_55

def crepBody764_57 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody764_56

def crepBody764_58 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody764_57

def crepBody764_59 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody764_58

def crepBody764_60 : CrepProg (BitVec 64) :=
.seq crepBody764_9 crepBody764_59

def crepBody764_61 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody764_60

def crepBody764_62 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody764_61

def crepBody764_63 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody764_62

def crepBody764_64 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody764_63

def crepBody764_65 : CrepProg (BitVec 64) :=
.seq crepBody764_8 crepBody764_64

def crepBody764_66 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody764_65

def crepBody764_67 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody764_66

def crepBody764_68 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody764_67

def crepBody764_69 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody764_68

def crepBody764_70 : CrepProg (BitVec 64) :=
.seq crepBody764_7 crepBody764_69

def crepBody764_71 : CrepProg (BitVec 64) :=
.seq crepBody764_5 crepBody764_70

def crepBody764_72 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody764_71

def crepBody764_73 : CrepProg (BitVec 64) :=
.seq crepBody764_4 crepBody764_72

def crepBody764_74 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody764_73

def crepBody764_75 : CrepProg (BitVec 64) :=
.seq crepBody764_3 crepBody764_74

def crepBody764_76 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody764_75

def crepBody764_77 : CrepProg (BitVec 64) :=
.seq crepBody764_2 crepBody764_76

def crepBody764_78 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody764_77

def crepBody764_79 : CrepProg (BitVec 64) :=
.seq crepBody764_1 crepBody764_78

def crepBody764_80 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 112#64])) crepBody764_79

def data764 : CrepProg (BitVec 64) := crepBody764_80
def output764 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 114#8, 101#8, 95#8, 101#8, 99#8, 114#8, 101#8, 99#8, 111#8, 118#8, 101#8, 114#8], [], crepProgToHOL data764)
end InitECandidate.Proofs.FrontendStages.Crep
