import InitECandidate.Proofs.FrontendStages.Crep.Translate302
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody318_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 40#64]

def crepBody318_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.var 5)

def crepBody318_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody318_3 : CrepProg (BitVec 64) :=
.seq crepBody318_1 crepBody318_2

def crepBody318_4 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.var 3) crepBody318_3

def crepBody318_5 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 168#64]) crepBody318_4

def crepBody318_6 : CrepProg (BitVec 64) :=
.seq crepBody318_0 crepBody318_5

def crepBody318_7 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody318_6

def crepBody318_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 4)

def crepBody318_9 : CrepProg (BitVec 64) :=
.seq crepBody318_8 crepBody318_2

def crepBody318_10 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.var 0) crepBody318_9

def crepBody318_11 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 168#64]),
    Flapjack.CrepExp.const 0#64]) crepBody318_10

def crepBody318_12 : CrepProg (BitVec 64) :=
.seq crepBody318_7 crepBody318_11

def crepBody318_13 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.var 1) crepBody318_9

def crepBody318_14 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 168#64]),
    Flapjack.CrepExp.const 8#64]) crepBody318_13

def crepBody318_15 : CrepProg (BitVec 64) :=
.seq crepBody318_12 crepBody318_14

def crepBody318_16 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.var 2) crepBody318_9

def crepBody318_17 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 168#64]),
    Flapjack.CrepExp.const 16#64]) crepBody318_16

def crepBody318_18 : CrepProg (BitVec 64) :=
.seq crepBody318_15 crepBody318_17

def crepBody318_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "decode_witness_to_mpt" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody318_20 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 168#64]),
    Flapjack.CrepExp.const 24#64]) crepBody318_4

def crepBody318_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "htab_new" [Flapjack.CrepExp.const 32#64, Flapjack.CrepExp.const 64#64]

def crepBody318_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 6)

def crepBody318_23 : CrepProg (BitVec 64) :=
.seq crepBody318_22 crepBody318_2

def crepBody318_24 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 4) crepBody318_23

def crepBody318_25 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 168#64]),
    Flapjack.CrepExp.const 32#64]) crepBody318_24

def crepBody318_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "alloc" [Flapjack.CrepExp.const 80#64]

def crepBody318_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 7)

def crepBody318_28 : CrepProg (BitVec 64) :=
.seq crepBody318_27 crepBody318_2

def crepBody318_29 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 5) crepBody318_28

def crepBody318_30 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]) crepBody318_29

def crepBody318_31 : CrepProg (BitVec 64) :=
.seq crepBody318_26 crepBody318_30

def crepBody318_32 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody318_31

def crepBody318_33 : CrepProg (BitVec 64) :=
.seq crepBody318_25 crepBody318_32

def crepBody318_34 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 168#64])) crepBody318_23

def crepBody318_35 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]),
    Flapjack.CrepExp.const 0#64]) crepBody318_34

def crepBody318_36 : CrepProg (BitVec 64) :=
.seq crepBody318_33 crepBody318_35

def crepBody318_37 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "htab_new" [Flapjack.CrepExp.const 20#64, Flapjack.CrepExp.const 256#64]

def crepBody318_38 : CrepProg (BitVec 64) :=
.seq crepBody318_36 crepBody318_37

def crepBody318_39 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]),
    Flapjack.CrepExp.const 8#64]) crepBody318_24

def crepBody318_40 : CrepProg (BitVec 64) :=
.seq crepBody318_38 crepBody318_39

def crepBody318_41 : CrepProg (BitVec 64) :=
.seq crepBody318_40 crepBody318_37

def crepBody318_42 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]),
    Flapjack.CrepExp.const 16#64]) crepBody318_24

def crepBody318_43 : CrepProg (BitVec 64) :=
.seq crepBody318_41 crepBody318_42

def crepBody318_44 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "htab_new" [Flapjack.CrepExp.const 52#64, Flapjack.CrepExp.const 256#64]

def crepBody318_45 : CrepProg (BitVec 64) :=
.seq crepBody318_43 crepBody318_44

def crepBody318_46 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]),
    Flapjack.CrepExp.const 24#64]) crepBody318_24

def crepBody318_47 : CrepProg (BitVec 64) :=
.seq crepBody318_45 crepBody318_46

def crepBody318_48 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "htab_new" [Flapjack.CrepExp.const 20#64, Flapjack.CrepExp.const 64#64]

def crepBody318_49 : CrepProg (BitVec 64) :=
.seq crepBody318_47 crepBody318_48

def crepBody318_50 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]),
    Flapjack.CrepExp.const 32#64]) crepBody318_24

def crepBody318_51 : CrepProg (BitVec 64) :=
.seq crepBody318_49 crepBody318_50

def crepBody318_52 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "htab_new" [Flapjack.CrepExp.const 52#64, Flapjack.CrepExp.const 64#64]

def crepBody318_53 : CrepProg (BitVec 64) :=
.seq crepBody318_51 crepBody318_52

def crepBody318_54 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]),
    Flapjack.CrepExp.const 40#64]) crepBody318_24

def crepBody318_55 : CrepProg (BitVec 64) :=
.seq crepBody318_53 crepBody318_54

def crepBody318_56 : CrepProg (BitVec 64) :=
.seq crepBody318_55 crepBody318_21

def crepBody318_57 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]),
    Flapjack.CrepExp.const 48#64]) crepBody318_24

def crepBody318_58 : CrepProg (BitVec 64) :=
.seq crepBody318_56 crepBody318_57

def crepBody318_59 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody318_23

def crepBody318_60 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]),
    Flapjack.CrepExp.const 56#64]) crepBody318_59

def crepBody318_61 : CrepProg (BitVec 64) :=
.seq crepBody318_58 crepBody318_60

def crepBody318_62 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]),
    Flapjack.CrepExp.const 64#64]) crepBody318_59

def crepBody318_63 : CrepProg (BitVec 64) :=
.seq crepBody318_61 crepBody318_62

def crepBody318_64 : CrepProg (BitVec 64) :=
.seq crepBody318_63 crepBody318_37

def crepBody318_65 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]),
    Flapjack.CrepExp.const 72#64]) crepBody318_24

def crepBody318_66 : CrepProg (BitVec 64) :=
.seq crepBody318_64 crepBody318_65

def crepBody318_67 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "alloc" [Flapjack.CrepExp.const 64#64]

def crepBody318_68 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 192#64]) crepBody318_29

def crepBody318_69 : CrepProg (BitVec 64) :=
.seq crepBody318_67 crepBody318_68

def crepBody318_70 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody318_69

def crepBody318_71 : CrepProg (BitVec 64) :=
.seq crepBody318_66 crepBody318_70

def crepBody318_72 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 524288#64) crepBody318_23

def crepBody318_73 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 208#64]) crepBody318_72

def crepBody318_74 : CrepProg (BitVec 64) :=
.seq crepBody318_71 crepBody318_73

def crepBody318_75 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 208#64]),
        Flapjack.CrepExp.const 32#64]]

def crepBody318_76 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 200#64]) crepBody318_29

def crepBody318_77 : CrepProg (BitVec 64) :=
.seq crepBody318_75 crepBody318_76

def crepBody318_78 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody318_77

def crepBody318_79 : CrepProg (BitVec 64) :=
.seq crepBody318_74 crepBody318_78

def crepBody318_80 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 16#64]) crepBody318_59

def crepBody318_81 : CrepProg (BitVec 64) :=
.seq crepBody318_79 crepBody318_80

def crepBody318_82 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]) crepBody318_59

def crepBody318_83 : CrepProg (BitVec 64) :=
.seq crepBody318_81 crepBody318_82

def crepBody318_84 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody318_85 : CrepProg (BitVec 64) :=
.seq crepBody318_83 crepBody318_84

def crepBody318_86 : CrepProg (BitVec 64) :=
.seq crepBody318_21 crepBody318_85

def crepBody318_87 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody318_86

def crepBody318_88 : CrepProg (BitVec 64) :=
.seq crepBody318_20 crepBody318_87

def crepBody318_89 : CrepProg (BitVec 64) :=
.seq crepBody318_19 crepBody318_88

def crepBody318_90 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody318_89

def crepBody318_91 : CrepProg (BitVec 64) :=
.seq crepBody318_18 crepBody318_90

def data318 : CrepProg (BitVec 64) := crepBody318_91
def output318 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [115#8, 116#8, 97#8, 116#8, 101#8, 95#8, 105#8, 110#8, 105#8, 116#8], [0, 1, 2], crepProgToHOL data318)
end InitECandidate.Proofs.FrontendStages.Crep
