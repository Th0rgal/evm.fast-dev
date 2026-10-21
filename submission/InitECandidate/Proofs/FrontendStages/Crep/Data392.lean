import InitECandidate.Proofs.FrontendStages.Crep.Translate376
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody392_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4, 5, 6], none)) "htab_item" [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 3]

def crepBody392_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "add_storage_read"
  [Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 20#64]]

def crepBody392_2 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody392_1

def crepBody392_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody392_4 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 0#64)) crepBody392_2 crepBody392_3

def crepBody392_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 7)

def crepBody392_6 : CrepProg (BitVec 64) :=
.seq crepBody392_5 crepBody392_3

def crepBody392_7 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64]) crepBody392_6

def crepBody392_8 : CrepProg (BitVec 64) :=
.seq crepBody392_4 crepBody392_7

def crepBody392_9 : CrepProg (BitVec 64) :=
.seq crepBody392_0 crepBody392_8

def crepBody392_10 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody392_9

def crepBody392_11 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody392_10

def crepBody392_12 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody392_11

def crepBody392_13 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 2)) crepBody392_12

def crepBody392_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 2
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 24#64]))

def crepBody392_15 : CrepProg (BitVec 64) :=
.seq crepBody392_14 crepBody392_3

def crepBody392_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.const 0#64)

def crepBody392_17 : CrepProg (BitVec 64) :=
.seq crepBody392_16 crepBody392_3

def crepBody392_18 : CrepProg (BitVec 64) :=
.seq crepBody392_15 crepBody392_17

def crepBody392_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6, 7], none)) "htab_item" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 3]

def crepBody392_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "add_touched_account" [Flapjack.CrepExp.var 6]

def crepBody392_21 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody392_20

def crepBody392_22 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64)) crepBody392_21 crepBody392_3

def crepBody392_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 8)

def crepBody392_24 : CrepProg (BitVec 64) :=
.seq crepBody392_23 crepBody392_3

def crepBody392_25 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64]) crepBody392_24

def crepBody392_26 : CrepProg (BitVec 64) :=
.seq crepBody392_22 crepBody392_25

def crepBody392_27 : CrepProg (BitVec 64) :=
.seq crepBody392_19 crepBody392_26

def crepBody392_28 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody392_27

def crepBody392_29 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody392_28

def crepBody392_30 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody392_29

def crepBody392_31 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 2)) crepBody392_30

def crepBody392_32 : CrepProg (BitVec 64) :=
.seq crepBody392_18 crepBody392_31

def crepBody392_33 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "alloc" [Flapjack.CrepExp.const 64#64]

def crepBody392_34 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6, 7], none)) "htab_keys"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 216#64])]

def crepBody392_35 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "sort_elems"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 24#64, Flapjack.CrepExp.const 1#64,
    Flapjack.CrepExp.var 5]

def crepBody392_36 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody392_35

def crepBody392_37 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9, 10], none)) "htab_get"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 216#64]),
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 6,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 24#64]]]

def crepBody392_38 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.var 12)

def crepBody392_39 : CrepProg (BitVec 64) :=
.seq crepBody392_38 crepBody392_3

def crepBody392_40 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 128#64,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.load
                (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 8#64]),
              Flapjack.CrepExp.const 24#64]),
        Flapjack.CrepExp.const 40#64]]) crepBody392_39

def crepBody392_41 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 8,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.load
                (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 0#64]),
              Flapjack.CrepExp.const 24#64]),
        Flapjack.CrepExp.const 96#64]]) crepBody392_39

def crepBody392_42 : CrepProg (BitVec 64) :=
.seq crepBody392_40 crepBody392_41

def crepBody392_43 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15, 16, 17], none)) "htab_item" [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 14]

def crepBody392_44 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.var 18)

def crepBody392_45 : CrepProg (BitVec 64) :=
.seq crepBody392_44 crepBody392_3

def crepBody392_46 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 8,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 17, Flapjack.CrepExp.const 8#64]),
        Flapjack.CrepExp.const 48#64]]) crepBody392_45

def crepBody392_47 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 15) (Flapjack.CrepExp.const 0#64)) crepBody392_46 crepBody392_3

def crepBody392_48 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 14 (Flapjack.CrepExp.var 18)

def crepBody392_49 : CrepProg (BitVec 64) :=
.seq crepBody392_48 crepBody392_3

def crepBody392_50 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 1#64]) crepBody392_49

def crepBody392_51 : CrepProg (BitVec 64) :=
.seq crepBody392_47 crepBody392_50

def crepBody392_52 : CrepProg (BitVec 64) :=
.seq crepBody392_43 crepBody392_51

def crepBody392_53 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody392_52

def crepBody392_54 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody392_53

def crepBody392_55 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody392_54

def crepBody392_56 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 14) (Flapjack.CrepExp.var 13)) crepBody392_55

def crepBody392_57 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.var 15)

def crepBody392_58 : CrepProg (BitVec 64) :=
.seq crepBody392_57 crepBody392_3

def crepBody392_59 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 8,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.load
                (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 16#64]),
              Flapjack.CrepExp.const 8#64]),
        Flapjack.CrepExp.const 48#64]]) crepBody392_58

def crepBody392_60 : CrepProg (BitVec 64) :=
.seq crepBody392_56 crepBody392_59

def crepBody392_61 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 8,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.load
                (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 24#64]),
              Flapjack.CrepExp.const 8#64]),
        Flapjack.CrepExp.const 24#64]]) crepBody392_58

def crepBody392_62 : CrepProg (BitVec 64) :=
.seq crepBody392_60 crepBody392_61

def crepBody392_63 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 14 (Flapjack.CrepExp.const 0#64)

def crepBody392_64 : CrepProg (BitVec 64) :=
.seq crepBody392_63 crepBody392_3

def crepBody392_65 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 32#64,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 17,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 24#64],
          Flapjack.CrepExp.const 16#64])]) crepBody392_45

def crepBody392_66 : CrepProg (BitVec 64) :=
.seq crepBody392_65 crepBody392_50

def crepBody392_67 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 14) (Flapjack.CrepExp.var 16)) crepBody392_66

def crepBody392_68 : CrepProg (BitVec 64) :=
.seq crepBody392_64 crepBody392_67

def crepBody392_69 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 18)

def crepBody392_70 : CrepProg (BitVec 64) :=
.seq crepBody392_69 crepBody392_3

def crepBody392_71 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64]) crepBody392_70

def crepBody392_72 : CrepProg (BitVec 64) :=
.seq crepBody392_68 crepBody392_71

def crepBody392_73 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 0#64])) crepBody392_72

def crepBody392_74 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 8#64])) crepBody392_73

def crepBody392_75 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 32#64])) crepBody392_74

def crepBody392_76 : CrepProg (BitVec 64) :=
.seq crepBody392_62 crepBody392_75

def crepBody392_77 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody392_76

def crepBody392_78 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 24#64])) crepBody392_77

def crepBody392_79 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 0#64])) crepBody392_78

def crepBody392_80 : CrepProg (BitVec 64) :=
.seq crepBody392_42 crepBody392_79

def crepBody392_81 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 10) crepBody392_80

def crepBody392_82 : CrepProg (BitVec 64) :=
.seq crepBody392_37 crepBody392_81

def crepBody392_83 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody392_82

def crepBody392_84 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody392_83

def crepBody392_85 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 7)) crepBody392_84

def crepBody392_86 : CrepProg (BitVec 64) :=
.seq crepBody392_17 crepBody392_85

def crepBody392_87 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "alloc"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 64#64]]

def crepBody392_88 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11, 12], none)) "htab_get"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 216#64]),
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 6,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 24#64]]]

def crepBody392_89 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "bal_encode_account"
  [Flapjack.CrepExp.var 10,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 6,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 24#64]],
    Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 5]

def crepBody392_90 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 10 (Flapjack.CrepExp.var 14)

def crepBody392_91 : CrepProg (BitVec 64) :=
.seq crepBody392_90 crepBody392_3

def crepBody392_92 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 13]) crepBody392_91

def crepBody392_93 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 14)

def crepBody392_94 : CrepProg (BitVec 64) :=
.seq crepBody392_93 crepBody392_3

def crepBody392_95 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64]) crepBody392_94

def crepBody392_96 : CrepProg (BitVec 64) :=
.seq crepBody392_92 crepBody392_95

def crepBody392_97 : CrepProg (BitVec 64) :=
.seq crepBody392_89 crepBody392_96

def crepBody392_98 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody392_97

def crepBody392_99 : CrepProg (BitVec 64) :=
.seq crepBody392_88 crepBody392_98

def crepBody392_100 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody392_99

def crepBody392_101 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody392_100

def crepBody392_102 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 7)) crepBody392_101

def crepBody392_103 : CrepProg (BitVec 64) :=
.seq crepBody392_17 crepBody392_102

def crepBody392_104 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "rlp_list_header_len" [Flapjack.CrepExp.var 11]

def crepBody392_105 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "rlp_encode_list_header" [Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 11]

def crepBody392_106 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody392_105

def crepBody392_107 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.var 13, Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 11]]

def crepBody392_108 : CrepProg (BitVec 64) :=
.seq crepBody392_106 crepBody392_107

def crepBody392_109 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.sub
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 9#64],
    Flapjack.CrepExp.var 12]) crepBody392_108

def crepBody392_110 : CrepProg (BitVec 64) :=
.seq crepBody392_104 crepBody392_109

def crepBody392_111 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody392_110

def crepBody392_112 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.sub
  [Flapjack.CrepExp.var 10,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 9#64]]) crepBody392_111

def crepBody392_113 : CrepProg (BitVec 64) :=
.seq crepBody392_103 crepBody392_112

def crepBody392_114 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 9#64]) crepBody392_113

def crepBody392_115 : CrepProg (BitVec 64) :=
.seq crepBody392_87 crepBody392_114

def crepBody392_116 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody392_115

def crepBody392_117 : CrepProg (BitVec 64) :=
.seq crepBody392_86 crepBody392_116

def crepBody392_118 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 1024#64) crepBody392_117

def crepBody392_119 : CrepProg (BitVec 64) :=
.seq crepBody392_36 crepBody392_118

def crepBody392_120 : CrepProg (BitVec 64) :=
.seq crepBody392_34 crepBody392_119

def crepBody392_121 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody392_120

def crepBody392_122 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody392_121

def crepBody392_123 : CrepProg (BitVec 64) :=
.seq crepBody392_33 crepBody392_122

def crepBody392_124 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody392_123

def crepBody392_125 : CrepProg (BitVec 64) :=
.seq crepBody392_32 crepBody392_124

def crepBody392_126 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]),
      Flapjack.CrepExp.const 8#64])) crepBody392_125

def crepBody392_127 : CrepProg (BitVec 64) :=
.seq crepBody392_13 crepBody392_126

def crepBody392_128 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody392_127

def crepBody392_129 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 24#64])) crepBody392_128

def crepBody392_130 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]),
      Flapjack.CrepExp.const 24#64])) crepBody392_129

def data392 : CrepProg (BitVec 64) := crepBody392_130
def output392 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [98#8, 117#8, 105#8, 108#8, 100#8, 95#8, 98#8, 108#8, 111#8, 99#8, 107#8, 95#8, 97#8, 99#8, 99#8, 101#8, 115#8, 115#8,
    95#8, 108#8, 105#8, 115#8, 116#8, 95#8, 114#8, 108#8, 112#8], [], crepProgToHOL data392)
end InitECandidate.Proofs.FrontendStages.Crep
