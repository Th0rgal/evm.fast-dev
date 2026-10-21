import InitECandidate.Proofs.FrontendStages.Crep.Translate766
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody782_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "htab_copy"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]),
          Flapjack.CrepExp.const 72#64])]

def crepBody782_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "htab_new" [Flapjack.CrepExp.const 20#64, Flapjack.CrepExp.const 64#64]

def crepBody782_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8, 9, 10], none)) "htab_item" [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 7]

def crepBody782_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "htab_has" [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 11]

def crepBody782_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "htab_set"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 1#64]

def crepBody782_5 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody782_4

def crepBody782_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody782_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.const 0#64)) crepBody782_5 crepBody782_6

def crepBody782_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "ws_storage_root_of" [Flapjack.CrepExp.var 11]

def crepBody782_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "mpt_from_witness"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 1#64]

def crepBody782_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "alloc" [Flapjack.CrepExp.const 96#64]

def crepBody782_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20, 21, 22], none)) "htab_item" [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 18]

def crepBody782_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "u256_is_zero"
  [Flapjack.CrepExp.var 23, Flapjack.CrepExp.var 24, Flapjack.CrepExp.var 25, Flapjack.CrepExp.var 26]

def crepBody782_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([28], none)) "u256_to_be_min"
  [Flapjack.CrepExp.var 23, Flapjack.CrepExp.var 24, Flapjack.CrepExp.var 25, Flapjack.CrepExp.var 26,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 16, Flapjack.CrepExp.const 8#64]]

def crepBody782_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([29], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 16, Flapjack.CrepExp.const 8#64, Flapjack.CrepExp.const 32#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 16, Flapjack.CrepExp.const 8#64],
    Flapjack.CrepExp.var 28]

def crepBody782_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([30], none)) "alloc" [Flapjack.CrepExp.const 40#64]

def crepBody782_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([31], none)) "memcpy"
  [Flapjack.CrepExp.var 30,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 16, Flapjack.CrepExp.const 40#64],
    Flapjack.CrepExp.var 29]

def crepBody782_17 : CrepProg (BitVec 64) :=
.dec 31 (Flapjack.CrepExp.const 0#64) crepBody782_16

def crepBody782_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([31], none)) "mpt_set"
  [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 21, Flapjack.CrepExp.const 32#64, Flapjack.CrepExp.var 30,
    Flapjack.CrepExp.var 29]

def crepBody782_19 : CrepProg (BitVec 64) :=
.dec 31 (Flapjack.CrepExp.const 0#64) crepBody782_18

def crepBody782_20 : CrepProg (BitVec 64) :=
.seq crepBody782_17 crepBody782_19

def crepBody782_21 : CrepProg (BitVec 64) :=
.seq crepBody782_15 crepBody782_20

def crepBody782_22 : CrepProg (BitVec 64) :=
.dec 30 (Flapjack.CrepExp.const 0#64) crepBody782_21

def crepBody782_23 : CrepProg (BitVec 64) :=
.seq crepBody782_14 crepBody782_22

def crepBody782_24 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.const 0#64) crepBody782_23

def crepBody782_25 : CrepProg (BitVec 64) :=
.seq crepBody782_13 crepBody782_24

def crepBody782_26 : CrepProg (BitVec 64) :=
.dec 28 (Flapjack.CrepExp.const 0#64) crepBody782_25

def crepBody782_27 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 17) (Flapjack.CrepExp.const 0#64)),
    Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 27) (Flapjack.CrepExp.const 0#64))]) crepBody782_26 crepBody782_6

def crepBody782_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([28], none)) "mpt_set"
  [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 21, Flapjack.CrepExp.const 32#64, Flapjack.CrepExp.const 0#64,
    Flapjack.CrepExp.const 0#64]

def crepBody782_29 : CrepProg (BitVec 64) :=
.dec 28 (Flapjack.CrepExp.const 0#64) crepBody782_28

def crepBody782_30 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 17) (Flapjack.CrepExp.const 1#64)),
    Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 27) (Flapjack.CrepExp.const 0#64))]) crepBody782_29 crepBody782_6

def crepBody782_31 : CrepProg (BitVec 64) :=
.seq crepBody782_27 crepBody782_30

def crepBody782_32 : CrepProg (BitVec 64) :=
.seq crepBody782_12 crepBody782_31

def crepBody782_33 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody782_32

def crepBody782_34 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 22, Flapjack.CrepExp.const 24#64])) crepBody782_33

def crepBody782_35 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 22, Flapjack.CrepExp.const 16#64])) crepBody782_34

def crepBody782_36 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 22, Flapjack.CrepExp.const 8#64])) crepBody782_35

def crepBody782_37 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.load (Flapjack.CrepExp.var 22)) crepBody782_36

def crepBody782_38 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 20) (Flapjack.CrepExp.const 0#64)) crepBody782_37 crepBody782_6

def crepBody782_39 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 18 (Flapjack.CrepExp.var 23)

def crepBody782_40 : CrepProg (BitVec 64) :=
.seq crepBody782_39 crepBody782_6

def crepBody782_41 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 1#64]) crepBody782_40

def crepBody782_42 : CrepProg (BitVec 64) :=
.seq crepBody782_38 crepBody782_41

def crepBody782_43 : CrepProg (BitVec 64) :=
.seq crepBody782_11 crepBody782_42

def crepBody782_44 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody782_43

def crepBody782_45 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody782_44

def crepBody782_46 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody782_45

def crepBody782_47 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 18) (Flapjack.CrepExp.var 19)) crepBody782_46

def crepBody782_48 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 17 (Flapjack.CrepExp.var 20)

def crepBody782_49 : CrepProg (BitVec 64) :=
.seq crepBody782_48 crepBody782_6

def crepBody782_50 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 17, Flapjack.CrepExp.const 1#64]) crepBody782_49

def crepBody782_51 : CrepProg (BitVec 64) :=
.seq crepBody782_47 crepBody782_50

def crepBody782_52 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 24#64])) crepBody782_51

def crepBody782_53 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody782_52

def crepBody782_54 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 17) (Flapjack.CrepExp.const 2#64)) crepBody782_53

def crepBody782_55 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody782_56 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "mpt_root" [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 18]

def crepBody782_57 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody782_56

def crepBody782_58 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "htab_set"
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 18]

def crepBody782_59 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody782_58

def crepBody782_60 : CrepProg (BitVec 64) :=
.seq crepBody782_57 crepBody782_59

def crepBody782_61 : CrepProg (BitVec 64) :=
.seq crepBody782_55 crepBody782_60

def crepBody782_62 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody782_61

def crepBody782_63 : CrepProg (BitVec 64) :=
.seq crepBody782_54 crepBody782_62

def crepBody782_64 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody782_63

def crepBody782_65 : CrepProg (BitVec 64) :=
.seq crepBody782_10 crepBody782_64

def crepBody782_66 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody782_65

def crepBody782_67 : CrepProg (BitVec 64) :=
.seq crepBody782_9 crepBody782_66

def crepBody782_68 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody782_67

def crepBody782_69 : CrepProg (BitVec 64) :=
.seq crepBody782_8 crepBody782_68

def crepBody782_70 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody782_69

def crepBody782_71 : CrepProg (BitVec 64) :=
.seq crepBody782_7 crepBody782_70

def crepBody782_72 : CrepProg (BitVec 64) :=
.seq crepBody782_3 crepBody782_71

def crepBody782_73 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody782_72

def crepBody782_74 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.var 10) crepBody782_73

def crepBody782_75 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 9) crepBody782_74

def crepBody782_76 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.const 0#64)) crepBody782_75 crepBody782_6

def crepBody782_77 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.var 11)

def crepBody782_78 : CrepProg (BitVec 64) :=
.seq crepBody782_77 crepBody782_6

def crepBody782_79 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 1#64]) crepBody782_78

def crepBody782_80 : CrepProg (BitVec 64) :=
.seq crepBody782_76 crepBody782_79

def crepBody782_81 : CrepProg (BitVec 64) :=
.seq crepBody782_2 crepBody782_80

def crepBody782_82 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody782_81

def crepBody782_83 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody782_82

def crepBody782_84 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody782_83

def crepBody782_85 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.var 6)) crepBody782_84

def crepBody782_86 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "mpt_from_witness"
  [Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 168#64]),
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.const 1#64]

def crepBody782_87 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.const 0#64)

def crepBody782_88 : CrepProg (BitVec 64) :=
.seq crepBody782_87 crepBody782_6

def crepBody782_89 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9, 10, 11], none)) "htab_item" [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 7]

def crepBody782_90 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "htab_has" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 10]

def crepBody782_91 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "ws_get_account_optional" [Flapjack.CrepExp.var 10]

def crepBody782_92 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "htab_set"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 1#64]

def crepBody782_93 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody782_92

def crepBody782_94 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14, 15], none)) "htab_get" [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 10]

def crepBody782_95 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 16 (Flapjack.CrepExp.var 15)

def crepBody782_96 : CrepProg (BitVec 64) :=
.seq crepBody782_95 crepBody782_6

def crepBody782_97 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 14) (Flapjack.CrepExp.const 0#64)) crepBody782_96 crepBody782_6

def crepBody782_98 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "alloc" [Flapjack.CrepExp.const 128#64]

def crepBody782_99 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "encode_account"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 0#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 24#64]),
    Flapjack.CrepExp.var 16,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 48#64]),
    Flapjack.CrepExp.var 17]

def crepBody782_100 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "mpt_set"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 20#64, Flapjack.CrepExp.var 17,
    Flapjack.CrepExp.var 18]

def crepBody782_101 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody782_100

def crepBody782_102 : CrepProg (BitVec 64) :=
.seq crepBody782_99 crepBody782_101

def crepBody782_103 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody782_102

def crepBody782_104 : CrepProg (BitVec 64) :=
.seq crepBody782_98 crepBody782_103

def crepBody782_105 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody782_104

def crepBody782_106 : CrepProg (BitVec 64) :=
.seq crepBody782_97 crepBody782_105

def crepBody782_107 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 128#64])) crepBody782_106

def crepBody782_108 : CrepProg (BitVec 64) :=
.seq crepBody782_94 crepBody782_107

def crepBody782_109 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody782_108

def crepBody782_110 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody782_109

def crepBody782_111 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.const 1#64)) crepBody782_110 crepBody782_6

def crepBody782_112 : CrepProg (BitVec 64) :=
.seq crepBody782_93 crepBody782_111

def crepBody782_113 : CrepProg (BitVec 64) :=
.seq crepBody782_91 crepBody782_112

def crepBody782_114 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody782_113

def crepBody782_115 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 12) (Flapjack.CrepExp.const 0#64)) crepBody782_114 crepBody782_6

def crepBody782_116 : CrepProg (BitVec 64) :=
.seq crepBody782_90 crepBody782_115

def crepBody782_117 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody782_116

def crepBody782_118 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.const 0#64)) crepBody782_117 crepBody782_6

def crepBody782_119 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.var 12)

def crepBody782_120 : CrepProg (BitVec 64) :=
.seq crepBody782_119 crepBody782_6

def crepBody782_121 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 1#64]) crepBody782_120

def crepBody782_122 : CrepProg (BitVec 64) :=
.seq crepBody782_118 crepBody782_121

def crepBody782_123 : CrepProg (BitVec 64) :=
.seq crepBody782_89 crepBody782_122

def crepBody782_124 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody782_123

def crepBody782_125 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody782_124

def crepBody782_126 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody782_125

def crepBody782_127 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.var 6)) crepBody782_126

def crepBody782_128 : CrepProg (BitVec 64) :=
.seq crepBody782_88 crepBody782_127

def crepBody782_129 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10, 11, 12], none)) "htab_item" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 7]

def crepBody782_130 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "mpt_set"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 20#64, Flapjack.CrepExp.const 0#64,
    Flapjack.CrepExp.const 0#64]

def crepBody782_131 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody782_130

def crepBody782_132 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15, 16], none)) "htab_get" [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 13]

def crepBody782_133 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 17 (Flapjack.CrepExp.var 16)

def crepBody782_134 : CrepProg (BitVec 64) :=
.seq crepBody782_133 crepBody782_6

def crepBody782_135 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "cache_get_root" [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 13]

def crepBody782_136 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 15) (Flapjack.CrepExp.const 0#64)) crepBody782_134 crepBody782_135

def crepBody782_137 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "alloc" [Flapjack.CrepExp.const 128#64]

def crepBody782_138 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "encode_account"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 0#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 24#64]),
    Flapjack.CrepExp.var 17,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 48#64]),
    Flapjack.CrepExp.var 18]

def crepBody782_139 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "mpt_set"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 20#64, Flapjack.CrepExp.var 18,
    Flapjack.CrepExp.var 19]

def crepBody782_140 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody782_139

def crepBody782_141 : CrepProg (BitVec 64) :=
.seq crepBody782_138 crepBody782_140

def crepBody782_142 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody782_141

def crepBody782_143 : CrepProg (BitVec 64) :=
.seq crepBody782_137 crepBody782_142

def crepBody782_144 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody782_143

def crepBody782_145 : CrepProg (BitVec 64) :=
.seq crepBody782_136 crepBody782_144

def crepBody782_146 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody782_145

def crepBody782_147 : CrepProg (BitVec 64) :=
.seq crepBody782_132 crepBody782_146

def crepBody782_148 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody782_147

def crepBody782_149 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody782_148

def crepBody782_150 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 14) (Flapjack.CrepExp.const 1#64)) crepBody782_131 crepBody782_149

def crepBody782_151 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.var 12) crepBody782_150

def crepBody782_152 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.var 11) crepBody782_151

def crepBody782_153 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 0#64)) crepBody782_152 crepBody782_6

def crepBody782_154 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.var 13)

def crepBody782_155 : CrepProg (BitVec 64) :=
.seq crepBody782_154 crepBody782_6

def crepBody782_156 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 1#64]) crepBody782_155

def crepBody782_157 : CrepProg (BitVec 64) :=
.seq crepBody782_153 crepBody782_156

def crepBody782_158 : CrepProg (BitVec 64) :=
.seq crepBody782_129 crepBody782_157

def crepBody782_159 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody782_158

def crepBody782_160 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody782_159

def crepBody782_161 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody782_160

def crepBody782_162 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.var 9)) crepBody782_161

def crepBody782_163 : CrepProg (BitVec 64) :=
.seq crepBody782_88 crepBody782_162

def crepBody782_164 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "mpt_root" [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 0]

def crepBody782_165 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody782_164

def crepBody782_166 : CrepProg (BitVec 64) :=
.seq crepBody782_163 crepBody782_165

def crepBody782_167 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody782_168 : CrepProg (BitVec 64) :=
.seq crepBody782_166 crepBody782_167

def crepBody782_169 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 24#64])) crepBody782_168

def crepBody782_170 : CrepProg (BitVec 64) :=
.seq crepBody782_128 crepBody782_169

def crepBody782_171 : CrepProg (BitVec 64) :=
.seq crepBody782_86 crepBody782_170

def crepBody782_172 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody782_171

def crepBody782_173 : CrepProg (BitVec 64) :=
.seq crepBody782_85 crepBody782_172

def crepBody782_174 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody782_173

def crepBody782_175 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 24#64])) crepBody782_174

def crepBody782_176 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 168#64]),
      Flapjack.CrepExp.const 0#64])) crepBody782_175

def crepBody782_177 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]),
      Flapjack.CrepExp.const 16#64])) crepBody782_176

def crepBody782_178 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]),
      Flapjack.CrepExp.const 32#64])) crepBody782_177

def crepBody782_179 : CrepProg (BitVec 64) :=
.seq crepBody782_1 crepBody782_178

def crepBody782_180 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody782_179

def crepBody782_181 : CrepProg (BitVec 64) :=
.seq crepBody782_0 crepBody782_180

def crepBody782_182 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody782_181

def data782 : CrepProg (BitVec 64) := crepBody782_182
def output782 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [99#8, 111#8, 109#8, 112#8, 117#8, 116#8, 101#8, 95#8, 115#8, 116#8, 97#8, 116#8, 101#8, 95#8, 114#8, 111#8, 111#8,
    116#8], [0], crepProgToHOL data782)
end InitECandidate.Proofs.FrontendStages.Crep
