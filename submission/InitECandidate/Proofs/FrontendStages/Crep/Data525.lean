import InitECandidate.Proofs.FrontendStages.Crep.Translate509
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody525_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "htab_new" [Flapjack.CrepExp.const 20#64, Flapjack.CrepExp.const 8#64]

def crepBody525_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "htab_set"
  [Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 0#64]),
    Flapjack.CrepExp.const 1#64]

def crepBody525_2 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody525_1

def crepBody525_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "u256_is_zero"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 16#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 16#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 16#64],
          Flapjack.CrepExp.const 24#64])]

def crepBody525_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "htab_set"
  [Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.const 1#64]

def crepBody525_5 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody525_4

def crepBody525_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody525_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64)) crepBody525_5 crepBody525_6

def crepBody525_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "htab_new" [Flapjack.CrepExp.const 20#64, Flapjack.CrepExp.const 8#64]

def crepBody525_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "u256_is_zero"
  [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15]

def crepBody525_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "u256_fits_word"
  [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15]

def crepBody525_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 18 (Flapjack.CrepExp.const 1#64)

def crepBody525_12 : CrepProg (BitVec 64) :=
.seq crepBody525_11 crepBody525_6

def crepBody525_13 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 16) (Flapjack.CrepExp.const 0#64)) crepBody525_12 crepBody525_6

def crepBody525_14 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 17) (Flapjack.CrepExp.const 0#64)),
    Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 12)
        (Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 0#64])))]) crepBody525_12 crepBody525_6

def crepBody525_15 : CrepProg (BitVec 64) :=
.seq crepBody525_13 crepBody525_14

def crepBody525_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "recover_authority" [Flapjack.CrepExp.var 10]

def crepBody525_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "warm_address" [Flapjack.CrepExp.var 19]

def crepBody525_18 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody525_17

def crepBody525_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "validate_authorization_checks"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 19]

def crepBody525_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 11 (Flapjack.CrepExp.var 19)

def crepBody525_21 : CrepProg (BitVec 64) :=
.seq crepBody525_20 crepBody525_6

def crepBody525_22 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 20) (Flapjack.CrepExp.const 0#64)) crepBody525_21 crepBody525_6

def crepBody525_23 : CrepProg (BitVec 64) :=
.seq crepBody525_19 crepBody525_22

def crepBody525_24 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody525_23

def crepBody525_25 : CrepProg (BitVec 64) :=
.seq crepBody525_18 crepBody525_24

def crepBody525_26 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 19) (Flapjack.CrepExp.const 0#64)) crepBody525_25 crepBody525_6

def crepBody525_27 : CrepProg (BitVec 64) :=
.seq crepBody525_16 crepBody525_26

def crepBody525_28 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody525_27

def crepBody525_29 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 40#64]))
  (Flapjack.CrepExp.const 18446744073709551615#64)) crepBody525_28 crepBody525_6

def crepBody525_30 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 18) (Flapjack.CrepExp.const 0#64)) crepBody525_29 crepBody525_6

def crepBody525_31 : CrepProg (BitVec 64) :=
.seq crepBody525_15 crepBody525_30

def crepBody525_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "account_exists" [Flapjack.CrepExp.var 11]

def crepBody525_33 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "charge_state_gas" [Flapjack.CrepExp.const 183600#64]

def crepBody525_34 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody525_33

def crepBody525_35 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 19) (Flapjack.CrepExp.const 0#64)) crepBody525_34 crepBody525_6

def crepBody525_36 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "htab_has" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 11]

def crepBody525_37 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "charge_gas" [Flapjack.CrepExp.const 9000#64]

def crepBody525_38 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody525_37

def crepBody525_39 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "htab_set"
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 1#64]

def crepBody525_40 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody525_39

def crepBody525_41 : CrepProg (BitVec 64) :=
.seq crepBody525_38 crepBody525_40

def crepBody525_42 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 20) (Flapjack.CrepExp.const 0#64)) crepBody525_41 crepBody525_6

def crepBody525_43 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "get_pre_state_account" [Flapjack.CrepExp.var 11]

def crepBody525_44 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22, 23], none)) "get_code"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 21, Flapjack.CrepExp.const 48#64]),
    Flapjack.CrepExp.var 11]

def crepBody525_45 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([24], none)) "is_valid_delegation" [Flapjack.CrepExp.var 22, Flapjack.CrepExp.var 23]

def crepBody525_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([25], none)) "memeq"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 312#64]),
    Flapjack.CrepExp.const 20#64]

def crepBody525_47 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([26], none)) "set_code"
  [Flapjack.CrepExp.var 11,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 312#64]),
    Flapjack.CrepExp.const 0#64]

def crepBody525_48 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.const 0#64) crepBody525_47

def crepBody525_49 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([26], none)) "htab_has" [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 11]

def crepBody525_50 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "charge_state_gas" [Flapjack.CrepExp.const 35190#64]

def crepBody525_51 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody525_50

def crepBody525_52 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 24) (Flapjack.CrepExp.const 0#64)),
    Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 26) (Flapjack.CrepExp.const 0#64))]) crepBody525_51 crepBody525_6

def crepBody525_53 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "htab_set"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 1#64]

def crepBody525_54 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody525_53

def crepBody525_55 : CrepProg (BitVec 64) :=
.seq crepBody525_52 crepBody525_54

def crepBody525_56 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "alloc" [Flapjack.CrepExp.const 24#64]

def crepBody525_57 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte (Flapjack.CrepExp.var 27) (Flapjack.CrepExp.const 239#64)

def crepBody525_58 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 27, Flapjack.CrepExp.const 1#64])
  (Flapjack.CrepExp.const 1#64)

def crepBody525_59 : CrepProg (BitVec 64) :=
.seq crepBody525_57 crepBody525_58

def crepBody525_60 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 27, Flapjack.CrepExp.const 2#64])
  (Flapjack.CrepExp.const 0#64)

def crepBody525_61 : CrepProg (BitVec 64) :=
.seq crepBody525_59 crepBody525_60

def crepBody525_62 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([28], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 27, Flapjack.CrepExp.const 3#64],
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.const 20#64]

def crepBody525_63 : CrepProg (BitVec 64) :=
.dec 28 (Flapjack.CrepExp.const 0#64) crepBody525_62

def crepBody525_64 : CrepProg (BitVec 64) :=
.seq crepBody525_61 crepBody525_63

def crepBody525_65 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([28], none)) "set_code"
  [Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 27, Flapjack.CrepExp.const 23#64]

def crepBody525_66 : CrepProg (BitVec 64) :=
.dec 28 (Flapjack.CrepExp.const 0#64) crepBody525_65

def crepBody525_67 : CrepProg (BitVec 64) :=
.seq crepBody525_64 crepBody525_66

def crepBody525_68 : CrepProg (BitVec 64) :=
.seq crepBody525_56 crepBody525_67

def crepBody525_69 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody525_68

def crepBody525_70 : CrepProg (BitVec 64) :=
.seq crepBody525_55 crepBody525_69

def crepBody525_71 : CrepProg (BitVec 64) :=
.seq crepBody525_49 crepBody525_70

def crepBody525_72 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.const 0#64) crepBody525_71

def crepBody525_73 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 25) (Flapjack.CrepExp.const 0#64)) crepBody525_48 crepBody525_72

def crepBody525_74 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([26], none)) "increment_nonce" [Flapjack.CrepExp.var 11]

def crepBody525_75 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.const 0#64) crepBody525_74

def crepBody525_76 : CrepProg (BitVec 64) :=
.seq crepBody525_73 crepBody525_75

def crepBody525_77 : CrepProg (BitVec 64) :=
.seq crepBody525_46 crepBody525_76

def crepBody525_78 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.const 0#64) crepBody525_77

def crepBody525_79 : CrepProg (BitVec 64) :=
.seq crepBody525_45 crepBody525_78

def crepBody525_80 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody525_79

def crepBody525_81 : CrepProg (BitVec 64) :=
.seq crepBody525_44 crepBody525_80

def crepBody525_82 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody525_81

def crepBody525_83 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody525_82

def crepBody525_84 : CrepProg (BitVec 64) :=
.seq crepBody525_43 crepBody525_83

def crepBody525_85 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody525_84

def crepBody525_86 : CrepProg (BitVec 64) :=
.seq crepBody525_42 crepBody525_85

def crepBody525_87 : CrepProg (BitVec 64) :=
.seq crepBody525_36 crepBody525_86

def crepBody525_88 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody525_87

def crepBody525_89 : CrepProg (BitVec 64) :=
.seq crepBody525_35 crepBody525_88

def crepBody525_90 : CrepProg (BitVec 64) :=
.seq crepBody525_32 crepBody525_89

def crepBody525_91 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody525_90

def crepBody525_92 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.const 0#64)) crepBody525_91 crepBody525_6

def crepBody525_93 : CrepProg (BitVec 64) :=
.seq crepBody525_31 crepBody525_92

def crepBody525_94 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 9 (Flapjack.CrepExp.var 19)

def crepBody525_95 : CrepProg (BitVec 64) :=
.seq crepBody525_94 crepBody525_6

def crepBody525_96 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 1#64]) crepBody525_95

def crepBody525_97 : CrepProg (BitVec 64) :=
.seq crepBody525_93 crepBody525_96

def crepBody525_98 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody525_97

def crepBody525_99 : CrepProg (BitVec 64) :=
.seq crepBody525_10 crepBody525_98

def crepBody525_100 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody525_99

def crepBody525_101 : CrepProg (BitVec 64) :=
.seq crepBody525_9 crepBody525_100

def crepBody525_102 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody525_101

def crepBody525_103 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 0#64],
      Flapjack.CrepExp.const 24#64])) crepBody525_102

def crepBody525_104 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 0#64],
      Flapjack.CrepExp.const 16#64])) crepBody525_103

def crepBody525_105 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 0#64],
      Flapjack.CrepExp.const 8#64])) crepBody525_104

def crepBody525_106 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 0#64])) crepBody525_105

def crepBody525_107 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody525_106

def crepBody525_108 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 7,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 120#64]]) crepBody525_107

def crepBody525_109 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.var 8)) crepBody525_108

def crepBody525_110 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody525_111 : CrepProg (BitVec 64) :=
.seq crepBody525_109 crepBody525_110

def crepBody525_112 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody525_111

def crepBody525_113 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 152#64])) crepBody525_112

def crepBody525_114 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 144#64])) crepBody525_113

def crepBody525_115 : CrepProg (BitVec 64) :=
.seq crepBody525_8 crepBody525_114

def crepBody525_116 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody525_115

def crepBody525_117 : CrepProg (BitVec 64) :=
.seq crepBody525_7 crepBody525_116

def crepBody525_118 : CrepProg (BitVec 64) :=
.seq crepBody525_3 crepBody525_117

def crepBody525_119 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody525_118

def crepBody525_120 : CrepProg (BitVec 64) :=
.seq crepBody525_2 crepBody525_119

def crepBody525_121 : CrepProg (BitVec 64) :=
.seq crepBody525_0 crepBody525_120

def crepBody525_122 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody525_121

def crepBody525_123 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 0#64])) crepBody525_122

def crepBody525_124 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 8#64])) crepBody525_123

def crepBody525_125 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 112#64])) crepBody525_124

def data525 : CrepProg (BitVec 64) := crepBody525_125
def output525 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [115#8, 101#8, 116#8, 95#8, 100#8, 101#8, 108#8, 101#8, 103#8, 97#8, 116#8, 105#8, 111#8, 110#8], [], crepProgToHOL data525)
end InitECandidate.Proofs.FrontendStages.Crep
