import InitECandidate.Proofs.FrontendStages.Crep.Translate370
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody386_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6, 7], none)) "htab_item" [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 4]

def crepBody386_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "idx_start_account" [Flapjack.CrepExp.var 8]

def crepBody386_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 17
  (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 8#64]))

def crepBody386_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 18
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 8#64],
        Flapjack.CrepExp.const 8#64]))

def crepBody386_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 19
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 8#64],
        Flapjack.CrepExp.const 16#64]))

def crepBody386_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 20
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 8#64],
        Flapjack.CrepExp.const 24#64]))

def crepBody386_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody386_7 : CrepProg (BitVec 64) :=
.seq crepBody386_5 crepBody386_6

def crepBody386_8 : CrepProg (BitVec 64) :=
.seq crepBody386_4 crepBody386_7

def crepBody386_9 : CrepProg (BitVec 64) :=
.seq crepBody386_3 crepBody386_8

def crepBody386_10 : CrepProg (BitVec 64) :=
.seq crepBody386_2 crepBody386_9

def crepBody386_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 21
  (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 0#64]))

def crepBody386_12 : CrepProg (BitVec 64) :=
.seq crepBody386_11 crepBody386_6

def crepBody386_13 : CrepProg (BitVec 64) :=
.seq crepBody386_10 crepBody386_12

def crepBody386_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 22
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 48#64]))

def crepBody386_15 : CrepProg (BitVec 64) :=
.seq crepBody386_14 crepBody386_6

def crepBody386_16 : CrepProg (BitVec 64) :=
.seq crepBody386_13 crepBody386_15

def crepBody386_17 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.const 1#64)) crepBody386_16 crepBody386_6

def crepBody386_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23], none)) "u256_eq"
  [Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14,
    Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20]

def crepBody386_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([24], none)) "add_balance_change"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18,
    Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20]

def crepBody386_20 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody386_19

def crepBody386_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([24], none)) "bal_remove_change"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 16#64, Flapjack.CrepExp.const 40#64, Flapjack.CrepExp.var 1]

def crepBody386_22 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody386_21

def crepBody386_23 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 23) (Flapjack.CrepExp.const 0#64)) crepBody386_20 crepBody386_22

def crepBody386_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([24], none)) "add_nonce_change"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 21]

def crepBody386_25 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody386_24

def crepBody386_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([24], none)) "bal_remove_change"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 24#64, Flapjack.CrepExp.const 16#64, Flapjack.CrepExp.var 1]

def crepBody386_27 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody386_26

def crepBody386_28 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 15) (Flapjack.CrepExp.var 21)) crepBody386_25 crepBody386_27

def crepBody386_29 : CrepProg (BitVec 64) :=
.seq crepBody386_23 crepBody386_28

def crepBody386_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23], none)) "memeq"
  [Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 22, Flapjack.CrepExp.const 32#64]

def crepBody386_31 : CrepProg (BitVec 64) :=
.seq crepBody386_29 crepBody386_30

def crepBody386_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([24, 25], none)) "get_code" [Flapjack.CrepExp.var 22, Flapjack.CrepExp.var 8]

def crepBody386_33 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([26], none)) "add_code_change"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 24, Flapjack.CrepExp.var 25]

def crepBody386_34 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.const 0#64) crepBody386_33

def crepBody386_35 : CrepProg (BitVec 64) :=
.seq crepBody386_32 crepBody386_34

def crepBody386_36 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.const 0#64) crepBody386_35

def crepBody386_37 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody386_36

def crepBody386_38 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([24], none)) "bal_remove_change"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 32#64, Flapjack.CrepExp.const 24#64, Flapjack.CrepExp.var 1]

def crepBody386_39 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody386_38

def crepBody386_40 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 23) (Flapjack.CrepExp.const 0#64)) crepBody386_37 crepBody386_39

def crepBody386_41 : CrepProg (BitVec 64) :=
.seq crepBody386_31 crepBody386_40

def crepBody386_42 : CrepProg (BitVec 64) :=
.seq crepBody386_18 crepBody386_41

def crepBody386_43 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody386_42

def crepBody386_44 : CrepProg (BitVec 64) :=
.seq crepBody386_17 crepBody386_43

def crepBody386_45 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 136#64])) crepBody386_44

def crepBody386_46 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody386_45

def crepBody386_47 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody386_46

def crepBody386_48 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody386_47

def crepBody386_49 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody386_48

def crepBody386_50 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody386_49

def crepBody386_51 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 48#64]) crepBody386_50

def crepBody386_52 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64])) crepBody386_51

def crepBody386_53 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 16#64],
      Flapjack.CrepExp.const 24#64])) crepBody386_52

def crepBody386_54 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 16#64],
      Flapjack.CrepExp.const 16#64])) crepBody386_53

def crepBody386_55 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 16#64],
      Flapjack.CrepExp.const 8#64])) crepBody386_54

def crepBody386_56 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 16#64])) crepBody386_55

def crepBody386_57 : CrepProg (BitVec 64) :=
.seq crepBody386_1 crepBody386_56

def crepBody386_58 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody386_57

def crepBody386_59 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 7) crepBody386_58

def crepBody386_60 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 6) crepBody386_59

def crepBody386_61 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64)) crepBody386_60 crepBody386_6

def crepBody386_62 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.var 8)

def crepBody386_63 : CrepProg (BitVec 64) :=
.seq crepBody386_62 crepBody386_6

def crepBody386_64 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 1#64]) crepBody386_63

def crepBody386_65 : CrepProg (BitVec 64) :=
.seq crepBody386_61 crepBody386_64

def crepBody386_66 : CrepProg (BitVec 64) :=
.seq crepBody386_0 crepBody386_65

def crepBody386_67 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody386_66

def crepBody386_68 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody386_67

def crepBody386_69 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody386_68

def crepBody386_70 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.var 3)) crepBody386_69

def crepBody386_71 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 24#64]))

def crepBody386_72 : CrepProg (BitVec 64) :=
.seq crepBody386_71 crepBody386_6

def crepBody386_73 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.const 0#64)

def crepBody386_74 : CrepProg (BitVec 64) :=
.seq crepBody386_73 crepBody386_6

def crepBody386_75 : CrepProg (BitVec 64) :=
.seq crepBody386_72 crepBody386_74

def crepBody386_76 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6, 7, 8], none)) "htab_item" [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 4]

def crepBody386_77 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12, 13, 14], none)) "htab_item" [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 11]

def crepBody386_78 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15, 16, 17, 18], none)) "idx_start_storage"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 13]

def crepBody386_79 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23], none)) "u256_eq"
  [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18,
    Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 21, Flapjack.CrepExp.var 22]

def crepBody386_80 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([24], none)) "add_storage_write"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 19,
    Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 21, Flapjack.CrepExp.var 22]

def crepBody386_81 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody386_80

def crepBody386_82 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([24], none)) "remove_storage_write"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 1]

def crepBody386_83 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody386_82

def crepBody386_84 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 23) (Flapjack.CrepExp.const 0#64)) crepBody386_81 crepBody386_83

def crepBody386_85 : CrepProg (BitVec 64) :=
.seq crepBody386_79 crepBody386_84

def crepBody386_86 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody386_85

def crepBody386_87 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 24#64])) crepBody386_86

def crepBody386_88 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 16#64])) crepBody386_87

def crepBody386_89 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 8#64])) crepBody386_88

def crepBody386_90 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.load (Flapjack.CrepExp.var 14)) crepBody386_89

def crepBody386_91 : CrepProg (BitVec 64) :=
.seq crepBody386_78 crepBody386_90

def crepBody386_92 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody386_91

def crepBody386_93 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody386_92

def crepBody386_94 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody386_93

def crepBody386_95 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody386_94

def crepBody386_96 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 12) (Flapjack.CrepExp.const 0#64)) crepBody386_95 crepBody386_6

def crepBody386_97 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 11 (Flapjack.CrepExp.var 15)

def crepBody386_98 : CrepProg (BitVec 64) :=
.seq crepBody386_97 crepBody386_6

def crepBody386_99 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 1#64]) crepBody386_98

def crepBody386_100 : CrepProg (BitVec 64) :=
.seq crepBody386_96 crepBody386_99

def crepBody386_101 : CrepProg (BitVec 64) :=
.seq crepBody386_77 crepBody386_100

def crepBody386_102 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody386_101

def crepBody386_103 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody386_102

def crepBody386_104 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody386_103

def crepBody386_105 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.var 10)) crepBody386_104

def crepBody386_106 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody386_105

def crepBody386_107 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 24#64])) crepBody386_106

def crepBody386_108 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 8) crepBody386_107

def crepBody386_109 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 0#64)) crepBody386_108 crepBody386_6

def crepBody386_110 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.var 9)

def crepBody386_111 : CrepProg (BitVec 64) :=
.seq crepBody386_110 crepBody386_6

def crepBody386_112 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 1#64]) crepBody386_111

def crepBody386_113 : CrepProg (BitVec 64) :=
.seq crepBody386_109 crepBody386_112

def crepBody386_114 : CrepProg (BitVec 64) :=
.seq crepBody386_76 crepBody386_113

def crepBody386_115 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody386_114

def crepBody386_116 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody386_115

def crepBody386_117 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody386_116

def crepBody386_118 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.var 3)) crepBody386_117

def crepBody386_119 : CrepProg (BitVec 64) :=
.seq crepBody386_75 crepBody386_118

def crepBody386_120 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody386_121 : CrepProg (BitVec 64) :=
.seq crepBody386_119 crepBody386_120

def crepBody386_122 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
      Flapjack.CrepExp.const 32#64])) crepBody386_121

def crepBody386_123 : CrepProg (BitVec 64) :=
.seq crepBody386_70 crepBody386_122

def crepBody386_124 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody386_123

def crepBody386_125 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 24#64])) crepBody386_124

def crepBody386_126 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
      Flapjack.CrepExp.const 16#64])) crepBody386_125

def crepBody386_127 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 224#64])) crepBody386_126

def data386 : CrepProg (BitVec 64) := crepBody386_127
def output386 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [117#8, 112#8, 100#8, 97#8, 116#8, 101#8, 95#8, 98#8, 117#8, 105#8, 108#8, 100#8, 101#8, 114#8, 95#8, 102#8, 114#8,
    111#8, 109#8, 95#8, 116#8, 120#8], [], crepProgToHOL data386)
end InitECandidate.Proofs.FrontendStages.Crep
