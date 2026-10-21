import InitECandidate.Proofs.FrontendStages.Crep.Translate785
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody801_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2, 3], none)) "validate_headers"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 72#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 80#64])]

def crepBody801_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 5)

def crepBody801_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody801_3 : CrepProg (BitVec 64) :=
.seq crepBody801_1 crepBody801_2

def crepBody801_4 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 3#64) crepBody801_3

def crepBody801_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 4#64

def crepBody801_6 : CrepProg (BitVec 64) :=
.seq crepBody801_4 crepBody801_5

def crepBody801_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 0#64)) crepBody801_6 crepBody801_2

def crepBody801_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 7)

def crepBody801_9 : CrepProg (BitVec 64) :=
.seq crepBody801_8 crepBody801_2

def crepBody801_10 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 3) crepBody801_9

def crepBody801_11 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 440#64]) crepBody801_10

def crepBody801_12 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 4) crepBody801_9

def crepBody801_13 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 448#64]) crepBody801_12

def crepBody801_14 : CrepProg (BitVec 64) :=
.seq crepBody801_11 crepBody801_13

def crepBody801_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "nodedb_build"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 40#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64])]

def crepBody801_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "nodedb_build"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 56#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 64#64])]

def crepBody801_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "state_init"
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.var 7]

def crepBody801_18 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody801_17

def crepBody801_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 11)

def crepBody801_20 : CrepProg (BitVec 64) :=
.seq crepBody801_19 crepBody801_2

def crepBody801_21 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 4#64) crepBody801_20

def crepBody801_22 : CrepProg (BitVec 64) :=
.seq crepBody801_21 crepBody801_5

def crepBody801_23 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 8,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 16#64],
        Flapjack.CrepExp.const 8#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody801_22 crepBody801_2

def crepBody801_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 10 (Flapjack.CrepExp.var 11)

def crepBody801_25 : CrepProg (BitVec 64) :=
.seq crepBody801_24 crepBody801_2

def crepBody801_26 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 1#64]) crepBody801_25

def crepBody801_27 : CrepProg (BitVec 64) :=
.seq crepBody801_23 crepBody801_26

def crepBody801_28 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.var 9)) crepBody801_27

def crepBody801_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "payload_header" [Flapjack.CrepExp.var 0]

def crepBody801_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody801_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "header_hash" [Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12]

def crepBody801_32 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody801_31

def crepBody801_33 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "memeq"
  [Flapjack.CrepExp.var 12,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 0#64]),
        Flapjack.CrepExp.const 472#64],
    Flapjack.CrepExp.const 32#64]

def crepBody801_34 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 14)

def crepBody801_35 : CrepProg (BitVec 64) :=
.seq crepBody801_34 crepBody801_2

def crepBody801_36 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 5#64) crepBody801_35

def crepBody801_37 : CrepProg (BitVec 64) :=
.seq crepBody801_36 crepBody801_5

def crepBody801_38 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.const 0#64)) crepBody801_37 crepBody801_2

def crepBody801_39 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "is_valid_versioned_hashes" [Flapjack.CrepExp.var 0]

def crepBody801_40 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 15)

def crepBody801_41 : CrepProg (BitVec 64) :=
.seq crepBody801_40 crepBody801_2

def crepBody801_42 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 6#64) crepBody801_41

def crepBody801_43 : CrepProg (BitVec 64) :=
.seq crepBody801_42 crepBody801_5

def crepBody801_44 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 14) (Flapjack.CrepExp.const 0#64)) crepBody801_43 crepBody801_2

def crepBody801_45 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "validate_header" [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 11]

def crepBody801_46 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody801_45

def crepBody801_47 : CrepProg (BitVec 64) :=
.seq crepBody801_44 crepBody801_46

def crepBody801_48 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "alloc" [Flapjack.CrepExp.const 120#64]

def crepBody801_49 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 16) (Flapjack.CrepExp.var 17)

def crepBody801_50 : CrepProg (BitVec 64) :=
.seq crepBody801_49 crepBody801_2

def crepBody801_51 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.var 15) crepBody801_50

def crepBody801_52 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 408#64]) crepBody801_51

def crepBody801_53 : CrepProg (BitVec 64) :=
.seq crepBody801_48 crepBody801_52

def crepBody801_54 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody801_53

def crepBody801_55 : CrepProg (BitVec 64) :=
.seq crepBody801_47 crepBody801_54

def crepBody801_56 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "memzero"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 408#64]),
    Flapjack.CrepExp.const 120#64]

def crepBody801_57 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody801_56

def crepBody801_58 : CrepProg (BitVec 64) :=
.seq crepBody801_55 crepBody801_57

def crepBody801_59 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 15) (Flapjack.CrepExp.var 16)

def crepBody801_60 : CrepProg (BitVec 64) :=
.seq crepBody801_59 crepBody801_2

def crepBody801_61 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 88#64])) crepBody801_60

def crepBody801_62 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 408#64]),
    Flapjack.CrepExp.const 0#64]) crepBody801_61

def crepBody801_63 : CrepProg (BitVec 64) :=
.seq crepBody801_58 crepBody801_62

def crepBody801_64 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 104#64])) crepBody801_60

def crepBody801_65 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 408#64]),
    Flapjack.CrepExp.const 8#64]) crepBody801_64

def crepBody801_66 : CrepProg (BitVec 64) :=
.seq crepBody801_63 crepBody801_65

def crepBody801_67 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 440#64])) crepBody801_60

def crepBody801_68 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 408#64]),
    Flapjack.CrepExp.const 16#64]) crepBody801_67

def crepBody801_69 : CrepProg (BitVec 64) :=
.seq crepBody801_66 crepBody801_68

def crepBody801_70 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 448#64])) crepBody801_60

def crepBody801_71 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 408#64]),
    Flapjack.CrepExp.const 24#64]) crepBody801_70

def crepBody801_72 : CrepProg (BitVec 64) :=
.seq crepBody801_69 crepBody801_71

def crepBody801_73 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 24#64])) crepBody801_60

def crepBody801_74 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 408#64]),
    Flapjack.CrepExp.const 32#64]) crepBody801_73

def crepBody801_75 : CrepProg (BitVec 64) :=
.seq crepBody801_72 crepBody801_74

def crepBody801_76 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 96#64])) crepBody801_60

def crepBody801_77 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 408#64]),
    Flapjack.CrepExp.const 40#64]) crepBody801_76

def crepBody801_78 : CrepProg (BitVec 64) :=
.seq crepBody801_75 crepBody801_77

def crepBody801_79 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 17)

def crepBody801_80 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 18)

def crepBody801_81 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 19)

def crepBody801_82 : CrepProg (BitVec 64) :=
.seq crepBody801_81 crepBody801_2

def crepBody801_83 : CrepProg (BitVec 64) :=
.seq crepBody801_80 crepBody801_82

def crepBody801_84 : CrepProg (BitVec 64) :=
.seq crepBody801_79 crepBody801_83

def crepBody801_85 : CrepProg (BitVec 64) :=
.seq crepBody801_59 crepBody801_84

def crepBody801_86 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 160#64],
      Flapjack.CrepExp.const 24#64])) crepBody801_85

def crepBody801_87 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 160#64],
      Flapjack.CrepExp.const 16#64])) crepBody801_86

def crepBody801_88 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 160#64],
      Flapjack.CrepExp.const 8#64])) crepBody801_87

def crepBody801_89 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 160#64])) crepBody801_88

def crepBody801_90 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 408#64]),
    Flapjack.CrepExp.const 48#64]) crepBody801_89

def crepBody801_91 : CrepProg (BitVec 64) :=
.seq crepBody801_78 crepBody801_90

def crepBody801_92 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 120#64])) crepBody801_60

def crepBody801_93 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 408#64]),
    Flapjack.CrepExp.const 80#64]) crepBody801_92

def crepBody801_94 : CrepProg (BitVec 64) :=
.seq crepBody801_91 crepBody801_93

def crepBody801_95 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 144#64])) crepBody801_60

def crepBody801_96 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 408#64]),
    Flapjack.CrepExp.const 88#64]) crepBody801_95

def crepBody801_97 : CrepProg (BitVec 64) :=
.seq crepBody801_94 crepBody801_96

def crepBody801_98 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 208#64])) crepBody801_60

def crepBody801_99 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 408#64]),
    Flapjack.CrepExp.const 96#64]) crepBody801_98

def crepBody801_100 : CrepProg (BitVec 64) :=
.seq crepBody801_97 crepBody801_99

def crepBody801_101 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 216#64])) crepBody801_60

def crepBody801_102 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 408#64]),
    Flapjack.CrepExp.const 104#64]) crepBody801_101

def crepBody801_103 : CrepProg (BitVec 64) :=
.seq crepBody801_100 crepBody801_102

def crepBody801_104 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 240#64])) crepBody801_60

def crepBody801_105 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 408#64]),
    Flapjack.CrepExp.const 112#64]) crepBody801_104

def crepBody801_106 : CrepProg (BitVec 64) :=
.seq crepBody801_103 crepBody801_105

def crepBody801_107 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "execute_block" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 11]

def crepBody801_108 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody801_107

def crepBody801_109 : CrepProg (BitVec 64) :=
.seq crepBody801_106 crepBody801_108

def crepBody801_110 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody801_111 : CrepProg (BitVec 64) :=
.seq crepBody801_109 crepBody801_110

def crepBody801_112 : CrepProg (BitVec 64) :=
.seq crepBody801_39 crepBody801_111

def crepBody801_113 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody801_112

def crepBody801_114 : CrepProg (BitVec 64) :=
.seq crepBody801_38 crepBody801_113

def crepBody801_115 : CrepProg (BitVec 64) :=
.seq crepBody801_33 crepBody801_114

def crepBody801_116 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody801_115

def crepBody801_117 : CrepProg (BitVec 64) :=
.seq crepBody801_32 crepBody801_116

def crepBody801_118 : CrepProg (BitVec 64) :=
.seq crepBody801_30 crepBody801_117

def crepBody801_119 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody801_118

def crepBody801_120 : CrepProg (BitVec 64) :=
.seq crepBody801_29 crepBody801_119

def crepBody801_121 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody801_120

def crepBody801_122 : CrepProg (BitVec 64) :=
.seq crepBody801_28 crepBody801_121

def crepBody801_123 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody801_122

def crepBody801_124 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 40#64])) crepBody801_123

def crepBody801_125 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64])) crepBody801_124

def crepBody801_126 : CrepProg (BitVec 64) :=
.seq crepBody801_18 crepBody801_125

def crepBody801_127 : CrepProg (BitVec 64) :=
.seq crepBody801_16 crepBody801_126

def crepBody801_128 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody801_127

def crepBody801_129 : CrepProg (BitVec 64) :=
.seq crepBody801_15 crepBody801_128

def crepBody801_130 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody801_129

def crepBody801_131 : CrepProg (BitVec 64) :=
.seq crepBody801_14 crepBody801_130

def crepBody801_132 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 2,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
        [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 1#64],
          Flapjack.CrepExp.const 8#64]])) crepBody801_131

def crepBody801_133 : CrepProg (BitVec 64) :=
.seq crepBody801_7 crepBody801_132

def crepBody801_134 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 80#64])) crepBody801_133

def crepBody801_135 : CrepProg (BitVec 64) :=
.seq crepBody801_0 crepBody801_134

def crepBody801_136 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody801_135

def crepBody801_137 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody801_136

def crepBody801_138 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64])) crepBody801_137

def data801 : CrepProg (BitVec 64) := crepBody801_138
def output801 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [114#8, 117#8, 110#8, 95#8, 97#8, 116#8, 116#8, 101#8, 109#8, 112#8, 116#8], [0], crepProgToHOL data801)
end InitECandidate.Proofs.FrontendStages.Crep
