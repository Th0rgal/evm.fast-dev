import InitECandidate.Proofs.FrontendStages.Crep.Translate510
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody526_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "get_pre_state_account"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64])]

def crepBody526_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "acct_is_empty" [Flapjack.CrepExp.var 2]

def crepBody526_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "charge_state_gas" [Flapjack.CrepExp.const 183600#64]

def crepBody526_3 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody526_2

def crepBody526_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody526_5 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 0#64)) crepBody526_3 crepBody526_4

def crepBody526_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody526_7 : CrepProg (BitVec 64) :=
.seq crepBody526_5 crepBody526_6

def crepBody526_8 : CrepProg (BitVec 64) :=
.seq crepBody526_1 crepBody526_7

def crepBody526_9 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody526_8

def crepBody526_10 : CrepProg (BitVec 64) :=
.seq crepBody526_0 crepBody526_9

def crepBody526_11 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody526_10

def crepBody526_12 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 24#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody526_11 crepBody526_4

def crepBody526_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "u256_is_zero"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 56#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 56#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 56#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 56#64],
          Flapjack.CrepExp.const 24#64])]

def crepBody526_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "is_account_alive" [Flapjack.CrepExp.var 2]

def crepBody526_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "charge_state_gas" [Flapjack.CrepExp.const 183600#64]

def crepBody526_16 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody526_15

def crepBody526_17 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 0#64)) crepBody526_16 crepBody526_4

def crepBody526_18 : CrepProg (BitVec 64) :=
.seq crepBody526_14 crepBody526_17

def crepBody526_19 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody526_18

def crepBody526_20 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 0#64)) crepBody526_19 crepBody526_4

def crepBody526_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4, 5], none)) "ext_code_of" [Flapjack.CrepExp.var 2]

def crepBody526_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "get_delegated_code_address" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody526_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "alloc" [Flapjack.CrepExp.const 24#64]

def crepBody526_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "memcpy"
  [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 20#64]

def crepBody526_25 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody526_24

def crepBody526_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "is_warm_address" [Flapjack.CrepExp.var 9]

def crepBody526_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "charge_gas" [Flapjack.CrepExp.const 100#64]

def crepBody526_28 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody526_27

def crepBody526_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "charge_gas" [Flapjack.CrepExp.const 3000#64]

def crepBody526_30 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody526_29

def crepBody526_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "warm_address" [Flapjack.CrepExp.var 9]

def crepBody526_32 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody526_31

def crepBody526_33 : CrepProg (BitVec 64) :=
.seq crepBody526_30 crepBody526_32

def crepBody526_34 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 0#64)) crepBody526_28 crepBody526_33

def crepBody526_35 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11, 12], none)) "ext_code_of" [Flapjack.CrepExp.var 9]

def crepBody526_36 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6 (Flapjack.CrepExp.var 11)

def crepBody526_37 : CrepProg (BitVec 64) :=
.seq crepBody526_36 crepBody526_4

def crepBody526_38 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.var 12)

def crepBody526_39 : CrepProg (BitVec 64) :=
.seq crepBody526_38 crepBody526_4

def crepBody526_40 : CrepProg (BitVec 64) :=
.seq crepBody526_37 crepBody526_39

def crepBody526_41 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.var 14)

def crepBody526_42 : CrepProg (BitVec 64) :=
.seq crepBody526_41 crepBody526_4

def crepBody526_43 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 1#64) crepBody526_42

def crepBody526_44 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 168#64]) crepBody526_43

def crepBody526_45 : CrepProg (BitVec 64) :=
.seq crepBody526_40 crepBody526_44

def crepBody526_46 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.var 9) crepBody526_42

def crepBody526_47 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 104#64]) crepBody526_46

def crepBody526_48 : CrepProg (BitVec 64) :=
.seq crepBody526_45 crepBody526_47

def crepBody526_49 : CrepProg (BitVec 64) :=
.seq crepBody526_35 crepBody526_48

def crepBody526_50 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody526_49

def crepBody526_51 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody526_50

def crepBody526_52 : CrepProg (BitVec 64) :=
.seq crepBody526_34 crepBody526_51

def crepBody526_53 : CrepProg (BitVec 64) :=
.seq crepBody526_26 crepBody526_52

def crepBody526_54 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody526_53

def crepBody526_55 : CrepProg (BitVec 64) :=
.seq crepBody526_25 crepBody526_54

def crepBody526_56 : CrepProg (BitVec 64) :=
.seq crepBody526_23 crepBody526_55

def crepBody526_57 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody526_56

def crepBody526_58 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.const 0#64)) crepBody526_57 crepBody526_4

def crepBody526_59 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.var 10)

def crepBody526_60 : CrepProg (BitVec 64) :=
.seq crepBody526_59 crepBody526_4

def crepBody526_61 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 6) crepBody526_60

def crepBody526_62 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 112#64]) crepBody526_61

def crepBody526_63 : CrepProg (BitVec 64) :=
.seq crepBody526_58 crepBody526_62

def crepBody526_64 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 7) crepBody526_60

def crepBody526_65 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 120#64]) crepBody526_64

def crepBody526_66 : CrepProg (BitVec 64) :=
.seq crepBody526_63 crepBody526_65

def crepBody526_67 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 48#64]) crepBody526_61

def crepBody526_68 : CrepProg (BitVec 64) :=
.seq crepBody526_66 crepBody526_67

def crepBody526_69 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 56#64]) crepBody526_64

def crepBody526_70 : CrepProg (BitVec 64) :=
.seq crepBody526_68 crepBody526_69

def crepBody526_71 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "compute_jumpdests" [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7]

def crepBody526_72 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.var 11)

def crepBody526_73 : CrepProg (BitVec 64) :=
.seq crepBody526_72 crepBody526_4

def crepBody526_74 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 9) crepBody526_73

def crepBody526_75 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 80#64]) crepBody526_74

def crepBody526_76 : CrepProg (BitVec 64) :=
.seq crepBody526_75 crepBody526_6

def crepBody526_77 : CrepProg (BitVec 64) :=
.seq crepBody526_71 crepBody526_76

def crepBody526_78 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody526_77

def crepBody526_79 : CrepProg (BitVec 64) :=
.seq crepBody526_70 crepBody526_78

def crepBody526_80 : CrepProg (BitVec 64) :=
.seq crepBody526_22 crepBody526_79

def crepBody526_81 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody526_80

def crepBody526_82 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 5) crepBody526_81

def crepBody526_83 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 4) crepBody526_82

def crepBody526_84 : CrepProg (BitVec 64) :=
.seq crepBody526_21 crepBody526_83

def crepBody526_85 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody526_84

def crepBody526_86 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody526_85

def crepBody526_87 : CrepProg (BitVec 64) :=
.seq crepBody526_20 crepBody526_86

def crepBody526_88 : CrepProg (BitVec 64) :=
.seq crepBody526_13 crepBody526_87

def crepBody526_89 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody526_88

def crepBody526_90 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64])) crepBody526_89

def crepBody526_91 : CrepProg (BitVec 64) :=
.seq crepBody526_12 crepBody526_90

def crepBody526_92 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 112#64])) crepBody526_91

def data526 : CrepProg (BitVec 64) := crepBody526_92
def output526 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 114#8, 101#8, 112#8, 97#8, 114#8, 101#8, 95#8, 100#8, 105#8, 115#8, 112#8, 97#8, 116#8, 99#8, 104#8], [], crepProgToHOL data526)
end InitECandidate.Proofs.FrontendStages.Crep
