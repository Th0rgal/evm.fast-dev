import InitECandidate.Proofs.FrontendStages.Crep.Translate504
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody520_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "require_not_static" []

def crepBody520_1 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody520_0

def crepBody520_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3, 4], none)) "stack_pop" []

def crepBody520_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "to_address_masked"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody520_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "is_warm_address" [Flapjack.CrepExp.var 5]

def crepBody520_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.var 8)

def crepBody520_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody520_7 : CrepProg (BitVec 64) :=
.seq crepBody520_5 crepBody520_6

def crepBody520_8 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 3000#64]) crepBody520_7

def crepBody520_9 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 0#64)) crepBody520_8 crepBody520_6

def crepBody520_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "charge_gas" [Flapjack.CrepExp.var 7]

def crepBody520_11 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody520_10

def crepBody520_12 : CrepProg (BitVec 64) :=
.seq crepBody520_9 crepBody520_11

def crepBody520_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "warm_address" [Flapjack.CrepExp.var 5]

def crepBody520_14 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody520_13

def crepBody520_15 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 0#64)) crepBody520_14 crepBody520_6

def crepBody520_16 : CrepProg (BitVec 64) :=
.seq crepBody520_12 crepBody520_15

def crepBody520_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "is_account_alive" [Flapjack.CrepExp.var 5]

def crepBody520_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "get_account" [Flapjack.CrepExp.var 8]

def crepBody520_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "u256_is_zero"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 24#64])]

def crepBody520_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 12 (Flapjack.CrepExp.const 183600#64)

def crepBody520_21 : CrepProg (BitVec 64) :=
.seq crepBody520_20 crepBody520_6

def crepBody520_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 13 (Flapjack.CrepExp.const 9000#64)

def crepBody520_23 : CrepProg (BitVec 64) :=
.seq crepBody520_22 crepBody520_6

def crepBody520_24 : CrepProg (BitVec 64) :=
.seq crepBody520_21 crepBody520_23

def crepBody520_25 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.const 0#64)),
    Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.const 0#64))]) crepBody520_24 crepBody520_6

def crepBody520_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "charge_gas" [Flapjack.CrepExp.var 13]

def crepBody520_27 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody520_26

def crepBody520_28 : CrepProg (BitVec 64) :=
.seq crepBody520_25 crepBody520_27

def crepBody520_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "charge_state_gas" [Flapjack.CrepExp.var 12]

def crepBody520_30 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody520_29

def crepBody520_31 : CrepProg (BitVec 64) :=
.seq crepBody520_28 crepBody520_30

def crepBody520_32 : CrepProg (BitVec 64) :=
.seq crepBody520_31 crepBody520_18

def crepBody520_33 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "move_ether"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15,
    Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17]

def crepBody520_34 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody520_33

def crepBody520_35 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "memeq"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 20#64]

def crepBody520_36 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "emit_transfer_log"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15,
    Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17]

def crepBody520_37 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody520_36

def crepBody520_38 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 18) (Flapjack.CrepExp.const 0#64)) crepBody520_37 crepBody520_6

def crepBody520_39 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "htab_has"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
          Flapjack.CrepExp.const 56#64]),
    Flapjack.CrepExp.var 8]

def crepBody520_40 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "htab_set"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
          Flapjack.CrepExp.const 136#64]),
    Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 1#64]

def crepBody520_41 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody520_40

def crepBody520_42 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 19) (Flapjack.CrepExp.const 0#64)) crepBody520_41 crepBody520_6

def crepBody520_43 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 20) (Flapjack.CrepExp.var 21)

def crepBody520_44 : CrepProg (BitVec 64) :=
.seq crepBody520_43 crepBody520_6

def crepBody520_45 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody520_44

def crepBody520_46 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 104#64]) crepBody520_45

def crepBody520_47 : CrepProg (BitVec 64) :=
.seq crepBody520_42 crepBody520_46

def crepBody520_48 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody520_49 : CrepProg (BitVec 64) :=
.seq crepBody520_47 crepBody520_48

def crepBody520_50 : CrepProg (BitVec 64) :=
.seq crepBody520_39 crepBody520_49

def crepBody520_51 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody520_50

def crepBody520_52 : CrepProg (BitVec 64) :=
.seq crepBody520_38 crepBody520_51

def crepBody520_53 : CrepProg (BitVec 64) :=
.seq crepBody520_35 crepBody520_52

def crepBody520_54 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody520_53

def crepBody520_55 : CrepProg (BitVec 64) :=
.seq crepBody520_34 crepBody520_54

def crepBody520_56 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64],
      Flapjack.CrepExp.const 24#64])) crepBody520_55

def crepBody520_57 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64],
      Flapjack.CrepExp.const 16#64])) crepBody520_56

def crepBody520_58 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64],
      Flapjack.CrepExp.const 8#64])) crepBody520_57

def crepBody520_59 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64])) crepBody520_58

def crepBody520_60 : CrepProg (BitVec 64) :=
.seq crepBody520_32 crepBody520_59

def crepBody520_61 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody520_60

def crepBody520_62 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody520_61

def crepBody520_63 : CrepProg (BitVec 64) :=
.seq crepBody520_19 crepBody520_62

def crepBody520_64 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody520_63

def crepBody520_65 : CrepProg (BitVec 64) :=
.seq crepBody520_18 crepBody520_64

def crepBody520_66 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody520_65

def crepBody520_67 : CrepProg (BitVec 64) :=
.seq crepBody520_17 crepBody520_66

def crepBody520_68 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody520_67

def crepBody520_69 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.load
              (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
            Flapjack.CrepExp.const 112#64]),
      Flapjack.CrepExp.const 32#64])) crepBody520_68

def crepBody520_70 : CrepProg (BitVec 64) :=
.seq crepBody520_16 crepBody520_69

def crepBody520_71 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 5000#64) crepBody520_70

def crepBody520_72 : CrepProg (BitVec 64) :=
.seq crepBody520_4 crepBody520_71

def crepBody520_73 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody520_72

def crepBody520_74 : CrepProg (BitVec 64) :=
.seq crepBody520_3 crepBody520_73

def crepBody520_75 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody520_74

def crepBody520_76 : CrepProg (BitVec 64) :=
.seq crepBody520_2 crepBody520_75

def crepBody520_77 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody520_76

def crepBody520_78 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody520_77

def crepBody520_79 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody520_78

def crepBody520_80 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody520_79

def crepBody520_81 : CrepProg (BitVec 64) :=
.seq crepBody520_1 crepBody520_80

def data520 : CrepProg (BitVec 64) := crepBody520_81
def output520 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [111#8, 112#8, 95#8, 115#8, 101#8, 108#8, 102#8, 100#8, 101#8, 115#8, 116#8, 114#8, 117#8, 99#8, 116#8], [], crepProgToHOL data520)
end InitECandidate.Proofs.FrontendStages.Crep
