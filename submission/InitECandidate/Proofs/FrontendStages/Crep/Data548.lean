import InitECandidate.Proofs.FrontendStages.Crep.Translate532
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody548_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 7)

def crepBody548_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody548_2 : CrepProg (BitVec 64) :=
.seq crepBody548_0 crepBody548_1

def crepBody548_3 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 4#64) crepBody548_2

def crepBody548_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 8#64

def crepBody548_5 : CrepProg (BitVec 64) :=
.seq crepBody548_3 crepBody548_4

def crepBody548_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 131072#64) (Flapjack.CrepExp.var 6)) crepBody548_5 crepBody548_1

def crepBody548_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "set_retdata" [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 0#64]

def crepBody548_8 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody548_7

def crepBody548_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "get_account" [Flapjack.CrepExp.var 10]

def crepBody548_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "u256_lt"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 24#64]),
    Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]

def crepBody548_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "stack_push"
  [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64]

def crepBody548_12 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody548_11

def crepBody548_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody548_14 : CrepProg (BitVec 64) :=
.seq crepBody548_12 crepBody548_13

def crepBody548_15 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 12) (Flapjack.CrepExp.const 0#64),
      Flapjack.CrepExp.cmp Flapjack.Cmp.equal
        (Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 0#64]))
        (Flapjack.CrepExp.const 18446744073709551615#64),
      Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 1024#64)
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.load
              (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 128#64]),
            Flapjack.CrepExp.const 1#64])])) crepBody548_14 crepBody548_1

def crepBody548_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "warm_address" [Flapjack.CrepExp.var 4]

def crepBody548_17 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody548_16

def crepBody548_18 : CrepProg (BitVec 64) :=
.seq crepBody548_15 crepBody548_17

def crepBody548_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "is_account_alive" [Flapjack.CrepExp.var 4]

def crepBody548_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 14 (Flapjack.CrepExp.const 1#64)

def crepBody548_21 : CrepProg (BitVec 64) :=
.seq crepBody548_20 crepBody548_1

def crepBody548_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "charge_state_gas" [Flapjack.CrepExp.const 183600#64]

def crepBody548_23 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody548_22

def crepBody548_24 : CrepProg (BitVec 64) :=
.seq crepBody548_21 crepBody548_23

def crepBody548_25 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.const 0#64)) crepBody548_24 crepBody548_1

def crepBody548_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 17) (Flapjack.CrepExp.var 18)

def crepBody548_27 : CrepProg (BitVec 64) :=
.seq crepBody548_26 crepBody548_1

def crepBody548_28 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16]) crepBody548_27

def crepBody548_29 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 64#64]) crepBody548_28

def crepBody548_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "account_deployable" [Flapjack.CrepExp.var 4]

def crepBody548_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "increment_nonce" [Flapjack.CrepExp.var 10]

def crepBody548_32 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody548_31

def crepBody548_33 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 18) (Flapjack.CrepExp.var 19)

def crepBody548_34 : CrepProg (BitVec 64) :=
.seq crepBody548_33 crepBody548_1

def crepBody548_35 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
          Flapjack.CrepExp.const 184#64]),
    Flapjack.CrepExp.var 16]) crepBody548_34

def crepBody548_36 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 184#64]) crepBody548_35

def crepBody548_37 : CrepProg (BitVec 64) :=
.seq crepBody548_32 crepBody548_36

def crepBody548_38 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "credit_state_gas_refund" [Flapjack.CrepExp.const 183600#64]

def crepBody548_39 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody548_38

def crepBody548_40 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 14) (Flapjack.CrepExp.const 0#64)) crepBody548_39 crepBody548_1

def crepBody548_41 : CrepProg (BitVec 64) :=
.seq crepBody548_37 crepBody548_40

def crepBody548_42 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "stack_push"
  [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64]

def crepBody548_43 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody548_42

def crepBody548_44 : CrepProg (BitVec 64) :=
.seq crepBody548_41 crepBody548_43

def crepBody548_45 : CrepProg (BitVec 64) :=
.seq crepBody548_44 crepBody548_13

def crepBody548_46 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 17) (Flapjack.CrepExp.const 0#64)) crepBody548_45 crepBody548_1

def crepBody548_47 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 19) (Flapjack.CrepExp.var 20)

def crepBody548_48 : CrepProg (BitVec 64) :=
.seq crepBody548_47 crepBody548_1

def crepBody548_49 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody548_48

def crepBody548_50 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 72#64]) crepBody548_49

def crepBody548_51 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "increment_nonce" [Flapjack.CrepExp.var 10]

def crepBody548_52 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody548_51

def crepBody548_53 : CrepProg (BitVec 64) :=
.seq crepBody548_50 crepBody548_52

def crepBody548_54 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "scratch_mark" []

def crepBody548_55 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "frame_mem_mark" []

def crepBody548_56 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "child_message"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 16,
    Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64,
    Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.const 0#64,
    Flapjack.CrepExp.const 0#64]

def crepBody548_57 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "start_child"
  [Flapjack.CrepExp.var 21, Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20,
    Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.var 4]

def crepBody548_58 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody548_57

def crepBody548_59 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1#64]

def crepBody548_60 : CrepProg (BitVec 64) :=
.seq crepBody548_58 crepBody548_59

def crepBody548_61 : CrepProg (BitVec 64) :=
.seq crepBody548_56 crepBody548_60

def crepBody548_62 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody548_61

def crepBody548_63 : CrepProg (BitVec 64) :=
.seq crepBody548_55 crepBody548_62

def crepBody548_64 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody548_63

def crepBody548_65 : CrepProg (BitVec 64) :=
.seq crepBody548_54 crepBody548_64

def crepBody548_66 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody548_65

def crepBody548_67 : CrepProg (BitVec 64) :=
.seq crepBody548_53 crepBody548_66

def crepBody548_68 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 72#64])) crepBody548_67

def crepBody548_69 : CrepProg (BitVec 64) :=
.seq crepBody548_46 crepBody548_68

def crepBody548_70 : CrepProg (BitVec 64) :=
.seq crepBody548_30 crepBody548_69

def crepBody548_71 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody548_70

def crepBody548_72 : CrepProg (BitVec 64) :=
.seq crepBody548_29 crepBody548_71

def crepBody548_73 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.op Flapjack.BinOp.sub
  [Flapjack.CrepExp.var 15,
    Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 15) (Flapjack.CrepExp.const 6#64)]) crepBody548_72

def crepBody548_74 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 64#64])) crepBody548_73

def crepBody548_75 : CrepProg (BitVec 64) :=
.seq crepBody548_25 crepBody548_74

def crepBody548_76 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody548_75

def crepBody548_77 : CrepProg (BitVec 64) :=
.seq crepBody548_19 crepBody548_76

def crepBody548_78 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody548_77

def crepBody548_79 : CrepProg (BitVec 64) :=
.seq crepBody548_18 crepBody548_78

def crepBody548_80 : CrepProg (BitVec 64) :=
.seq crepBody548_10 crepBody548_79

def crepBody548_81 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody548_80

def crepBody548_82 : CrepProg (BitVec 64) :=
.seq crepBody548_9 crepBody548_81

def crepBody548_83 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody548_82

def crepBody548_84 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 32#64])) crepBody548_83

def crepBody548_85 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 112#64])) crepBody548_84

def crepBody548_86 : CrepProg (BitVec 64) :=
.seq crepBody548_8 crepBody548_85

def crepBody548_87 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 264#64])) crepBody548_86

def crepBody548_88 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
          Flapjack.CrepExp.const 24#64]),
    Flapjack.CrepExp.var 5]) crepBody548_87

def crepBody548_89 : CrepProg (BitVec 64) :=
.seq crepBody548_6 crepBody548_88

def data548 : CrepProg (BitVec 64) := crepBody548_89
def output548 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [103#8, 101#8, 110#8, 101#8, 114#8, 105#8, 99#8, 95#8, 99#8, 114#8, 101#8, 97#8, 116#8, 101#8], [0, 1, 2, 3, 4, 5, 6], crepProgToHOL data548)
end InitECandidate.Proofs.FrontendStages.Crep
