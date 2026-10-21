import InitECandidate.Proofs.FrontendStages.Crep.Translate170
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody186_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "ssz_fail" [Flapjack.CrepExp.const 60#64]

def crepBody186_1 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody186_0

def crepBody186_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody186_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 20#64)) crepBody186_1 crepBody186_2

def crepBody186_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 4)

def crepBody186_5 : CrepProg (BitVec 64) :=
.seq crepBody186_4 crepBody186_2

def crepBody186_6 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.loadByte
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 0,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 4#64]]),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0,
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 4#64],
            Flapjack.CrepExp.const 1#64]))
      (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0,
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 4#64],
            Flapjack.CrepExp.const 2#64]))
      (Flapjack.CrepExp.const 16#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0,
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 4#64],
            Flapjack.CrepExp.const 3#64]))
      (Flapjack.CrepExp.const 24#64)]) crepBody186_5

def crepBody186_7 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 112#64]),
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 8#64]]) crepBody186_6

def crepBody186_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 2 (Flapjack.CrepExp.var 3)

def crepBody186_9 : CrepProg (BitVec 64) :=
.seq crepBody186_8 crepBody186_2

def crepBody186_10 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 1#64]) crepBody186_9

def crepBody186_11 : CrepProg (BitVec 64) :=
.seq crepBody186_7 crepBody186_10

def crepBody186_12 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 5#64)) crepBody186_11

def crepBody186_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "ssz_check_offsets"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 112#64]),
    Flapjack.CrepExp.const 5#64, Flapjack.CrepExp.const 20#64, Flapjack.CrepExp.var 1]

def crepBody186_14 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody186_13

def crepBody186_15 : CrepProg (BitVec 64) :=
.seq crepBody186_12 crepBody186_14

def crepBody186_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 80#64]

def crepBody186_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "ssz_fixed_list_count"
  [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 4],
    Flapjack.CrepExp.const 192#64, Flapjack.CrepExp.const 9223372036854775807#64]

def crepBody186_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "ssz_fixed_list_count"
  [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 5],
    Flapjack.CrepExp.const 76#64, Flapjack.CrepExp.const 9223372036854775807#64]

def crepBody186_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "ssz_fixed_list_count"
  [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 6],
    Flapjack.CrepExp.const 116#64, Flapjack.CrepExp.const 9223372036854775807#64]

def crepBody186_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "ssz_fixed_list_count"
  [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 7],
    Flapjack.CrepExp.const 184#64, Flapjack.CrepExp.const 9223372036854775807#64]

def crepBody186_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "ssz_fixed_list_count"
  [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 8],
    Flapjack.CrepExp.const 68#64, Flapjack.CrepExp.const 9223372036854775807#64]

def crepBody186_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 14) (Flapjack.CrepExp.var 15)

def crepBody186_23 : CrepProg (BitVec 64) :=
.seq crepBody186_22 crepBody186_2

def crepBody186_24 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 4]) crepBody186_23

def crepBody186_25 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 0#64]) crepBody186_24

def crepBody186_26 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.var 9) crepBody186_23

def crepBody186_27 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 8#64]) crepBody186_26

def crepBody186_28 : CrepProg (BitVec 64) :=
.seq crepBody186_25 crepBody186_27

def crepBody186_29 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 5]) crepBody186_23

def crepBody186_30 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 16#64]) crepBody186_29

def crepBody186_31 : CrepProg (BitVec 64) :=
.seq crepBody186_28 crepBody186_30

def crepBody186_32 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.var 10) crepBody186_23

def crepBody186_33 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 24#64]) crepBody186_32

def crepBody186_34 : CrepProg (BitVec 64) :=
.seq crepBody186_31 crepBody186_33

def crepBody186_35 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 6]) crepBody186_23

def crepBody186_36 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 32#64]) crepBody186_35

def crepBody186_37 : CrepProg (BitVec 64) :=
.seq crepBody186_34 crepBody186_36

def crepBody186_38 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.var 11) crepBody186_23

def crepBody186_39 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 40#64]) crepBody186_38

def crepBody186_40 : CrepProg (BitVec 64) :=
.seq crepBody186_37 crepBody186_39

def crepBody186_41 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 7]) crepBody186_23

def crepBody186_42 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 48#64]) crepBody186_41

def crepBody186_43 : CrepProg (BitVec 64) :=
.seq crepBody186_40 crepBody186_42

def crepBody186_44 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.var 12) crepBody186_23

def crepBody186_45 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 56#64]) crepBody186_44

def crepBody186_46 : CrepProg (BitVec 64) :=
.seq crepBody186_43 crepBody186_45

def crepBody186_47 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 8]) crepBody186_23

def crepBody186_48 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 64#64]) crepBody186_47

def crepBody186_49 : CrepProg (BitVec 64) :=
.seq crepBody186_46 crepBody186_48

def crepBody186_50 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.var 13) crepBody186_23

def crepBody186_51 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 72#64]) crepBody186_50

def crepBody186_52 : CrepProg (BitVec 64) :=
.seq crepBody186_49 crepBody186_51

def crepBody186_53 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 3]

def crepBody186_54 : CrepProg (BitVec 64) :=
.seq crepBody186_52 crepBody186_53

def crepBody186_55 : CrepProg (BitVec 64) :=
.seq crepBody186_21 crepBody186_54

def crepBody186_56 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody186_55

def crepBody186_57 : CrepProg (BitVec 64) :=
.seq crepBody186_20 crepBody186_56

def crepBody186_58 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody186_57

def crepBody186_59 : CrepProg (BitVec 64) :=
.seq crepBody186_19 crepBody186_58

def crepBody186_60 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody186_59

def crepBody186_61 : CrepProg (BitVec 64) :=
.seq crepBody186_18 crepBody186_60

def crepBody186_62 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody186_61

def crepBody186_63 : CrepProg (BitVec 64) :=
.seq crepBody186_17 crepBody186_62

def crepBody186_64 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody186_63

def crepBody186_65 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 112#64]),
      Flapjack.CrepExp.const 32#64])) crepBody186_64

def crepBody186_66 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 112#64]),
      Flapjack.CrepExp.const 24#64])) crepBody186_65

def crepBody186_67 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 112#64]),
      Flapjack.CrepExp.const 16#64])) crepBody186_66

def crepBody186_68 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 112#64]),
      Flapjack.CrepExp.const 8#64])) crepBody186_67

def crepBody186_69 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 112#64]))) crepBody186_68

def crepBody186_70 : CrepProg (BitVec 64) :=
.seq crepBody186_16 crepBody186_69

def crepBody186_71 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody186_70

def crepBody186_72 : CrepProg (BitVec 64) :=
.seq crepBody186_15 crepBody186_71

def crepBody186_73 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody186_72

def crepBody186_74 : CrepProg (BitVec 64) :=
.seq crepBody186_3 crepBody186_73

def data186 : CrepProg (BitVec 64) := crepBody186_74
def output186 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 114#8, 101#8, 113#8, 117#8, 101#8, 115#8, 116#8, 115#8], [0, 1], crepProgToHOL data186)
end InitECandidate.Proofs.FrontendStages.Crep
