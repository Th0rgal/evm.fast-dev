import InitECandidate.Proofs.FrontendStages.Crep.Translate172
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody188_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "ssz_fail" [Flapjack.CrepExp.const 1#64]

def crepBody188_1 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody188_0

def crepBody188_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody188_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 2#64)) crepBody188_1 crepBody188_2

def crepBody188_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "ssz_fail" [Flapjack.CrepExp.const 2#64]

def crepBody188_5 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody188_4

def crepBody188_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.loadByte (Flapjack.CrepExp.var 0))
        (Flapjack.CrepExp.const 21#64),
      Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
        (Flapjack.CrepExp.loadByte
          (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 1#64]))
        (Flapjack.CrepExp.const 1#64)])) crepBody188_5 crepBody188_2

def crepBody188_7 : CrepProg (BitVec 64) :=
.seq crepBody188_3 crepBody188_6

def crepBody188_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 0 (Flapjack.CrepExp.var 2)

def crepBody188_9 : CrepProg (BitVec 64) :=
.seq crepBody188_8 crepBody188_2

def crepBody188_10 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 2#64]) crepBody188_9

def crepBody188_11 : CrepProg (BitVec 64) :=
.seq crepBody188_7 crepBody188_10

def crepBody188_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 1 (Flapjack.CrepExp.var 2)

def crepBody188_13 : CrepProg (BitVec 64) :=
.seq crepBody188_12 crepBody188_2

def crepBody188_14 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 2#64]) crepBody188_13

def crepBody188_15 : CrepProg (BitVec 64) :=
.seq crepBody188_11 crepBody188_14

def crepBody188_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "ssz_fail" [Flapjack.CrepExp.const 80#64]

def crepBody188_17 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody188_16

def crepBody188_18 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 16#64)) crepBody188_17 crepBody188_2

def crepBody188_19 : CrepProg (BitVec 64) :=
.seq crepBody188_15 crepBody188_18

def crepBody188_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.var 3)

def crepBody188_21 : CrepProg (BitVec 64) :=
.seq crepBody188_20 crepBody188_2

def crepBody188_22 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.loadByte (Flapjack.CrepExp.var 0),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 1#64]))
      (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 2#64]))
      (Flapjack.CrepExp.const 16#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 3#64]))
      (Flapjack.CrepExp.const 24#64)]) crepBody188_21

def crepBody188_23 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 112#64])) crepBody188_22

def crepBody188_24 : CrepProg (BitVec 64) :=
.seq crepBody188_19 crepBody188_23

def crepBody188_25 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.loadByte
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 4#64]),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.const 1#64]))
      (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.const 2#64]))
      (Flapjack.CrepExp.const 16#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.const 3#64]))
      (Flapjack.CrepExp.const 24#64)]) crepBody188_21

def crepBody188_26 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 112#64]),
    Flapjack.CrepExp.const 8#64]) crepBody188_25

def crepBody188_27 : CrepProg (BitVec 64) :=
.seq crepBody188_24 crepBody188_26

def crepBody188_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "ssz_check_offsets"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 112#64]),
    Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.const 16#64, Flapjack.CrepExp.var 1]

def crepBody188_29 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody188_28

def crepBody188_30 : CrepProg (BitVec 64) :=
.seq crepBody188_27 crepBody188_29

def crepBody188_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc" [Flapjack.CrepExp.const 96#64]

def crepBody188_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 6)

def crepBody188_33 : CrepProg (BitVec 64) :=
.seq crepBody188_32 crepBody188_2

def crepBody188_34 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.loadByte
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64, Flapjack.CrepExp.const 1#64]))
      (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64, Flapjack.CrepExp.const 2#64]))
      (Flapjack.CrepExp.const 16#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64, Flapjack.CrepExp.const 3#64]))
      (Flapjack.CrepExp.const 24#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.op Flapjack.BinOp.or
        [Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64, Flapjack.CrepExp.const 4#64]),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 1#64]))
            (Flapjack.CrepExp.const 8#64),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 2#64]))
            (Flapjack.CrepExp.const 16#64),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 3#64]))
            (Flapjack.CrepExp.const 24#64)])
      (Flapjack.CrepExp.const 32#64)]) crepBody188_33

def crepBody188_35 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 88#64]) crepBody188_34

def crepBody188_36 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "ssz_fail" [Flapjack.CrepExp.const 81#64]

def crepBody188_37 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody188_36

def crepBody188_38 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 44#64)) crepBody188_37 crepBody188_2

def crepBody188_39 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.var 11)

def crepBody188_40 : CrepProg (BitVec 64) :=
.seq crepBody188_39 crepBody188_2

def crepBody188_41 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 7) crepBody188_40

def crepBody188_42 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 112#64])) crepBody188_41

def crepBody188_43 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 8) crepBody188_40

def crepBody188_44 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 112#64]),
    Flapjack.CrepExp.const 8#64]) crepBody188_43

def crepBody188_45 : CrepProg (BitVec 64) :=
.seq crepBody188_42 crepBody188_44

def crepBody188_46 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 9) crepBody188_40

def crepBody188_47 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 112#64]),
    Flapjack.CrepExp.const 16#64]) crepBody188_46

def crepBody188_48 : CrepProg (BitVec 64) :=
.seq crepBody188_45 crepBody188_47

def crepBody188_49 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "ssz_check_offsets"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 112#64]),
    Flapjack.CrepExp.const 3#64, Flapjack.CrepExp.const 44#64, Flapjack.CrepExp.var 6]

def crepBody188_50 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody188_49

def crepBody188_51 : CrepProg (BitVec 64) :=
.seq crepBody188_48 crepBody188_50

def crepBody188_52 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "decode_payload"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 7],
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 7]]

def crepBody188_53 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.var 12)

def crepBody188_54 : CrepProg (BitVec 64) :=
.seq crepBody188_53 crepBody188_2

def crepBody188_55 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.var 10) crepBody188_54

def crepBody188_56 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 0#64]) crepBody188_55

def crepBody188_57 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "ssz_fixed_list_count"
  [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 8],
    Flapjack.CrepExp.const 32#64, Flapjack.CrepExp.const 9223372036854775807#64]

def crepBody188_58 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 12) (Flapjack.CrepExp.var 13)

def crepBody188_59 : CrepProg (BitVec 64) :=
.seq crepBody188_58 crepBody188_2

def crepBody188_60 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 8]) crepBody188_59

def crepBody188_61 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 8#64]) crepBody188_60

def crepBody188_62 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.var 11) crepBody188_59

def crepBody188_63 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 16#64]) crepBody188_62

def crepBody188_64 : CrepProg (BitVec 64) :=
.seq crepBody188_61 crepBody188_63

def crepBody188_65 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 8#64]) crepBody188_59

def crepBody188_66 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 24#64]) crepBody188_65

def crepBody188_67 : CrepProg (BitVec 64) :=
.seq crepBody188_64 crepBody188_66

def crepBody188_68 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "decode_requests"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 9],
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 9]]

def crepBody188_69 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.var 14)

def crepBody188_70 : CrepProg (BitVec 64) :=
.seq crepBody188_69 crepBody188_2

def crepBody188_71 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.var 12) crepBody188_70

def crepBody188_72 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 32#64]) crepBody188_71

def crepBody188_73 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "ssz_fail" [Flapjack.CrepExp.const 82#64]

def crepBody188_74 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody188_73

def crepBody188_75 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 14) (Flapjack.CrepExp.const 12#64)) crepBody188_74 crepBody188_2

def crepBody188_76 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 16) (Flapjack.CrepExp.var 17)

def crepBody188_77 : CrepProg (BitVec 64) :=
.seq crepBody188_76 crepBody188_2

def crepBody188_78 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.loadByte
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 13,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 4#64]]),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 13,
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 4#64],
            Flapjack.CrepExp.const 1#64]))
      (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 13,
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 4#64],
            Flapjack.CrepExp.const 2#64]))
      (Flapjack.CrepExp.const 16#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 13,
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 4#64],
            Flapjack.CrepExp.const 3#64]))
      (Flapjack.CrepExp.const 24#64)]) crepBody188_77

def crepBody188_79 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 112#64]),
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 8#64]]) crepBody188_78

def crepBody188_80 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 15 (Flapjack.CrepExp.var 16)

def crepBody188_81 : CrepProg (BitVec 64) :=
.seq crepBody188_80 crepBody188_2

def crepBody188_82 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 1#64]) crepBody188_81

def crepBody188_83 : CrepProg (BitVec 64) :=
.seq crepBody188_79 crepBody188_82

def crepBody188_84 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 15) (Flapjack.CrepExp.const 3#64)) crepBody188_83

def crepBody188_85 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "ssz_check_offsets"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 112#64]),
    Flapjack.CrepExp.const 3#64, Flapjack.CrepExp.const 12#64, Flapjack.CrepExp.var 14]

def crepBody188_86 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody188_85

def crepBody188_87 : CrepProg (BitVec 64) :=
.seq crepBody188_84 crepBody188_86

def crepBody188_88 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19, 20], none)) "decode_bytes_list"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 16],
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 16],
    Flapjack.CrepExp.const 9223372036854775807#64, Flapjack.CrepExp.const 1024#64]

def crepBody188_89 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 21) (Flapjack.CrepExp.var 22)

def crepBody188_90 : CrepProg (BitVec 64) :=
.seq crepBody188_89 crepBody188_2

def crepBody188_91 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.var 19) crepBody188_90

def crepBody188_92 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 40#64]) crepBody188_91

def crepBody188_93 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.var 20) crepBody188_90

def crepBody188_94 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 48#64]) crepBody188_93

def crepBody188_95 : CrepProg (BitVec 64) :=
.seq crepBody188_92 crepBody188_94

def crepBody188_96 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21, 22], none)) "decode_bytes_list"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 17],
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 17],
    Flapjack.CrepExp.const 9223372036854775807#64, Flapjack.CrepExp.const 65536#64]

def crepBody188_97 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 23) (Flapjack.CrepExp.var 24)

def crepBody188_98 : CrepProg (BitVec 64) :=
.seq crepBody188_97 crepBody188_2

def crepBody188_99 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.var 21) crepBody188_98

def crepBody188_100 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 56#64]) crepBody188_99

def crepBody188_101 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.var 22) crepBody188_98

def crepBody188_102 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 64#64]) crepBody188_101

def crepBody188_103 : CrepProg (BitVec 64) :=
.seq crepBody188_100 crepBody188_102

def crepBody188_104 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23, 24], none)) "decode_bytes_list"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 18],
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 18],
    Flapjack.CrepExp.const 256#64, Flapjack.CrepExp.const 1024#64]

def crepBody188_105 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 25) (Flapjack.CrepExp.var 26)

def crepBody188_106 : CrepProg (BitVec 64) :=
.seq crepBody188_105 crepBody188_2

def crepBody188_107 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.var 23) crepBody188_106

def crepBody188_108 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 72#64]) crepBody188_107

def crepBody188_109 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.var 24) crepBody188_106

def crepBody188_110 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 80#64]) crepBody188_109

def crepBody188_111 : CrepProg (BitVec 64) :=
.seq crepBody188_108 crepBody188_110

def crepBody188_112 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 4]

def crepBody188_113 : CrepProg (BitVec 64) :=
.seq crepBody188_111 crepBody188_112

def crepBody188_114 : CrepProg (BitVec 64) :=
.seq crepBody188_104 crepBody188_113

def crepBody188_115 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody188_114

def crepBody188_116 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody188_115

def crepBody188_117 : CrepProg (BitVec 64) :=
.seq crepBody188_103 crepBody188_116

def crepBody188_118 : CrepProg (BitVec 64) :=
.seq crepBody188_96 crepBody188_117

def crepBody188_119 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody188_118

def crepBody188_120 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody188_119

def crepBody188_121 : CrepProg (BitVec 64) :=
.seq crepBody188_95 crepBody188_120

def crepBody188_122 : CrepProg (BitVec 64) :=
.seq crepBody188_88 crepBody188_121

def crepBody188_123 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody188_122

def crepBody188_124 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody188_123

def crepBody188_125 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 112#64]),
      Flapjack.CrepExp.const 16#64])) crepBody188_124

def crepBody188_126 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 112#64]),
      Flapjack.CrepExp.const 8#64])) crepBody188_125

def crepBody188_127 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 112#64]))) crepBody188_126

def crepBody188_128 : CrepProg (BitVec 64) :=
.seq crepBody188_87 crepBody188_127

def crepBody188_129 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody188_128

def crepBody188_130 : CrepProg (BitVec 64) :=
.seq crepBody188_75 crepBody188_129

def crepBody188_131 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 3]) crepBody188_130

def crepBody188_132 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3]) crepBody188_131

def crepBody188_133 : CrepProg (BitVec 64) :=
.seq crepBody188_72 crepBody188_132

def crepBody188_134 : CrepProg (BitVec 64) :=
.seq crepBody188_68 crepBody188_133

def crepBody188_135 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody188_134

def crepBody188_136 : CrepProg (BitVec 64) :=
.seq crepBody188_67 crepBody188_135

def crepBody188_137 : CrepProg (BitVec 64) :=
.seq crepBody188_57 crepBody188_136

def crepBody188_138 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody188_137

def crepBody188_139 : CrepProg (BitVec 64) :=
.seq crepBody188_56 crepBody188_138

def crepBody188_140 : CrepProg (BitVec 64) :=
.seq crepBody188_52 crepBody188_139

def crepBody188_141 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody188_140

def crepBody188_142 : CrepProg (BitVec 64) :=
.seq crepBody188_51 crepBody188_141

def crepBody188_143 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.loadByte
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 40#64]),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 40#64, Flapjack.CrepExp.const 1#64]))
      (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 40#64, Flapjack.CrepExp.const 2#64]))
      (Flapjack.CrepExp.const 16#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 40#64, Flapjack.CrepExp.const 3#64]))
      (Flapjack.CrepExp.const 24#64)]) crepBody188_142

def crepBody188_144 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.loadByte
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 4#64]),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.const 1#64]))
      (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.const 2#64]))
      (Flapjack.CrepExp.const 16#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.const 3#64]))
      (Flapjack.CrepExp.const 24#64)]) crepBody188_143

def crepBody188_145 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.loadByte (Flapjack.CrepExp.var 5),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 1#64]))
      (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 2#64]))
      (Flapjack.CrepExp.const 16#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 3#64]))
      (Flapjack.CrepExp.const 24#64)]) crepBody188_144

def crepBody188_146 : CrepProg (BitVec 64) :=
.seq crepBody188_38 crepBody188_145

def crepBody188_147 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 2]) crepBody188_146

def crepBody188_148 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 2]) crepBody188_147

def crepBody188_149 : CrepProg (BitVec 64) :=
.seq crepBody188_35 crepBody188_148

def crepBody188_150 : CrepProg (BitVec 64) :=
.seq crepBody188_31 crepBody188_149

def crepBody188_151 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody188_150

def crepBody188_152 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 112#64]),
      Flapjack.CrepExp.const 8#64])) crepBody188_151

def crepBody188_153 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 112#64]))) crepBody188_152

def crepBody188_154 : CrepProg (BitVec 64) :=
.seq crepBody188_30 crepBody188_153

def data188 : CrepProg (BitVec 64) := crepBody188_154
def output188 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 115#8, 116#8, 97#8, 116#8, 101#8, 108#8, 101#8, 115#8, 115#8, 95#8,
    105#8, 110#8, 112#8, 117#8, 116#8], [0, 1], crepProgToHOL data188)
end InitECandidate.Proofs.FrontendStages.Crep
