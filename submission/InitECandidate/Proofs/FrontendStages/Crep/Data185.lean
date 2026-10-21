import InitECandidate.Proofs.FrontendStages.Crep.Translate169
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody185_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "ssz_fail" [Flapjack.CrepExp.const 50#64]

def crepBody185_1 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody185_0

def crepBody185_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody185_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 540#64)) crepBody185_1 crepBody185_2

def crepBody185_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "alloc" [Flapjack.CrepExp.const 136#64]

def crepBody185_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 4)

def crepBody185_6 : CrepProg (BitVec 64) :=
.seq crepBody185_5 crepBody185_2

def crepBody185_7 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.var 0) crepBody185_6

def crepBody185_8 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 0#64]) crepBody185_7

def crepBody185_9 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.var 1) crepBody185_6

def crepBody185_10 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 8#64]) crepBody185_9

def crepBody185_11 : CrepProg (BitVec 64) :=
.seq crepBody185_8 crepBody185_10

def crepBody185_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.var 8)

def crepBody185_13 : CrepProg (BitVec 64) :=
.seq crepBody185_12 crepBody185_2

def crepBody185_14 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 3) crepBody185_13

def crepBody185_15 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 112#64])) crepBody185_14

def crepBody185_16 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 4) crepBody185_13

def crepBody185_17 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 112#64]),
    Flapjack.CrepExp.const 8#64]) crepBody185_16

def crepBody185_18 : CrepProg (BitVec 64) :=
.seq crepBody185_15 crepBody185_17

def crepBody185_19 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 5) crepBody185_13

def crepBody185_20 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 112#64]),
    Flapjack.CrepExp.const 16#64]) crepBody185_19

def crepBody185_21 : CrepProg (BitVec 64) :=
.seq crepBody185_18 crepBody185_20

def crepBody185_22 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 6) crepBody185_13

def crepBody185_23 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 112#64]),
    Flapjack.CrepExp.const 24#64]) crepBody185_22

def crepBody185_24 : CrepProg (BitVec 64) :=
.seq crepBody185_21 crepBody185_23

def crepBody185_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "ssz_check_offsets"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 112#64]),
    Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.const 540#64, Flapjack.CrepExp.var 1]

def crepBody185_26 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody185_25

def crepBody185_27 : CrepProg (BitVec 64) :=
.seq crepBody185_24 crepBody185_26

def crepBody185_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "ssz_fail" [Flapjack.CrepExp.const 51#64]

def crepBody185_29 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody185_28

def crepBody185_30 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 32#64)
  (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 3])) crepBody185_29 crepBody185_2

def crepBody185_31 : CrepProg (BitVec 64) :=
.seq crepBody185_27 crepBody185_30

def crepBody185_32 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3]) crepBody185_13

def crepBody185_33 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 16#64]) crepBody185_32

def crepBody185_34 : CrepProg (BitVec 64) :=
.seq crepBody185_31 crepBody185_33

def crepBody185_35 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 3]) crepBody185_13

def crepBody185_36 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 24#64]) crepBody185_35

def crepBody185_37 : CrepProg (BitVec 64) :=
.seq crepBody185_34 crepBody185_36

def crepBody185_38 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7, 8], none)) "ssz_split_var_list"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 4],
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 4],
    Flapjack.CrepExp.const 9223372036854775807#64]

def crepBody185_39 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.var 10)

def crepBody185_40 : CrepProg (BitVec 64) :=
.seq crepBody185_39 crepBody185_2

def crepBody185_41 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 7) crepBody185_40

def crepBody185_42 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 32#64]) crepBody185_41

def crepBody185_43 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 8) crepBody185_40

def crepBody185_44 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 40#64]) crepBody185_43

def crepBody185_45 : CrepProg (BitVec 64) :=
.seq crepBody185_42 crepBody185_44

def crepBody185_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "ssz_fixed_list_count"
  [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 5],
    Flapjack.CrepExp.const 44#64, Flapjack.CrepExp.const 9223372036854775807#64]

def crepBody185_47 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.var 11)

def crepBody185_48 : CrepProg (BitVec 64) :=
.seq crepBody185_47 crepBody185_2

def crepBody185_49 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 5]) crepBody185_48

def crepBody185_50 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 48#64]) crepBody185_49

def crepBody185_51 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 9) crepBody185_48

def crepBody185_52 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 56#64]) crepBody185_51

def crepBody185_53 : CrepProg (BitVec 64) :=
.seq crepBody185_50 crepBody185_52

def crepBody185_54 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 6]) crepBody185_48

def crepBody185_55 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 64#64]) crepBody185_54

def crepBody185_56 : CrepProg (BitVec 64) :=
.seq crepBody185_53 crepBody185_55

def crepBody185_57 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 6]) crepBody185_48

def crepBody185_58 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 72#64]) crepBody185_57

def crepBody185_59 : CrepProg (BitVec 64) :=
.seq crepBody185_56 crepBody185_58

def crepBody185_60 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.loadByte
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 404#64]),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 404#64, Flapjack.CrepExp.const 1#64]))
      (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 404#64, Flapjack.CrepExp.const 2#64]))
      (Flapjack.CrepExp.const 16#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 404#64, Flapjack.CrepExp.const 3#64]))
      (Flapjack.CrepExp.const 24#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.op Flapjack.BinOp.or
        [Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 404#64, Flapjack.CrepExp.const 4#64]),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 404#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 1#64]))
            (Flapjack.CrepExp.const 8#64),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 404#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 2#64]))
            (Flapjack.CrepExp.const 16#64),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 404#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 3#64]))
            (Flapjack.CrepExp.const 24#64)])
      (Flapjack.CrepExp.const 32#64)]) crepBody185_48

def crepBody185_61 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 80#64]) crepBody185_60

def crepBody185_62 : CrepProg (BitVec 64) :=
.seq crepBody185_59 crepBody185_61

def crepBody185_63 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.loadByte
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 412#64]),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 412#64, Flapjack.CrepExp.const 1#64]))
      (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 412#64, Flapjack.CrepExp.const 2#64]))
      (Flapjack.CrepExp.const 16#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 412#64, Flapjack.CrepExp.const 3#64]))
      (Flapjack.CrepExp.const 24#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.op Flapjack.BinOp.or
        [Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 412#64, Flapjack.CrepExp.const 4#64]),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 412#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 1#64]))
            (Flapjack.CrepExp.const 8#64),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 412#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 2#64]))
            (Flapjack.CrepExp.const 16#64),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 412#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 3#64]))
            (Flapjack.CrepExp.const 24#64)])
      (Flapjack.CrepExp.const 32#64)]) crepBody185_48

def crepBody185_64 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 88#64]) crepBody185_63

def crepBody185_65 : CrepProg (BitVec 64) :=
.seq crepBody185_62 crepBody185_64

def crepBody185_66 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.loadByte
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 420#64]),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 420#64, Flapjack.CrepExp.const 1#64]))
      (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 420#64, Flapjack.CrepExp.const 2#64]))
      (Flapjack.CrepExp.const 16#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 420#64, Flapjack.CrepExp.const 3#64]))
      (Flapjack.CrepExp.const 24#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.op Flapjack.BinOp.or
        [Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 420#64, Flapjack.CrepExp.const 4#64]),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 420#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 1#64]))
            (Flapjack.CrepExp.const 8#64),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 420#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 2#64]))
            (Flapjack.CrepExp.const 16#64),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 420#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 3#64]))
            (Flapjack.CrepExp.const 24#64)])
      (Flapjack.CrepExp.const 32#64)]) crepBody185_48

def crepBody185_67 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 96#64]) crepBody185_66

def crepBody185_68 : CrepProg (BitVec 64) :=
.seq crepBody185_65 crepBody185_67

def crepBody185_69 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.loadByte
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 428#64]),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 428#64, Flapjack.CrepExp.const 1#64]))
      (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 428#64, Flapjack.CrepExp.const 2#64]))
      (Flapjack.CrepExp.const 16#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 428#64, Flapjack.CrepExp.const 3#64]))
      (Flapjack.CrepExp.const 24#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.op Flapjack.BinOp.or
        [Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 428#64, Flapjack.CrepExp.const 4#64]),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 428#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 1#64]))
            (Flapjack.CrepExp.const 8#64),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 428#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 2#64]))
            (Flapjack.CrepExp.const 16#64),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 428#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 3#64]))
            (Flapjack.CrepExp.const 24#64)])
      (Flapjack.CrepExp.const 32#64)]) crepBody185_48

def crepBody185_70 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 104#64]) crepBody185_69

def crepBody185_71 : CrepProg (BitVec 64) :=
.seq crepBody185_68 crepBody185_70

def crepBody185_72 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.loadByte
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 512#64]),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 512#64, Flapjack.CrepExp.const 1#64]))
      (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 512#64, Flapjack.CrepExp.const 2#64]))
      (Flapjack.CrepExp.const 16#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 512#64, Flapjack.CrepExp.const 3#64]))
      (Flapjack.CrepExp.const 24#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.op Flapjack.BinOp.or
        [Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 512#64, Flapjack.CrepExp.const 4#64]),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 512#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 1#64]))
            (Flapjack.CrepExp.const 8#64),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 512#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 2#64]))
            (Flapjack.CrepExp.const 16#64),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 512#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 3#64]))
            (Flapjack.CrepExp.const 24#64)])
      (Flapjack.CrepExp.const 32#64)]) crepBody185_48

def crepBody185_73 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 112#64]) crepBody185_72

def crepBody185_74 : CrepProg (BitVec 64) :=
.seq crepBody185_71 crepBody185_73

def crepBody185_75 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.loadByte
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 520#64]),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 520#64, Flapjack.CrepExp.const 1#64]))
      (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 520#64, Flapjack.CrepExp.const 2#64]))
      (Flapjack.CrepExp.const 16#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 520#64, Flapjack.CrepExp.const 3#64]))
      (Flapjack.CrepExp.const 24#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.op Flapjack.BinOp.or
        [Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 520#64, Flapjack.CrepExp.const 4#64]),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 520#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 1#64]))
            (Flapjack.CrepExp.const 8#64),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 520#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 2#64]))
            (Flapjack.CrepExp.const 16#64),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 520#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 3#64]))
            (Flapjack.CrepExp.const 24#64)])
      (Flapjack.CrepExp.const 32#64)]) crepBody185_48

def crepBody185_76 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 120#64]) crepBody185_75

def crepBody185_77 : CrepProg (BitVec 64) :=
.seq crepBody185_74 crepBody185_76

def crepBody185_78 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.loadByte
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 532#64]),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 532#64, Flapjack.CrepExp.const 1#64]))
      (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 532#64, Flapjack.CrepExp.const 2#64]))
      (Flapjack.CrepExp.const 16#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 532#64, Flapjack.CrepExp.const 3#64]))
      (Flapjack.CrepExp.const 24#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.op Flapjack.BinOp.or
        [Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 532#64, Flapjack.CrepExp.const 4#64]),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 532#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 1#64]))
            (Flapjack.CrepExp.const 8#64),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 532#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 2#64]))
            (Flapjack.CrepExp.const 16#64),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 532#64, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.const 3#64]))
            (Flapjack.CrepExp.const 24#64)])
      (Flapjack.CrepExp.const 32#64)]) crepBody185_48

def crepBody185_79 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 128#64]) crepBody185_78

def crepBody185_80 : CrepProg (BitVec 64) :=
.seq crepBody185_77 crepBody185_79

def crepBody185_81 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 2]

def crepBody185_82 : CrepProg (BitVec 64) :=
.seq crepBody185_80 crepBody185_81

def crepBody185_83 : CrepProg (BitVec 64) :=
.seq crepBody185_46 crepBody185_82

def crepBody185_84 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody185_83

def crepBody185_85 : CrepProg (BitVec 64) :=
.seq crepBody185_45 crepBody185_84

def crepBody185_86 : CrepProg (BitVec 64) :=
.seq crepBody185_38 crepBody185_85

def crepBody185_87 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody185_86

def crepBody185_88 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody185_87

def crepBody185_89 : CrepProg (BitVec 64) :=
.seq crepBody185_37 crepBody185_88

def crepBody185_90 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.loadByte
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 528#64]),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 528#64, Flapjack.CrepExp.const 1#64]))
      (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 528#64, Flapjack.CrepExp.const 2#64]))
      (Flapjack.CrepExp.const 16#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 528#64, Flapjack.CrepExp.const 3#64]))
      (Flapjack.CrepExp.const 24#64)]) crepBody185_89

def crepBody185_91 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.loadByte
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 508#64]),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 508#64, Flapjack.CrepExp.const 1#64]))
      (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 508#64, Flapjack.CrepExp.const 2#64]))
      (Flapjack.CrepExp.const 16#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 508#64, Flapjack.CrepExp.const 3#64]))
      (Flapjack.CrepExp.const 24#64)]) crepBody185_90

def crepBody185_92 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.loadByte
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 504#64]),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 504#64, Flapjack.CrepExp.const 1#64]))
      (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 504#64, Flapjack.CrepExp.const 2#64]))
      (Flapjack.CrepExp.const 16#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 504#64, Flapjack.CrepExp.const 3#64]))
      (Flapjack.CrepExp.const 24#64)]) crepBody185_91

def crepBody185_93 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.loadByte
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 436#64]),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 436#64, Flapjack.CrepExp.const 1#64]))
      (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 436#64, Flapjack.CrepExp.const 2#64]))
      (Flapjack.CrepExp.const 16#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 436#64, Flapjack.CrepExp.const 3#64]))
      (Flapjack.CrepExp.const 24#64)]) crepBody185_92

def crepBody185_94 : CrepProg (BitVec 64) :=
.seq crepBody185_11 crepBody185_93

def crepBody185_95 : CrepProg (BitVec 64) :=
.seq crepBody185_4 crepBody185_94

def crepBody185_96 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody185_95

def crepBody185_97 : CrepProg (BitVec 64) :=
.seq crepBody185_3 crepBody185_96

def data185 : CrepProg (BitVec 64) := crepBody185_97
def output185 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 112#8, 97#8, 121#8, 108#8, 111#8, 97#8, 100#8], [0, 1], crepProgToHOL data185)
end InitECandidate.Proofs.FrontendStages.Crep
