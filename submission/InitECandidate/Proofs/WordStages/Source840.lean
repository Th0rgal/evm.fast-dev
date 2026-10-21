import InitECandidate.Proofs.WordStages.Source824
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody840_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody840_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 2)

def sourceBody840_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 22 (Flapjack.WordLangAddr.addr 22 0#64))

def sourceBody840_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody840_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 6 (Flapjack.WordLangAddr.addr 6 0#64))

def sourceBody840_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody840_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 18 (Flapjack.WordLangAddr.addr 18 0#64))

def sourceBody840_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 3#64])

def sourceBody840_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 14 (Flapjack.WordLangAddr.addr 14 0#64))

def sourceBody840_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 4#64])

def sourceBody840_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 26 (Flapjack.WordLangAddr.addr 26 0#64))

def sourceBody840_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 4#64, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody840_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 4 (Flapjack.WordLangAddr.addr 4 0#64))

def sourceBody840_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 4#64, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody840_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 16 (Flapjack.WordLangAddr.addr 16 0#64))

def sourceBody840_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 4#64, Flapjack.WordLangExpHOL.const 3#64])

def sourceBody840_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 12 (Flapjack.WordLangAddr.addr 12 0#64))

def sourceBody840_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 22,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 6)
        (Flapjack.WordLangExpHOL.const 8#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 18)
        (Flapjack.WordLangExpHOL.const 16#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 14)
        (Flapjack.WordLangExpHOL.const 24#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
          [Flapjack.WordLangExpHOL.var 26,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
              (Flapjack.WordLangExpHOL.const 8#64),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
              (Flapjack.WordLangExpHOL.const 16#64),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 12)
              (Flapjack.WordLangExpHOL.const 24#64)])
        (Flapjack.WordLangExpHOL.const 32#64)])

def sourceBody840_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody840_19 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody840_0, 840, 2)) (some 181) ([24]) (some (22, sourceBody840_18, 840, 3))

def sourceBody840_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody840_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_19 sourceBody840_20

def sourceBody840_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_21 sourceBody840_0

def sourceBody840_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_17 sourceBody840_22

def sourceBody840_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_16 sourceBody840_23

def sourceBody840_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_15 sourceBody840_24

def sourceBody840_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_14 sourceBody840_25

def sourceBody840_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_13 sourceBody840_26

def sourceBody840_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_12 sourceBody840_27

def sourceBody840_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_11 sourceBody840_28

def sourceBody840_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_10 sourceBody840_29

def sourceBody840_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_9 sourceBody840_30

def sourceBody840_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_8 sourceBody840_31

def sourceBody840_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_7 sourceBody840_32

def sourceBody840_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_6 sourceBody840_33

def sourceBody840_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_5 sourceBody840_34

def sourceBody840_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_4 sourceBody840_35

def sourceBody840_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_3 sourceBody840_36

def sourceBody840_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_2 sourceBody840_37

def sourceBody840_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_1 sourceBody840_38

def sourceBody840_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody840_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody840_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody840_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64, Flapjack.WordLangExpHOL.const 3#64])

def sourceBody840_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64, Flapjack.WordLangExpHOL.const 4#64])

def sourceBody840_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody840_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.const 2#64])

def sourceBody840_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.const 3#64])

def sourceBody840_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 24 (Flapjack.WordLangAddr.addr 24 0#64))

def sourceBody840_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 6,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 18)
        (Flapjack.WordLangExpHOL.const 8#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 14)
        (Flapjack.WordLangExpHOL.const 16#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 26)
        (Flapjack.WordLangExpHOL.const 24#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
          [Flapjack.WordLangExpHOL.var 4,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
              (Flapjack.WordLangExpHOL.const 8#64),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 12)
              (Flapjack.WordLangExpHOL.const 16#64),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 24)
              (Flapjack.WordLangExpHOL.const 24#64)])
        (Flapjack.WordLangExpHOL.const 32#64)])

def sourceBody840_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody840_51 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody840_0, 840, 4)) (some 181) ([8]) (some (6, sourceBody840_50, 840, 5))

def sourceBody840_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_51 sourceBody840_20

def sourceBody840_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_52 sourceBody840_0

def sourceBody840_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_49 sourceBody840_53

def sourceBody840_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_48 sourceBody840_54

def sourceBody840_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_47 sourceBody840_55

def sourceBody840_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_16 sourceBody840_56

def sourceBody840_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_46 sourceBody840_57

def sourceBody840_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_14 sourceBody840_58

def sourceBody840_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_45 sourceBody840_59

def sourceBody840_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_12 sourceBody840_60

def sourceBody840_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_44 sourceBody840_61

def sourceBody840_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_10 sourceBody840_62

def sourceBody840_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_43 sourceBody840_63

def sourceBody840_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_8 sourceBody840_64

def sourceBody840_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_42 sourceBody840_65

def sourceBody840_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_6 sourceBody840_66

def sourceBody840_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_41 sourceBody840_67

def sourceBody840_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_4 sourceBody840_68

def sourceBody840_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_40 sourceBody840_69

def sourceBody840_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 36#64])

def sourceBody840_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 36#64, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody840_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 36#64, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody840_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 36#64, Flapjack.WordLangExpHOL.const 3#64])

def sourceBody840_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 36#64, Flapjack.WordLangExpHOL.const 4#64])

def sourceBody840_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 36#64, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody840_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 36#64, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.const 2#64])

def sourceBody840_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 36#64, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.const 3#64])

def sourceBody840_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 8 (Flapjack.WordLangAddr.addr 8 0#64))

def sourceBody840_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 18,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 14)
        (Flapjack.WordLangExpHOL.const 8#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 26)
        (Flapjack.WordLangExpHOL.const 16#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 24#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
          [Flapjack.WordLangExpHOL.var 16,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 12)
              (Flapjack.WordLangExpHOL.const 8#64),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 24)
              (Flapjack.WordLangExpHOL.const 16#64),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 8)
              (Flapjack.WordLangExpHOL.const 24#64)])
        (Flapjack.WordLangExpHOL.const 32#64)])

def sourceBody840_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody840_82 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody840_0, 840, 6)) (some 181) ([20]) (some (18, sourceBody840_81, 840, 7))

def sourceBody840_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_82 sourceBody840_20

def sourceBody840_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_83 sourceBody840_0

def sourceBody840_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_80 sourceBody840_84

def sourceBody840_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_79 sourceBody840_85

def sourceBody840_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_78 sourceBody840_86

def sourceBody840_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_48 sourceBody840_87

def sourceBody840_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_77 sourceBody840_88

def sourceBody840_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_16 sourceBody840_89

def sourceBody840_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_76 sourceBody840_90

def sourceBody840_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_14 sourceBody840_91

def sourceBody840_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_75 sourceBody840_92

def sourceBody840_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_12 sourceBody840_93

def sourceBody840_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_74 sourceBody840_94

def sourceBody840_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_10 sourceBody840_95

def sourceBody840_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_73 sourceBody840_96

def sourceBody840_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_8 sourceBody840_97

def sourceBody840_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_72 sourceBody840_98

def sourceBody840_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_6 sourceBody840_99

def sourceBody840_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_71 sourceBody840_100

def sourceBody840_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 21#64,
      Flapjack.WordLangExpHOL.var 6])

def sourceBody840_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 18)

def sourceBody840_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody840_105 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody840_0, 840, 8)) (some 180) ([26]) (some (26, sourceBody840_104, 840, 9))

def sourceBody840_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_105 sourceBody840_20

def sourceBody840_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_106 sourceBody840_0

def sourceBody840_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_103 sourceBody840_107

def sourceBody840_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.var 14])

def sourceBody840_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [26]

def sourceBody840_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_110 sourceBody840_0

def sourceBody840_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_109 sourceBody840_111

def sourceBody840_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_108 sourceBody840_112

def sourceBody840_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_0 sourceBody840_113

def sourceBody840_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_0 sourceBody840_114

def sourceBody840_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_102 sourceBody840_115

def sourceBody840_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_0 sourceBody840_116

def sourceBody840_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_101 sourceBody840_117

def sourceBody840_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_0 sourceBody840_118

def sourceBody840_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_0 sourceBody840_119

def sourceBody840_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_70 sourceBody840_120

def sourceBody840_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_0 sourceBody840_121

def sourceBody840_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_0 sourceBody840_122

def sourceBody840_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_39 sourceBody840_123

def sourceBody840_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_0 sourceBody840_124

def sourceBody840_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody840_0 sourceBody840_125

def source840 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (840, 2, sourceBody840_126)
end InitECandidate.Proofs.WordStages
