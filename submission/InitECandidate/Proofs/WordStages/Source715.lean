import InitECandidate.Proofs.WordStages.Source699
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody715_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody715_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody715_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody715_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody715_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 16 (Flapjack.WordRegImm.reg 34) sourceBody715_2 sourceBody715_3

def sourceBody715_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody715_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_4 sourceBody715_5

def sourceBody715_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 16)

def sourceBody715_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 2)

def sourceBody715_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody715_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 6)

def sourceBody715_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 8)

def sourceBody715_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 10)

def sourceBody715_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 12)

def sourceBody715_14 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 714) ([0, 46, 16, 34, 26, 44, 22]) (none)

def sourceBody715_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody715_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_14 sourceBody715_15

def sourceBody715_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_13 sourceBody715_16

def sourceBody715_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_12 sourceBody715_17

def sourceBody715_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_11 sourceBody715_18

def sourceBody715_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_10 sourceBody715_19

def sourceBody715_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_9 sourceBody715_20

def sourceBody715_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_8 sourceBody715_21

def sourceBody715_23 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody715_22 sourceBody715_15

def sourceBody715_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_23 sourceBody715_5

def sourceBody715_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_24 sourceBody715_15

def sourceBody715_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_7 sourceBody715_25

def sourceBody715_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_6 sourceBody715_26

def sourceBody715_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_1 sourceBody715_27

def sourceBody715_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_0 sourceBody715_28

def sourceBody715_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 2)

def sourceBody715_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 4)

def sourceBody715_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody715_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 8)

def sourceBody715_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 10)

def sourceBody715_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 12)

def sourceBody715_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 13402431016077863595#64)

def sourceBody715_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 2210141511517208575#64)

def sourceBody715_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 7435674573564081700#64)

def sourceBody715_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 7239337960414712511#64)

def sourceBody715_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 5412103778470702295#64)

def sourceBody715_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 1873798617647539866#64)

def sourceBody715_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody715_43 : WordLangProgHOL (BitVec 64) :=
.call (some (([46, 16, 34, 26, 44, 22, 40]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody715_15, 715, 2)) (some 704) ([30, 50, 14, 32, 24, 42, 20, 38, 28, 48, 18, 36]) (some (30, sourceBody715_42, 715, 3))

def sourceBody715_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_43 sourceBody715_5

def sourceBody715_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_44 sourceBody715_15

def sourceBody715_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_41 sourceBody715_45

def sourceBody715_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_40 sourceBody715_46

def sourceBody715_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_39 sourceBody715_47

def sourceBody715_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_38 sourceBody715_48

def sourceBody715_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_37 sourceBody715_49

def sourceBody715_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_36 sourceBody715_50

def sourceBody715_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_35 sourceBody715_51

def sourceBody715_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_34 sourceBody715_52

def sourceBody715_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_33 sourceBody715_53

def sourceBody715_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_32 sourceBody715_54

def sourceBody715_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_31 sourceBody715_55

def sourceBody715_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_30 sourceBody715_56

def sourceBody715_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 46)
        (Flapjack.WordLangExpHOL.const 1#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
        (Flapjack.WordLangExpHOL.const 63#64)])

def sourceBody715_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 16)
        (Flapjack.WordLangExpHOL.const 1#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 34)
        (Flapjack.WordLangExpHOL.const 63#64)])

def sourceBody715_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 34)
        (Flapjack.WordLangExpHOL.const 1#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 26)
        (Flapjack.WordLangExpHOL.const 63#64)])

def sourceBody715_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 26)
        (Flapjack.WordLangExpHOL.const 1#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 44)
        (Flapjack.WordLangExpHOL.const 63#64)])

def sourceBody715_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 44)
        (Flapjack.WordLangExpHOL.const 1#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 22)
        (Flapjack.WordLangExpHOL.const 63#64)])

def sourceBody715_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 22)
        (Flapjack.WordLangExpHOL.const 1#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 40)
        (Flapjack.WordLangExpHOL.const 63#64)])

def sourceBody715_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [30, 50, 14, 32, 24, 42]

def sourceBody715_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_64 sourceBody715_15

def sourceBody715_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_63 sourceBody715_65

def sourceBody715_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_62 sourceBody715_66

def sourceBody715_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_61 sourceBody715_67

def sourceBody715_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_60 sourceBody715_68

def sourceBody715_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_59 sourceBody715_69

def sourceBody715_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_58 sourceBody715_70

def sourceBody715_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_57 sourceBody715_71

def sourceBody715_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_15 sourceBody715_72

def sourceBody715_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_15 sourceBody715_73

def sourceBody715_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_15 sourceBody715_74

def sourceBody715_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_15 sourceBody715_75

def sourceBody715_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_15 sourceBody715_76

def sourceBody715_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_15 sourceBody715_77

def sourceBody715_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_15 sourceBody715_78

def sourceBody715_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_15 sourceBody715_79

def sourceBody715_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_15 sourceBody715_80

def sourceBody715_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_15 sourceBody715_81

def sourceBody715_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_15 sourceBody715_82

def sourceBody715_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_15 sourceBody715_83

def sourceBody715_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_15 sourceBody715_84

def sourceBody715_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_15 sourceBody715_85

def sourceBody715_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody715_29 sourceBody715_86

def source715 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (715, 7, sourceBody715_87)
end InitECandidate.Proofs.WordStages
