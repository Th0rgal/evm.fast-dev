import InitECandidate.Proofs.WordStages.Source595
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody611_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody611_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody611_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody611_0, 611, 2)) (some 69) ([]) (some (24, sourceBody611_1, 611, 3))

def sourceBody611_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody611_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_2 sourceBody611_3

def sourceBody611_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_4 sourceBody611_0

def sourceBody611_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody611_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody611_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody611_0, 611, 4)) (some 68) ([12]) (some (12, sourceBody611_7, 611, 5))

def sourceBody611_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_8 sourceBody611_3

def sourceBody611_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_9 sourceBody611_0

def sourceBody611_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_6 sourceBody611_10

def sourceBody611_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 24)

def sourceBody611_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 255#64)

def sourceBody611_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 20 (Flapjack.WordLangAddr.addr 12 0#64))

def sourceBody611_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_14 sourceBody611_0

def sourceBody611_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_13 sourceBody611_15

def sourceBody611_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_12 sourceBody611_16

def sourceBody611_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody611_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody611_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody611_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody611_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody611_0, 611, 6)) (some 77) ([20, 16, 22]) (some (20, sourceBody611_21, 611, 7))

def sourceBody611_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_22 sourceBody611_3

def sourceBody611_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_23 sourceBody611_0

def sourceBody611_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_20 sourceBody611_24

def sourceBody611_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_19 sourceBody611_25

def sourceBody611_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_18 sourceBody611_26

def sourceBody611_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_0 sourceBody611_27

def sourceBody611_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_0 sourceBody611_28

def sourceBody611_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_17 sourceBody611_29

def sourceBody611_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 21#64])

def sourceBody611_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody611_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody611_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody611_0, 611, 8)) (some 77) ([20, 16, 22]) (some (20, sourceBody611_21, 611, 9))

def sourceBody611_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_34 sourceBody611_3

def sourceBody611_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_35 sourceBody611_0

def sourceBody611_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_33 sourceBody611_36

def sourceBody611_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_32 sourceBody611_37

def sourceBody611_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_31 sourceBody611_38

def sourceBody611_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_0 sourceBody611_39

def sourceBody611_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_0 sourceBody611_40

def sourceBody611_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_30 sourceBody611_41

def sourceBody611_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 6)

def sourceBody611_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody611_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 53#64])

def sourceBody611_46 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody611_0, 611, 10)) (some 158) ([20, 16, 22]) (some (20, sourceBody611_21, 611, 11))

def sourceBody611_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_46 sourceBody611_3

def sourceBody611_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_47 sourceBody611_0

def sourceBody611_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_45 sourceBody611_48

def sourceBody611_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_44 sourceBody611_49

def sourceBody611_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_43 sourceBody611_50

def sourceBody611_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_0 sourceBody611_51

def sourceBody611_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_0 sourceBody611_52

def sourceBody611_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_42 sourceBody611_53

def sourceBody611_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody611_56 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody611_0, 611, 12)) (some 68) ([20]) (some (20, sourceBody611_21, 611, 13))

def sourceBody611_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_56 sourceBody611_3

def sourceBody611_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_57 sourceBody611_0

def sourceBody611_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_55 sourceBody611_58

def sourceBody611_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 24)

def sourceBody611_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 85#64)

def sourceBody611_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 12)

def sourceBody611_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody611_64 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody611_0, 611, 14)) (some 158) ([16, 22, 14]) (some (16, sourceBody611_63, 611, 15))

def sourceBody611_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_64 sourceBody611_3

def sourceBody611_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_65 sourceBody611_0

def sourceBody611_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_62 sourceBody611_66

def sourceBody611_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_61 sourceBody611_67

def sourceBody611_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_60 sourceBody611_68

def sourceBody611_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_0 sourceBody611_69

def sourceBody611_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_0 sourceBody611_70

def sourceBody611_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 10)

def sourceBody611_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 12#64])

def sourceBody611_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody611_75 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody611_0, 611, 16)) (some 77) ([16, 22, 14]) (some (16, sourceBody611_63, 611, 17))

def sourceBody611_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_75 sourceBody611_3

def sourceBody611_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_76 sourceBody611_0

def sourceBody611_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_74 sourceBody611_77

def sourceBody611_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_73 sourceBody611_78

def sourceBody611_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_72 sourceBody611_79

def sourceBody611_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_0 sourceBody611_80

def sourceBody611_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_0 sourceBody611_81

def sourceBody611_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_71 sourceBody611_82

def sourceBody611_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody611_85 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody611_0, 611, 18)) (some 70) ([16]) (some (16, sourceBody611_63, 611, 19))

def sourceBody611_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_85 sourceBody611_3

def sourceBody611_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_86 sourceBody611_0

def sourceBody611_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_84 sourceBody611_87

def sourceBody611_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_0 sourceBody611_88

def sourceBody611_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_0 sourceBody611_89

def sourceBody611_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_83 sourceBody611_90

def sourceBody611_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody611_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody611_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_93 sourceBody611_0

def sourceBody611_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_92 sourceBody611_94

def sourceBody611_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_91 sourceBody611_95

def sourceBody611_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_59 sourceBody611_96

def sourceBody611_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_0 sourceBody611_97

def sourceBody611_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_0 sourceBody611_98

def sourceBody611_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_54 sourceBody611_99

def sourceBody611_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_11 sourceBody611_100

def sourceBody611_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_0 sourceBody611_101

def sourceBody611_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_0 sourceBody611_102

def sourceBody611_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_5 sourceBody611_103

def sourceBody611_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_0 sourceBody611_104

def sourceBody611_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody611_0 sourceBody611_105

def source611 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (611, 6, sourceBody611_106)
end InitECandidate.Proofs.WordStages
