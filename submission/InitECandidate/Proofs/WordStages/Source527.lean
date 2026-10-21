import InitECandidate.Proofs.WordStages.Source511
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody527_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody527_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody527_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 28, 6, 24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody527_0, 527, 2)) (some 471) ([]) (some (16, sourceBody527_1, 527, 3))

def sourceBody527_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody527_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_2 sourceBody527_3

def sourceBody527_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_4 sourceBody527_0

def sourceBody527_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody527_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 34, 4, 22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody527_0, 527, 4)) (some 471) ([]) (some (14, sourceBody527_6, 527, 5))

def sourceBody527_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_7 sourceBody527_3

def sourceBody527_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_8 sourceBody527_0

def sourceBody527_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody527_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody527_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 28)

def sourceBody527_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody527_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 24)

def sourceBody527_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody527_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody527_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody527_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody527_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody527_20 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody527_0, 527, 6)) (some 479) ([32, 8, 26, 18, 36, 2, 20, 12, 30]) (some (32, sourceBody527_19, 527, 7))

def sourceBody527_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_20 sourceBody527_3

def sourceBody527_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_21 sourceBody527_0

def sourceBody527_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_18 sourceBody527_22

def sourceBody527_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_17 sourceBody527_23

def sourceBody527_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_16 sourceBody527_24

def sourceBody527_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_15 sourceBody527_25

def sourceBody527_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_14 sourceBody527_26

def sourceBody527_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_13 sourceBody527_27

def sourceBody527_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_12 sourceBody527_28

def sourceBody527_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_11 sourceBody527_29

def sourceBody527_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_10 sourceBody527_30

def sourceBody527_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_0 sourceBody527_31

def sourceBody527_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_0 sourceBody527_32

def sourceBody527_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 10)

def sourceBody527_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 28)

def sourceBody527_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 6)

def sourceBody527_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 24)

def sourceBody527_38 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody527_0, 527, 8)) (some 458) ([32, 8, 26, 18]) (some (32, sourceBody527_19, 527, 9))

def sourceBody527_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_38 sourceBody527_3

def sourceBody527_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_39 sourceBody527_0

def sourceBody527_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_37 sourceBody527_40

def sourceBody527_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_36 sourceBody527_41

def sourceBody527_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_35 sourceBody527_42

def sourceBody527_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_34 sourceBody527_43

def sourceBody527_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 256#64]),
            Flapjack.WordLangExpHOL.const 24#64]),
      Flapjack.WordLangExpHOL.var 14])

def sourceBody527_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 255#64])

def sourceBody527_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 8 (Flapjack.WordLangAddr.addr 32 0#64))

def sourceBody527_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_47 sourceBody527_0

def sourceBody527_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_46 sourceBody527_48

def sourceBody527_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_45 sourceBody527_49

def sourceBody527_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody527_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody527_53 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody527_0, 527, 10)) (some 486) ([8]) (some (8, sourceBody527_52, 527, 11))

def sourceBody527_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_53 sourceBody527_3

def sourceBody527_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_54 sourceBody527_0

def sourceBody527_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_51 sourceBody527_55

def sourceBody527_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_0 sourceBody527_56

def sourceBody527_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_0 sourceBody527_57

def sourceBody527_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_50 sourceBody527_58

def sourceBody527_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody527_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [32]

def sourceBody527_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_61 sourceBody527_0

def sourceBody527_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_60 sourceBody527_62

def sourceBody527_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_59 sourceBody527_63

def sourceBody527_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_44 sourceBody527_64

def sourceBody527_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_0 sourceBody527_65

def sourceBody527_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_0 sourceBody527_66

def sourceBody527_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_33 sourceBody527_67

def sourceBody527_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_9 sourceBody527_68

def sourceBody527_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_0 sourceBody527_69

def sourceBody527_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_0 sourceBody527_70

def sourceBody527_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_0 sourceBody527_71

def sourceBody527_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_0 sourceBody527_72

def sourceBody527_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_0 sourceBody527_73

def sourceBody527_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_0 sourceBody527_74

def sourceBody527_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_0 sourceBody527_75

def sourceBody527_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_0 sourceBody527_76

def sourceBody527_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_5 sourceBody527_77

def sourceBody527_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_0 sourceBody527_78

def sourceBody527_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_0 sourceBody527_79

def sourceBody527_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_0 sourceBody527_80

def sourceBody527_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_0 sourceBody527_81

def sourceBody527_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_0 sourceBody527_82

def sourceBody527_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_0 sourceBody527_83

def sourceBody527_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_0 sourceBody527_84

def sourceBody527_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody527_0 sourceBody527_85

def source527 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (527, 1, sourceBody527_86)
end InitECandidate.Proofs.WordStages
