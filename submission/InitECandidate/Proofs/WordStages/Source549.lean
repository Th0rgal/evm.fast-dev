import InitECandidate.Proofs.WordStages.Source533
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody549_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody549_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody549_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody549_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody549_0, 549, 2)) (some 466) ([16]) (some (16, sourceBody549_2, 549, 3))

def sourceBody549_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody549_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_3 sourceBody549_4

def sourceBody549_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_5 sourceBody549_0

def sourceBody549_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_1 sourceBody549_6

def sourceBody549_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_0 sourceBody549_7

def sourceBody549_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_0 sourceBody549_8

def sourceBody549_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
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
              Flapjack.WordLangExpHOL.const 112#64]),
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody549_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody549_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([6, 16, 4, 14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody549_0, 549, 4)) (some 463) ([10]) (some (10, sourceBody549_11, 549, 5))

def sourceBody549_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_12 sourceBody549_4

def sourceBody549_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_13 sourceBody549_0

def sourceBody549_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_10 sourceBody549_14

def sourceBody549_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody549_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 16)

def sourceBody549_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody549_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody549_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody549_21 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody549_0, 549, 6)) (some 472) ([18, 2, 12, 8]) (some (18, sourceBody549_20, 549, 7))

def sourceBody549_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_21 sourceBody549_4

def sourceBody549_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_22 sourceBody549_0

def sourceBody549_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_19 sourceBody549_23

def sourceBody549_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_18 sourceBody549_24

def sourceBody549_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_17 sourceBody549_25

def sourceBody549_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_16 sourceBody549_26

def sourceBody549_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_0 sourceBody549_27

def sourceBody549_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_0 sourceBody549_28

def sourceBody549_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody549_31 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody549_0, 549, 8)) (some 486) ([18]) (some (18, sourceBody549_20, 549, 9))

def sourceBody549_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_31 sourceBody549_4

def sourceBody549_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_32 sourceBody549_0

def sourceBody549_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_30 sourceBody549_33

def sourceBody549_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_0 sourceBody549_34

def sourceBody549_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_0 sourceBody549_35

def sourceBody549_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_29 sourceBody549_36

def sourceBody549_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody549_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody549_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_39 sourceBody549_0

def sourceBody549_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_38 sourceBody549_40

def sourceBody549_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_37 sourceBody549_41

def sourceBody549_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_15 sourceBody549_42

def sourceBody549_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_0 sourceBody549_43

def sourceBody549_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_0 sourceBody549_44

def sourceBody549_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_0 sourceBody549_45

def sourceBody549_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_0 sourceBody549_46

def sourceBody549_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_0 sourceBody549_47

def sourceBody549_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_0 sourceBody549_48

def sourceBody549_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_0 sourceBody549_49

def sourceBody549_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_0 sourceBody549_50

def sourceBody549_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody549_9 sourceBody549_51

def source549 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (549, 1, sourceBody549_52)
end InitECandidate.Proofs.WordStages
