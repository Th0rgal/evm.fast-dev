import InitECandidate.Proofs.WordStages.Source535
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody551_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody551_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody551_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody551_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody551_0, 551, 2)) (some 466) ([16]) (some (16, sourceBody551_2, 551, 3))

def sourceBody551_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody551_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_3 sourceBody551_4

def sourceBody551_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_5 sourceBody551_0

def sourceBody551_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_1 sourceBody551_6

def sourceBody551_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_0 sourceBody551_7

def sourceBody551_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_0 sourceBody551_8

def sourceBody551_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
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
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody551_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody551_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody551_13 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 4, 14, 10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody551_0, 551, 4)) (some 463) ([20]) (some (20, sourceBody551_12, 551, 5))

def sourceBody551_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_13 sourceBody551_4

def sourceBody551_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_14 sourceBody551_0

def sourceBody551_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_11 sourceBody551_15

def sourceBody551_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 16)

def sourceBody551_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody551_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody551_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 10)

def sourceBody551_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody551_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody551_0, 551, 6)) (some 472) ([2, 12, 8, 18]) (some (2, sourceBody551_21, 551, 7))

def sourceBody551_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_22 sourceBody551_4

def sourceBody551_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_23 sourceBody551_0

def sourceBody551_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_20 sourceBody551_24

def sourceBody551_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_19 sourceBody551_25

def sourceBody551_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_18 sourceBody551_26

def sourceBody551_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_17 sourceBody551_27

def sourceBody551_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_0 sourceBody551_28

def sourceBody551_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_0 sourceBody551_29

def sourceBody551_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody551_32 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody551_0, 551, 8)) (some 486) ([2]) (some (2, sourceBody551_21, 551, 9))

def sourceBody551_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_32 sourceBody551_4

def sourceBody551_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_33 sourceBody551_0

def sourceBody551_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_31 sourceBody551_34

def sourceBody551_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_0 sourceBody551_35

def sourceBody551_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_0 sourceBody551_36

def sourceBody551_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_30 sourceBody551_37

def sourceBody551_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody551_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody551_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_40 sourceBody551_0

def sourceBody551_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_39 sourceBody551_41

def sourceBody551_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_38 sourceBody551_42

def sourceBody551_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_16 sourceBody551_43

def sourceBody551_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_0 sourceBody551_44

def sourceBody551_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_0 sourceBody551_45

def sourceBody551_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_0 sourceBody551_46

def sourceBody551_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_0 sourceBody551_47

def sourceBody551_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_0 sourceBody551_48

def sourceBody551_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_0 sourceBody551_49

def sourceBody551_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_0 sourceBody551_50

def sourceBody551_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_0 sourceBody551_51

def sourceBody551_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_10 sourceBody551_52

def sourceBody551_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_0 sourceBody551_53

def sourceBody551_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody551_9 sourceBody551_54

def source551 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (551, 1, sourceBody551_55)
end InitECandidate.Proofs.WordStages
