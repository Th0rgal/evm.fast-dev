import InitECandidate.Proofs.WordStages.Source536
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody552_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody552_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody552_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody552_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody552_0, 552, 2)) (some 466) ([16]) (some (16, sourceBody552_2, 552, 3))

def sourceBody552_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody552_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_3 sourceBody552_4

def sourceBody552_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_5 sourceBody552_0

def sourceBody552_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_1 sourceBody552_6

def sourceBody552_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_0 sourceBody552_7

def sourceBody552_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_0 sourceBody552_8

def sourceBody552_10 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody552_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody552_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([6, 16, 4, 14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody552_0, 552, 4)) (some 463) ([10]) (some (10, sourceBody552_11, 552, 5))

def sourceBody552_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_12 sourceBody552_4

def sourceBody552_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_13 sourceBody552_0

def sourceBody552_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_10 sourceBody552_14

def sourceBody552_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody552_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 16)

def sourceBody552_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody552_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody552_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody552_21 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody552_0, 552, 6)) (some 472) ([18, 2, 12, 8]) (some (18, sourceBody552_20, 552, 7))

def sourceBody552_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_21 sourceBody552_4

def sourceBody552_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_22 sourceBody552_0

def sourceBody552_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_19 sourceBody552_23

def sourceBody552_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_18 sourceBody552_24

def sourceBody552_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_17 sourceBody552_25

def sourceBody552_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_16 sourceBody552_26

def sourceBody552_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_0 sourceBody552_27

def sourceBody552_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_0 sourceBody552_28

def sourceBody552_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody552_31 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody552_0, 552, 8)) (some 486) ([18]) (some (18, sourceBody552_20, 552, 9))

def sourceBody552_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_31 sourceBody552_4

def sourceBody552_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_32 sourceBody552_0

def sourceBody552_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_30 sourceBody552_33

def sourceBody552_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_0 sourceBody552_34

def sourceBody552_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_0 sourceBody552_35

def sourceBody552_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_29 sourceBody552_36

def sourceBody552_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody552_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody552_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_39 sourceBody552_0

def sourceBody552_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_38 sourceBody552_40

def sourceBody552_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_37 sourceBody552_41

def sourceBody552_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_15 sourceBody552_42

def sourceBody552_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_0 sourceBody552_43

def sourceBody552_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_0 sourceBody552_44

def sourceBody552_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_0 sourceBody552_45

def sourceBody552_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_0 sourceBody552_46

def sourceBody552_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_0 sourceBody552_47

def sourceBody552_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_0 sourceBody552_48

def sourceBody552_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_0 sourceBody552_49

def sourceBody552_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_0 sourceBody552_50

def sourceBody552_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody552_9 sourceBody552_51

def source552 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (552, 1, sourceBody552_52)
end InitECandidate.Proofs.WordStages
