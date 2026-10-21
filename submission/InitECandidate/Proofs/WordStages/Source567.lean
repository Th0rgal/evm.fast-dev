import InitECandidate.Proofs.WordStages.Source551
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody567_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody567_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 5#64)

def sourceBody567_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody567_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody567_0, 567, 2)) (some 466) ([10]) (some (10, sourceBody567_2, 567, 3))

def sourceBody567_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody567_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_3 sourceBody567_4

def sourceBody567_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_5 sourceBody567_0

def sourceBody567_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_1 sourceBody567_6

def sourceBody567_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_0 sourceBody567_7

def sourceBody567_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_0 sourceBody567_8

def sourceBody567_10 : WordLangProgHOL (BitVec 64) :=
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

def sourceBody567_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody567_0, 567, 4)) (some 403) ([10]) (some (10, sourceBody567_2, 567, 5))

def sourceBody567_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_11 sourceBody567_4

def sourceBody567_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_12 sourceBody567_0

def sourceBody567_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_10 sourceBody567_13

def sourceBody567_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody567_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody567_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody567_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody567_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody567_20 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody567_0, 567, 6)) (some 472) ([2, 8, 6, 12]) (some (2, sourceBody567_19, 567, 7))

def sourceBody567_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_20 sourceBody567_4

def sourceBody567_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_21 sourceBody567_0

def sourceBody567_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_18 sourceBody567_22

def sourceBody567_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_17 sourceBody567_23

def sourceBody567_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_16 sourceBody567_24

def sourceBody567_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_15 sourceBody567_25

def sourceBody567_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_0 sourceBody567_26

def sourceBody567_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_0 sourceBody567_27

def sourceBody567_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody567_30 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody567_0, 567, 8)) (some 486) ([2]) (some (2, sourceBody567_19, 567, 9))

def sourceBody567_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_30 sourceBody567_4

def sourceBody567_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_31 sourceBody567_0

def sourceBody567_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_29 sourceBody567_32

def sourceBody567_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_0 sourceBody567_33

def sourceBody567_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_0 sourceBody567_34

def sourceBody567_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_28 sourceBody567_35

def sourceBody567_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody567_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody567_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_38 sourceBody567_0

def sourceBody567_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_37 sourceBody567_39

def sourceBody567_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_36 sourceBody567_40

def sourceBody567_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_14 sourceBody567_41

def sourceBody567_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_0 sourceBody567_42

def sourceBody567_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_0 sourceBody567_43

def sourceBody567_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody567_9 sourceBody567_44

def source567 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (567, 1, sourceBody567_45)
end InitECandidate.Proofs.WordStages
