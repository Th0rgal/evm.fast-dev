import InitECandidate.Proofs.WordStages.Source553
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody569_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody569_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody569_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody569_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody569_0, 569, 2)) (some 466) ([10]) (some (10, sourceBody569_2, 569, 3))

def sourceBody569_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody569_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_3 sourceBody569_4

def sourceBody569_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_5 sourceBody569_0

def sourceBody569_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_1 sourceBody569_6

def sourceBody569_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_0 sourceBody569_7

def sourceBody569_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_0 sourceBody569_8

def sourceBody569_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody569_0, 569, 4)) (some 568) ([]) (some (10, sourceBody569_2, 569, 5))

def sourceBody569_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_10 sourceBody569_4

def sourceBody569_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_11 sourceBody569_0

def sourceBody569_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody569_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody569_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody569_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody569_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody569_18 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody569_0, 569, 6)) (some 472) ([2, 8, 6, 12]) (some (2, sourceBody569_17, 569, 7))

def sourceBody569_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_18 sourceBody569_4

def sourceBody569_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_19 sourceBody569_0

def sourceBody569_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_16 sourceBody569_20

def sourceBody569_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_15 sourceBody569_21

def sourceBody569_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_14 sourceBody569_22

def sourceBody569_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_13 sourceBody569_23

def sourceBody569_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_0 sourceBody569_24

def sourceBody569_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_0 sourceBody569_25

def sourceBody569_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody569_28 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody569_0, 569, 8)) (some 486) ([2]) (some (2, sourceBody569_17, 569, 9))

def sourceBody569_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_28 sourceBody569_4

def sourceBody569_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_29 sourceBody569_0

def sourceBody569_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_27 sourceBody569_30

def sourceBody569_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_0 sourceBody569_31

def sourceBody569_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_0 sourceBody569_32

def sourceBody569_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_26 sourceBody569_33

def sourceBody569_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody569_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody569_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_36 sourceBody569_0

def sourceBody569_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_35 sourceBody569_37

def sourceBody569_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_34 sourceBody569_38

def sourceBody569_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_12 sourceBody569_39

def sourceBody569_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_0 sourceBody569_40

def sourceBody569_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_0 sourceBody569_41

def sourceBody569_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody569_9 sourceBody569_42

def source569 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (569, 1, sourceBody569_43)
end InitECandidate.Proofs.WordStages
