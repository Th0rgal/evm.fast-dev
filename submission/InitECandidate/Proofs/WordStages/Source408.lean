import InitECandidate.Proofs.WordStages.Source392
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody408_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody408_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody408_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody408_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody408_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody408_0, 408, 2)) (some 388) ([8, 14]) (some (8, sourceBody408_3, 408, 3))

def sourceBody408_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody408_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_4 sourceBody408_5

def sourceBody408_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_6 sourceBody408_0

def sourceBody408_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_2 sourceBody408_7

def sourceBody408_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_1 sourceBody408_8

def sourceBody408_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 184#64]),
        Flapjack.WordLangExpHOL.const 64#64]))

def sourceBody408_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody408_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody408_13 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody408_0, 408, 4)) (some 186) ([10, 18]) (some (10, sourceBody408_12, 408, 5))

def sourceBody408_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_13 sourceBody408_5

def sourceBody408_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_14 sourceBody408_0

def sourceBody408_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_11 sourceBody408_15

def sourceBody408_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_10 sourceBody408_16

def sourceBody408_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody408_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody408_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody408_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody408_22 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 18 (Flapjack.WordRegImm.reg 6) sourceBody408_20 sourceBody408_21

def sourceBody408_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_22 sourceBody408_5

def sourceBody408_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody408_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody408_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody408_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10, 18, 6, 12]

def sourceBody408_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_27 sourceBody408_0

def sourceBody408_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_26 sourceBody408_28

def sourceBody408_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_19 sourceBody408_29

def sourceBody408_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_21 sourceBody408_30

def sourceBody408_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_25 sourceBody408_31

def sourceBody408_33 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody408_32 sourceBody408_0

def sourceBody408_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_33 sourceBody408_5

def sourceBody408_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_34 sourceBody408_0

def sourceBody408_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_24 sourceBody408_35

def sourceBody408_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_23 sourceBody408_36

def sourceBody408_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_19 sourceBody408_37

def sourceBody408_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_18 sourceBody408_38

def sourceBody408_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 14))

def sourceBody408_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody408_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody408_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody408_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_43 sourceBody408_28

def sourceBody408_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_42 sourceBody408_44

def sourceBody408_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_41 sourceBody408_45

def sourceBody408_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_40 sourceBody408_46

def sourceBody408_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_39 sourceBody408_47

def sourceBody408_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_17 sourceBody408_48

def sourceBody408_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_0 sourceBody408_49

def sourceBody408_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_0 sourceBody408_50

def sourceBody408_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_0 sourceBody408_51

def sourceBody408_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_0 sourceBody408_52

def sourceBody408_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_9 sourceBody408_53

def sourceBody408_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_0 sourceBody408_54

def sourceBody408_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody408_0 sourceBody408_55

def source408 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (408, 3, sourceBody408_56)
end InitECandidate.Proofs.WordStages
