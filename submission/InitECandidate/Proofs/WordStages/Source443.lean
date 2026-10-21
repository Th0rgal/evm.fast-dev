import InitECandidate.Proofs.WordStages.Source427
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody443_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody443_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 176#64]),
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody443_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody443_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody443_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([6, 12]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody443_0, 443, 2)) (some 186) ([4, 10]) (some (4, sourceBody443_3, 443, 3))

def sourceBody443_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody443_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_4 sourceBody443_5

def sourceBody443_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_6 sourceBody443_0

def sourceBody443_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_2 sourceBody443_7

def sourceBody443_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_1 sourceBody443_8

def sourceBody443_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody443_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody443_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody443_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody443_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.reg 8) sourceBody443_12 sourceBody443_13

def sourceBody443_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_14 sourceBody443_5

def sourceBody443_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody443_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 12)

def sourceBody443_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody443_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_18 sourceBody443_0

def sourceBody443_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_17 sourceBody443_19

def sourceBody443_21 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody443_20 sourceBody443_0

def sourceBody443_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_21 sourceBody443_5

def sourceBody443_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_22 sourceBody443_0

def sourceBody443_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_16 sourceBody443_23

def sourceBody443_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_15 sourceBody443_24

def sourceBody443_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_11 sourceBody443_25

def sourceBody443_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_10 sourceBody443_26

def sourceBody443_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody443_29 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody443_0, 443, 4)) (some 392) ([10]) (some (10, sourceBody443_28, 443, 5))

def sourceBody443_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_29 sourceBody443_5

def sourceBody443_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_30 sourceBody443_0

def sourceBody443_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_2 sourceBody443_31

def sourceBody443_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_0 sourceBody443_32

def sourceBody443_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_0 sourceBody443_33

def sourceBody443_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_27 sourceBody443_34

def sourceBody443_36 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody443_0, 443, 6)) (some 394) ([10]) (some (10, sourceBody443_28, 443, 7))

def sourceBody443_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_36 sourceBody443_5

def sourceBody443_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_37 sourceBody443_0

def sourceBody443_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_2 sourceBody443_38

def sourceBody443_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody443_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody443_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_41 sourceBody443_0

def sourceBody443_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_40 sourceBody443_42

def sourceBody443_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_39 sourceBody443_43

def sourceBody443_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_0 sourceBody443_44

def sourceBody443_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_0 sourceBody443_45

def sourceBody443_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_35 sourceBody443_46

def sourceBody443_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_9 sourceBody443_47

def sourceBody443_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_0 sourceBody443_48

def sourceBody443_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_0 sourceBody443_49

def sourceBody443_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_0 sourceBody443_50

def sourceBody443_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody443_0 sourceBody443_51

def source443 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (443, 2, sourceBody443_52)
end InitECandidate.Proofs.WordStages
