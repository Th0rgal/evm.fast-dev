import InitECandidate.Proofs.WordStages.Source318
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody334_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody334_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
          (Flapjack.WordLangExpHOL.const 4#64)]))

def sourceBody334_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
          (Flapjack.WordLangExpHOL.const 4#64),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody334_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody334_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 8, 16, 12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody334_0, 334, 2)) (some 161) ([20, 6]) (some (20, sourceBody334_3, 334, 3))

def sourceBody334_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody334_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_4 sourceBody334_5

def sourceBody334_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_6 sourceBody334_0

def sourceBody334_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_2 sourceBody334_7

def sourceBody334_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_1 sourceBody334_8

def sourceBody334_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 18)

def sourceBody334_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody334_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody334_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody334_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.reg 14) sourceBody334_12 sourceBody334_13

def sourceBody334_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_14 sourceBody334_5

def sourceBody334_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody334_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 15#64)

def sourceBody334_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 20)

def sourceBody334_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_18 sourceBody334_0

def sourceBody334_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_19 sourceBody334_0

def sourceBody334_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_17 sourceBody334_20

def sourceBody334_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_0 sourceBody334_21

def sourceBody334_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody334_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_23 sourceBody334_3

def sourceBody334_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_22 sourceBody334_24

def sourceBody334_26 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody334_25 sourceBody334_0

def sourceBody334_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_26 sourceBody334_5

def sourceBody334_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_27 sourceBody334_0

def sourceBody334_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_16 sourceBody334_28

def sourceBody334_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_15 sourceBody334_29

def sourceBody334_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_11 sourceBody334_30

def sourceBody334_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_10 sourceBody334_31

def sourceBody334_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody334_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 16)

def sourceBody334_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20, 6]

def sourceBody334_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_35 sourceBody334_0

def sourceBody334_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_34 sourceBody334_36

def sourceBody334_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_33 sourceBody334_37

def sourceBody334_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_32 sourceBody334_38

def sourceBody334_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_9 sourceBody334_39

def sourceBody334_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_0 sourceBody334_40

def sourceBody334_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_0 sourceBody334_41

def sourceBody334_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_0 sourceBody334_42

def sourceBody334_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_0 sourceBody334_43

def sourceBody334_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_0 sourceBody334_44

def sourceBody334_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_0 sourceBody334_45

def sourceBody334_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_0 sourceBody334_46

def sourceBody334_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody334_0 sourceBody334_47

def source334 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (334, 3, sourceBody334_48)
end InitECandidate.Proofs.WordStages
