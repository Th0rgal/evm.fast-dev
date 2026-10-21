import InitECandidate.Proofs.WordStages.Source321
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody337_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody337_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
          (Flapjack.WordLangExpHOL.const 4#64)]))

def sourceBody337_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
          (Flapjack.WordLangExpHOL.const 4#64),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody337_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody337_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 8, 16, 12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody337_0, 337, 2)) (some 161) ([20, 6]) (some (20, sourceBody337_3, 337, 3))

def sourceBody337_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody337_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_4 sourceBody337_5

def sourceBody337_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_6 sourceBody337_0

def sourceBody337_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_2 sourceBody337_7

def sourceBody337_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_1 sourceBody337_8

def sourceBody337_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 18)

def sourceBody337_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody337_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody337_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody337_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.reg 14) sourceBody337_12 sourceBody337_13

def sourceBody337_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_14 sourceBody337_5

def sourceBody337_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody337_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 18#64)

def sourceBody337_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 20)

def sourceBody337_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_18 sourceBody337_0

def sourceBody337_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_19 sourceBody337_0

def sourceBody337_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_17 sourceBody337_20

def sourceBody337_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_0 sourceBody337_21

def sourceBody337_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody337_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_23 sourceBody337_3

def sourceBody337_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_22 sourceBody337_24

def sourceBody337_26 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody337_25 sourceBody337_0

def sourceBody337_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_26 sourceBody337_5

def sourceBody337_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_27 sourceBody337_0

def sourceBody337_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_16 sourceBody337_28

def sourceBody337_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_15 sourceBody337_29

def sourceBody337_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_11 sourceBody337_30

def sourceBody337_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_10 sourceBody337_31

def sourceBody337_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody337_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 16)

def sourceBody337_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20, 6]

def sourceBody337_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_35 sourceBody337_0

def sourceBody337_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_34 sourceBody337_36

def sourceBody337_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_33 sourceBody337_37

def sourceBody337_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_32 sourceBody337_38

def sourceBody337_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_9 sourceBody337_39

def sourceBody337_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_0 sourceBody337_40

def sourceBody337_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_0 sourceBody337_41

def sourceBody337_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_0 sourceBody337_42

def sourceBody337_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_0 sourceBody337_43

def sourceBody337_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_0 sourceBody337_44

def sourceBody337_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_0 sourceBody337_45

def sourceBody337_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_0 sourceBody337_46

def sourceBody337_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody337_0 sourceBody337_47

def source337 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (337, 3, sourceBody337_48)
end InitECandidate.Proofs.WordStages
