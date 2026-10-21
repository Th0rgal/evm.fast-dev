import InitECandidate.Proofs.WordStages.Source253
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody269_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody269_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
          (Flapjack.WordLangExpHOL.const 4#64)]))

def sourceBody269_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
          (Flapjack.WordLangExpHOL.const 4#64),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody269_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody269_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 8, 16, 12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody269_0, 269, 2)) (some 161) ([20, 6]) (some (20, sourceBody269_3, 269, 3))

def sourceBody269_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody269_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_4 sourceBody269_5

def sourceBody269_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_6 sourceBody269_0

def sourceBody269_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_2 sourceBody269_7

def sourceBody269_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_1 sourceBody269_8

def sourceBody269_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 18)

def sourceBody269_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody269_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody269_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody269_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.reg 14) sourceBody269_12 sourceBody269_13

def sourceBody269_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_14 sourceBody269_5

def sourceBody269_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody269_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody269_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 20)

def sourceBody269_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_18 sourceBody269_0

def sourceBody269_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_19 sourceBody269_0

def sourceBody269_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_17 sourceBody269_20

def sourceBody269_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_0 sourceBody269_21

def sourceBody269_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody269_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_23 sourceBody269_3

def sourceBody269_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_22 sourceBody269_24

def sourceBody269_26 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody269_25 sourceBody269_0

def sourceBody269_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_26 sourceBody269_5

def sourceBody269_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_27 sourceBody269_0

def sourceBody269_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_16 sourceBody269_28

def sourceBody269_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_15 sourceBody269_29

def sourceBody269_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_11 sourceBody269_30

def sourceBody269_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_10 sourceBody269_31

def sourceBody269_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody269_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 16)

def sourceBody269_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20, 6]

def sourceBody269_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_35 sourceBody269_0

def sourceBody269_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_34 sourceBody269_36

def sourceBody269_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_33 sourceBody269_37

def sourceBody269_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_32 sourceBody269_38

def sourceBody269_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_9 sourceBody269_39

def sourceBody269_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_0 sourceBody269_40

def sourceBody269_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_0 sourceBody269_41

def sourceBody269_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_0 sourceBody269_42

def sourceBody269_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_0 sourceBody269_43

def sourceBody269_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_0 sourceBody269_44

def sourceBody269_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_0 sourceBody269_45

def sourceBody269_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_0 sourceBody269_46

def sourceBody269_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody269_0 sourceBody269_47

def source269 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (269, 3, sourceBody269_48)
end InitECandidate.Proofs.WordStages
