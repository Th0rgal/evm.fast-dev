import InitECandidate.Proofs.WordStages.Source320
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody336_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody336_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
          (Flapjack.WordLangExpHOL.const 4#64)]))

def sourceBody336_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
          (Flapjack.WordLangExpHOL.const 4#64),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody336_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody336_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 8, 16, 12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody336_0, 336, 2)) (some 161) ([20, 6]) (some (20, sourceBody336_3, 336, 3))

def sourceBody336_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody336_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_4 sourceBody336_5

def sourceBody336_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_6 sourceBody336_0

def sourceBody336_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_2 sourceBody336_7

def sourceBody336_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_1 sourceBody336_8

def sourceBody336_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 18)

def sourceBody336_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody336_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody336_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody336_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.reg 14) sourceBody336_12 sourceBody336_13

def sourceBody336_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_14 sourceBody336_5

def sourceBody336_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody336_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 17#64)

def sourceBody336_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 20)

def sourceBody336_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_18 sourceBody336_0

def sourceBody336_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_19 sourceBody336_0

def sourceBody336_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_17 sourceBody336_20

def sourceBody336_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_0 sourceBody336_21

def sourceBody336_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody336_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_23 sourceBody336_3

def sourceBody336_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_22 sourceBody336_24

def sourceBody336_26 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody336_25 sourceBody336_0

def sourceBody336_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_26 sourceBody336_5

def sourceBody336_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_27 sourceBody336_0

def sourceBody336_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_16 sourceBody336_28

def sourceBody336_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_15 sourceBody336_29

def sourceBody336_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_11 sourceBody336_30

def sourceBody336_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_10 sourceBody336_31

def sourceBody336_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 16)

def sourceBody336_34 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.WordRegImm.reg 14) sourceBody336_12 sourceBody336_13

def sourceBody336_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_34 sourceBody336_5

def sourceBody336_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody336_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody336_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_37 sourceBody336_0

def sourceBody336_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_36 sourceBody336_38

def sourceBody336_40 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody336_39 sourceBody336_0

def sourceBody336_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_40 sourceBody336_5

def sourceBody336_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_41 sourceBody336_0

def sourceBody336_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_16 sourceBody336_42

def sourceBody336_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_35 sourceBody336_43

def sourceBody336_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_11 sourceBody336_44

def sourceBody336_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_33 sourceBody336_45

def sourceBody336_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_32 sourceBody336_46

def sourceBody336_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody336_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_48 sourceBody336_30

def sourceBody336_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_33 sourceBody336_49

def sourceBody336_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_47 sourceBody336_50

def sourceBody336_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody336_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_52 sourceBody336_38

def sourceBody336_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_51 sourceBody336_53

def sourceBody336_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_9 sourceBody336_54

def sourceBody336_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_0 sourceBody336_55

def sourceBody336_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_0 sourceBody336_56

def sourceBody336_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_0 sourceBody336_57

def sourceBody336_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_0 sourceBody336_58

def sourceBody336_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_0 sourceBody336_59

def sourceBody336_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_0 sourceBody336_60

def sourceBody336_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_0 sourceBody336_61

def sourceBody336_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody336_0 sourceBody336_62

def source336 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (336, 3, sourceBody336_63)
end InitECandidate.Proofs.WordStages
