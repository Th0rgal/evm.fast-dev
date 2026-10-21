import InitECandidate.Proofs.WordStages.Source319
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody335_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody335_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
          (Flapjack.WordLangExpHOL.const 4#64)]))

def sourceBody335_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
          (Flapjack.WordLangExpHOL.const 4#64),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody335_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody335_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 18, 14, 22]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody335_0, 335, 2)) (some 161) ([8, 16]) (some (8, sourceBody335_3, 335, 3))

def sourceBody335_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody335_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_4 sourceBody335_5

def sourceBody335_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_6 sourceBody335_0

def sourceBody335_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_2 sourceBody335_7

def sourceBody335_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_1 sourceBody335_8

def sourceBody335_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 10)

def sourceBody335_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody335_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody335_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody335_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.reg 12) sourceBody335_12 sourceBody335_13

def sourceBody335_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_14 sourceBody335_5

def sourceBody335_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody335_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 15#64)

def sourceBody335_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 8)

def sourceBody335_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_18 sourceBody335_0

def sourceBody335_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_19 sourceBody335_0

def sourceBody335_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_17 sourceBody335_20

def sourceBody335_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_0 sourceBody335_21

def sourceBody335_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody335_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_23 sourceBody335_3

def sourceBody335_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_22 sourceBody335_24

def sourceBody335_26 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody335_25 sourceBody335_0

def sourceBody335_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_26 sourceBody335_5

def sourceBody335_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_27 sourceBody335_0

def sourceBody335_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_16 sourceBody335_28

def sourceBody335_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_15 sourceBody335_29

def sourceBody335_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_11 sourceBody335_30

def sourceBody335_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_10 sourceBody335_31

def sourceBody335_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 14)

def sourceBody335_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody335_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 16#64)

def sourceBody335_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_35 sourceBody335_20

def sourceBody335_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_0 sourceBody335_36

def sourceBody335_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_37 sourceBody335_24

def sourceBody335_39 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody335_38 sourceBody335_0

def sourceBody335_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_39 sourceBody335_5

def sourceBody335_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_40 sourceBody335_0

def sourceBody335_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_16 sourceBody335_41

def sourceBody335_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_15 sourceBody335_42

def sourceBody335_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_34 sourceBody335_43

def sourceBody335_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_33 sourceBody335_44

def sourceBody335_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_32 sourceBody335_45

def sourceBody335_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 18)

def sourceBody335_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody335_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_48 sourceBody335_0

def sourceBody335_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_47 sourceBody335_49

def sourceBody335_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_46 sourceBody335_50

def sourceBody335_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_9 sourceBody335_51

def sourceBody335_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_0 sourceBody335_52

def sourceBody335_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_0 sourceBody335_53

def sourceBody335_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_0 sourceBody335_54

def sourceBody335_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_0 sourceBody335_55

def sourceBody335_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_0 sourceBody335_56

def sourceBody335_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_0 sourceBody335_57

def sourceBody335_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_0 sourceBody335_58

def sourceBody335_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody335_0 sourceBody335_59

def source335 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (335, 4, sourceBody335_60)
end InitECandidate.Proofs.WordStages
