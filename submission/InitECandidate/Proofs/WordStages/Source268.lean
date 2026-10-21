import InitECandidate.Proofs.WordStages.Source252
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody268_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody268_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
          (Flapjack.WordLangExpHOL.const 4#64)]))

def sourceBody268_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
          (Flapjack.WordLangExpHOL.const 4#64),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody268_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody268_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 18, 14, 22]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody268_0, 268, 2)) (some 161) ([8, 16]) (some (8, sourceBody268_3, 268, 3))

def sourceBody268_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody268_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_4 sourceBody268_5

def sourceBody268_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_6 sourceBody268_0

def sourceBody268_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_2 sourceBody268_7

def sourceBody268_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_1 sourceBody268_8

def sourceBody268_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 10)

def sourceBody268_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody268_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody268_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody268_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.reg 12) sourceBody268_12 sourceBody268_13

def sourceBody268_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_14 sourceBody268_5

def sourceBody268_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody268_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody268_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 8)

def sourceBody268_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_18 sourceBody268_0

def sourceBody268_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_19 sourceBody268_0

def sourceBody268_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_17 sourceBody268_20

def sourceBody268_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_0 sourceBody268_21

def sourceBody268_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody268_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_23 sourceBody268_3

def sourceBody268_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_22 sourceBody268_24

def sourceBody268_26 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody268_25 sourceBody268_0

def sourceBody268_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_26 sourceBody268_5

def sourceBody268_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_27 sourceBody268_0

def sourceBody268_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_16 sourceBody268_28

def sourceBody268_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_15 sourceBody268_29

def sourceBody268_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_11 sourceBody268_30

def sourceBody268_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_10 sourceBody268_31

def sourceBody268_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 14)

def sourceBody268_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody268_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 7#64)

def sourceBody268_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_35 sourceBody268_20

def sourceBody268_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_0 sourceBody268_36

def sourceBody268_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_37 sourceBody268_24

def sourceBody268_39 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody268_38 sourceBody268_0

def sourceBody268_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_39 sourceBody268_5

def sourceBody268_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_40 sourceBody268_0

def sourceBody268_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_16 sourceBody268_41

def sourceBody268_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_15 sourceBody268_42

def sourceBody268_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_34 sourceBody268_43

def sourceBody268_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_33 sourceBody268_44

def sourceBody268_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_32 sourceBody268_45

def sourceBody268_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 18)

def sourceBody268_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody268_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_48 sourceBody268_0

def sourceBody268_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_47 sourceBody268_49

def sourceBody268_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_46 sourceBody268_50

def sourceBody268_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_9 sourceBody268_51

def sourceBody268_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_0 sourceBody268_52

def sourceBody268_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_0 sourceBody268_53

def sourceBody268_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_0 sourceBody268_54

def sourceBody268_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_0 sourceBody268_55

def sourceBody268_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_0 sourceBody268_56

def sourceBody268_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_0 sourceBody268_57

def sourceBody268_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_0 sourceBody268_58

def sourceBody268_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody268_0 sourceBody268_59

def source268 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (268, 4, sourceBody268_60)
end InitECandidate.Proofs.WordStages
