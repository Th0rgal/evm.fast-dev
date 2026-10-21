import InitECandidate.Proofs.WordStages.Source669
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody685_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody685_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody685_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody685_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody685_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody685_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody685_6 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 12 (Flapjack.WordRegImm.reg 10) sourceBody685_5 sourceBody685_3

def sourceBody685_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_6 sourceBody685_2

def sourceBody685_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 12)

def sourceBody685_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody685_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody685_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_10 sourceBody685_0

def sourceBody685_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_11 sourceBody685_0

def sourceBody685_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_9 sourceBody685_12

def sourceBody685_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_0 sourceBody685_13

def sourceBody685_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 14)
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody685_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody685_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody685_18 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody685_0, 685, 2)) (some 80) ([12, 10]) (some (12, sourceBody685_17, 685, 3))

def sourceBody685_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_18 sourceBody685_2

def sourceBody685_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_19 sourceBody685_0

def sourceBody685_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_16 sourceBody685_20

def sourceBody685_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_15 sourceBody685_21

def sourceBody685_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody685_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody685_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody685_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody685_27 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 10 (Flapjack.WordRegImm.reg 16) sourceBody685_25 sourceBody685_26

def sourceBody685_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_27 sourceBody685_2

def sourceBody685_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 10)

def sourceBody685_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody685_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody685_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_31 sourceBody685_0

def sourceBody685_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_30 sourceBody685_32

def sourceBody685_34 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody685_33 sourceBody685_0

def sourceBody685_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_34 sourceBody685_2

def sourceBody685_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_35 sourceBody685_0

def sourceBody685_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_29 sourceBody685_36

def sourceBody685_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_28 sourceBody685_37

def sourceBody685_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_24 sourceBody685_38

def sourceBody685_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_23 sourceBody685_39

def sourceBody685_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_22 sourceBody685_40

def sourceBody685_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_0 sourceBody685_41

def sourceBody685_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_0 sourceBody685_42

def sourceBody685_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_14 sourceBody685_43

def sourceBody685_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody685_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_44 sourceBody685_45

def sourceBody685_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody685_48 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody685_46 sourceBody685_47

def sourceBody685_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_48 sourceBody685_2

def sourceBody685_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_49 sourceBody685_0

def sourceBody685_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_8 sourceBody685_50

def sourceBody685_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_7 sourceBody685_51

def sourceBody685_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_4 sourceBody685_52

def sourceBody685_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_3 sourceBody685_53

def sourceBody685_55 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
    (Flapjack.Spt.ls PUnit.unit))
  PUnit.unit Flapjack.Spt.ln) sourceBody685_54 (Flapjack.Spt.ls PUnit.unit)

def sourceBody685_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_55 sourceBody685_2

def sourceBody685_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_2 sourceBody685_56

def sourceBody685_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.const 0#64, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody685_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody685_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_59 sourceBody685_0

def sourceBody685_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_58 sourceBody685_60

def sourceBody685_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_57 sourceBody685_61

def sourceBody685_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_1 sourceBody685_62

def sourceBody685_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody685_0 sourceBody685_63

def source685 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (685, 3, sourceBody685_64)
end InitECandidate.Proofs.WordStages
