import InitECandidate.Proofs.WordStages.Source362
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody378_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody378_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody378_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody378_0, 378, 2)) (some 69) ([]) (some (16, sourceBody378_1, 378, 3))

def sourceBody378_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody378_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_2 sourceBody378_3

def sourceBody378_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_4 sourceBody378_0

def sourceBody378_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 72#64)

def sourceBody378_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody378_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody378_0, 378, 4)) (some 68) ([12]) (some (12, sourceBody378_7, 378, 5))

def sourceBody378_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_8 sourceBody378_3

def sourceBody378_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_9 sourceBody378_0

def sourceBody378_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_6 sourceBody378_10

def sourceBody378_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 16)

def sourceBody378_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody378_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 18 (Flapjack.WordLangAddr.addr 12 0#64))

def sourceBody378_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_14 sourceBody378_0

def sourceBody378_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_13 sourceBody378_15

def sourceBody378_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_12 sourceBody378_16

def sourceBody378_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 2)

def sourceBody378_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody378_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody378_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody378_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody378_0, 378, 6)) (some 375) ([18, 8, 14]) (some (18, sourceBody378_21, 378, 7))

def sourceBody378_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_22 sourceBody378_3

def sourceBody378_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_23 sourceBody378_0

def sourceBody378_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_20 sourceBody378_24

def sourceBody378_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_19 sourceBody378_25

def sourceBody378_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_18 sourceBody378_26

def sourceBody378_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_0 sourceBody378_27

def sourceBody378_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_0 sourceBody378_28

def sourceBody378_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_17 sourceBody378_29

def sourceBody378_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody378_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 6)

def sourceBody378_33 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody378_0, 378, 8)) (some 376) ([18, 8]) (some (18, sourceBody378_21, 378, 9))

def sourceBody378_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_33 sourceBody378_3

def sourceBody378_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_34 sourceBody378_0

def sourceBody378_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_32 sourceBody378_35

def sourceBody378_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_31 sourceBody378_36

def sourceBody378_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_0 sourceBody378_37

def sourceBody378_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_0 sourceBody378_38

def sourceBody378_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_30 sourceBody378_39

def sourceBody378_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 10)

def sourceBody378_42 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody378_0, 378, 10)) (some 70) ([18]) (some (18, sourceBody378_21, 378, 11))

def sourceBody378_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_42 sourceBody378_3

def sourceBody378_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_43 sourceBody378_0

def sourceBody378_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_41 sourceBody378_44

def sourceBody378_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_0 sourceBody378_45

def sourceBody378_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_0 sourceBody378_46

def sourceBody378_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_40 sourceBody378_47

def sourceBody378_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody378_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody378_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_50 sourceBody378_0

def sourceBody378_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_49 sourceBody378_51

def sourceBody378_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_48 sourceBody378_52

def sourceBody378_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_11 sourceBody378_53

def sourceBody378_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_0 sourceBody378_54

def sourceBody378_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_0 sourceBody378_55

def sourceBody378_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_5 sourceBody378_56

def sourceBody378_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_0 sourceBody378_57

def sourceBody378_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody378_0 sourceBody378_58

def source378 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (378, 4, sourceBody378_59)
end InitECandidate.Proofs.WordStages
