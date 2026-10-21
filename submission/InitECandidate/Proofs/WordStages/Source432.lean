import InitECandidate.Proofs.WordStages.Source416
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody432_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody432_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 24#64)

def sourceBody432_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody432_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody432_0, 432, 2)) (some 74) ([8]) (some (8, sourceBody432_2, 432, 3))

def sourceBody432_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody432_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_3 sourceBody432_4

def sourceBody432_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_5 sourceBody432_0

def sourceBody432_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_1 sourceBody432_6

def sourceBody432_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody432_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody432_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 16 16 12 10))

def sourceBody432_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 16)

def sourceBody432_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody432_13 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody432_0, 432, 4)) (some 74) ([6]) (some (12, sourceBody432_12, 432, 5))

def sourceBody432_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_13 sourceBody432_4

def sourceBody432_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_14 sourceBody432_0

def sourceBody432_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_11 sourceBody432_15

def sourceBody432_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_10 sourceBody432_16

def sourceBody432_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_9 sourceBody432_17

def sourceBody432_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_8 sourceBody432_18

def sourceBody432_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody432_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody432_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 10)

def sourceBody432_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 12) 16

def sourceBody432_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_23 sourceBody432_0

def sourceBody432_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_22 sourceBody432_24

def sourceBody432_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_25 sourceBody432_0

def sourceBody432_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_21 sourceBody432_26

def sourceBody432_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_0 sourceBody432_27

def sourceBody432_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_20 sourceBody432_28

def sourceBody432_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_0 sourceBody432_29

def sourceBody432_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody432_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody432_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_32 sourceBody432_26

def sourceBody432_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_0 sourceBody432_33

def sourceBody432_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_31 sourceBody432_34

def sourceBody432_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_0 sourceBody432_35

def sourceBody432_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_30 sourceBody432_36

def sourceBody432_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody432_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_9 sourceBody432_26

def sourceBody432_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_0 sourceBody432_39

def sourceBody432_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_38 sourceBody432_40

def sourceBody432_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_0 sourceBody432_41

def sourceBody432_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_37 sourceBody432_42

def sourceBody432_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody432_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody432_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_45 sourceBody432_0

def sourceBody432_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_44 sourceBody432_46

def sourceBody432_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_43 sourceBody432_47

def sourceBody432_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_19 sourceBody432_48

def sourceBody432_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_0 sourceBody432_49

def sourceBody432_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_0 sourceBody432_50

def sourceBody432_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_7 sourceBody432_51

def sourceBody432_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_0 sourceBody432_52

def sourceBody432_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody432_0 sourceBody432_53

def source432 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (432, 3, sourceBody432_54)
end InitECandidate.Proofs.WordStages
