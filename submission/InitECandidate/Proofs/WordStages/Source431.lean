import InitECandidate.Proofs.WordStages.Source415
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody431_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody431_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 24#64)

def sourceBody431_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody431_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody431_0, 431, 2)) (some 68) ([8]) (some (8, sourceBody431_2, 431, 3))

def sourceBody431_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody431_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_3 sourceBody431_4

def sourceBody431_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_5 sourceBody431_0

def sourceBody431_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_1 sourceBody431_6

def sourceBody431_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody431_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody431_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 16 16 12 10))

def sourceBody431_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 16)

def sourceBody431_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody431_13 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody431_0, 431, 4)) (some 68) ([6]) (some (12, sourceBody431_12, 431, 5))

def sourceBody431_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_13 sourceBody431_4

def sourceBody431_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_14 sourceBody431_0

def sourceBody431_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_11 sourceBody431_15

def sourceBody431_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_10 sourceBody431_16

def sourceBody431_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_9 sourceBody431_17

def sourceBody431_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_8 sourceBody431_18

def sourceBody431_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody431_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody431_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 10)

def sourceBody431_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 12) 16

def sourceBody431_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_23 sourceBody431_0

def sourceBody431_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_22 sourceBody431_24

def sourceBody431_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_25 sourceBody431_0

def sourceBody431_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_21 sourceBody431_26

def sourceBody431_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_0 sourceBody431_27

def sourceBody431_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_20 sourceBody431_28

def sourceBody431_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_0 sourceBody431_29

def sourceBody431_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody431_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody431_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_32 sourceBody431_26

def sourceBody431_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_0 sourceBody431_33

def sourceBody431_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_31 sourceBody431_34

def sourceBody431_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_0 sourceBody431_35

def sourceBody431_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_30 sourceBody431_36

def sourceBody431_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody431_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_9 sourceBody431_26

def sourceBody431_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_0 sourceBody431_39

def sourceBody431_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_38 sourceBody431_40

def sourceBody431_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_0 sourceBody431_41

def sourceBody431_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_37 sourceBody431_42

def sourceBody431_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody431_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody431_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_45 sourceBody431_0

def sourceBody431_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_44 sourceBody431_46

def sourceBody431_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_43 sourceBody431_47

def sourceBody431_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_19 sourceBody431_48

def sourceBody431_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_0 sourceBody431_49

def sourceBody431_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_0 sourceBody431_50

def sourceBody431_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_7 sourceBody431_51

def sourceBody431_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_0 sourceBody431_52

def sourceBody431_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody431_0 sourceBody431_53

def source431 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (431, 3, sourceBody431_54)
end InitECandidate.Proofs.WordStages
