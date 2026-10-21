import InitECandidate.Proofs.WordStages.Source277
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody293_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody293_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 56#64)

def sourceBody293_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody293_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody293_0, 293, 2)) (some 68) ([12]) (some (12, sourceBody293_2, 293, 3))

def sourceBody293_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody293_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_3 sourceBody293_4

def sourceBody293_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_5 sourceBody293_0

def sourceBody293_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_1 sourceBody293_6

def sourceBody293_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody293_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody293_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody293_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 12) 14

def sourceBody293_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_11 sourceBody293_0

def sourceBody293_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_10 sourceBody293_12

def sourceBody293_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_13 sourceBody293_0

def sourceBody293_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_9 sourceBody293_14

def sourceBody293_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_0 sourceBody293_15

def sourceBody293_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_8 sourceBody293_16

def sourceBody293_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_0 sourceBody293_17

def sourceBody293_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody293_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody293_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_20 sourceBody293_14

def sourceBody293_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_0 sourceBody293_21

def sourceBody293_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_19 sourceBody293_22

def sourceBody293_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_0 sourceBody293_23

def sourceBody293_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_18 sourceBody293_24

def sourceBody293_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody293_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_26 sourceBody293_22

def sourceBody293_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_0 sourceBody293_27

def sourceBody293_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_25 sourceBody293_28

def sourceBody293_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 24#64])

def sourceBody293_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_30 sourceBody293_22

def sourceBody293_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_0 sourceBody293_31

def sourceBody293_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_29 sourceBody293_32

def sourceBody293_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody293_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody293_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_35 sourceBody293_14

def sourceBody293_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_0 sourceBody293_36

def sourceBody293_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_34 sourceBody293_37

def sourceBody293_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_0 sourceBody293_38

def sourceBody293_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_33 sourceBody293_39

def sourceBody293_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 40#64])

def sourceBody293_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody293_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_42 sourceBody293_14

def sourceBody293_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_0 sourceBody293_43

def sourceBody293_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_41 sourceBody293_44

def sourceBody293_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_0 sourceBody293_45

def sourceBody293_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_40 sourceBody293_46

def sourceBody293_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody293_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody293_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_49 sourceBody293_14

def sourceBody293_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_0 sourceBody293_50

def sourceBody293_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_48 sourceBody293_51

def sourceBody293_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_0 sourceBody293_52

def sourceBody293_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_47 sourceBody293_53

def sourceBody293_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody293_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody293_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_56 sourceBody293_0

def sourceBody293_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_55 sourceBody293_57

def sourceBody293_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_54 sourceBody293_58

def sourceBody293_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_7 sourceBody293_59

def sourceBody293_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_0 sourceBody293_60

def sourceBody293_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody293_0 sourceBody293_61

def source293 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (293, 4, sourceBody293_62)
end InitECandidate.Proofs.WordStages
