import InitECandidate.Proofs.WordStages.Source628
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody644_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody644_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody644_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody644_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody644_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody644_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody644_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 12)

def sourceBody644_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 6) 14

def sourceBody644_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_7 sourceBody644_0

def sourceBody644_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_6 sourceBody644_8

def sourceBody644_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody644_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 8#64]) 14

def sourceBody644_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_11 sourceBody644_0

def sourceBody644_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_10 sourceBody644_12

def sourceBody644_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody644_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 16#64])
  14

def sourceBody644_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_15 sourceBody644_0

def sourceBody644_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_14 sourceBody644_16

def sourceBody644_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody644_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 24#64])
  14

def sourceBody644_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_19 sourceBody644_0

def sourceBody644_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_18 sourceBody644_20

def sourceBody644_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_21 sourceBody644_0

def sourceBody644_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_17 sourceBody644_22

def sourceBody644_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_13 sourceBody644_23

def sourceBody644_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_9 sourceBody644_24

def sourceBody644_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_5 sourceBody644_25

def sourceBody644_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_0 sourceBody644_26

def sourceBody644_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_4 sourceBody644_27

def sourceBody644_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_0 sourceBody644_28

def sourceBody644_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_3 sourceBody644_29

def sourceBody644_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_0 sourceBody644_30

def sourceBody644_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_2 sourceBody644_31

def sourceBody644_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_0 sourceBody644_32

def sourceBody644_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_1 sourceBody644_33

def sourceBody644_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_0 sourceBody644_34

def sourceBody644_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody644_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_36 sourceBody644_33

def sourceBody644_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_0 sourceBody644_37

def sourceBody644_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_35 sourceBody644_38

def sourceBody644_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody644_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody644_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_41 sourceBody644_31

def sourceBody644_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_0 sourceBody644_42

def sourceBody644_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_40 sourceBody644_43

def sourceBody644_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_0 sourceBody644_44

def sourceBody644_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_39 sourceBody644_45

def sourceBody644_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody644_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody644_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_48 sourceBody644_0

def sourceBody644_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_47 sourceBody644_49

def sourceBody644_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody644_46 sourceBody644_50

def source644 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (644, 2, sourceBody644_51)
end InitECandidate.Proofs.WordStages
