import InitECandidate.Proofs.WordStages.Source659
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody675_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody675_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody675_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 2)
    (Flapjack.WordLangExpHOL.const 5#64))

def sourceBody675_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody675_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody675_0, 675, 2)) (some 78) ([8, 12]) (some (8, sourceBody675_3, 675, 3))

def sourceBody675_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody675_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_4 sourceBody675_5

def sourceBody675_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_6 sourceBody675_0

def sourceBody675_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_2 sourceBody675_7

def sourceBody675_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_1 sourceBody675_8

def sourceBody675_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_0 sourceBody675_9

def sourceBody675_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_0 sourceBody675_10

def sourceBody675_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody675_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 15230403791020821917#64)

def sourceBody675_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 754611498739239741#64)

def sourceBody675_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 7381016538464732716#64)

def sourceBody675_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1011752739694698287#64)

def sourceBody675_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody675_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 14) 6

def sourceBody675_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_18 sourceBody675_0

def sourceBody675_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_17 sourceBody675_19

def sourceBody675_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def sourceBody675_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 8#64]) 6

def sourceBody675_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_22 sourceBody675_0

def sourceBody675_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_21 sourceBody675_23

def sourceBody675_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 10)

def sourceBody675_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 16#64])
  6

def sourceBody675_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_26 sourceBody675_0

def sourceBody675_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_25 sourceBody675_27

def sourceBody675_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 16)

def sourceBody675_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 24#64])
  6

def sourceBody675_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_30 sourceBody675_0

def sourceBody675_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_29 sourceBody675_31

def sourceBody675_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_32 sourceBody675_0

def sourceBody675_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_28 sourceBody675_33

def sourceBody675_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_24 sourceBody675_34

def sourceBody675_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_20 sourceBody675_35

def sourceBody675_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_16 sourceBody675_36

def sourceBody675_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_0 sourceBody675_37

def sourceBody675_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_15 sourceBody675_38

def sourceBody675_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_0 sourceBody675_39

def sourceBody675_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_14 sourceBody675_40

def sourceBody675_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_0 sourceBody675_41

def sourceBody675_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_13 sourceBody675_42

def sourceBody675_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_0 sourceBody675_43

def sourceBody675_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_12 sourceBody675_44

def sourceBody675_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_0 sourceBody675_45

def sourceBody675_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_11 sourceBody675_46

def sourceBody675_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody675_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody675_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_49 sourceBody675_0

def sourceBody675_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_48 sourceBody675_50

def sourceBody675_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody675_47 sourceBody675_51

def source675 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (675, 3, sourceBody675_52)
end InitECandidate.Proofs.WordStages
