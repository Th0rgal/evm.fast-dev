import InitECandidate.Proofs.WordStages.Source820
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody836_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody836_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.var 4,
      Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 9#64]])

def sourceBody836_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody836_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody836_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody836_0, 836, 2)) (some 180) ([12]) (some (12, sourceBody836_3, 836, 3))

def sourceBody836_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody836_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody836_4 sourceBody836_5

def sourceBody836_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody836_6 sourceBody836_0

def sourceBody836_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody836_2 sourceBody836_7

def sourceBody836_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 8])

def sourceBody836_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 9#64])

def sourceBody836_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 14)

def sourceBody836_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody836_13 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody836_0, 836, 4)) (some 77) ([10, 16, 6]) (some (10, sourceBody836_12, 836, 5))

def sourceBody836_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody836_13 sourceBody836_5

def sourceBody836_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody836_14 sourceBody836_0

def sourceBody836_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody836_11 sourceBody836_15

def sourceBody836_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody836_10 sourceBody836_16

def sourceBody836_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody836_9 sourceBody836_17

def sourceBody836_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody836_0 sourceBody836_18

def sourceBody836_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody836_0 sourceBody836_19

def sourceBody836_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody836_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 14)

def sourceBody836_23 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody836_0, 836, 6)) (some 178) ([10, 16]) (some (10, sourceBody836_12, 836, 7))

def sourceBody836_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody836_23 sourceBody836_5

def sourceBody836_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody836_24 sourceBody836_0

def sourceBody836_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody836_22 sourceBody836_25

def sourceBody836_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody836_21 sourceBody836_26

def sourceBody836_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody836_0 sourceBody836_27

def sourceBody836_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody836_0 sourceBody836_28

def sourceBody836_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody836_20 sourceBody836_29

def sourceBody836_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.var 14])

def sourceBody836_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody836_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody836_32 sourceBody836_0

def sourceBody836_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody836_31 sourceBody836_33

def sourceBody836_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody836_30 sourceBody836_34

def sourceBody836_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody836_8 sourceBody836_35

def sourceBody836_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody836_0 sourceBody836_36

def sourceBody836_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody836_0 sourceBody836_37

def sourceBody836_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody836_1 sourceBody836_38

def sourceBody836_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody836_0 sourceBody836_39

def source836 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (836, 3, sourceBody836_40)
end InitECandidate.Proofs.WordStages
