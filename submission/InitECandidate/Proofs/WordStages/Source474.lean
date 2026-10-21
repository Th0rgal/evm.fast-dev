import InitECandidate.Proofs.WordStages.Source458
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody474_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody474_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody474_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody474_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody474_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.reg 4) sourceBody474_2 sourceBody474_3

def sourceBody474_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody474_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody474_4 sourceBody474_5

def sourceBody474_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody474_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody474_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody474_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody474_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody474_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody474_8, 474, 2)) (some 472) ([12, 4, 10, 8]) (some (12, sourceBody474_11, 474, 3))

def sourceBody474_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody474_12 sourceBody474_5

def sourceBody474_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody474_13 sourceBody474_8

def sourceBody474_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody474_10 sourceBody474_14

def sourceBody474_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody474_9 sourceBody474_15

def sourceBody474_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody474_1 sourceBody474_16

def sourceBody474_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody474_2 sourceBody474_17

def sourceBody474_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody474_8 sourceBody474_18

def sourceBody474_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody474_8 sourceBody474_19

def sourceBody474_21 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody474_8, 474, 4)) (some 472) ([12, 4, 10, 8]) (some (12, sourceBody474_11, 474, 5))

def sourceBody474_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody474_21 sourceBody474_5

def sourceBody474_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody474_22 sourceBody474_8

def sourceBody474_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody474_10 sourceBody474_23

def sourceBody474_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody474_9 sourceBody474_24

def sourceBody474_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody474_1 sourceBody474_25

def sourceBody474_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody474_3 sourceBody474_26

def sourceBody474_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody474_8 sourceBody474_27

def sourceBody474_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody474_8 sourceBody474_28

def sourceBody474_30 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody474_20 sourceBody474_29

def sourceBody474_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody474_30 sourceBody474_5

def sourceBody474_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody474_31 sourceBody474_8

def sourceBody474_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody474_7 sourceBody474_32

def sourceBody474_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody474_6 sourceBody474_33

def sourceBody474_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody474_1 sourceBody474_34

def sourceBody474_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody474_0 sourceBody474_35

def sourceBody474_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody474_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody474_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody474_38 sourceBody474_8

def sourceBody474_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody474_37 sourceBody474_39

def sourceBody474_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody474_36 sourceBody474_40

def source474 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (474, 2, sourceBody474_41)
end InitECandidate.Proofs.WordStages
