import InitECandidate.Proofs.WordStages.Source316
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody332_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody332_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody332_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 4)

def sourceBody332_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 6)

def sourceBody332_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody332_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody332_0, 332, 2)) (some 331) ([12, 18, 8]) (some (12, sourceBody332_4, 332, 3))

def sourceBody332_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody332_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_5 sourceBody332_6

def sourceBody332_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_7 sourceBody332_0

def sourceBody332_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_3 sourceBody332_8

def sourceBody332_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_2 sourceBody332_9

def sourceBody332_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_1 sourceBody332_10

def sourceBody332_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody332_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 16)

def sourceBody332_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody332_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody332_16 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 18 (Flapjack.WordRegImm.reg 8) sourceBody332_14 sourceBody332_15

def sourceBody332_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_16 sourceBody332_6

def sourceBody332_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 18)

def sourceBody332_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 13#64)

def sourceBody332_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 12)

def sourceBody332_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_20 sourceBody332_0

def sourceBody332_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_21 sourceBody332_0

def sourceBody332_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_19 sourceBody332_22

def sourceBody332_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_0 sourceBody332_23

def sourceBody332_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody332_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_25 sourceBody332_4

def sourceBody332_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_24 sourceBody332_26

def sourceBody332_28 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody332_27 sourceBody332_0

def sourceBody332_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_28 sourceBody332_6

def sourceBody332_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_29 sourceBody332_0

def sourceBody332_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_18 sourceBody332_30

def sourceBody332_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_17 sourceBody332_31

def sourceBody332_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_13 sourceBody332_32

def sourceBody332_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_12 sourceBody332_33

def sourceBody332_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 10)

def sourceBody332_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody332_37 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 146) ([0, 12, 18]) (none)

def sourceBody332_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_37 sourceBody332_0

def sourceBody332_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_36 sourceBody332_38

def sourceBody332_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_35 sourceBody332_39

def sourceBody332_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_34 sourceBody332_40

def sourceBody332_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_11 sourceBody332_41

def sourceBody332_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_0 sourceBody332_42

def sourceBody332_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_0 sourceBody332_43

def sourceBody332_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_0 sourceBody332_44

def sourceBody332_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody332_0 sourceBody332_45

def source332 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (332, 4, sourceBody332_46)
end InitECandidate.Proofs.WordStages
