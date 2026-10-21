import InitECandidate.Proofs.WordStages.Source476
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody492_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody492_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 3000#64)

def sourceBody492_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody492_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody492_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.WordRegImm.reg 10) sourceBody492_2 sourceBody492_3

def sourceBody492_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody492_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody492_4 sourceBody492_5

def sourceBody492_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 6)

def sourceBody492_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody492_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody492_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody492_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody492_8, 492, 2)) (some 490) ([6]) (some (6, sourceBody492_10, 492, 3))

def sourceBody492_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody492_11 sourceBody492_5

def sourceBody492_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody492_12 sourceBody492_8

def sourceBody492_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody492_9 sourceBody492_13

def sourceBody492_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody492_8 sourceBody492_14

def sourceBody492_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody492_8 sourceBody492_15

def sourceBody492_17 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody492_16 sourceBody492_8

def sourceBody492_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody492_17 sourceBody492_5

def sourceBody492_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody492_18 sourceBody492_8

def sourceBody492_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody492_7 sourceBody492_19

def sourceBody492_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody492_6 sourceBody492_20

def sourceBody492_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody492_1 sourceBody492_21

def sourceBody492_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody492_0 sourceBody492_22

def sourceBody492_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody492_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody492_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody492_25 sourceBody492_8

def sourceBody492_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody492_24 sourceBody492_26

def sourceBody492_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody492_23 sourceBody492_27

def source492 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (492, 3, sourceBody492_28)
end InitECandidate.Proofs.WordStages
