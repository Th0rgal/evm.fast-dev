import InitECandidate.Proofs.WordStages.Source306
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody322_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody322_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody322_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody322_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody322_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody322_5 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.WordRegImm.reg 8) sourceBody322_4 sourceBody322_2

def sourceBody322_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody322_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody322_5 sourceBody322_6

def sourceBody322_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody322_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody322_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 6 (Flapjack.WordLangAddr.addr 6 0#64))

def sourceBody322_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody322_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody322_11 sourceBody322_0

def sourceBody322_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody322_10 sourceBody322_12

def sourceBody322_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody322_9 sourceBody322_13

def sourceBody322_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody322_14 sourceBody322_0

def sourceBody322_16 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody322_15 sourceBody322_0

def sourceBody322_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody322_16 sourceBody322_6

def sourceBody322_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody322_17 sourceBody322_0

def sourceBody322_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody322_8 sourceBody322_18

def sourceBody322_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody322_7 sourceBody322_19

def sourceBody322_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody322_3 sourceBody322_20

def sourceBody322_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody322_2 sourceBody322_21

def sourceBody322_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def sourceBody322_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody322_25 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 179) ([0, 6, 10]) (none)

def sourceBody322_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody322_25 sourceBody322_0

def sourceBody322_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody322_24 sourceBody322_26

def sourceBody322_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody322_23 sourceBody322_27

def sourceBody322_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody322_22 sourceBody322_28

def sourceBody322_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody322_1 sourceBody322_29

def sourceBody322_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody322_0 sourceBody322_30

def source322 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (322, 3, sourceBody322_31)
end InitECandidate.Proofs.WordStages
