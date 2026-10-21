import InitECandidate.Proofs.WordStages.Source657
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody673_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody673_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody673_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 2)
    (Flapjack.WordLangExpHOL.const 5#64))

def sourceBody673_3 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 79) ([0, 8, 12, 10]) (none)

def sourceBody673_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody673_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody673_3 sourceBody673_4

def sourceBody673_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody673_2 sourceBody673_5

def sourceBody673_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody673_1 sourceBody673_6

def sourceBody673_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody673_0 sourceBody673_7

def source673 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (673, 4, sourceBody673_8)
end InitECandidate.Proofs.WordStages
