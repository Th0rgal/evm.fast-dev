import InitECandidate.Proofs.WordStages.Source627
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody643_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 2)

def sourceBody643_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody643_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 6)

def sourceBody643_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody643_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 18446744073709551615#64)

def sourceBody643_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 4294967295#64)

def sourceBody643_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody643_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 18446744069414584321#64)

def sourceBody643_8 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 210) ([0, 20, 16, 24, 10, 18, 14, 22, 12]) (none)

def sourceBody643_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody643_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody643_8 sourceBody643_9

def sourceBody643_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody643_7 sourceBody643_10

def sourceBody643_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody643_6 sourceBody643_11

def sourceBody643_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody643_5 sourceBody643_12

def sourceBody643_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody643_4 sourceBody643_13

def sourceBody643_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody643_3 sourceBody643_14

def sourceBody643_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody643_2 sourceBody643_15

def sourceBody643_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody643_1 sourceBody643_16

def sourceBody643_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody643_0 sourceBody643_17

def source643 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (643, 5, sourceBody643_18)
end InitECandidate.Proofs.WordStages
