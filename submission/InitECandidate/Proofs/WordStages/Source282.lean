import InitECandidate.Proofs.WordStages.Source266
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody282_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody282_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody282_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 4)

def sourceBody282_3 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody282_2 sourceBody282_0

def sourceBody282_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody282_3 sourceBody282_0

def sourceBody282_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody282_1 sourceBody282_4

def sourceBody282_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody282_0 sourceBody282_5

def sourceBody282_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 5#64)

def sourceBody282_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody282_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody282_7 sourceBody282_8

def sourceBody282_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody282_6 sourceBody282_9

def sourceBody282_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody282_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody282_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody282_12 sourceBody282_0

def sourceBody282_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody282_11 sourceBody282_13

def sourceBody282_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody282_10 sourceBody282_14

def source282 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (282, 2, sourceBody282_15)
end InitECandidate.Proofs.WordStages
