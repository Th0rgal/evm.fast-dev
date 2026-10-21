import InitECandidate.Proofs.WordStages.Source696
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody712_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 2)

def sourceBody712_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody712_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 6)

def sourceBody712_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 8)

def sourceBody712_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 10)

def sourceBody712_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 12)

def sourceBody712_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 17644856173732828998#64)

def sourceBody712_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 754043588434789617#64)

def sourceBody712_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 10224657059481499349#64)

def sourceBody712_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 7488229067341005760#64)

def sourceBody712_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 11130996698012816685#64)

def sourceBody712_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1267921511277847466#64)

def sourceBody712_12 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 710) ([0, 34, 16, 28, 22, 32, 18, 30, 24, 36, 14, 26, 20]) (none)

def sourceBody712_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody712_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody712_12 sourceBody712_13

def sourceBody712_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody712_11 sourceBody712_14

def sourceBody712_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody712_10 sourceBody712_15

def sourceBody712_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody712_9 sourceBody712_16

def sourceBody712_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody712_8 sourceBody712_17

def sourceBody712_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody712_7 sourceBody712_18

def sourceBody712_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody712_6 sourceBody712_19

def sourceBody712_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody712_5 sourceBody712_20

def sourceBody712_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody712_4 sourceBody712_21

def sourceBody712_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody712_3 sourceBody712_22

def sourceBody712_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody712_2 sourceBody712_23

def sourceBody712_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody712_1 sourceBody712_24

def sourceBody712_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody712_0 sourceBody712_25

def source712 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (712, 7, sourceBody712_26)
end InitECandidate.Proofs.WordStages
