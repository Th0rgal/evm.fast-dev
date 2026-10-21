import InitECandidate.Proofs.WordStages.Source703
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody719_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody719_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 2)

def sourceBody719_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 4)

def sourceBody719_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 6)

def sourceBody719_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody719_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 10)

def sourceBody719_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 12)

def sourceBody719_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody719_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([34, 16, 28, 22, 32, 18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody719_0, 719, 2)) (some 713) ([30, 24, 36, 14, 26, 20]) (some (30, sourceBody719_7, 719, 3))

def sourceBody719_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody719_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody719_8 sourceBody719_9

def sourceBody719_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody719_10 sourceBody719_0

def sourceBody719_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody719_6 sourceBody719_11

def sourceBody719_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody719_5 sourceBody719_12

def sourceBody719_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody719_4 sourceBody719_13

def sourceBody719_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody719_3 sourceBody719_14

def sourceBody719_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody719_2 sourceBody719_15

def sourceBody719_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody719_1 sourceBody719_16

def sourceBody719_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody719_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [30]

def sourceBody719_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody719_19 sourceBody719_0

def sourceBody719_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody719_18 sourceBody719_20

def sourceBody719_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody719_17 sourceBody719_21

def sourceBody719_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody719_0 sourceBody719_22

def sourceBody719_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody719_0 sourceBody719_23

def sourceBody719_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody719_0 sourceBody719_24

def sourceBody719_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody719_0 sourceBody719_25

def sourceBody719_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody719_0 sourceBody719_26

def sourceBody719_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody719_0 sourceBody719_27

def sourceBody719_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody719_0 sourceBody719_28

def sourceBody719_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody719_0 sourceBody719_29

def sourceBody719_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody719_0 sourceBody719_30

def sourceBody719_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody719_0 sourceBody719_31

def sourceBody719_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody719_0 sourceBody719_32

def sourceBody719_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody719_0 sourceBody719_33

def source719 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (719, 7, sourceBody719_34)
end InitECandidate.Proofs.WordStages
