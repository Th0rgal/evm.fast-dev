import InitECandidate.Proofs.WordStages.Source852
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody868_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody868_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody868_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody868_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody868_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.lookup (Flapjack.WordStore.temp 0#5))

def sourceBody868_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody868_4 sourceBody868_0

def sourceBody868_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody868_5 sourceBody868_0

def sourceBody868_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 6)

def sourceBody868_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.shareInst Flapjack.WordMemOp.store8 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.const 2688614400#64, Flapjack.WordLangExpHOL.const 70#64])

def sourceBody868_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody868_8 sourceBody868_0

def sourceBody868_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody868_7 sourceBody868_9

def sourceBody868_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody868_0 sourceBody868_10

def sourceBody868_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody868_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 4)

def sourceBody868_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody868_13 sourceBody868_0

def sourceBody868_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody868_14 sourceBody868_0

def sourceBody868_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody868_12 sourceBody868_15

def sourceBody868_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody868_0 sourceBody868_16

def sourceBody868_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 9#64)

def sourceBody868_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody868_18 sourceBody868_2

def sourceBody868_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody868_17 sourceBody868_19

def sourceBody868_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody868_11 sourceBody868_20

def sourceBody868_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody868_6 sourceBody868_21

def sourceBody868_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody868_3 sourceBody868_22

def sourceBody868_24 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.imm 1#64) sourceBody868_2 sourceBody868_23

def sourceBody868_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody868_24 sourceBody868_3

def sourceBody868_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody868_0, 868, 2)) (some 867) ([4]) (some (4, sourceBody868_25, 868, 3))

def sourceBody868_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody868_26 sourceBody868_3

def sourceBody868_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody868_27 sourceBody868_0

def sourceBody868_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody868_1 sourceBody868_28

def sourceBody868_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody868_0 sourceBody868_29

def sourceBody868_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody868_0 sourceBody868_30

def sourceBody868_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody868_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody868_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody868_33 sourceBody868_0

def sourceBody868_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody868_32 sourceBody868_34

def sourceBody868_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody868_31 sourceBody868_35

def sourceBody868_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody868_0 sourceBody868_36

def sourceBody868_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody868_0 sourceBody868_37

def source868 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (868, 2, sourceBody868_38)
end InitECandidate.Proofs.WordStages
