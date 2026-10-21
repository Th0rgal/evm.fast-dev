import InitECandidate.Proofs.WordStages.Source850
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody866_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody866_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody866_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody866_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody866_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.lookup (Flapjack.WordStore.temp 0#5))

def sourceBody866_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody866_4 sourceBody866_0

def sourceBody866_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody866_5 sourceBody866_0

def sourceBody866_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 6)

def sourceBody866_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.shareInst Flapjack.WordMemOp.store8 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.const 2688614400#64, Flapjack.WordLangExpHOL.const 70#64])

def sourceBody866_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody866_8 sourceBody866_0

def sourceBody866_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody866_7 sourceBody866_9

def sourceBody866_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody866_0 sourceBody866_10

def sourceBody866_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody866_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 4)

def sourceBody866_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody866_13 sourceBody866_0

def sourceBody866_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody866_14 sourceBody866_0

def sourceBody866_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody866_12 sourceBody866_15

def sourceBody866_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody866_0 sourceBody866_16

def sourceBody866_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 9#64)

def sourceBody866_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody866_18 sourceBody866_2

def sourceBody866_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody866_17 sourceBody866_19

def sourceBody866_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody866_11 sourceBody866_20

def sourceBody866_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody866_6 sourceBody866_21

def sourceBody866_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody866_3 sourceBody866_22

def sourceBody866_24 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.imm 4#64) sourceBody866_2 sourceBody866_23

def sourceBody866_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody866_24 sourceBody866_3

def sourceBody866_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody866_0, 866, 2)) (some 865) ([4]) (some (4, sourceBody866_25, 866, 3))

def sourceBody866_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody866_26 sourceBody866_3

def sourceBody866_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody866_27 sourceBody866_0

def sourceBody866_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody866_1 sourceBody866_28

def sourceBody866_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody866_0 sourceBody866_29

def sourceBody866_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody866_0 sourceBody866_30

def sourceBody866_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody866_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody866_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody866_33 sourceBody866_0

def sourceBody866_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody866_32 sourceBody866_34

def sourceBody866_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody866_31 sourceBody866_35

def sourceBody866_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody866_0 sourceBody866_36

def sourceBody866_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody866_0 sourceBody866_37

def source866 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (866, 2, sourceBody866_38)
end InitECandidate.Proofs.WordStages
