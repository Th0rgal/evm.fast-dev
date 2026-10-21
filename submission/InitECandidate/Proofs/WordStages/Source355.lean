import InitECandidate.Proofs.WordStages.Source339
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody355_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody355_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody355_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody355_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody355_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.WordRegImm.reg 10) sourceBody355_2 sourceBody355_3

def sourceBody355_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody355_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody355_4 sourceBody355_5

def sourceBody355_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 6)

def sourceBody355_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody355_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody355_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 6 (Flapjack.WordLangAddr.addr 12 0#64))

def sourceBody355_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody355_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody355_10 sourceBody355_11

def sourceBody355_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody355_9 sourceBody355_12

def sourceBody355_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody355_8 sourceBody355_13

def sourceBody355_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody355_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody355_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody355_16 sourceBody355_11

def sourceBody355_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody355_15 sourceBody355_17

def sourceBody355_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody355_14 sourceBody355_18

def sourceBody355_20 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody355_19 sourceBody355_11

def sourceBody355_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody355_20 sourceBody355_5

def sourceBody355_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody355_21 sourceBody355_11

def sourceBody355_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody355_7 sourceBody355_22

def sourceBody355_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody355_6 sourceBody355_23

def sourceBody355_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody355_1 sourceBody355_24

def sourceBody355_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody355_0 sourceBody355_25

def sourceBody355_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody355_28 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 176) ([0, 12, 6, 10]) (none)

def sourceBody355_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody355_28 sourceBody355_11

def sourceBody355_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody355_27 sourceBody355_29

def sourceBody355_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody355_0 sourceBody355_30

def sourceBody355_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody355_8 sourceBody355_31

def sourceBody355_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody355_26 sourceBody355_32

def source355 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (355, 3, sourceBody355_33)
end InitECandidate.Proofs.WordStages
