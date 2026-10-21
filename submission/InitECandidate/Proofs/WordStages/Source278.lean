import InitECandidate.Proofs.WordStages.Source262
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody278_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody278_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody278_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1024#64)

def sourceBody278_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody278_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody278_0, 278, 2)) (some 95) ([6, 10]) (some (6, sourceBody278_3, 278, 3))

def sourceBody278_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody278_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody278_4 sourceBody278_5

def sourceBody278_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody278_6 sourceBody278_0

def sourceBody278_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody278_2 sourceBody278_7

def sourceBody278_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody278_1 sourceBody278_8

def sourceBody278_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody278_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 12])

def sourceBody278_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody278_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody278_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 10 (Flapjack.WordRegImm.reg 8) sourceBody278_12 sourceBody278_13

def sourceBody278_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody278_14 sourceBody278_5

def sourceBody278_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody278_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody278_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody278_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody278_18 sourceBody278_0

def sourceBody278_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody278_17 sourceBody278_19

def sourceBody278_21 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody278_20 sourceBody278_0

def sourceBody278_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody278_21 sourceBody278_5

def sourceBody278_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody278_22 sourceBody278_0

def sourceBody278_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody278_16 sourceBody278_23

def sourceBody278_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody278_15 sourceBody278_24

def sourceBody278_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody278_11 sourceBody278_25

def sourceBody278_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody278_10 sourceBody278_26

def sourceBody278_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody278_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 12])

def sourceBody278_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody278_29 sourceBody278_25

def sourceBody278_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody278_28 sourceBody278_30

def sourceBody278_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody278_27 sourceBody278_31

def sourceBody278_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 5000#64)

def sourceBody278_34 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.WordRegImm.reg 8) sourceBody278_12 sourceBody278_13

def sourceBody278_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody278_34 sourceBody278_5

def sourceBody278_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody278_35 sourceBody278_24

def sourceBody278_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody278_33 sourceBody278_36

def sourceBody278_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody278_10 sourceBody278_37

def sourceBody278_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody278_32 sourceBody278_38

def sourceBody278_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody278_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody278_40 sourceBody278_19

def sourceBody278_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody278_39 sourceBody278_41

def sourceBody278_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody278_9 sourceBody278_42

def sourceBody278_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody278_0 sourceBody278_43

def sourceBody278_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody278_0 sourceBody278_44

def source278 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (278, 3, sourceBody278_45)
end InitECandidate.Proofs.WordStages
