import InitECandidate.Proofs.WordStages.Source761
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody777_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody777_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody777_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody777_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody777_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.reg 10) sourceBody777_2 sourceBody777_3

def sourceBody777_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody777_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_4 sourceBody777_5

def sourceBody777_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 6)

def sourceBody777_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody777_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody777_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody777_8, 777, 2)) (some 725) ([6, 10]) (some (6, sourceBody777_9, 777, 3))

def sourceBody777_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_10 sourceBody777_5

def sourceBody777_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_11 sourceBody777_8

def sourceBody777_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_1 sourceBody777_12

def sourceBody777_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_0 sourceBody777_13

def sourceBody777_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_8 sourceBody777_14

def sourceBody777_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_8 sourceBody777_15

def sourceBody777_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody777_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody777_19 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody777_8, 777, 4)) (some 725) ([6, 10]) (some (6, sourceBody777_9, 777, 5))

def sourceBody777_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_19 sourceBody777_5

def sourceBody777_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_20 sourceBody777_8

def sourceBody777_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_18 sourceBody777_21

def sourceBody777_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_17 sourceBody777_22

def sourceBody777_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_8 sourceBody777_23

def sourceBody777_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_8 sourceBody777_24

def sourceBody777_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_16 sourceBody777_25

def sourceBody777_27 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody777_26 sourceBody777_8

def sourceBody777_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_27 sourceBody777_5

def sourceBody777_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_28 sourceBody777_8

def sourceBody777_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_7 sourceBody777_29

def sourceBody777_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_6 sourceBody777_30

def sourceBody777_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_1 sourceBody777_31

def sourceBody777_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_0 sourceBody777_32

def sourceBody777_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody777_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody777_36 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody777_8, 777, 6)) (some 732) ([6, 10]) (some (6, sourceBody777_9, 777, 7))

def sourceBody777_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_36 sourceBody777_5

def sourceBody777_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_37 sourceBody777_8

def sourceBody777_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_35 sourceBody777_38

def sourceBody777_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_34 sourceBody777_39

def sourceBody777_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_8 sourceBody777_40

def sourceBody777_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_8 sourceBody777_41

def sourceBody777_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_33 sourceBody777_42

def sourceBody777_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody777_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody777_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_45 sourceBody777_8

def sourceBody777_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_44 sourceBody777_46

def sourceBody777_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody777_43 sourceBody777_47

def source777 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (777, 3, sourceBody777_48)
end InitECandidate.Proofs.WordStages
