import InitECandidate.Proofs.WordStages.Source464
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody480_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody480_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody480_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody480_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 4)

def sourceBody480_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody480_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody480_6 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 12 (Flapjack.WordRegImm.reg 18) sourceBody480_4 sourceBody480_5

def sourceBody480_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody480_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_6 sourceBody480_7

def sourceBody480_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 12)

def sourceBody480_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 6])

def sourceBody480_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_10 sourceBody480_0

def sourceBody480_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_11 sourceBody480_0

def sourceBody480_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody480_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody480_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody480_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_15 sourceBody480_0

def sourceBody480_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_16 sourceBody480_0

def sourceBody480_18 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody480_17 sourceBody480_0

def sourceBody480_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_18 sourceBody480_7

def sourceBody480_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_19 sourceBody480_0

def sourceBody480_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_9 sourceBody480_20

def sourceBody480_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_8 sourceBody480_21

def sourceBody480_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_14 sourceBody480_22

def sourceBody480_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_13 sourceBody480_23

def sourceBody480_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_12 sourceBody480_24

def sourceBody480_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 10)

def sourceBody480_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 6])

def sourceBody480_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody480_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody480_30 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody480_0, 480, 2)) (some 77) ([12, 18, 14]) (some (12, sourceBody480_29, 480, 3))

def sourceBody480_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_30 sourceBody480_7

def sourceBody480_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_31 sourceBody480_0

def sourceBody480_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_28 sourceBody480_32

def sourceBody480_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_27 sourceBody480_33

def sourceBody480_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_26 sourceBody480_34

def sourceBody480_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_0 sourceBody480_35

def sourceBody480_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_0 sourceBody480_36

def sourceBody480_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_25 sourceBody480_37

def sourceBody480_39 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody480_38 sourceBody480_0

def sourceBody480_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_39 sourceBody480_7

def sourceBody480_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_40 sourceBody480_0

def sourceBody480_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_9 sourceBody480_41

def sourceBody480_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_8 sourceBody480_42

def sourceBody480_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_3 sourceBody480_43

def sourceBody480_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_2 sourceBody480_44

def sourceBody480_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.var 16])

def sourceBody480_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.var 16])

def sourceBody480_48 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody480_0, 480, 4)) (some 78) ([12, 18]) (some (12, sourceBody480_29, 480, 5))

def sourceBody480_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_48 sourceBody480_7

def sourceBody480_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_49 sourceBody480_0

def sourceBody480_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_47 sourceBody480_50

def sourceBody480_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_46 sourceBody480_51

def sourceBody480_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_0 sourceBody480_52

def sourceBody480_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_0 sourceBody480_53

def sourceBody480_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_45 sourceBody480_54

def sourceBody480_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody480_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody480_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_57 sourceBody480_0

def sourceBody480_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_56 sourceBody480_58

def sourceBody480_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_55 sourceBody480_59

def sourceBody480_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_1 sourceBody480_60

def sourceBody480_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody480_0 sourceBody480_61

def source480 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (480, 6, sourceBody480_62)
end InitECandidate.Proofs.WordStages
