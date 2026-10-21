import InitECandidate.Proofs.WordStages.Source305
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody321_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody321_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody321_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 6)

def sourceBody321_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody321_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody321_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody321_6 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.reg 10) sourceBody321_4 sourceBody321_5

def sourceBody321_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody321_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_6 sourceBody321_7

def sourceBody321_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody321_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody321_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody321_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12, 4]

def sourceBody321_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_12 sourceBody321_0

def sourceBody321_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_11 sourceBody321_13

def sourceBody321_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_10 sourceBody321_14

def sourceBody321_16 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody321_15 sourceBody321_0

def sourceBody321_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_16 sourceBody321_7

def sourceBody321_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_17 sourceBody321_0

def sourceBody321_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_9 sourceBody321_18

def sourceBody321_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_8 sourceBody321_19

def sourceBody321_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_3 sourceBody321_20

def sourceBody321_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_2 sourceBody321_21

def sourceBody321_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody321_24 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 4 (Flapjack.WordRegImm.reg 10) sourceBody321_4 sourceBody321_5

def sourceBody321_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_24 sourceBody321_7

def sourceBody321_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody321_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody321_28 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody321_0, 321, 2)) (some 282) ([4]) (some (4, sourceBody321_27, 321, 3))

def sourceBody321_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_28 sourceBody321_7

def sourceBody321_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_29 sourceBody321_0

def sourceBody321_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_26 sourceBody321_30

def sourceBody321_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_0 sourceBody321_31

def sourceBody321_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_0 sourceBody321_32

def sourceBody321_34 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody321_33 sourceBody321_0

def sourceBody321_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_34 sourceBody321_7

def sourceBody321_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_35 sourceBody321_0

def sourceBody321_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_9 sourceBody321_36

def sourceBody321_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_25 sourceBody321_37

def sourceBody321_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_3 sourceBody321_38

def sourceBody321_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_23 sourceBody321_39

def sourceBody321_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_22 sourceBody321_40

def sourceBody321_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody321_43 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody321_0, 321, 4)) (some 320) ([4]) (some (4, sourceBody321_27, 321, 5))

def sourceBody321_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_43 sourceBody321_7

def sourceBody321_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_44 sourceBody321_0

def sourceBody321_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_42 sourceBody321_45

def sourceBody321_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_0 sourceBody321_46

def sourceBody321_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_0 sourceBody321_47

def sourceBody321_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_41 sourceBody321_48

def sourceBody321_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody321_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_50 sourceBody321_14

def sourceBody321_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_49 sourceBody321_51

def sourceBody321_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_1 sourceBody321_52

def sourceBody321_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody321_0 sourceBody321_53

def source321 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (321, 2, sourceBody321_54)
end InitECandidate.Proofs.WordStages
