import InitECandidate.Proofs.WordStages.Source607
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody623_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody623_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 16#64)

def sourceBody623_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody623_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody623_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 12 (Flapjack.WordRegImm.reg 16) sourceBody623_2 sourceBody623_3

def sourceBody623_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody623_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_4 sourceBody623_5

def sourceBody623_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody623_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor
    [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 8])

def sourceBody623_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody623_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody623_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_9 sourceBody623_10

def sourceBody623_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_8 sourceBody623_11

def sourceBody623_13 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody623_12 sourceBody623_10

def sourceBody623_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_13 sourceBody623_5

def sourceBody623_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_14 sourceBody623_10

def sourceBody623_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_7 sourceBody623_15

def sourceBody623_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_6 sourceBody623_16

def sourceBody623_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_1 sourceBody623_17

def sourceBody623_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_0 sourceBody623_18

def sourceBody623_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody623_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 6],
      Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
        [Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor
            [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 4294967295#64],
          Flapjack.WordLangExpHOL.var 8]])

def sourceBody623_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_21 sourceBody623_11

def sourceBody623_23 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody623_22 sourceBody623_10

def sourceBody623_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_23 sourceBody623_5

def sourceBody623_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_24 sourceBody623_10

def sourceBody623_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_7 sourceBody623_25

def sourceBody623_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_6 sourceBody623_26

def sourceBody623_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_20 sourceBody623_27

def sourceBody623_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_0 sourceBody623_28

def sourceBody623_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_19 sourceBody623_29

def sourceBody623_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 48#64)

def sourceBody623_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
        [Flapjack.WordLangExpHOL.var 4,
          Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor
            [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 4294967295#64]],
      Flapjack.WordLangExpHOL.var 8])

def sourceBody623_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_32 sourceBody623_11

def sourceBody623_34 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody623_33 sourceBody623_10

def sourceBody623_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_34 sourceBody623_5

def sourceBody623_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_35 sourceBody623_10

def sourceBody623_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_7 sourceBody623_36

def sourceBody623_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_6 sourceBody623_37

def sourceBody623_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_31 sourceBody623_38

def sourceBody623_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_0 sourceBody623_39

def sourceBody623_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_30 sourceBody623_40

def sourceBody623_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody623_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 8],
      Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
        [Flapjack.WordLangExpHOL.var 6,
          Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor
            [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 4294967295#64]]])

def sourceBody623_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_43 sourceBody623_11

def sourceBody623_45 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody623_44 sourceBody623_10

def sourceBody623_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_45 sourceBody623_5

def sourceBody623_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_46 sourceBody623_10

def sourceBody623_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_7 sourceBody623_47

def sourceBody623_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_6 sourceBody623_48

def sourceBody623_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_42 sourceBody623_49

def sourceBody623_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_0 sourceBody623_50

def sourceBody623_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_41 sourceBody623_51

def sourceBody623_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor
    [Flapjack.WordLangExpHOL.var 4,
      Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
        [Flapjack.WordLangExpHOL.var 6,
          Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor
            [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 4294967295#64]]])

def sourceBody623_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_53 sourceBody623_11

def sourceBody623_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody623_52 sourceBody623_54

def source623 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (623, 5, sourceBody623_55)
end InitECandidate.Proofs.WordStages
