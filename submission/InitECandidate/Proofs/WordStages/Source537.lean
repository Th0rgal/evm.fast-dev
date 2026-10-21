import InitECandidate.Proofs.WordStages.Source521
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody537_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 90#64)

def sourceBody537_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody537_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody537_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody537_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 14 (Flapjack.WordRegImm.reg 4) sourceBody537_2 sourceBody537_3

def sourceBody537_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody537_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody537_4 sourceBody537_5

def sourceBody537_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody537_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody537_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody537_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody537_11 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 10 (Flapjack.WordRegImm.reg 18) sourceBody537_9 sourceBody537_10

def sourceBody537_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody537_11 sourceBody537_5

def sourceBody537_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody537_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.var 10])

def sourceBody537_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody537_16 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.reg 8) sourceBody537_15 sourceBody537_13

def sourceBody537_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody537_16 sourceBody537_5

def sourceBody537_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 12)

def sourceBody537_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 145#64],
      Flapjack.WordLangExpHOL.const 255#64])

def sourceBody537_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody537_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody537_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody537_20 sourceBody537_21

def sourceBody537_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody537_19 sourceBody537_22

def sourceBody537_24 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody537_23 sourceBody537_21

def sourceBody537_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody537_24 sourceBody537_5

def sourceBody537_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody537_25 sourceBody537_21

def sourceBody537_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody537_18 sourceBody537_26

def sourceBody537_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody537_17 sourceBody537_27

def sourceBody537_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody537_14 sourceBody537_28

def sourceBody537_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody537_13 sourceBody537_29

def sourceBody537_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody537_12 sourceBody537_30

def sourceBody537_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody537_8 sourceBody537_31

def sourceBody537_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody537_7 sourceBody537_32

def sourceBody537_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody537_6 sourceBody537_33

def sourceBody537_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody537_1 sourceBody537_34

def sourceBody537_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody537_0 sourceBody537_35

def sourceBody537_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 10#64)

def sourceBody537_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 6)

def sourceBody537_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody537_38 sourceBody537_21

def sourceBody537_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody537_39 sourceBody537_21

def sourceBody537_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody537_37 sourceBody537_40

def sourceBody537_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody537_21 sourceBody537_41

def sourceBody537_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody537_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody537_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody537_43 sourceBody537_44

def sourceBody537_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody537_42 sourceBody537_45

def sourceBody537_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody537_36 sourceBody537_46

def sourceBody537_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody537_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody537_48 sourceBody537_22

def sourceBody537_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody537_47 sourceBody537_49

def source537 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (537, 2, sourceBody537_50)
end InitECandidate.Proofs.WordStages
