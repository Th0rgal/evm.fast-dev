import InitECandidate.Proofs.WordStages.Source712
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody728_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody728_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 2))

def sourceBody728_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody728_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody728_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody728_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody728_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody728_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody728_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody728_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody728_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody728_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody728_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody728_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.var 8,
      Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.var 32,
      Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.var 14,
      Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.var 26])

def sourceBody728_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody728_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody728_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody728_17 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 34 (Flapjack.WordRegImm.reg 4) sourceBody728_15 sourceBody728_16

def sourceBody728_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody728_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_17 sourceBody728_18

def sourceBody728_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 34)

def sourceBody728_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody728_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody728_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_22 sourceBody728_0

def sourceBody728_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_21 sourceBody728_23

def sourceBody728_25 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody728_24 sourceBody728_0

def sourceBody728_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_25 sourceBody728_18

def sourceBody728_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_26 sourceBody728_0

def sourceBody728_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_20 sourceBody728_27

def sourceBody728_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_19 sourceBody728_28

def sourceBody728_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_14 sourceBody728_29

def sourceBody728_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_13 sourceBody728_30

def sourceBody728_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody728_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_32 sourceBody728_23

def sourceBody728_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_31 sourceBody728_33

def sourceBody728_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_12 sourceBody728_34

def sourceBody728_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_0 sourceBody728_35

def sourceBody728_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_11 sourceBody728_36

def sourceBody728_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_0 sourceBody728_37

def sourceBody728_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_10 sourceBody728_38

def sourceBody728_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_0 sourceBody728_39

def sourceBody728_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_9 sourceBody728_40

def sourceBody728_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_0 sourceBody728_41

def sourceBody728_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_8 sourceBody728_42

def sourceBody728_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_0 sourceBody728_43

def sourceBody728_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_7 sourceBody728_44

def sourceBody728_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_0 sourceBody728_45

def sourceBody728_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_6 sourceBody728_46

def sourceBody728_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_0 sourceBody728_47

def sourceBody728_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_5 sourceBody728_48

def sourceBody728_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_0 sourceBody728_49

def sourceBody728_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_4 sourceBody728_50

def sourceBody728_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_0 sourceBody728_51

def sourceBody728_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_3 sourceBody728_52

def sourceBody728_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_0 sourceBody728_53

def sourceBody728_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_2 sourceBody728_54

def sourceBody728_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_0 sourceBody728_55

def sourceBody728_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_1 sourceBody728_56

def sourceBody728_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody728_0 sourceBody728_57

def source728 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (728, 2, sourceBody728_58)
end InitECandidate.Proofs.WordStages
