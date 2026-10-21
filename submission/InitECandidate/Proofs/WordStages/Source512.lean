import InitECandidate.Proofs.WordStages.Source496
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody512_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody512_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody512_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 22, 4, 18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody512_0, 512, 2)) (some 471) ([]) (some (12, sourceBody512_1, 512, 3))

def sourceBody512_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody512_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_2 sourceBody512_3

def sourceBody512_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_4 sourceBody512_0

def sourceBody512_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody512_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([12, 26, 2, 16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody512_0, 512, 4)) (some 471) ([]) (some (10, sourceBody512_6, 512, 5))

def sourceBody512_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_7 sourceBody512_3

def sourceBody512_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_8 sourceBody512_0

def sourceBody512_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody512_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody512_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody512_0, 512, 6)) (some 466) ([24]) (some (24, sourceBody512_11, 512, 7))

def sourceBody512_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_12 sourceBody512_3

def sourceBody512_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_13 sourceBody512_0

def sourceBody512_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_10 sourceBody512_14

def sourceBody512_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_0 sourceBody512_15

def sourceBody512_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_0 sourceBody512_16

def sourceBody512_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.var 12])

def sourceBody512_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.var 26])

def sourceBody512_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 2])

def sourceBody512_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.var 16])

def sourceBody512_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody512_0, 512, 8)) (some 472) ([24, 6, 20, 14]) (some (24, sourceBody512_11, 512, 9))

def sourceBody512_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_22 sourceBody512_3

def sourceBody512_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_23 sourceBody512_0

def sourceBody512_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_21 sourceBody512_24

def sourceBody512_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_20 sourceBody512_25

def sourceBody512_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_19 sourceBody512_26

def sourceBody512_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_18 sourceBody512_27

def sourceBody512_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_0 sourceBody512_28

def sourceBody512_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_0 sourceBody512_29

def sourceBody512_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_17 sourceBody512_30

def sourceBody512_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody512_33 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody512_0, 512, 10)) (some 486) ([24]) (some (24, sourceBody512_11, 512, 11))

def sourceBody512_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_33 sourceBody512_3

def sourceBody512_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_34 sourceBody512_0

def sourceBody512_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_32 sourceBody512_35

def sourceBody512_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_0 sourceBody512_36

def sourceBody512_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_0 sourceBody512_37

def sourceBody512_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_31 sourceBody512_38

def sourceBody512_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody512_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody512_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_41 sourceBody512_0

def sourceBody512_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_40 sourceBody512_42

def sourceBody512_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_39 sourceBody512_43

def sourceBody512_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_9 sourceBody512_44

def sourceBody512_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_0 sourceBody512_45

def sourceBody512_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_0 sourceBody512_46

def sourceBody512_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_0 sourceBody512_47

def sourceBody512_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_0 sourceBody512_48

def sourceBody512_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_0 sourceBody512_49

def sourceBody512_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_0 sourceBody512_50

def sourceBody512_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_0 sourceBody512_51

def sourceBody512_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_0 sourceBody512_52

def sourceBody512_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_5 sourceBody512_53

def sourceBody512_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_0 sourceBody512_54

def sourceBody512_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_0 sourceBody512_55

def sourceBody512_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_0 sourceBody512_56

def sourceBody512_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_0 sourceBody512_57

def sourceBody512_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_0 sourceBody512_58

def sourceBody512_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_0 sourceBody512_59

def sourceBody512_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_0 sourceBody512_60

def sourceBody512_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody512_0 sourceBody512_61

def source512 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (512, 1, sourceBody512_62)
end InitECandidate.Proofs.WordStages
