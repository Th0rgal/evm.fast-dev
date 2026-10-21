import InitECandidate.Proofs.WordStages.Source423
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody439_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody439_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody439_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody439_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody439_0, 439, 2)) (some 435) ([14]) (some (14, sourceBody439_2, 439, 3))

def sourceBody439_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody439_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_3 sourceBody439_4

def sourceBody439_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_5 sourceBody439_0

def sourceBody439_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_1 sourceBody439_6

def sourceBody439_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody439_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 40#64)

def sourceBody439_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 4)

def sourceBody439_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody439_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody439_0, 439, 4)) (some 436) ([22, 18, 26]) (some (22, sourceBody439_11, 439, 5))

def sourceBody439_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_12 sourceBody439_4

def sourceBody439_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_13 sourceBody439_0

def sourceBody439_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_10 sourceBody439_14

def sourceBody439_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_9 sourceBody439_15

def sourceBody439_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_8 sourceBody439_16

def sourceBody439_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody439_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody439_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 8)

def sourceBody439_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 10)

def sourceBody439_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 12)

def sourceBody439_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 18)

def sourceBody439_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 22) 20

def sourceBody439_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_24 sourceBody439_0

def sourceBody439_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_23 sourceBody439_25

def sourceBody439_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 26)

def sourceBody439_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 8#64])
  20

def sourceBody439_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_28 sourceBody439_0

def sourceBody439_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_27 sourceBody439_29

def sourceBody439_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody439_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 16#64])
  20

def sourceBody439_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_32 sourceBody439_0

def sourceBody439_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_31 sourceBody439_33

def sourceBody439_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 24)

def sourceBody439_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 24#64])
  20

def sourceBody439_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_36 sourceBody439_0

def sourceBody439_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_35 sourceBody439_37

def sourceBody439_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_38 sourceBody439_0

def sourceBody439_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_34 sourceBody439_39

def sourceBody439_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_30 sourceBody439_40

def sourceBody439_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_26 sourceBody439_41

def sourceBody439_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_22 sourceBody439_42

def sourceBody439_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_0 sourceBody439_43

def sourceBody439_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_21 sourceBody439_44

def sourceBody439_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_0 sourceBody439_45

def sourceBody439_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_20 sourceBody439_46

def sourceBody439_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_0 sourceBody439_47

def sourceBody439_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_19 sourceBody439_48

def sourceBody439_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_0 sourceBody439_49

def sourceBody439_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_18 sourceBody439_50

def sourceBody439_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_0 sourceBody439_51

def sourceBody439_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody439_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [22]

def sourceBody439_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_54 sourceBody439_0

def sourceBody439_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_53 sourceBody439_55

def sourceBody439_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_52 sourceBody439_56

def sourceBody439_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_17 sourceBody439_57

def sourceBody439_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_0 sourceBody439_58

def sourceBody439_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_0 sourceBody439_59

def sourceBody439_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_7 sourceBody439_60

def sourceBody439_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_0 sourceBody439_61

def sourceBody439_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody439_0 sourceBody439_62

def source439 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (439, 7, sourceBody439_63)
end InitECandidate.Proofs.WordStages
