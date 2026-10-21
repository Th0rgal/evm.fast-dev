import InitECandidate.Proofs.WordStages.Source821
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody837_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody837_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody837_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody837_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 16#64)

def sourceBody837_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody837_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody837_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody837_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 8)

def sourceBody837_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody837_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody837_10 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 20 (Flapjack.WordRegImm.reg 4) sourceBody837_8 sourceBody837_9

def sourceBody837_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_10 sourceBody837_5

def sourceBody837_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 20)

def sourceBody837_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 18,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody837_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody837_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 33#64)

def sourceBody837_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 14 14 20 4))

def sourceBody837_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_16 sourceBody837_0

def sourceBody837_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_15 sourceBody837_17

def sourceBody837_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_14 sourceBody837_18

def sourceBody837_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 64#64, Flapjack.WordLangExpHOL.var 14,
      Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 32#64])])

def sourceBody837_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 10)

def sourceBody837_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_21 sourceBody837_0

def sourceBody837_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_22 sourceBody837_0

def sourceBody837_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_20 sourceBody837_23

def sourceBody837_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_19 sourceBody837_24

def sourceBody837_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody837_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 20)

def sourceBody837_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_27 sourceBody837_0

def sourceBody837_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_28 sourceBody837_0

def sourceBody837_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_26 sourceBody837_29

def sourceBody837_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_0 sourceBody837_30

def sourceBody837_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_25 sourceBody837_31

def sourceBody837_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_13 sourceBody837_32

def sourceBody837_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_0 sourceBody837_33

def sourceBody837_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody837_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_34 sourceBody837_35

def sourceBody837_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody837_38 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody837_36 sourceBody837_37

def sourceBody837_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_38 sourceBody837_5

def sourceBody837_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_39 sourceBody837_0

def sourceBody837_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_12 sourceBody837_40

def sourceBody837_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_11 sourceBody837_41

def sourceBody837_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_7 sourceBody837_42

def sourceBody837_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_6 sourceBody837_43

def sourceBody837_45 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody837_44 (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)

def sourceBody837_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_45 sourceBody837_5

def sourceBody837_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_5 sourceBody837_46

def sourceBody837_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody837_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody837_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_49 sourceBody837_0

def sourceBody837_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_48 sourceBody837_50

def sourceBody837_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_47 sourceBody837_51

def sourceBody837_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_4 sourceBody837_52

def sourceBody837_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_0 sourceBody837_53

def sourceBody837_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_3 sourceBody837_54

def sourceBody837_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_0 sourceBody837_55

def sourceBody837_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_2 sourceBody837_56

def sourceBody837_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_0 sourceBody837_57

def sourceBody837_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_1 sourceBody837_58

def sourceBody837_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody837_0 sourceBody837_59

def source837 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (837, 2, sourceBody837_60)
end InitECandidate.Proofs.WordStages
