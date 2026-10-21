import InitECandidate.Proofs.WordStages.Source616
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody632_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody632_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody632_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody632_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 18)

def sourceBody632_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody632_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody632_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody632_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 22 (Flapjack.WordRegImm.reg 10) sourceBody632_5 sourceBody632_6

def sourceBody632_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_7 sourceBody632_2

def sourceBody632_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 22)

def sourceBody632_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 1#64],
      Flapjack.WordLangExpHOL.var 18])

def sourceBody632_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 14)
    (Flapjack.WordLangExpHOL.const 2#64))

def sourceBody632_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody632_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody632_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody632_15 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 16 (Flapjack.WordRegImm.reg 12) sourceBody632_13 sourceBody632_14

def sourceBody632_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_15 sourceBody632_2

def sourceBody632_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody632_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr
        (Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
            [Flapjack.WordLangExpHOL.var 2,
              Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 14)
                  (Flapjack.WordLangExpHOL.const 2#64))
                (Flapjack.WordLangExpHOL.const 3#64)]))
        (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
            [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 3#64])
          (Flapjack.WordLangExpHOL.const 3#64)),
      Flapjack.WordLangExpHOL.const 255#64])

def sourceBody632_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_18 sourceBody632_0

def sourceBody632_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_19 sourceBody632_0

def sourceBody632_21 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody632_20 sourceBody632_0

def sourceBody632_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_21 sourceBody632_2

def sourceBody632_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_22 sourceBody632_0

def sourceBody632_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_17 sourceBody632_23

def sourceBody632_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_16 sourceBody632_24

def sourceBody632_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_12 sourceBody632_25

def sourceBody632_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_11 sourceBody632_26

def sourceBody632_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 18])

def sourceBody632_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 16 (Flapjack.WordLangAddr.addr 10 0#64))

def sourceBody632_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_29 sourceBody632_0

def sourceBody632_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_9 sourceBody632_30

def sourceBody632_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_28 sourceBody632_31

def sourceBody632_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_27 sourceBody632_32

def sourceBody632_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody632_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 10)

def sourceBody632_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_35 sourceBody632_0

def sourceBody632_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_36 sourceBody632_0

def sourceBody632_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_34 sourceBody632_37

def sourceBody632_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_0 sourceBody632_38

def sourceBody632_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_33 sourceBody632_39

def sourceBody632_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_6 sourceBody632_40

def sourceBody632_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_0 sourceBody632_41

def sourceBody632_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_10 sourceBody632_42

def sourceBody632_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_0 sourceBody632_43

def sourceBody632_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody632_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_44 sourceBody632_45

def sourceBody632_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody632_48 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody632_46 sourceBody632_47

def sourceBody632_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_48 sourceBody632_2

def sourceBody632_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_49 sourceBody632_0

def sourceBody632_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_9 sourceBody632_50

def sourceBody632_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_8 sourceBody632_51

def sourceBody632_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_4 sourceBody632_52

def sourceBody632_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_3 sourceBody632_53

def sourceBody632_55 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit Flapjack.Spt.ln) sourceBody632_54 (Flapjack.Spt.ls PUnit.unit)

def sourceBody632_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_55 sourceBody632_2

def sourceBody632_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_2 sourceBody632_56

def sourceBody632_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody632_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody632_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_59 sourceBody632_0

def sourceBody632_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_58 sourceBody632_60

def sourceBody632_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_57 sourceBody632_61

def sourceBody632_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_1 sourceBody632_62

def sourceBody632_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody632_0 sourceBody632_63

def source632 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (632, 5, sourceBody632_64)
end InitECandidate.Proofs.WordStages
