import InitECandidate.Proofs.WordStages.Source363
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody379_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody379_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody379_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody379_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody379_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody379_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 4)

def sourceBody379_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody379_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody379_8 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.WordRegImm.reg 18) sourceBody379_6 sourceBody379_7

def sourceBody379_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_8 sourceBody379_3

def sourceBody379_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 10)

def sourceBody379_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 8])

def sourceBody379_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 14 (Flapjack.WordLangAddr.addr 14 0#64))

def sourceBody379_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody379_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody379_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody379_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody379_17 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 18 (Flapjack.WordRegImm.reg 6) sourceBody379_15 sourceBody379_16

def sourceBody379_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_17 sourceBody379_3

def sourceBody379_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody379_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody379_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 14)

def sourceBody379_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_21 sourceBody379_0

def sourceBody379_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_22 sourceBody379_0

def sourceBody379_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_20 sourceBody379_23

def sourceBody379_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_0 sourceBody379_24

def sourceBody379_26 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody379_25 sourceBody379_0

def sourceBody379_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_26 sourceBody379_3

def sourceBody379_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_27 sourceBody379_0

def sourceBody379_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_19 sourceBody379_28

def sourceBody379_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_18 sourceBody379_29

def sourceBody379_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_14 sourceBody379_30

def sourceBody379_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_13 sourceBody379_31

def sourceBody379_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_12 sourceBody379_32

def sourceBody379_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_11 sourceBody379_33

def sourceBody379_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody379_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody379_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_36 sourceBody379_0

def sourceBody379_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_37 sourceBody379_0

def sourceBody379_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_35 sourceBody379_38

def sourceBody379_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_0 sourceBody379_39

def sourceBody379_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_34 sourceBody379_40

def sourceBody379_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody379_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_41 sourceBody379_42

def sourceBody379_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody379_45 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody379_43 sourceBody379_44

def sourceBody379_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_45 sourceBody379_3

def sourceBody379_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_46 sourceBody379_0

def sourceBody379_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_10 sourceBody379_47

def sourceBody379_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_9 sourceBody379_48

def sourceBody379_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_5 sourceBody379_49

def sourceBody379_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_4 sourceBody379_50

def sourceBody379_52 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody379_51 (Flapjack.Spt.bs
  (Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody379_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_52 sourceBody379_3

def sourceBody379_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_3 sourceBody379_53

def sourceBody379_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 16,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 16])
        (Flapjack.WordLangExpHOL.const 2#64)])

def sourceBody379_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody379_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_56 sourceBody379_0

def sourceBody379_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_55 sourceBody379_57

def sourceBody379_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_54 sourceBody379_58

def sourceBody379_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_2 sourceBody379_59

def sourceBody379_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_0 sourceBody379_60

def sourceBody379_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_1 sourceBody379_61

def sourceBody379_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody379_0 sourceBody379_62

def source379 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (379, 3, sourceBody379_63)
end InitECandidate.Proofs.WordStages
