import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify243
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body259_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "result"
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "d"))

def body259_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "mode" (Flapjack.Exp.const 0#64)

def body259_2 : Prog (BitVec 64) :=
.seq body259_0 body259_1

def body259_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "d"), Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "top")

def body259_4 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "top" (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "d"))

def body259_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "slot" (Flapjack.Exp.const 1#64)

def body259_6 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "slot" (Flapjack.Exp.const 0#64)

def body259_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 8#64]))
  (Flapjack.Exp.const 1#64)) body259_5 body259_6

def body259_8 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "mode" (Flapjack.Exp.const 2#64)

def body259_9 : Prog (BitVec 64) :=
.seq body259_7 body259_8

def body259_10 : Prog (BitVec 64) :=
.seq body259_4 body259_9

def body259_11 : Prog (BitVec 64) :=
.seq body259_3 body259_10

def body259_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "d"))
  (Flapjack.Exp.const 0#64)) body259_2 body259_11

def body259_13 : Prog (BitVec 64) :=
.decCall ("d") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("_decode_step") ([Flapjack.Exp.var Flapjack.VarKind.local "db", Flapjack.Exp.var Flapjack.VarKind.local "cur_p",
  Flapjack.Exp.var Flapjack.VarKind.local "cur_n"]) body259_12

def body259_14 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 80#64])
  (Flapjack.Exp.const 0#64)

def body259_15 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "result"
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "r"))

def body259_16 : Prog (BitVec 64) :=
.seq body259_15 body259_1

def body259_17 : Prog (BitVec 64) :=
.seq body259_14 body259_16

def body259_18 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 80#64])
  (Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "r"))

def body259_19 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "cur_p"
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "r"))

def body259_20 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "cur_n"
  (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "r"))

def body259_21 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "mode" (Flapjack.Exp.const 1#64)

def body259_22 : Prog (BitVec 64) :=
.seq body259_20 body259_21

def body259_23 : Prog (BitVec 64) :=
.seq body259_19 body259_22

def body259_24 : Prog (BitVec 64) :=
.seq body259_18 body259_23

def body259_25 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "r"))
  (Flapjack.Exp.const 0#64)) body259_17 body259_24

def body259_26 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("_resolve_step") ([Flapjack.Exp.var Flapjack.VarKind.local "db",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "arr",
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.var Flapjack.VarKind.local "slot", Flapjack.Exp.const 16#64]]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "arr",
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.var Flapjack.VarKind.local "slot", Flapjack.Exp.const 16#64],
        Flapjack.Exp.const 8#64])]) body259_25

def body259_27 : Prog (BitVec 64) :=
.dec ("arr") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 24#64])) body259_26

def body259_28 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "go" (Flapjack.Exp.const 0#64)

def body259_29 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "result", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "hash")

def body259_30 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body259_31 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "hash")
        (Flapjack.Exp.const 0#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "result")
        (Flapjack.Exp.const 0#64))]) body259_29 body259_30

def body259_32 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 8#64]

def body259_33 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "result") (Flapjack.Exp.const 0#64)) body259_32 body259_30

def body259_34 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "ck") (Flapjack.Exp.const 3#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "ck") (Flapjack.Exp.const 0#64))]) body259_32 body259_30

def body259_35 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ex", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 48#64]))

def body259_36 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ex", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 56#64]))

def body259_37 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "top"
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 0#64]))

def body259_38 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "result" (Flapjack.Exp.var Flapjack.VarKind.local "ex")

def body259_39 : Prog (BitVec 64) :=
.seq body259_37 body259_38

def body259_40 : Prog (BitVec 64) :=
.seq body259_36 body259_39

def body259_41 : Prog (BitVec 64) :=
.seq body259_35 body259_40

def body259_42 : Prog (BitVec 64) :=
.decCall ("ex") (Flapjack.Shape.one) ("node_new_ext") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 64#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 72#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "result"]) body259_41

def body259_43 : Prog (BitVec 64) :=
.seq body259_34 body259_42

def body259_44 : Prog (BitVec 64) :=
.dec ("ck") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "result", Flapjack.Exp.const 0#64])) body259_43

def body259_45 : Prog (BitVec 64) :=
.seq body259_33 body259_44

def body259_46 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "br", Flapjack.Exp.const 32#64,
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]])
  (Flapjack.Exp.var Flapjack.VarKind.local "result")

def body259_47 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 40#64]),
      Flapjack.Exp.const 1#64])

def body259_48 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "result") (Flapjack.Exp.const 0#64)) body259_47 body259_30

def body259_49 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body259_50 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "i")

def body259_51 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "slot" (Flapjack.Exp.var Flapjack.VarKind.local "i")

def body259_52 : Prog (BitVec 64) :=
.seq body259_51 body259_8

def body259_53 : Prog (BitVec 64) :=
.seq body259_50 body259_52

def body259_54 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "br", Flapjack.Exp.const 160#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "bv"))

def body259_55 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "br", Flapjack.Exp.const 168#64])
  (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "bv"))

def body259_56 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "occ"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "occ", Flapjack.Exp.const 1#64])

def body259_57 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "bv"))
  (Flapjack.Exp.const 0#64)) body259_56 body259_30

def body259_58 : Prog (BitVec 64) :=
.seq body259_55 body259_57

def body259_59 : Prog (BitVec 64) :=
.seq body259_54 body259_58

def body259_60 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "bv"))
  (Flapjack.Exp.const 0#64)) body259_59 body259_30

def body259_61 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 9#64]

def body259_62 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "occ") (Flapjack.Exp.const 2#64)) body259_61 body259_30

def body259_63 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "br", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 48#64]))

def body259_64 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "br", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 56#64]))

def body259_65 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "result" (Flapjack.Exp.var Flapjack.VarKind.local "br")

def body259_66 : Prog (BitVec 64) :=
.seq body259_37 body259_65

def body259_67 : Prog (BitVec 64) :=
.seq body259_64 body259_66

def body259_68 : Prog (BitVec 64) :=
.seq body259_63 body259_67

def body259_69 : Prog (BitVec 64) :=
.seq body259_62 body259_68

def body259_70 : Prog (BitVec 64) :=
.seq body259_60 body259_69

def body259_71 : Prog (BitVec 64) :=
.dec ("occ") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 40#64])) body259_70

def body259_72 : Prog (BitVec 64) :=
.decCall ("bv") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("rlp_item") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "arr2",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 16#64, Flapjack.Exp.const 16#64]]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "arr2",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 16#64, Flapjack.Exp.const 16#64],
        Flapjack.Exp.const 8#64])]) body259_71

def body259_73 : Prog (BitVec 64) :=
.dec ("arr2") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 24#64])) body259_72

def body259_74 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 16#64)) body259_53 body259_73

def body259_75 : Prog (BitVec 64) :=
.seq body259_49 body259_74

def body259_76 : Prog (BitVec 64) :=
.seq body259_48 body259_75

def body259_77 : Prog (BitVec 64) :=
.seq body259_46 body259_76

def body259_78 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 32#64])) body259_77

def body259_79 : Prog (BitVec 64) :=
.dec ("br") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 16#64])) body259_78

def body259_80 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 8#64]))
  (Flapjack.Exp.const 1#64)) body259_45 body259_79

def body259_81 : Prog (BitVec 64) :=
.seq body259_31 body259_80

def body259_82 : Prog (BitVec 64) :=
.dec ("hash") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 80#64])) body259_81

def body259_83 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "top") (Flapjack.Exp.const 0#64)) body259_28 body259_82

def body259_84 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "mode") (Flapjack.Exp.const 2#64)) body259_27 body259_83

def body259_85 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "mode") (Flapjack.Exp.const 1#64)) body259_13 body259_84

def body259_86 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "go") (Flapjack.Exp.const 0#64)) body259_85

def body259_87 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "result")

def body259_88 : Prog (BitVec 64) :=
.seq body259_86 body259_87

def body259_89 : Prog (BitVec 64) :=
.dec ("go") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) body259_88

def body259_90 : Prog (BitVec 64) :=
.dec ("slot") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body259_89

def body259_91 : Prog (BitVec 64) :=
.dec ("mode") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) body259_90

def body259_92 : Prog (BitVec 64) :=
.dec ("cur_n") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "n") body259_91

def body259_93 : Prog (BitVec 64) :=
.dec ("cur_p") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "p") body259_92

def body259_94 : Prog (BitVec 64) :=
.dec ("result") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body259_93

def body259_95 : Prog (BitVec 64) :=
.dec ("top") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body259_94

def body259_96 : Prog (BitVec 64) :=
.seq body259_3 body259_4

def body259_97 : Prog (BitVec 64) :=
.seq body259_96 body259_7

def body259_98 : Prog (BitVec 64) :=
.seq body259_97 body259_8

def body259_99 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "d"))
  (Flapjack.Exp.const 0#64)) body259_2 body259_98

def body259_100 : Prog (BitVec 64) :=
.decCall ("d") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("_decode_step") ([Flapjack.Exp.var Flapjack.VarKind.local "db", Flapjack.Exp.var Flapjack.VarKind.local "cur_p",
  Flapjack.Exp.var Flapjack.VarKind.local "cur_n"]) body259_99

def body259_101 : Prog (BitVec 64) :=
.seq body259_14 body259_15

def body259_102 : Prog (BitVec 64) :=
.seq body259_101 body259_1

def body259_103 : Prog (BitVec 64) :=
.seq body259_18 body259_19

def body259_104 : Prog (BitVec 64) :=
.seq body259_103 body259_20

def body259_105 : Prog (BitVec 64) :=
.seq body259_104 body259_21

def body259_106 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "r"))
  (Flapjack.Exp.const 0#64)) body259_102 body259_105

def body259_107 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("_resolve_step") ([Flapjack.Exp.var Flapjack.VarKind.local "db",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "arr",
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.var Flapjack.VarKind.local "slot", Flapjack.Exp.const 16#64]]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "arr",
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.var Flapjack.VarKind.local "slot", Flapjack.Exp.const 16#64],
        Flapjack.Exp.const 8#64])]) body259_106

def body259_108 : Prog (BitVec 64) :=
.dec ("arr") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 24#64])) body259_107

def body259_109 : Prog (BitVec 64) :=
.seq body259_35 body259_36

def body259_110 : Prog (BitVec 64) :=
.seq body259_109 body259_37

def body259_111 : Prog (BitVec 64) :=
.seq body259_110 body259_38

def body259_112 : Prog (BitVec 64) :=
.decCall ("ex") (Flapjack.Shape.one) ("node_new_ext") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 64#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 72#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "result"]) body259_111

def body259_113 : Prog (BitVec 64) :=
.seq body259_34 body259_112

def body259_114 : Prog (BitVec 64) :=
.dec ("ck") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "result", Flapjack.Exp.const 0#64])) body259_113

def body259_115 : Prog (BitVec 64) :=
.seq body259_33 body259_114

def body259_116 : Prog (BitVec 64) :=
.seq body259_46 body259_48

def body259_117 : Prog (BitVec 64) :=
.seq body259_116 body259_49

def body259_118 : Prog (BitVec 64) :=
.seq body259_50 body259_51

def body259_119 : Prog (BitVec 64) :=
.seq body259_118 body259_8

def body259_120 : Prog (BitVec 64) :=
.seq body259_54 body259_55

def body259_121 : Prog (BitVec 64) :=
.seq body259_120 body259_57

def body259_122 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "bv"))
  (Flapjack.Exp.const 0#64)) body259_121 body259_30

def body259_123 : Prog (BitVec 64) :=
.seq body259_122 body259_62

def body259_124 : Prog (BitVec 64) :=
.seq body259_123 body259_63

def body259_125 : Prog (BitVec 64) :=
.seq body259_124 body259_64

def body259_126 : Prog (BitVec 64) :=
.seq body259_125 body259_37

def body259_127 : Prog (BitVec 64) :=
.seq body259_126 body259_65

def body259_128 : Prog (BitVec 64) :=
.dec ("occ") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 40#64])) body259_127

def body259_129 : Prog (BitVec 64) :=
.decCall ("bv") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("rlp_item") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "arr2",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 16#64, Flapjack.Exp.const 16#64]]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "arr2",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 16#64, Flapjack.Exp.const 16#64],
        Flapjack.Exp.const 8#64])]) body259_128

def body259_130 : Prog (BitVec 64) :=
.dec ("arr2") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 24#64])) body259_129

def body259_131 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 16#64)) body259_119 body259_130

def body259_132 : Prog (BitVec 64) :=
.seq body259_117 body259_131

def body259_133 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 32#64])) body259_132

def body259_134 : Prog (BitVec 64) :=
.dec ("br") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 16#64])) body259_133

def body259_135 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 8#64]))
  (Flapjack.Exp.const 1#64)) body259_115 body259_134

def body259_136 : Prog (BitVec 64) :=
.seq body259_31 body259_135

def body259_137 : Prog (BitVec 64) :=
.dec ("hash") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 80#64])) body259_136

def body259_138 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "top") (Flapjack.Exp.const 0#64)) body259_28 body259_137

def body259_139 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "mode") (Flapjack.Exp.const 2#64)) body259_108 body259_138

def body259_140 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "mode") (Flapjack.Exp.const 1#64)) body259_100 body259_139

def body259_141 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "go") (Flapjack.Exp.const 0#64)) body259_140

def body259_142 : Prog (BitVec 64) :=
.seq body259_141 body259_87

def body259_143 : Prog (BitVec 64) :=
.dec ("go") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) body259_142

def body259_144 : Prog (BitVec 64) :=
.dec ("slot") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body259_143

def body259_145 : Prog (BitVec 64) :=
.dec ("mode") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) body259_144

def body259_146 : Prog (BitVec 64) :=
.dec ("cur_n") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "n") body259_145

def body259_147 : Prog (BitVec 64) :=
.dec ("cur_p") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "p") body259_146

def body259_148 : Prog (BitVec 64) :=
.dec ("result") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body259_147

def body259_149 : Prog (BitVec 64) :=
.dec ("top") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body259_148

def originalData259 : Decl (BitVec 64) :=
.function { name := "_decode_witness_node_body", inline := false, exported := false, params := [("db", Flapjack.Shape.one), ("p", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body259_95, returnShape := (Flapjack.Shape.one) }
def simplifiedData259 : Decl (BitVec 64) :=
.function { name := "_decode_witness_node_body", inline := false, exported := false, params := [("db", Flapjack.Shape.one), ("p", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body259_149, returnShape := (Flapjack.Shape.one) }
def original259 := Pancake.PanLang.declToHOL originalData259
def simplified259 := Pancake.PanLang.declToHOL simplifiedData259
end InitECandidate.Proofs.FrontendStages.Declarations
