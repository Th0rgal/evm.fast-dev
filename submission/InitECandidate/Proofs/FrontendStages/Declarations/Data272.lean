import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify256
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body272_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "go" (Flapjack.Exp.const 0#64)

def body272_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "r"), none)) "node_new_leaf"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "key", Flapjack.Exp.var Flapjack.VarKind.local "level"],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "klen", Flapjack.Exp.var Flapjack.VarKind.local "level"],
    Flapjack.Exp.var Flapjack.VarKind.local "vptr", Flapjack.Exp.var Flapjack.VarKind.local "vlen"]

def body272_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 2#64]

def body272_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body272_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 0#64)) body272_2 body272_3

def body272_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "node_invalidate" [Flapjack.Exp.var Flapjack.VarKind.local "node"]

def body272_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "r"), none)) "_insert_into_leaf"
  [Flapjack.Exp.var Flapjack.VarKind.local "node",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "key", Flapjack.Exp.var Flapjack.VarKind.local "level"],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "klen", Flapjack.Exp.var Flapjack.VarKind.local "level"],
    Flapjack.Exp.var Flapjack.VarKind.local "vptr", Flapjack.Exp.var Flapjack.VarKind.local "vlen"]

def body272_7 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "r" (Flapjack.Exp.var Flapjack.VarKind.local "node")

def body272_8 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "next_node"
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 48#64]))

def body272_9 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "next_slot"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 48#64])

def body272_10 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "next_level"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "level", Flapjack.Exp.var Flapjack.VarKind.local "pl"])

def body272_11 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "go" (Flapjack.Exp.const 1#64)

def body272_12 : Prog (BitVec 64) :=
.seq body272_10 body272_11

def body272_13 : Prog (BitVec 64) :=
.seq body272_9 body272_12

def body272_14 : Prog (BitVec 64) :=
.seq body272_8 body272_13

def body272_15 : Prog (BitVec 64) :=
.seq body272_7 body272_14

def body272_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "r"), none)) "node_new_ext"
  [Flapjack.Exp.var Flapjack.VarKind.local "seg", Flapjack.Exp.var Flapjack.VarKind.local "pl",
    Flapjack.Exp.var Flapjack.VarKind.local "br"]

def body272_17 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "r" (Flapjack.Exp.var Flapjack.VarKind.local "br")

def body272_18 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "pl")) body272_16 body272_17

def body272_19 : Prog (BitVec 64) :=
.decCall ("br") (Flapjack.Shape.one) ("_split_extension") ([Flapjack.Exp.var Flapjack.VarKind.local "node",
  Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "key", Flapjack.Exp.var Flapjack.VarKind.local "level"],
  Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "klen", Flapjack.Exp.var Flapjack.VarKind.local "level"],
  Flapjack.Exp.var Flapjack.VarKind.local "vptr", Flapjack.Exp.var Flapjack.VarKind.local "vlen",
  Flapjack.Exp.var Flapjack.VarKind.local "pl"]) body272_18

def body272_20 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "pl")
  (Flapjack.Exp.var Flapjack.VarKind.local "sl")) body272_15 body272_19

def body272_21 : Prog (BitVec 64) :=
.decCall ("pl") (Flapjack.Shape.one) ("common_prefix_length") ([Flapjack.Exp.var Flapjack.VarKind.local "seg", Flapjack.Exp.var Flapjack.VarKind.local "sl",
  Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "key", Flapjack.Exp.var Flapjack.VarKind.local "level"],
  Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "klen", Flapjack.Exp.var Flapjack.VarKind.local "level"]]) body272_20

def body272_22 : Prog (BitVec 64) :=
.dec ("sl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 40#64])) body272_21

def body272_23 : Prog (BitVec 64) :=
.dec ("seg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 32#64])) body272_22

def body272_24 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 160#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "vptr")

def body272_25 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 168#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "vlen")

def body272_26 : Prog (BitVec 64) :=
.seq body272_25 body272_7

def body272_27 : Prog (BitVec 64) :=
.seq body272_24 body272_26

def body272_28 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "next_node"
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 32#64,
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.var Flapjack.VarKind.local "idx", Flapjack.Exp.const 8#64]]))

def body272_29 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "next_slot"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 32#64,
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "idx", Flapjack.Exp.const 8#64]])

def body272_30 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "next_level"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "level", Flapjack.Exp.const 1#64])

def body272_31 : Prog (BitVec 64) :=
.seq body272_30 body272_11

def body272_32 : Prog (BitVec 64) :=
.seq body272_29 body272_31

def body272_33 : Prog (BitVec 64) :=
.seq body272_28 body272_32

def body272_34 : Prog (BitVec 64) :=
.seq body272_7 body272_33

def body272_35 : Prog (BitVec 64) :=
.dec ("idx") (Flapjack.Shape.one) (Flapjack.Exp.loadByte
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "key", Flapjack.Exp.var Flapjack.VarKind.local "level"])) body272_34

def body272_36 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "level")
  (Flapjack.Exp.var Flapjack.VarKind.local "klen")) body272_27 body272_35

def body272_37 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 2#64)) body272_23 body272_36

def body272_38 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 1#64)) body272_6 body272_37

def body272_39 : Prog (BitVec 64) :=
.seq body272_5 body272_38

def body272_40 : Prog (BitVec 64) :=
.seq body272_4 body272_39

def body272_41 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 0#64])) body272_40

def body272_42 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "node") (Flapjack.Exp.const 0#64)) body272_1 body272_41

def body272_43 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "result" (Flapjack.Exp.var Flapjack.VarKind.local "r")

def body272_44 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "slot") (Flapjack.Exp.var Flapjack.VarKind.local "r")

def body272_45 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "slot") (Flapjack.Exp.const 0#64)) body272_43 body272_44

def body272_46 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "node" (Flapjack.Exp.var Flapjack.VarKind.local "next_node")

def body272_47 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "slot" (Flapjack.Exp.var Flapjack.VarKind.local "next_slot")

def body272_48 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "level" (Flapjack.Exp.var Flapjack.VarKind.local "next_level")

def body272_49 : Prog (BitVec 64) :=
.seq body272_47 body272_48

def body272_50 : Prog (BitVec 64) :=
.seq body272_46 body272_49

def body272_51 : Prog (BitVec 64) :=
.seq body272_45 body272_50

def body272_52 : Prog (BitVec 64) :=
.seq body272_42 body272_51

def body272_53 : Prog (BitVec 64) :=
.seq body272_0 body272_52

def body272_54 : Prog (BitVec 64) :=
.dec ("next_level") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body272_53

def body272_55 : Prog (BitVec 64) :=
.dec ("next_slot") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body272_54

def body272_56 : Prog (BitVec 64) :=
.dec ("next_node") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body272_55

def body272_57 : Prog (BitVec 64) :=
.dec ("r") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body272_56

def body272_58 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "go") (Flapjack.Exp.const 0#64)) body272_57

def body272_59 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "result")

def body272_60 : Prog (BitVec 64) :=
.seq body272_58 body272_59

def body272_61 : Prog (BitVec 64) :=
.dec ("go") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) body272_60

def body272_62 : Prog (BitVec 64) :=
.dec ("slot") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body272_61

def body272_63 : Prog (BitVec 64) :=
.dec ("result") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body272_62

def body272_64 : Prog (BitVec 64) :=
.seq body272_4 body272_5

def body272_65 : Prog (BitVec 64) :=
.seq body272_7 body272_8

def body272_66 : Prog (BitVec 64) :=
.seq body272_65 body272_9

def body272_67 : Prog (BitVec 64) :=
.seq body272_66 body272_10

def body272_68 : Prog (BitVec 64) :=
.seq body272_67 body272_11

def body272_69 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "pl")
  (Flapjack.Exp.var Flapjack.VarKind.local "sl")) body272_68 body272_19

def body272_70 : Prog (BitVec 64) :=
.decCall ("pl") (Flapjack.Shape.one) ("common_prefix_length") ([Flapjack.Exp.var Flapjack.VarKind.local "seg", Flapjack.Exp.var Flapjack.VarKind.local "sl",
  Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "key", Flapjack.Exp.var Flapjack.VarKind.local "level"],
  Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "klen", Flapjack.Exp.var Flapjack.VarKind.local "level"]]) body272_69

def body272_71 : Prog (BitVec 64) :=
.dec ("sl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 40#64])) body272_70

def body272_72 : Prog (BitVec 64) :=
.dec ("seg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 32#64])) body272_71

def body272_73 : Prog (BitVec 64) :=
.seq body272_24 body272_25

def body272_74 : Prog (BitVec 64) :=
.seq body272_73 body272_7

def body272_75 : Prog (BitVec 64) :=
.seq body272_7 body272_28

def body272_76 : Prog (BitVec 64) :=
.seq body272_75 body272_29

def body272_77 : Prog (BitVec 64) :=
.seq body272_76 body272_30

def body272_78 : Prog (BitVec 64) :=
.seq body272_77 body272_11

def body272_79 : Prog (BitVec 64) :=
.dec ("idx") (Flapjack.Shape.one) (Flapjack.Exp.loadByte
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "key", Flapjack.Exp.var Flapjack.VarKind.local "level"])) body272_78

def body272_80 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "level")
  (Flapjack.Exp.var Flapjack.VarKind.local "klen")) body272_74 body272_79

def body272_81 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 2#64)) body272_72 body272_80

def body272_82 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 1#64)) body272_6 body272_81

def body272_83 : Prog (BitVec 64) :=
.seq body272_64 body272_82

def body272_84 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 0#64])) body272_83

def body272_85 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "node") (Flapjack.Exp.const 0#64)) body272_1 body272_84

def body272_86 : Prog (BitVec 64) :=
.seq body272_0 body272_85

def body272_87 : Prog (BitVec 64) :=
.seq body272_86 body272_45

def body272_88 : Prog (BitVec 64) :=
.seq body272_87 body272_46

def body272_89 : Prog (BitVec 64) :=
.seq body272_88 body272_47

def body272_90 : Prog (BitVec 64) :=
.seq body272_89 body272_48

def body272_91 : Prog (BitVec 64) :=
.dec ("next_level") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body272_90

def body272_92 : Prog (BitVec 64) :=
.dec ("next_slot") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body272_91

def body272_93 : Prog (BitVec 64) :=
.dec ("next_node") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body272_92

def body272_94 : Prog (BitVec 64) :=
.dec ("r") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body272_93

def body272_95 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "go") (Flapjack.Exp.const 0#64)) body272_94

def body272_96 : Prog (BitVec 64) :=
.seq body272_95 body272_59

def body272_97 : Prog (BitVec 64) :=
.dec ("go") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) body272_96

def body272_98 : Prog (BitVec 64) :=
.dec ("slot") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body272_97

def body272_99 : Prog (BitVec 64) :=
.dec ("result") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body272_98

def originalData272 : Decl (BitVec 64) :=
.function { name := "_mpt_insert_node", inline := false, exported := false, params := [("node", Flapjack.Shape.one), ("key", Flapjack.Shape.one), ("klen", Flapjack.Shape.one), ("level", Flapjack.Shape.one),
  ("vptr", Flapjack.Shape.one), ("vlen", Flapjack.Shape.one)], body := body272_63, returnShape := (Flapjack.Shape.one) }
def simplifiedData272 : Decl (BitVec 64) :=
.function { name := "_mpt_insert_node", inline := false, exported := false, params := [("node", Flapjack.Shape.one), ("key", Flapjack.Shape.one), ("klen", Flapjack.Shape.one), ("level", Flapjack.Shape.one),
  ("vptr", Flapjack.Shape.one), ("vlen", Flapjack.Shape.one)], body := body272_99, returnShape := (Flapjack.Shape.one) }
def original272 := Pancake.PanLang.declToHOL originalData272
def simplified272 := Pancake.PanLang.declToHOL simplifiedData272
end InitECandidate.Proofs.FrontendStages.Declarations
