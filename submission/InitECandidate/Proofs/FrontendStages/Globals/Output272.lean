import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data272
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate256
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody272_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "go" (Flapjack.Exp.const 0#64)

def globalBody272_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "r"), none)) "node_new_leaf"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "key", Flapjack.Exp.var Flapjack.VarKind.local "level"],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "klen", Flapjack.Exp.var Flapjack.VarKind.local "level"],
    Flapjack.Exp.var Flapjack.VarKind.local "vptr", Flapjack.Exp.var Flapjack.VarKind.local "vlen"]

def globalBody272_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 2#64]

def globalBody272_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody272_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 0#64)) globalBody272_2 globalBody272_3

def globalBody272_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "node_invalidate" [Flapjack.Exp.var Flapjack.VarKind.local "node"]

def globalBody272_6 : Prog (BitVec 64) :=
.seq globalBody272_4 globalBody272_5

def globalBody272_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "r"), none)) "_insert_into_leaf"
  [Flapjack.Exp.var Flapjack.VarKind.local "node",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "key", Flapjack.Exp.var Flapjack.VarKind.local "level"],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "klen", Flapjack.Exp.var Flapjack.VarKind.local "level"],
    Flapjack.Exp.var Flapjack.VarKind.local "vptr", Flapjack.Exp.var Flapjack.VarKind.local "vlen"]

def globalBody272_8 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "r" (Flapjack.Exp.var Flapjack.VarKind.local "node")

def globalBody272_9 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "next_node"
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 48#64]))

def globalBody272_10 : Prog (BitVec 64) :=
.seq globalBody272_8 globalBody272_9

def globalBody272_11 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "next_slot"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 48#64])

def globalBody272_12 : Prog (BitVec 64) :=
.seq globalBody272_10 globalBody272_11

def globalBody272_13 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "next_level"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "level", Flapjack.Exp.var Flapjack.VarKind.local "pl"])

def globalBody272_14 : Prog (BitVec 64) :=
.seq globalBody272_12 globalBody272_13

def globalBody272_15 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "go" (Flapjack.Exp.const 1#64)

def globalBody272_16 : Prog (BitVec 64) :=
.seq globalBody272_14 globalBody272_15

def globalBody272_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "r"), none)) "node_new_ext"
  [Flapjack.Exp.var Flapjack.VarKind.local "seg", Flapjack.Exp.var Flapjack.VarKind.local "pl",
    Flapjack.Exp.var Flapjack.VarKind.local "br"]

def globalBody272_18 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "r" (Flapjack.Exp.var Flapjack.VarKind.local "br")

def globalBody272_19 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "pl")) globalBody272_17 globalBody272_18

def globalBody272_20 : Prog (BitVec 64) :=
.decCall ("br") (Flapjack.Shape.one) ("_split_extension") ([Flapjack.Exp.var Flapjack.VarKind.local "node",
  Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "key", Flapjack.Exp.var Flapjack.VarKind.local "level"],
  Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "klen", Flapjack.Exp.var Flapjack.VarKind.local "level"],
  Flapjack.Exp.var Flapjack.VarKind.local "vptr", Flapjack.Exp.var Flapjack.VarKind.local "vlen",
  Flapjack.Exp.var Flapjack.VarKind.local "pl"]) globalBody272_19

def globalBody272_21 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "pl")
  (Flapjack.Exp.var Flapjack.VarKind.local "sl")) globalBody272_16 globalBody272_20

def globalBody272_22 : Prog (BitVec 64) :=
.decCall ("pl") (Flapjack.Shape.one) ("common_prefix_length") ([Flapjack.Exp.var Flapjack.VarKind.local "seg", Flapjack.Exp.var Flapjack.VarKind.local "sl",
  Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "key", Flapjack.Exp.var Flapjack.VarKind.local "level"],
  Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "klen", Flapjack.Exp.var Flapjack.VarKind.local "level"]]) globalBody272_21

def globalBody272_23 : Prog (BitVec 64) :=
.dec ("sl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 40#64])) globalBody272_22

def globalBody272_24 : Prog (BitVec 64) :=
.dec ("seg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 32#64])) globalBody272_23

def globalBody272_25 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 160#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "vptr")

def globalBody272_26 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 168#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "vlen")

def globalBody272_27 : Prog (BitVec 64) :=
.seq globalBody272_25 globalBody272_26

def globalBody272_28 : Prog (BitVec 64) :=
.seq globalBody272_27 globalBody272_8

def globalBody272_29 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "next_node"
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 32#64,
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.var Flapjack.VarKind.local "idx", Flapjack.Exp.const 8#64]]))

def globalBody272_30 : Prog (BitVec 64) :=
.seq globalBody272_8 globalBody272_29

def globalBody272_31 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "next_slot"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 32#64,
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "idx", Flapjack.Exp.const 8#64]])

def globalBody272_32 : Prog (BitVec 64) :=
.seq globalBody272_30 globalBody272_31

def globalBody272_33 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "next_level"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "level", Flapjack.Exp.const 1#64])

def globalBody272_34 : Prog (BitVec 64) :=
.seq globalBody272_32 globalBody272_33

def globalBody272_35 : Prog (BitVec 64) :=
.seq globalBody272_34 globalBody272_15

def globalBody272_36 : Prog (BitVec 64) :=
.dec ("idx") (Flapjack.Shape.one) (Flapjack.Exp.loadByte
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "key", Flapjack.Exp.var Flapjack.VarKind.local "level"])) globalBody272_35

def globalBody272_37 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "level")
  (Flapjack.Exp.var Flapjack.VarKind.local "klen")) globalBody272_28 globalBody272_36

def globalBody272_38 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 2#64)) globalBody272_24 globalBody272_37

def globalBody272_39 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 1#64)) globalBody272_7 globalBody272_38

def globalBody272_40 : Prog (BitVec 64) :=
.seq globalBody272_6 globalBody272_39

def globalBody272_41 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 0#64])) globalBody272_40

def globalBody272_42 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "node") (Flapjack.Exp.const 0#64)) globalBody272_1 globalBody272_41

def globalBody272_43 : Prog (BitVec 64) :=
.seq globalBody272_0 globalBody272_42

def globalBody272_44 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "result" (Flapjack.Exp.var Flapjack.VarKind.local "r")

def globalBody272_45 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "slot") (Flapjack.Exp.var Flapjack.VarKind.local "r")

def globalBody272_46 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "slot") (Flapjack.Exp.const 0#64)) globalBody272_44 globalBody272_45

def globalBody272_47 : Prog (BitVec 64) :=
.seq globalBody272_43 globalBody272_46

def globalBody272_48 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "node" (Flapjack.Exp.var Flapjack.VarKind.local "next_node")

def globalBody272_49 : Prog (BitVec 64) :=
.seq globalBody272_47 globalBody272_48

def globalBody272_50 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "slot" (Flapjack.Exp.var Flapjack.VarKind.local "next_slot")

def globalBody272_51 : Prog (BitVec 64) :=
.seq globalBody272_49 globalBody272_50

def globalBody272_52 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "level" (Flapjack.Exp.var Flapjack.VarKind.local "next_level")

def globalBody272_53 : Prog (BitVec 64) :=
.seq globalBody272_51 globalBody272_52

def globalBody272_54 : Prog (BitVec 64) :=
.dec ("next_level") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody272_53

def globalBody272_55 : Prog (BitVec 64) :=
.dec ("next_slot") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody272_54

def globalBody272_56 : Prog (BitVec 64) :=
.dec ("next_node") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody272_55

def globalBody272_57 : Prog (BitVec 64) :=
.dec ("r") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody272_56

def globalBody272_58 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "go") (Flapjack.Exp.const 0#64)) globalBody272_57

def globalBody272_59 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "result")

def globalBody272_60 : Prog (BitVec 64) :=
.seq globalBody272_58 globalBody272_59

def globalBody272_61 : Prog (BitVec 64) :=
.dec ("go") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) globalBody272_60

def globalBody272_62 : Prog (BitVec 64) :=
.dec ("slot") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody272_61

def globalBody272_63 : Prog (BitVec 64) :=
.dec ("result") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody272_62

def globalData272 : Decl (BitVec 64) :=
.function { name := "_mpt_insert_node", inline := false, exported := false, params := [("node", Flapjack.Shape.one), ("key", Flapjack.Shape.one), ("klen", Flapjack.Shape.one), ("level", Flapjack.Shape.one),
  ("vptr", Flapjack.Shape.one), ("vlen", Flapjack.Shape.one)], body := globalBody272_63, returnShape := (Flapjack.Shape.one) }
def globalOutput272 := Pancake.PanLang.declToHOL globalData272
end InitECandidate.Proofs.FrontendStages.Declarations
