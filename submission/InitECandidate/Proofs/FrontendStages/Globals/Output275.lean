import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data275
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate259
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody275_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "go" (Flapjack.Exp.const 0#64)

def globalBody275_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "res" (Flapjack.Exp.const 0#64)

def globalBody275_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 2#64]

def globalBody275_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody275_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 0#64)) globalBody275_2 globalBody275_3

def globalBody275_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "node_invalidate" [Flapjack.Exp.var Flapjack.VarKind.local "node"]

def globalBody275_6 : Prog (BitVec 64) :=
.seq globalBody275_4 globalBody275_5

def globalBody275_7 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "res" (Flapjack.Exp.var Flapjack.VarKind.local "node")

def globalBody275_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) globalBody275_1 globalBody275_3

def globalBody275_9 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 32#64]),
  Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "key", Flapjack.Exp.var Flapjack.VarKind.local "level"],
  Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "klen", Flapjack.Exp.var Flapjack.VarKind.local "level"]]) globalBody275_8

def globalBody275_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 40#64]))
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "klen", Flapjack.Exp.var Flapjack.VarKind.local "level"])) globalBody275_9 globalBody275_3

def globalBody275_11 : Prog (BitVec 64) :=
.seq globalBody275_7 globalBody275_10

def globalBody275_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "fr", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "top")

def globalBody275_13 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "fr", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "node")

def globalBody275_14 : Prog (BitVec 64) :=
.seq globalBody275_12 globalBody275_13

def globalBody275_15 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "fr", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.const 2#64)

def globalBody275_16 : Prog (BitVec 64) :=
.seq globalBody275_14 globalBody275_15

def globalBody275_17 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "fr", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "seg")

def globalBody275_18 : Prog (BitVec 64) :=
.seq globalBody275_16 globalBody275_17

def globalBody275_19 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "fr", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "sl")

def globalBody275_20 : Prog (BitVec 64) :=
.seq globalBody275_18 globalBody275_19

def globalBody275_21 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "top" (Flapjack.Exp.var Flapjack.VarKind.local "fr")

def globalBody275_22 : Prog (BitVec 64) :=
.seq globalBody275_20 globalBody275_21

def globalBody275_23 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "node"
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 48#64]))

def globalBody275_24 : Prog (BitVec 64) :=
.seq globalBody275_22 globalBody275_23

def globalBody275_25 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "level"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "level", Flapjack.Exp.var Flapjack.VarKind.local "sl"])

def globalBody275_26 : Prog (BitVec 64) :=
.seq globalBody275_24 globalBody275_25

def globalBody275_27 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "go" (Flapjack.Exp.const 1#64)

def globalBody275_28 : Prog (BitVec 64) :=
.seq globalBody275_26 globalBody275_27

def globalBody275_29 : Prog (BitVec 64) :=
.decCall ("fr") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.const 40#64]) globalBody275_28

def globalBody275_30 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "pl")
  (Flapjack.Exp.var Flapjack.VarKind.local "sl")) globalBody275_7 globalBody275_29

def globalBody275_31 : Prog (BitVec 64) :=
.decCall ("pl") (Flapjack.Shape.one) ("common_prefix_length") ([Flapjack.Exp.var Flapjack.VarKind.local "seg", Flapjack.Exp.var Flapjack.VarKind.local "sl",
  Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "key", Flapjack.Exp.var Flapjack.VarKind.local "level"],
  Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "klen", Flapjack.Exp.var Flapjack.VarKind.local "level"]]) globalBody275_30

def globalBody275_32 : Prog (BitVec 64) :=
.dec ("sl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 40#64])) globalBody275_31

def globalBody275_33 : Prog (BitVec 64) :=
.dec ("seg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 32#64])) globalBody275_32

def globalBody275_34 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 160#64])
  (Flapjack.Exp.const 0#64)

def globalBody275_35 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 168#64])
  (Flapjack.Exp.const 0#64)

def globalBody275_36 : Prog (BitVec 64) :=
.seq globalBody275_34 globalBody275_35

def globalBody275_37 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "res"), none)) "_collapse_branch"
  [Flapjack.Exp.var Flapjack.VarKind.local "node"]

def globalBody275_38 : Prog (BitVec 64) :=
.seq globalBody275_36 globalBody275_37

def globalBody275_39 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 168#64]))
  (Flapjack.Exp.const 0#64)) globalBody275_7 globalBody275_38

def globalBody275_40 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "fr2", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "top")

def globalBody275_41 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "fr2", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "node")

def globalBody275_42 : Prog (BitVec 64) :=
.seq globalBody275_40 globalBody275_41

def globalBody275_43 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "fr2", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.const 3#64)

def globalBody275_44 : Prog (BitVec 64) :=
.seq globalBody275_42 globalBody275_43

def globalBody275_45 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "fr2", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "idx")

def globalBody275_46 : Prog (BitVec 64) :=
.seq globalBody275_44 globalBody275_45

def globalBody275_47 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "top" (Flapjack.Exp.var Flapjack.VarKind.local "fr2")

def globalBody275_48 : Prog (BitVec 64) :=
.seq globalBody275_46 globalBody275_47

def globalBody275_49 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "node"
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 32#64,
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.var Flapjack.VarKind.local "idx", Flapjack.Exp.const 8#64]]))

def globalBody275_50 : Prog (BitVec 64) :=
.seq globalBody275_48 globalBody275_49

def globalBody275_51 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "level"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "level", Flapjack.Exp.const 1#64])

def globalBody275_52 : Prog (BitVec 64) :=
.seq globalBody275_50 globalBody275_51

def globalBody275_53 : Prog (BitVec 64) :=
.seq globalBody275_52 globalBody275_27

def globalBody275_54 : Prog (BitVec 64) :=
.decCall ("fr2") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.const 40#64]) globalBody275_53

def globalBody275_55 : Prog (BitVec 64) :=
.dec ("idx") (Flapjack.Shape.one) (Flapjack.Exp.loadByte
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "key", Flapjack.Exp.var Flapjack.VarKind.local "level"])) globalBody275_54

def globalBody275_56 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "level")
  (Flapjack.Exp.var Flapjack.VarKind.local "klen")) globalBody275_39 globalBody275_55

def globalBody275_57 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 2#64)) globalBody275_33 globalBody275_56

def globalBody275_58 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 1#64)) globalBody275_11 globalBody275_57

def globalBody275_59 : Prog (BitVec 64) :=
.seq globalBody275_6 globalBody275_58

def globalBody275_60 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 0#64])) globalBody275_59

def globalBody275_61 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "node") (Flapjack.Exp.const 0#64)) globalBody275_1 globalBody275_60

def globalBody275_62 : Prog (BitVec 64) :=
.seq globalBody275_0 globalBody275_61

def globalBody275_63 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "go") (Flapjack.Exp.const 0#64)) globalBody275_62

def globalBody275_64 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "res"), none)) "_delete_ext_finish"
  [Flapjack.Exp.var Flapjack.VarKind.local "fnode",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 24#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 32#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "res"]

def globalBody275_65 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "fnode", Flapjack.Exp.const 32#64,
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.load Flapjack.Shape.one
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 32#64]),
          Flapjack.Exp.const 8#64]])
  (Flapjack.Exp.var Flapjack.VarKind.local "res")

def globalBody275_66 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "res"), none)) "_collapse_branch"
  [Flapjack.Exp.var Flapjack.VarKind.local "fnode"]

def globalBody275_67 : Prog (BitVec 64) :=
.seq globalBody275_65 globalBody275_66

def globalBody275_68 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 16#64]))
  (Flapjack.Exp.const 2#64)) globalBody275_64 globalBody275_67

def globalBody275_69 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "top"
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 0#64]))

def globalBody275_70 : Prog (BitVec 64) :=
.seq globalBody275_68 globalBody275_69

def globalBody275_71 : Prog (BitVec 64) :=
.dec ("fnode") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 8#64])) globalBody275_70

def globalBody275_72 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "top") (Flapjack.Exp.const 0#64)) globalBody275_71

def globalBody275_73 : Prog (BitVec 64) :=
.seq globalBody275_63 globalBody275_72

def globalBody275_74 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "res")

def globalBody275_75 : Prog (BitVec 64) :=
.seq globalBody275_73 globalBody275_74

def globalBody275_76 : Prog (BitVec 64) :=
.dec ("go") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) globalBody275_75

def globalBody275_77 : Prog (BitVec 64) :=
.dec ("res") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody275_76

def globalBody275_78 : Prog (BitVec 64) :=
.dec ("top") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody275_77

def globalData275 : Decl (BitVec 64) :=
.function { name := "_mpt_delete_node_body", inline := false, exported := false, params := [("node", Flapjack.Shape.one), ("key", Flapjack.Shape.one), ("klen", Flapjack.Shape.one), ("level", Flapjack.Shape.one)], body := globalBody275_78, returnShape := (Flapjack.Shape.one) }
def globalOutput275 := Pancake.PanLang.declToHOL globalData275
end InitECandidate.Proofs.FrontendStages.Declarations
