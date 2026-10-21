import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data838
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate822
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody838_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 60#64)

def globalBody838_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody838_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 576#64)) globalBody838_0 globalBody838_1

def globalBody838_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "z"), none)) "is_zero_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 24#64]

def globalBody838_4 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "ok" (Flapjack.Exp.const 0#64)

def globalBody838_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "w0")
        (Flapjack.Exp.const 160#64)])) globalBody838_4 globalBody838_1

def globalBody838_6 : Prog (BitVec 64) :=
.seq globalBody838_3 globalBody838_5

def globalBody838_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "z"), none)) "is_zero_bytes"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 32#64],
    Flapjack.Exp.const 24#64]

def globalBody838_8 : Prog (BitVec 64) :=
.seq globalBody838_6 globalBody838_7

def globalBody838_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w0"), none)) "ld_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 56#64]]

def globalBody838_10 : Prog (BitVec 64) :=
.seq globalBody838_8 globalBody838_9

def globalBody838_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "w0")
        (Flapjack.Exp.const 256#64)])) globalBody838_4 globalBody838_1

def globalBody838_12 : Prog (BitVec 64) :=
.seq globalBody838_10 globalBody838_11

def globalBody838_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "z"), none)) "is_zero_bytes"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 64#64],
    Flapjack.Exp.const 24#64]

def globalBody838_14 : Prog (BitVec 64) :=
.seq globalBody838_12 globalBody838_13

def globalBody838_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w0"), none)) "ld_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 88#64]]

def globalBody838_16 : Prog (BitVec 64) :=
.seq globalBody838_14 globalBody838_15

def globalBody838_17 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "w0")
        (Flapjack.Exp.const 320#64)])) globalBody838_4 globalBody838_1

def globalBody838_18 : Prog (BitVec 64) :=
.seq globalBody838_16 globalBody838_17

def globalBody838_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "z"), none)) "is_zero_bytes"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 96#64],
    Flapjack.Exp.const 24#64]

def globalBody838_20 : Prog (BitVec 64) :=
.seq globalBody838_18 globalBody838_19

def globalBody838_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w0"), none)) "ld_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 120#64]]

def globalBody838_22 : Prog (BitVec 64) :=
.seq globalBody838_20 globalBody838_21

def globalBody838_23 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "w0")
        (Flapjack.Exp.const 384#64)])) globalBody838_4 globalBody838_1

def globalBody838_24 : Prog (BitVec 64) :=
.seq globalBody838_22 globalBody838_23

def globalBody838_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "z"), none)) "is_zero_bytes"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 128#64],
    Flapjack.Exp.const 24#64]

def globalBody838_26 : Prog (BitVec 64) :=
.seq globalBody838_24 globalBody838_25

def globalBody838_27 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w0"), none)) "ld_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 152#64]]

def globalBody838_28 : Prog (BitVec 64) :=
.seq globalBody838_26 globalBody838_27

def globalBody838_29 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "w0")
        (Flapjack.Exp.const 512#64)])) globalBody838_4 globalBody838_1

def globalBody838_30 : Prog (BitVec 64) :=
.seq globalBody838_28 globalBody838_29

def globalBody838_31 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "z"), none)) "is_zero_bytes"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 160#64],
    Flapjack.Exp.const 24#64]

def globalBody838_32 : Prog (BitVec 64) :=
.seq globalBody838_30 globalBody838_31

def globalBody838_33 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w0"), none)) "ld_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 184#64]]

def globalBody838_34 : Prog (BitVec 64) :=
.seq globalBody838_32 globalBody838_33

def globalBody838_35 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "w0") (Flapjack.Exp.const 48#64)])) globalBody838_4 globalBody838_1

def globalBody838_36 : Prog (BitVec 64) :=
.seq globalBody838_34 globalBody838_35

def globalBody838_37 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "z"), none)) "is_zero_bytes"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 256#64],
    Flapjack.Exp.const 24#64]

def globalBody838_38 : Prog (BitVec 64) :=
.seq globalBody838_36 globalBody838_37

def globalBody838_39 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w0"), none)) "ld_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 280#64]]

def globalBody838_40 : Prog (BitVec 64) :=
.seq globalBody838_38 globalBody838_39

def globalBody838_41 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "w0") (Flapjack.Exp.const 32#64)])) globalBody838_4 globalBody838_1

def globalBody838_42 : Prog (BitVec 64) :=
.seq globalBody838_40 globalBody838_41

def globalBody838_43 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "z"), none)) "is_zero_bytes"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 320#64],
    Flapjack.Exp.const 24#64]

def globalBody838_44 : Prog (BitVec 64) :=
.seq globalBody838_42 globalBody838_43

def globalBody838_45 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w0"), none)) "ld_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 344#64]]

def globalBody838_46 : Prog (BitVec 64) :=
.seq globalBody838_44 globalBody838_45

def globalBody838_47 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "w0") (Flapjack.Exp.const 8#64)])) globalBody838_4 globalBody838_1

def globalBody838_48 : Prog (BitVec 64) :=
.seq globalBody838_46 globalBody838_47

def globalBody838_49 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "z"), none)) "is_zero_bytes"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 384#64],
    Flapjack.Exp.const 24#64]

def globalBody838_50 : Prog (BitVec 64) :=
.seq globalBody838_48 globalBody838_49

def globalBody838_51 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w0"), none)) "ld_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 408#64]]

def globalBody838_52 : Prog (BitVec 64) :=
.seq globalBody838_50 globalBody838_51

def globalBody838_53 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "w0") (Flapjack.Exp.const 96#64)])) globalBody838_4 globalBody838_1

def globalBody838_54 : Prog (BitVec 64) :=
.seq globalBody838_52 globalBody838_53

def globalBody838_55 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "z"), none)) "is_zero_bytes"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 512#64],
    Flapjack.Exp.const 24#64]

def globalBody838_56 : Prog (BitVec 64) :=
.seq globalBody838_54 globalBody838_55

def globalBody838_57 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w0"), none)) "ld_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 536#64]]

def globalBody838_58 : Prog (BitVec 64) :=
.seq globalBody838_56 globalBody838_57

def globalBody838_59 : Prog (BitVec 64) :=
.seq globalBody838_58 globalBody838_47

def globalBody838_60 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody838_61 : Prog (BitVec 64) :=
.seq globalBody838_59 globalBody838_60

def globalBody838_62 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 61#64)

def globalBody838_63 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 0#64)) globalBody838_62 globalBody838_1

def globalBody838_64 : Prog (BitVec 64) :=
.seq globalBody838_61 globalBody838_63

def globalBody838_65 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "out",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 192#64],
    Flapjack.Exp.const 48#64]

def globalBody838_66 : Prog (BitVec 64) :=
.seq globalBody838_64 globalBody838_65

def globalBody838_67 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 48#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 288#64],
    Flapjack.Exp.const 32#64]

def globalBody838_68 : Prog (BitVec 64) :=
.seq globalBody838_66 globalBody838_67

def globalBody838_69 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 80#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 352#64],
    Flapjack.Exp.const 8#64]

def globalBody838_70 : Prog (BitVec 64) :=
.seq globalBody838_68 globalBody838_69

def globalBody838_71 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 88#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 416#64],
    Flapjack.Exp.const 96#64]

def globalBody838_72 : Prog (BitVec 64) :=
.seq globalBody838_70 globalBody838_71

def globalBody838_73 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 184#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 544#64],
    Flapjack.Exp.const 8#64]

def globalBody838_74 : Prog (BitVec 64) :=
.seq globalBody838_72 globalBody838_73

def globalBody838_75 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody838_76 : Prog (BitVec 64) :=
.seq globalBody838_74 globalBody838_75

def globalBody838_77 : Prog (BitVec 64) :=
.decCall ("w0") (Flapjack.Shape.one) ("ld_be64") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 24#64]]) globalBody838_76

def globalBody838_78 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody838_77

def globalBody838_79 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("is_zero_bytes") ([Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 24#64]) globalBody838_78

def globalBody838_80 : Prog (BitVec 64) :=
.dec ("ok") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) globalBody838_79

def globalBody838_81 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody838_80

def globalBody838_82 : Prog (BitVec 64) :=
.seq globalBody838_2 globalBody838_81

def globalData838 : Decl (BitVec 64) :=
.function { name := "extract_deposit_data", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("n", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := globalBody838_82, returnShape := (Flapjack.Shape.one) }
def globalOutput838 := Pancake.PanLang.declToHOL globalData838
end InitECandidate.Proofs.FrontendStages.Declarations
