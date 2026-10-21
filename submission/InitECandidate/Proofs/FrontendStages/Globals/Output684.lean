import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data684
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate668
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody684_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def globalBody684_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody684_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.var Flapjack.VarKind.local "l0", Flapjack.Exp.var Flapjack.VarKind.local "l1",
      Flapjack.Exp.var Flapjack.VarKind.local "l2", Flapjack.Exp.var Flapjack.VarKind.local "l3"])
  (Flapjack.Exp.const 0#64)) globalBody684_0 globalBody684_1

def globalBody684_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_set_inf"
  [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "out"]

def globalBody684_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody684_5 : Prog (BitVec 64) :=
.seq globalBody684_3 globalBody684_4

def globalBody684_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 1#64)) globalBody684_5 globalBody684_1

def globalBody684_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "x0"), none)) "fq_to_mont"
  [Flapjack.Exp.var Flapjack.VarKind.local "x0"]

def globalBody684_8 : Prog (BitVec 64) :=
.seq globalBody684_6 globalBody684_7

def globalBody684_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "x1"), none)) "fq_to_mont"
  [Flapjack.Exp.var Flapjack.VarKind.local "x1"]

def globalBody684_10 : Prog (BitVec 64) :=
.seq globalBody684_8 globalBody684_9

def globalBody684_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "y0"), none)) "fq_to_mont"
  [Flapjack.Exp.var Flapjack.VarKind.local "y0"]

def globalBody684_12 : Prog (BitVec 64) :=
.seq globalBody684_10 globalBody684_11

def globalBody684_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "y1"), none)) "fq_to_mont"
  [Flapjack.Exp.var Flapjack.VarKind.local "y1"]

def globalBody684_14 : Prog (BitVec 64) :=
.seq globalBody684_12 globalBody684_13

def globalBody684_15 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "out") (Flapjack.Exp.var Flapjack.VarKind.local "x0")

def globalBody684_16 : Prog (BitVec 64) :=
.seq globalBody684_14 globalBody684_15

def globalBody684_17 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "x1")

def globalBody684_18 : Prog (BitVec 64) :=
.seq globalBody684_16 globalBody684_17

def globalBody684_19 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "y0")

def globalBody684_20 : Prog (BitVec 64) :=
.seq globalBody684_18 globalBody684_19

def globalBody684_21 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "y1")

def globalBody684_22 : Prog (BitVec 64) :=
.seq globalBody684_20 globalBody684_21

def globalBody684_23 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 128#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 15230403791020821917#64, Flapjack.Exp.const 754611498739239741#64,
      Flapjack.Exp.const 7381016538464732716#64, Flapjack.Exp.const 1011752739694698287#64])

def globalBody684_24 : Prog (BitVec 64) :=
.seq globalBody684_22 globalBody684_23

def globalBody684_25 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 160#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64])

def globalBody684_26 : Prog (BitVec 64) :=
.seq globalBody684_24 globalBody684_25

def globalBody684_27 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "b2")
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 4321547867055981224#64, Flapjack.Exp.const 147241268046680925#64,
      Flapjack.Exp.const 2789960110459671136#64, Flapjack.Exp.const 2671978398120978541#64])

def globalBody684_28 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "b2", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 4100506350182530919#64, Flapjack.Exp.const 7345568344173317438#64,
      Flapjack.Exp.const 15513160039642431658#64, Flapjack.Exp.const 90557763186888013#64])

def globalBody684_29 : Prog (BitVec 64) :=
.seq globalBody684_27 globalBody684_28

def globalBody684_30 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 64#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 64#64]]

def globalBody684_31 : Prog (BitVec 64) :=
.seq globalBody684_29 globalBody684_30

def globalBody684_32 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.var Flapjack.VarKind.local "out",
    Flapjack.Exp.var Flapjack.VarKind.local "out"]

def globalBody684_33 : Prog (BitVec 64) :=
.seq globalBody684_31 globalBody684_32

def globalBody684_34 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.var Flapjack.VarKind.local "t2",
    Flapjack.Exp.var Flapjack.VarKind.local "out"]

def globalBody684_35 : Prog (BitVec 64) :=
.seq globalBody684_33 globalBody684_34

def globalBody684_36 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_add"
  [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.var Flapjack.VarKind.local "t2",
    Flapjack.Exp.var Flapjack.VarKind.local "b2"]

def globalBody684_37 : Prog (BitVec 64) :=
.seq globalBody684_35 globalBody684_36

def globalBody684_38 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody684_39 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) globalBody684_0 globalBody684_1

def globalBody684_40 : Prog (BitVec 64) :=
.seq globalBody684_38 globalBody684_39

def globalBody684_41 : Prog (BitVec 64) :=
.seq globalBody684_40 globalBody684_4

def globalBody684_42 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.const 64#64]) globalBody684_41

def globalBody684_43 : Prog (BitVec 64) :=
.seq globalBody684_37 globalBody684_42

def globalBody684_44 : Prog (BitVec 64) :=
.decCall ("b2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) globalBody684_43

def globalBody684_45 : Prog (BitVec 64) :=
.decCall ("t2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) globalBody684_44

def globalBody684_46 : Prog (BitVec 64) :=
.decCall ("t1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) globalBody684_45

def globalBody684_47 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody684_46

def globalBody684_48 : Prog (BitVec 64) :=
.seq globalBody684_26 globalBody684_47

def globalBody684_49 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("is_zero_bytes") ([Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 128#64]) globalBody684_48

def globalBody684_50 : Prog (BitVec 64) :=
.seq globalBody684_2 globalBody684_49

def globalBody684_51 : Prog (BitVec 64) :=
.decCall ("l3") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "y1",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 4332616871279656263#64, Flapjack.Exp.const 10917124144477883021#64,
      Flapjack.Exp.const 13281191951274694749#64, Flapjack.Exp.const 3486998266802970665#64]]) globalBody684_50

def globalBody684_52 : Prog (BitVec 64) :=
.decCall ("l2") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "y0",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 4332616871279656263#64, Flapjack.Exp.const 10917124144477883021#64,
      Flapjack.Exp.const 13281191951274694749#64, Flapjack.Exp.const 3486998266802970665#64]]) globalBody684_51

def globalBody684_53 : Prog (BitVec 64) :=
.decCall ("l1") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "x1",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 4332616871279656263#64, Flapjack.Exp.const 10917124144477883021#64,
      Flapjack.Exp.const 13281191951274694749#64, Flapjack.Exp.const 3486998266802970665#64]]) globalBody684_52

def globalBody684_54 : Prog (BitVec 64) :=
.decCall ("l0") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "x0",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 4332616871279656263#64, Flapjack.Exp.const 10917124144477883021#64,
      Flapjack.Exp.const 13281191951274694749#64, Flapjack.Exp.const 3486998266802970665#64]]) globalBody684_53

def globalBody684_55 : Prog (BitVec 64) :=
.decCall ("y0") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 96#64],
  Flapjack.Exp.const 32#64]) globalBody684_54

def globalBody684_56 : Prog (BitVec 64) :=
.decCall ("y1") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 64#64],
  Flapjack.Exp.const 32#64]) globalBody684_55

def globalBody684_57 : Prog (BitVec 64) :=
.decCall ("x0") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 32#64],
  Flapjack.Exp.const 32#64]) globalBody684_56

def globalBody684_58 : Prog (BitVec 64) :=
.decCall ("x1") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 32#64]) globalBody684_57

def globalData684 : Decl (BitVec 64) :=
.function { name := "bn254_parse_g2", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := globalBody684_58, returnShape := (Flapjack.Shape.one) }
def globalOutput684 := Pancake.PanLang.declToHOL globalData684
end InitECandidate.Proofs.FrontendStages.Declarations
