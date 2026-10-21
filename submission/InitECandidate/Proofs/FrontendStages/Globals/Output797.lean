import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data797
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate781
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody797_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "g2",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
        Flapjack.Exp.const 480#64]]

def globalBody797_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "g2", Flapjack.Exp.const 96#64],
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
        Flapjack.Exp.const 576#64]]

def globalBody797_2 : Prog (BitVec 64) :=
.seq globalBody797_0 globalBody797_1

def globalBody797_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_set_one"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "g2", Flapjack.Exp.const 192#64]]

def globalBody797_4 : Prog (BitVec 64) :=
.seq globalBody797_2 globalBody797_3

def globalBody797_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "kzg_neg_scalar"
  [Flapjack.Exp.var Flapjack.VarKind.local "zb", Flapjack.Exp.var Flapjack.VarKind.local "k"]

def globalBody797_6 : Prog (BitVec 64) :=
.seq globalBody797_4 globalBody797_5

def globalBody797_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "xmz", Flapjack.Exp.var Flapjack.VarKind.local "g2",
    Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 4#64]

def globalBody797_8 : Prog (BitVec 64) :=
.seq globalBody797_6 globalBody797_7

def globalBody797_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "setup",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
        Flapjack.Exp.const 672#64]]

def globalBody797_10 : Prog (BitVec 64) :=
.seq globalBody797_8 globalBody797_9

def globalBody797_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "setup", Flapjack.Exp.const 96#64],
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
        Flapjack.Exp.const 768#64]]

def globalBody797_12 : Prog (BitVec 64) :=
.seq globalBody797_10 globalBody797_11

def globalBody797_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_set_one"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "setup", Flapjack.Exp.const 192#64]]

def globalBody797_14 : Prog (BitVec 64) :=
.seq globalBody797_12 globalBody797_13

def globalBody797_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "xmz", Flapjack.Exp.var Flapjack.VarKind.local "setup",
    Flapjack.Exp.var Flapjack.VarKind.local "xmz"]

def globalBody797_16 : Prog (BitVec 64) :=
.seq globalBody797_14 globalBody797_15

def globalBody797_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "g1",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
        Flapjack.Exp.const 384#64],
    Flapjack.Exp.const 48#64]

def globalBody797_18 : Prog (BitVec 64) :=
.seq globalBody797_16 globalBody797_17

def globalBody797_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "g1", Flapjack.Exp.const 48#64],
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
        Flapjack.Exp.const 432#64],
    Flapjack.Exp.const 48#64]

def globalBody797_20 : Prog (BitVec 64) :=
.seq globalBody797_18 globalBody797_19

def globalBody797_21 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "g1", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 8505329371266088957#64, Flapjack.Exp.const 17002214543764226050#64,
      Flapjack.Exp.const 6865905132761471162#64, Flapjack.Exp.const 8632934651105793861#64,
      Flapjack.Exp.const 6631298214892334189#64, Flapjack.Exp.const 1582556514881692819#64])

def globalBody797_22 : Prog (BitVec 64) :=
.seq globalBody797_20 globalBody797_21

def globalBody797_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "kzg_neg_scalar"
  [Flapjack.Exp.var Flapjack.VarKind.local "yb", Flapjack.Exp.var Flapjack.VarKind.local "k"]

def globalBody797_24 : Prog (BitVec 64) :=
.seq globalBody797_22 globalBody797_23

def globalBody797_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "pmy", Flapjack.Exp.var Flapjack.VarKind.local "g1",
    Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 4#64]

def globalBody797_26 : Prog (BitVec 64) :=
.seq globalBody797_24 globalBody797_25

def globalBody797_27 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "pmy", Flapjack.Exp.var Flapjack.VarKind.local "commitment",
    Flapjack.Exp.var Flapjack.VarKind.local "pmy"]

def globalBody797_28 : Prog (BitVec 64) :=
.seq globalBody797_26 globalBody797_27

def globalBody797_29 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_neg"
  [Flapjack.Exp.var Flapjack.VarKind.local "g2", Flapjack.Exp.var Flapjack.VarKind.local "g2"]

def globalBody797_30 : Prog (BitVec 64) :=
.seq globalBody797_28 globalBody797_29

def globalBody797_31 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_set_one" [Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def globalBody797_32 : Prog (BitVec 64) :=
.seq globalBody797_30 globalBody797_31

def globalBody797_33 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pair_accumulate"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "pmy",
    Flapjack.Exp.var Flapjack.VarKind.local "g2"]

def globalBody797_34 : Prog (BitVec 64) :=
.seq globalBody797_32 globalBody797_33

def globalBody797_35 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pair_accumulate"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "proof",
    Flapjack.Exp.var Flapjack.VarKind.local "xmz"]

def globalBody797_36 : Prog (BitVec 64) :=
.seq globalBody797_34 globalBody797_35

def globalBody797_37 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_final_exp"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def globalBody797_38 : Prog (BitVec 64) :=
.seq globalBody797_36 globalBody797_37

def globalBody797_39 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody797_40 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "one")

def globalBody797_41 : Prog (BitVec 64) :=
.seq globalBody797_39 globalBody797_40

def globalBody797_42 : Prog (BitVec 64) :=
.decCall ("one") (Flapjack.Shape.one) ("fp12_is_one") ([Flapjack.Exp.var Flapjack.VarKind.local "acc"]) globalBody797_41

def globalBody797_43 : Prog (BitVec 64) :=
.seq globalBody797_38 globalBody797_42

def globalBody797_44 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 576#64]) globalBody797_43

def globalBody797_45 : Prog (BitVec 64) :=
.decCall ("xmz") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) globalBody797_44

def globalBody797_46 : Prog (BitVec 64) :=
.decCall ("pmy") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) globalBody797_45

def globalBody797_47 : Prog (BitVec 64) :=
.decCall ("setup") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) globalBody797_46

def globalBody797_48 : Prog (BitVec 64) :=
.decCall ("g2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) globalBody797_47

def globalBody797_49 : Prog (BitVec 64) :=
.decCall ("g1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) globalBody797_48

def globalBody797_50 : Prog (BitVec 64) :=
.decCall ("k") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) globalBody797_49

def globalBody797_51 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody797_50

def globalData797 : Decl (BitVec 64) :=
.function { name := "kzg_verify", inline := false, exported := false, params := [("commitment", Flapjack.Shape.one), ("zb", Flapjack.Shape.one), ("yb", Flapjack.Shape.one),
  ("proof", Flapjack.Shape.one)], body := globalBody797_51, returnShape := (Flapjack.Shape.one) }
def globalOutput797 := Pancake.PanLang.declToHOL globalData797
end InitECandidate.Proofs.FrontendStages.Declarations
