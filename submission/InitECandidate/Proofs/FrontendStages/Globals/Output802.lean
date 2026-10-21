import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data802
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate786
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody802_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody802_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def globalBody802_2 : Prog (BitVec 64) :=
.seq globalBody802_0 globalBody802_1

def globalBody802_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody802_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 0#64)) globalBody802_2 globalBody802_3

def globalBody802_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "sg") (Flapjack.Exp.const 0#64)) globalBody802_2 globalBody802_3

def globalBody802_6 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "s") (Flapjack.Exp.var Flapjack.VarKind.local "m")

def globalBody802_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 4#64]

def globalBody802_8 : Prog (BitVec 64) :=
.seq globalBody802_6 globalBody802_7

def globalBody802_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "p"]

def globalBody802_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "acc",
    Flapjack.Exp.var Flapjack.VarKind.local "p"]

def globalBody802_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 0#64)) globalBody802_9 globalBody802_10

def globalBody802_12 : Prog (BitVec 64) :=
.seq globalBody802_8 globalBody802_11

def globalBody802_13 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody802_14 : Prog (BitVec 64) :=
.seq globalBody802_12 globalBody802_13

def globalBody802_15 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.const 256#64],
  Flapjack.Exp.const 32#64]) globalBody802_14

def globalBody802_16 : Prog (BitVec 64) :=
.seq globalBody802_5 globalBody802_15

def globalBody802_17 : Prog (BitVec 64) :=
.decCall ("sg") (Flapjack.Shape.one) ("g2_subgroup_check") ([Flapjack.Exp.var Flapjack.VarKind.local "p"]) globalBody802_16

def globalBody802_18 : Prog (BitVec 64) :=
.seq globalBody802_4 globalBody802_17

def globalBody802_19 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("g2_decode") ([Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.var Flapjack.VarKind.local "p"]) globalBody802_18

def globalBody802_20 : Prog (BitVec 64) :=
.dec ("d") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "data",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 288#64]]) globalBody802_19

def globalBody802_21 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "k")) globalBody802_20

def globalBody802_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_encode"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "out"]

def globalBody802_23 : Prog (BitVec 64) :=
.seq globalBody802_21 globalBody802_22

def globalBody802_24 : Prog (BitVec 64) :=
.seq globalBody802_23 globalBody802_0

def globalBody802_25 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody802_26 : Prog (BitVec 64) :=
.seq globalBody802_24 globalBody802_25

def globalBody802_27 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody802_26

def globalBody802_28 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) globalBody802_27

def globalBody802_29 : Prog (BitVec 64) :=
.decCall ("p") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) globalBody802_28

def globalBody802_30 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) globalBody802_29

def globalBody802_31 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody802_30

def globalData802 : Decl (BitVec 64) :=
.function { name := "bls_g2_msm_exec", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("k", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := globalBody802_31, returnShape := (Flapjack.Shape.one) }
def globalOutput802 := Pancake.PanLang.declToHOL globalData802
end InitECandidate.Proofs.FrontendStages.Declarations
