import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data803
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate787
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody803_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_set_one" [Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def globalBody803_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody803_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def globalBody803_3 : Prog (BitVec 64) :=
.seq globalBody803_1 globalBody803_2

def globalBody803_4 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody803_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 0#64)) globalBody803_3 globalBody803_4

def globalBody803_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "sg") (Flapjack.Exp.const 0#64)) globalBody803_3 globalBody803_4

def globalBody803_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "ok"), none)) "g2_decode"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.const 128#64],
    Flapjack.Exp.var Flapjack.VarKind.local "q"]

def globalBody803_8 : Prog (BitVec 64) :=
.seq globalBody803_6 globalBody803_7

def globalBody803_9 : Prog (BitVec 64) :=
.seq globalBody803_8 globalBody803_5

def globalBody803_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "sg"), none)) "g2_subgroup_check"
  [Flapjack.Exp.var Flapjack.VarKind.local "q"]

def globalBody803_11 : Prog (BitVec 64) :=
.seq globalBody803_9 globalBody803_10

def globalBody803_12 : Prog (BitVec 64) :=
.seq globalBody803_11 globalBody803_6

def globalBody803_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pair_accumulate"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.var Flapjack.VarKind.local "q"]

def globalBody803_14 : Prog (BitVec 64) :=
.seq globalBody803_12 globalBody803_13

def globalBody803_15 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody803_16 : Prog (BitVec 64) :=
.seq globalBody803_14 globalBody803_15

def globalBody803_17 : Prog (BitVec 64) :=
.decCall ("sg") (Flapjack.Shape.one) ("g1_subgroup_check") ([Flapjack.Exp.var Flapjack.VarKind.local "p"]) globalBody803_16

def globalBody803_18 : Prog (BitVec 64) :=
.seq globalBody803_5 globalBody803_17

def globalBody803_19 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("g1_decode") ([Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.var Flapjack.VarKind.local "p"]) globalBody803_18

def globalBody803_20 : Prog (BitVec 64) :=
.dec ("d") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "data",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 384#64]]) globalBody803_19

def globalBody803_21 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "k")) globalBody803_20

def globalBody803_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_final_exp"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def globalBody803_23 : Prog (BitVec 64) :=
.seq globalBody803_21 globalBody803_22

def globalBody803_24 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 32#64]

def globalBody803_25 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 31#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "one")

def globalBody803_26 : Prog (BitVec 64) :=
.seq globalBody803_24 globalBody803_25

def globalBody803_27 : Prog (BitVec 64) :=
.seq globalBody803_26 globalBody803_1

def globalBody803_28 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody803_29 : Prog (BitVec 64) :=
.seq globalBody803_27 globalBody803_28

def globalBody803_30 : Prog (BitVec 64) :=
.decCall ("one") (Flapjack.Shape.one) ("fp12_is_one") ([Flapjack.Exp.var Flapjack.VarKind.local "acc"]) globalBody803_29

def globalBody803_31 : Prog (BitVec 64) :=
.seq globalBody803_23 globalBody803_30

def globalBody803_32 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody803_31

def globalBody803_33 : Prog (BitVec 64) :=
.seq globalBody803_0 globalBody803_32

def globalBody803_34 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 576#64]) globalBody803_33

def globalBody803_35 : Prog (BitVec 64) :=
.decCall ("q") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) globalBody803_34

def globalBody803_36 : Prog (BitVec 64) :=
.decCall ("p") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) globalBody803_35

def globalBody803_37 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody803_36

def globalData803 : Decl (BitVec 64) :=
.function { name := "bls_pairing_exec", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("k", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := globalBody803_37, returnShape := (Flapjack.Shape.one) }
def globalOutput803 := Pancake.PanLang.declToHOL globalData803
end InitECandidate.Proofs.FrontendStages.Declarations
