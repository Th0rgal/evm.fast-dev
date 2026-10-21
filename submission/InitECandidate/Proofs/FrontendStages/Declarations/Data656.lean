import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify640
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body656_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 11#64])

def body656_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body656_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 11#64) (Flapjack.Exp.var Flapjack.VarKind.local "k")) body656_0 body656_1

def body656_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "iend" (Flapjack.Exp.const 11#64)

def body656_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 11#64) (Flapjack.Exp.var Flapjack.VarKind.local "iend")) body656_3 body656_1

def body656_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "acc"), none)) "fq_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "p"]

def body656_6 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body656_7 : Prog (BitVec 64) :=
.seq body656_5 body656_6

def body656_8 : Prog (BitVec 64) :=
.decCall ("p") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "ai", Flapjack.Exp.var Flapjack.VarKind.local "bj"]) body656_7

def body656_9 : Prog (BitVec 64) :=
.dec ("bj") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "b",
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.sub
            [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.var Flapjack.VarKind.local "i"],
          Flapjack.Exp.const 32#64]])) body656_8

def body656_10 : Prog (BitVec 64) :=
.dec ("ai") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "a",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 32#64]])) body656_9

def body656_11 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "iend")
  (Flapjack.Exp.var Flapjack.VarKind.local "i")) body656_10

def body656_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 32#64]])
  (Flapjack.Exp.var Flapjack.VarKind.local "acc")

def body656_13 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "k"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 1#64])

def body656_14 : Prog (BitVec 64) :=
.seq body656_12 body656_13

def body656_15 : Prog (BitVec 64) :=
.seq body656_11 body656_14

def body656_16 : Prog (BitVec 64) :=
.seq body656_4 body656_15

def body656_17 : Prog (BitVec 64) :=
.dec ("iend") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "k") body656_16

def body656_18 : Prog (BitVec 64) :=
.seq body656_2 body656_17

def body656_19 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body656_18

def body656_20 : Prog (BitVec 64) :=
.dec ("acc") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body656_19

def body656_21 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 23#64)) body656_20

def body656_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_reduce" [Flapjack.Exp.var Flapjack.VarKind.local "t"]

def body656_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 384#64]

def body656_24 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body656_25 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body656_26 : Prog (BitVec 64) :=
.seq body656_24 body656_25

def body656_27 : Prog (BitVec 64) :=
.seq body656_23 body656_26

def body656_28 : Prog (BitVec 64) :=
.seq body656_22 body656_27

def body656_29 : Prog (BitVec 64) :=
.seq body656_21 body656_28

def body656_30 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body656_29

def body656_31 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 23#64, Flapjack.Exp.const 32#64]]) body656_30

def body656_32 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body656_31

def body656_33 : Prog (BitVec 64) :=
.seq body656_4 body656_11

def body656_34 : Prog (BitVec 64) :=
.seq body656_33 body656_12

def body656_35 : Prog (BitVec 64) :=
.seq body656_34 body656_13

def body656_36 : Prog (BitVec 64) :=
.dec ("iend") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "k") body656_35

def body656_37 : Prog (BitVec 64) :=
.seq body656_2 body656_36

def body656_38 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body656_37

def body656_39 : Prog (BitVec 64) :=
.dec ("acc") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body656_38

def body656_40 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 23#64)) body656_39

def body656_41 : Prog (BitVec 64) :=
.seq body656_40 body656_22

def body656_42 : Prog (BitVec 64) :=
.seq body656_41 body656_23

def body656_43 : Prog (BitVec 64) :=
.seq body656_42 body656_24

def body656_44 : Prog (BitVec 64) :=
.seq body656_43 body656_25

def body656_45 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body656_44

def body656_46 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 23#64, Flapjack.Exp.const 32#64]]) body656_45

def body656_47 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body656_46

def originalData656 : Decl (BitVec 64) :=
.function { name := "fq12_mul", inline := false, exported := false, params := [("d", Flapjack.Shape.one), ("a", Flapjack.Shape.one), ("b", Flapjack.Shape.one)], body := body656_32, returnShape := (Flapjack.Shape.one) }
def simplifiedData656 : Decl (BitVec 64) :=
.function { name := "fq12_mul", inline := false, exported := false, params := [("d", Flapjack.Shape.one), ("a", Flapjack.Shape.one), ("b", Flapjack.Shape.one)], body := body656_47, returnShape := (Flapjack.Shape.one) }
def original656 := Pancake.PanLang.declToHOL originalData656
def simplified656 := Pancake.PanLang.declToHOL simplifiedData656
end InitECandidate.Proofs.FrontendStages.Declarations
