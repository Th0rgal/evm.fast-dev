import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify656
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body672_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_set_inf"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def body672_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "base", Flapjack.Exp.var Flapjack.VarKind.local "pt",
    Flapjack.Exp.var Flapjack.VarKind.local "psz"]

def body672_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "acc",
    Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "base"]

def body672_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body672_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "bit") (Flapjack.Exp.const 1#64)) body672_2 body672_3

def body672_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body672_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_double"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "base",
    Flapjack.Exp.var Flapjack.VarKind.local "base"]

def body672_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "len")) body672_6 body672_3

def body672_8 : Prog (BitVec 64) :=
.seq body672_5 body672_7

def body672_9 : Prog (BitVec 64) :=
.seq body672_4 body672_8

def body672_10 : Prog (BitVec 64) :=
.decCall ("bit") (Flapjack.Shape.one) ("u256_bit") ([Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "i"]) body672_9

def body672_11 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "len")) body672_10

def body672_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "acc",
    Flapjack.Exp.var Flapjack.VarKind.local "psz"]

def body672_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body672_14 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body672_15 : Prog (BitVec 64) :=
.seq body672_13 body672_14

def body672_16 : Prog (BitVec 64) :=
.seq body672_12 body672_15

def body672_17 : Prog (BitVec 64) :=
.seq body672_11 body672_16

def body672_18 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body672_17

def body672_19 : Prog (BitVec 64) :=
.decCall ("len") (Flapjack.Shape.one) ("u256_bit_length") ([Flapjack.Exp.var Flapjack.VarKind.local "n"]) body672_18

def body672_20 : Prog (BitVec 64) :=
.seq body672_1 body672_19

def body672_21 : Prog (BitVec 64) :=
.seq body672_0 body672_20

def body672_22 : Prog (BitVec 64) :=
.decCall ("base") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "psz"]) body672_21

def body672_23 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "psz"]) body672_22

def body672_24 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body672_23

def body672_25 : Prog (BitVec 64) :=
.dec ("psz") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul
  [Flapjack.Exp.const 3#64,
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.const 32#64]]) body672_24

def body672_26 : Prog (BitVec 64) :=
.seq body672_0 body672_1

def body672_27 : Prog (BitVec 64) :=
.seq body672_4 body672_5

def body672_28 : Prog (BitVec 64) :=
.seq body672_27 body672_7

def body672_29 : Prog (BitVec 64) :=
.decCall ("bit") (Flapjack.Shape.one) ("u256_bit") ([Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "i"]) body672_28

def body672_30 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "len")) body672_29

def body672_31 : Prog (BitVec 64) :=
.seq body672_30 body672_12

def body672_32 : Prog (BitVec 64) :=
.seq body672_31 body672_13

def body672_33 : Prog (BitVec 64) :=
.seq body672_32 body672_14

def body672_34 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body672_33

def body672_35 : Prog (BitVec 64) :=
.decCall ("len") (Flapjack.Shape.one) ("u256_bit_length") ([Flapjack.Exp.var Flapjack.VarKind.local "n"]) body672_34

def body672_36 : Prog (BitVec 64) :=
.seq body672_26 body672_35

def body672_37 : Prog (BitVec 64) :=
.decCall ("base") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "psz"]) body672_36

def body672_38 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "psz"]) body672_37

def body672_39 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body672_38

def body672_40 : Prog (BitVec 64) :=
.dec ("psz") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul
  [Flapjack.Exp.const 3#64,
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.const 32#64]]) body672_39

def originalData672 : Decl (BitVec 64) :=
.function { name := "ecp_mul", inline := false, exported := false, params := [("fld", Flapjack.Shape.one), ("out", Flapjack.Shape.one), ("pt", Flapjack.Shape.one),
  ("n", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body672_25, returnShape := (Flapjack.Shape.one) }
def simplifiedData672 : Decl (BitVec 64) :=
.function { name := "ecp_mul", inline := false, exported := false, params := [("fld", Flapjack.Shape.one), ("out", Flapjack.Shape.one), ("pt", Flapjack.Shape.one),
  ("n", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body672_40, returnShape := (Flapjack.Shape.one) }
def original672 := Pancake.PanLang.declToHOL originalData672
def simplified672 := Pancake.PanLang.declToHOL simplifiedData672
end InitECandidate.Proofs.FrontendStages.Declarations
