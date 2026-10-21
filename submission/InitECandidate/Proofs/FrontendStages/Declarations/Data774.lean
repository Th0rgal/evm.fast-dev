import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify758
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body774_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 192#64]

def body774_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body774_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body774_3 : Prog (BitVec 64) :=
.seq body774_1 body774_2

def body774_4 : Prog (BitVec 64) :=
.seq body774_0 body774_3

def body774_5 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body774_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "inf") (Flapjack.Exp.const 1#64)) body774_4 body774_5

def body774_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_inv"
  [Flapjack.Exp.var Flapjack.VarKind.local "zi",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 192#64]]

def body774_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.var Flapjack.VarKind.local "zi"]

def body774_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 96#64],
    Flapjack.Exp.var Flapjack.VarKind.local "zi"]

def body774_10 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body774_11 : Prog (BitVec 64) :=
.seq body774_1 body774_10

def body774_12 : Prog (BitVec 64) :=
.seq body774_9 body774_11

def body774_13 : Prog (BitVec 64) :=
.seq body774_8 body774_12

def body774_14 : Prog (BitVec 64) :=
.seq body774_7 body774_13

def body774_15 : Prog (BitVec 64) :=
.seq body774_6 body774_14

def body774_16 : Prog (BitVec 64) :=
.decCall ("inf") (Flapjack.Shape.one) ("g2_is_inf") ([Flapjack.Exp.var Flapjack.VarKind.local "p"]) body774_15

def body774_17 : Prog (BitVec 64) :=
.decCall ("zi") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body774_16

def body774_18 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body774_17

def body774_19 : Prog (BitVec 64) :=
.seq body774_0 body774_1

def body774_20 : Prog (BitVec 64) :=
.seq body774_19 body774_2

def body774_21 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "inf") (Flapjack.Exp.const 1#64)) body774_20 body774_5

def body774_22 : Prog (BitVec 64) :=
.seq body774_21 body774_7

def body774_23 : Prog (BitVec 64) :=
.seq body774_22 body774_8

def body774_24 : Prog (BitVec 64) :=
.seq body774_23 body774_9

def body774_25 : Prog (BitVec 64) :=
.seq body774_24 body774_1

def body774_26 : Prog (BitVec 64) :=
.seq body774_25 body774_10

def body774_27 : Prog (BitVec 64) :=
.decCall ("inf") (Flapjack.Shape.one) ("g2_is_inf") ([Flapjack.Exp.var Flapjack.VarKind.local "p"]) body774_26

def body774_28 : Prog (BitVec 64) :=
.decCall ("zi") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body774_27

def body774_29 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body774_28

def originalData774 : Decl (BitVec 64) :=
.function { name := "g2_normalize", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("p", Flapjack.Shape.one)], body := body774_18, returnShape := (Flapjack.Shape.one) }
def simplifiedData774 : Decl (BitVec 64) :=
.function { name := "g2_normalize", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("p", Flapjack.Shape.one)], body := body774_29, returnShape := (Flapjack.Shape.one) }
def original774 := Pancake.PanLang.declToHOL originalData774
def simplified774 := Pancake.PanLang.declToHOL simplifiedData774
end InitECandidate.Proofs.FrontendStages.Declarations
