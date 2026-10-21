import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify233
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body249_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "a",
    Flapjack.Exp.var Flapjack.VarKind.local "al"]

def body249_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "al"],
    Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.var Flapjack.VarKind.local "bl"]

def body249_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "out")

def body249_3 : Prog (BitVec 64) :=
.seq body249_1 body249_2

def body249_4 : Prog (BitVec 64) :=
.seq body249_0 body249_3

def body249_5 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "al", Flapjack.Exp.var Flapjack.VarKind.local "bl"]]) body249_4

def body249_6 : Prog (BitVec 64) :=
.seq body249_0 body249_1

def body249_7 : Prog (BitVec 64) :=
.seq body249_6 body249_2

def body249_8 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "al", Flapjack.Exp.var Flapjack.VarKind.local "bl"]]) body249_7

def originalData249 : Decl (BitVec 64) :=
.function { name := "nibbles_concat", inline := false, exported := false, params := [("a", Flapjack.Shape.one), ("al", Flapjack.Shape.one), ("b", Flapjack.Shape.one), ("bl", Flapjack.Shape.one)], body := body249_5, returnShape := (Flapjack.Shape.one) }
def simplifiedData249 : Decl (BitVec 64) :=
.function { name := "nibbles_concat", inline := false, exported := false, params := [("a", Flapjack.Shape.one), ("al", Flapjack.Shape.one), ("b", Flapjack.Shape.one), ("bl", Flapjack.Shape.one)], body := body249_8, returnShape := (Flapjack.Shape.one) }
def original249 := Pancake.PanLang.declToHOL originalData249
def simplified249 := Pancake.PanLang.declToHOL simplifiedData249
end InitECandidate.Proofs.FrontendStages.Declarations
