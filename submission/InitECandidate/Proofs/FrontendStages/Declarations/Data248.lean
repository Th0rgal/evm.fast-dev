import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify232
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body248_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "i")

def body248_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body248_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.loadByte
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "i"]))
  (Flapjack.Exp.loadByte
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.var Flapjack.VarKind.local "i"]))) body248_0 body248_1

def body248_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body248_4 : Prog (BitVec 64) :=
.seq body248_2 body248_3

def body248_5 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body248_4

def body248_6 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "n")

def body248_7 : Prog (BitVec 64) :=
.seq body248_5 body248_6

def body248_8 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body248_7

def body248_9 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("min") ([Flapjack.Exp.var Flapjack.VarKind.local "al", Flapjack.Exp.var Flapjack.VarKind.local "bl"]) body248_8

def originalData248 : Decl (BitVec 64) :=
.function { name := "common_prefix_length", inline := false, exported := false, params := [("a", Flapjack.Shape.one), ("al", Flapjack.Shape.one), ("b", Flapjack.Shape.one), ("bl", Flapjack.Shape.one)], body := body248_9, returnShape := (Flapjack.Shape.one) }
def simplifiedData248 : Decl (BitVec 64) :=
.function { name := "common_prefix_length", inline := false, exported := false, params := [("a", Flapjack.Shape.one), ("al", Flapjack.Shape.one), ("b", Flapjack.Shape.one), ("bl", Flapjack.Shape.one)], body := body248_9, returnShape := (Flapjack.Shape.one) }
def original248 := Pancake.PanLang.declToHOL originalData248
def simplified248 := Pancake.PanLang.declToHOL simplifiedData248
end InitECandidate.Proofs.FrontendStages.Declarations
