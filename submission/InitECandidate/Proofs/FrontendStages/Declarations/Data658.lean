import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify642
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body658_0 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "d") (Flapjack.Exp.var Flapjack.VarKind.local "r")

def body658_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body658_2 : Prog (BitVec 64) :=
.seq body658_0 body658_1

def body658_3 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "y"]) body658_2

def body658_4 : Prog (BitVec 64) :=
.dec ("y") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "b")) body658_3

def body658_5 : Prog (BitVec 64) :=
.dec ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "a")) body658_4

def body658_6 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body658_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "fld") (Flapjack.Exp.const 1#64)) body658_5 body658_6

def body658_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.var Flapjack.VarKind.local "a",
    Flapjack.Exp.var Flapjack.VarKind.local "b"]

def body658_9 : Prog (BitVec 64) :=
.seq body658_8 body658_1

def body658_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "fld") (Flapjack.Exp.const 2#64)) body658_9 body658_6

def body658_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.var Flapjack.VarKind.local "a",
    Flapjack.Exp.var Flapjack.VarKind.local "b"]

def body658_12 : Prog (BitVec 64) :=
.seq body658_11 body658_1

def body658_13 : Prog (BitVec 64) :=
.seq body658_10 body658_12

def body658_14 : Prog (BitVec 64) :=
.seq body658_7 body658_13

def body658_15 : Prog (BitVec 64) :=
.seq body658_7 body658_10

def body658_16 : Prog (BitVec 64) :=
.seq body658_15 body658_11

def body658_17 : Prog (BitVec 64) :=
.seq body658_16 body658_1

def originalData658 : Decl (BitVec 64) :=
.function { name := "fe_mul", inline := false, exported := false, params := [("fld", Flapjack.Shape.one), ("d", Flapjack.Shape.one), ("a", Flapjack.Shape.one), ("b", Flapjack.Shape.one)], body := body658_14, returnShape := (Flapjack.Shape.one) }
def simplifiedData658 : Decl (BitVec 64) :=
.function { name := "fe_mul", inline := false, exported := false, params := [("fld", Flapjack.Shape.one), ("d", Flapjack.Shape.one), ("a", Flapjack.Shape.one), ("b", Flapjack.Shape.one)], body := body658_17, returnShape := (Flapjack.Shape.one) }
def original658 := Pancake.PanLang.declToHOL originalData658
def simplified658 := Pancake.PanLang.declToHOL simplifiedData658
end InitECandidate.Proofs.FrontendStages.Declarations
