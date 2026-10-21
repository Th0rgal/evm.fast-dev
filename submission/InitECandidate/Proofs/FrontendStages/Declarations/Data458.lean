import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify442
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body458_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.var Flapjack.VarKind.local "total"]

def body458_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "extend_memory"
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "x")]

def body458_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body458_3 : Prog (BitVec 64) :=
.seq body458_1 body458_2

def body458_4 : Prog (BitVec 64) :=
.seq body458_0 body458_3

def body458_5 : Prog (BitVec 64) :=
.decCall ("total") (Flapjack.Shape.one) ("add_sat") ([Flapjack.Exp.var Flapjack.VarKind.local "base", Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "x")]) body458_4

def body458_6 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("extend_memory_cost1") ([Flapjack.Exp.var Flapjack.VarKind.local "start", Flapjack.Exp.var Flapjack.VarKind.local "size"]) body458_5

def body458_7 : Prog (BitVec 64) :=
.seq body458_0 body458_1

def body458_8 : Prog (BitVec 64) :=
.seq body458_7 body458_2

def body458_9 : Prog (BitVec 64) :=
.decCall ("total") (Flapjack.Shape.one) ("add_sat") ([Flapjack.Exp.var Flapjack.VarKind.local "base", Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "x")]) body458_8

def body458_10 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("extend_memory_cost1") ([Flapjack.Exp.var Flapjack.VarKind.local "start", Flapjack.Exp.var Flapjack.VarKind.local "size"]) body458_9

def originalData458 : Decl (BitVec 64) :=
.function { name := "charge_with_memory", inline := false, exported := false, params := [("base", Flapjack.Shape.one),
  ("start", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("size", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body458_6, returnShape := (Flapjack.Shape.one) }
def simplifiedData458 : Decl (BitVec 64) :=
.function { name := "charge_with_memory", inline := false, exported := false, params := [("base", Flapjack.Shape.one),
  ("start", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("size", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body458_10, returnShape := (Flapjack.Shape.one) }
def original458 := Pancake.PanLang.declToHOL originalData458
def simplified458 := Pancake.PanLang.declToHOL simplifiedData458
end InitECandidate.Proofs.FrontendStages.Declarations
