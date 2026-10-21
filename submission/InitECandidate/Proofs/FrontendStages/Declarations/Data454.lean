import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify438
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body454_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 18446744073709551615#64)

def body454_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body454_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "sq"))
  (Flapjack.Exp.const 0#64)) body454_0 body454_1

def body454_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "a")

def body454_4 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("add_sat") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.const 3#64],
  Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "sq"))
    (Flapjack.Exp.const 9#64)]) body454_3

def body454_5 : Prog (BitVec 64) :=
.seq body454_2 body454_4

def body454_6 : Prog (BitVec 64) :=
.decCall ("sq") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("mul64x64") ([Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.var Flapjack.VarKind.local "w"]) body454_5

def body454_7 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("words_of") ([Flapjack.Exp.var Flapjack.VarKind.local "size"]) body454_6

def originalData454 : Decl (BitVec 64) :=
.function { name := "memory_gas_cost", inline := false, exported := false, params := [("size", Flapjack.Shape.one)], body := body454_7, returnShape := (Flapjack.Shape.one) }
def simplifiedData454 : Decl (BitVec 64) :=
.function { name := "memory_gas_cost", inline := false, exported := false, params := [("size", Flapjack.Shape.one)], body := body454_7, returnShape := (Flapjack.Shape.one) }
def original454 := Pancake.PanLang.declToHOL originalData454
def simplified454 := Pancake.PanLang.declToHOL simplifiedData454
end InitECandidate.Proofs.FrontendStages.Declarations
