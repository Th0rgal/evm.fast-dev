import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify494
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body510_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 2#64]

def body510_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body510_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body510_3 : Prog (BitVec 64) :=
.seq body510_1 body510_2

def body510_4 : Prog (BitVec 64) :=
.seq body510_0 body510_3

def body510_5 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body510_4

def body510_6 : Prog (BitVec 64) :=
.seq body510_0 body510_1

def body510_7 : Prog (BitVec 64) :=
.seq body510_6 body510_2

def body510_8 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body510_7

def originalData510 : Decl (BitVec 64) :=
.function { name := "op_pop", inline := false, exported := false, params := [], body := body510_5, returnShape := (Flapjack.Shape.one) }
def simplifiedData510 : Decl (BitVec 64) :=
.function { name := "op_pop", inline := false, exported := false, params := [], body := body510_8, returnShape := (Flapjack.Shape.one) }
def original510 := Pancake.PanLang.declToHOL originalData510
def simplified510 := Pancake.PanLang.declToHOL simplifiedData510
end InitECandidate.Proofs.FrontendStages.Declarations
