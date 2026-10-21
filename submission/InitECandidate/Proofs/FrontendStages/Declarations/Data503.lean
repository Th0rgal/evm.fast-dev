import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify487
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body503_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 2#64]

def body503_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push_word"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 64#64])]

def body503_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body503_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body503_4 : Prog (BitVec 64) :=
.seq body503_2 body503_3

def body503_5 : Prog (BitVec 64) :=
.seq body503_1 body503_4

def body503_6 : Prog (BitVec 64) :=
.seq body503_0 body503_5

def body503_7 : Prog (BitVec 64) :=
.seq body503_0 body503_1

def body503_8 : Prog (BitVec 64) :=
.seq body503_7 body503_2

def body503_9 : Prog (BitVec 64) :=
.seq body503_8 body503_3

def originalData503 : Decl (BitVec 64) :=
.function { name := "op_gas", inline := false, exported := false, params := [], body := body503_6, returnShape := (Flapjack.Shape.one) }
def simplifiedData503 : Decl (BitVec 64) :=
.function { name := "op_gas", inline := false, exported := false, params := [], body := body503_9, returnShape := (Flapjack.Shape.one) }
def original503 := Pancake.PanLang.declToHOL originalData503
def simplified503 := Pancake.PanLang.declToHOL simplifiedData503
end InitECandidate.Proofs.FrontendStages.Declarations
