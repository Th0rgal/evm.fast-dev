import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify521
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body537_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 2#64]

def body537_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push_word"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 56#64])]

def body537_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body537_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body537_4 : Prog (BitVec 64) :=
.seq body537_2 body537_3

def body537_5 : Prog (BitVec 64) :=
.seq body537_1 body537_4

def body537_6 : Prog (BitVec 64) :=
.seq body537_0 body537_5

def body537_7 : Prog (BitVec 64) :=
.seq body537_0 body537_1

def body537_8 : Prog (BitVec 64) :=
.seq body537_7 body537_2

def body537_9 : Prog (BitVec 64) :=
.seq body537_8 body537_3

def originalData537 : Decl (BitVec 64) :=
.function { name := "op_codesize", inline := false, exported := false, params := [], body := body537_6, returnShape := (Flapjack.Shape.one) }
def simplifiedData537 : Decl (BitVec 64) :=
.function { name := "op_codesize", inline := false, exported := false, params := [], body := body537_9, returnShape := (Flapjack.Shape.one) }
def original537 := Pancake.PanLang.declToHOL originalData537
def simplified537 := Pancake.PanLang.declToHOL simplifiedData537
end InitECandidate.Proofs.FrontendStages.Declarations
