import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify486
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body502_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 2#64]

def body502_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push_word"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 0#64])]

def body502_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body502_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body502_4 : Prog (BitVec 64) :=
.seq body502_2 body502_3

def body502_5 : Prog (BitVec 64) :=
.seq body502_1 body502_4

def body502_6 : Prog (BitVec 64) :=
.seq body502_0 body502_5

def body502_7 : Prog (BitVec 64) :=
.seq body502_0 body502_1

def body502_8 : Prog (BitVec 64) :=
.seq body502_7 body502_2

def body502_9 : Prog (BitVec 64) :=
.seq body502_8 body502_3

def originalData502 : Decl (BitVec 64) :=
.function { name := "op_pc", inline := false, exported := false, params := [], body := body502_6, returnShape := (Flapjack.Shape.one) }
def simplifiedData502 : Decl (BitVec 64) :=
.function { name := "op_pc", inline := false, exported := false, params := [], body := body502_9, returnShape := (Flapjack.Shape.one) }
def original502 := Pancake.PanLang.declToHOL originalData502
def simplified502 := Pancake.PanLang.declToHOL simplifiedData502
end InitECandidate.Proofs.FrontendStages.Declarations
