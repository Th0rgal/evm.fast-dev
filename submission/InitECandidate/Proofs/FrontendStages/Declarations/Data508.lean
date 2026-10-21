import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify492
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body508_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 2#64]

def body508_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push_word"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 32#64])]

def body508_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body508_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body508_4 : Prog (BitVec 64) :=
.seq body508_2 body508_3

def body508_5 : Prog (BitVec 64) :=
.seq body508_1 body508_4

def body508_6 : Prog (BitVec 64) :=
.seq body508_0 body508_5

def body508_7 : Prog (BitVec 64) :=
.seq body508_0 body508_1

def body508_8 : Prog (BitVec 64) :=
.seq body508_7 body508_2

def body508_9 : Prog (BitVec 64) :=
.seq body508_8 body508_3

def originalData508 : Decl (BitVec 64) :=
.function { name := "op_msize", inline := false, exported := false, params := [], body := body508_6, returnShape := (Flapjack.Shape.one) }
def simplifiedData508 : Decl (BitVec 64) :=
.function { name := "op_msize", inline := false, exported := false, params := [], body := body508_9, returnShape := (Flapjack.Shape.one) }
def original508 := Pancake.PanLang.declToHOL originalData508
def simplified508 := Pancake.PanLang.declToHOL simplifiedData508
end InitECandidate.Proofs.FrontendStages.Declarations
