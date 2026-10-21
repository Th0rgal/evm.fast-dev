import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify721
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body737_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_set_one" [Flapjack.Exp.var Flapjack.VarKind.local "r"]

def body737_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_set_zero"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64]]

def body737_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_set_zero"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 192#64]]

def body737_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body737_4 : Prog (BitVec 64) :=
.seq body737_2 body737_3

def body737_5 : Prog (BitVec 64) :=
.seq body737_1 body737_4

def body737_6 : Prog (BitVec 64) :=
.seq body737_0 body737_5

def body737_7 : Prog (BitVec 64) :=
.seq body737_0 body737_1

def body737_8 : Prog (BitVec 64) :=
.seq body737_7 body737_2

def body737_9 : Prog (BitVec 64) :=
.seq body737_8 body737_3

def originalData737 : Decl (BitVec 64) :=
.function { name := "fp6_set_one", inline := false, exported := false, params := [("r", Flapjack.Shape.one)], body := body737_6, returnShape := (Flapjack.Shape.one) }
def simplifiedData737 : Decl (BitVec 64) :=
.function { name := "fp6_set_one", inline := false, exported := false, params := [("r", Flapjack.Shape.one)], body := body737_9, returnShape := (Flapjack.Shape.one) }
def original737 := Pancake.PanLang.declToHOL originalData737
def simplified737 := Pancake.PanLang.declToHOL simplifiedData737
end InitECandidate.Proofs.FrontendStages.Declarations
