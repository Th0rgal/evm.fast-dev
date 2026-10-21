import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify751
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body767_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_set_one" [Flapjack.Exp.var Flapjack.VarKind.local "r"]

def body767_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_set_one"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64]]

def body767_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_set_zero"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 192#64]]

def body767_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body767_4 : Prog (BitVec 64) :=
.seq body767_2 body767_3

def body767_5 : Prog (BitVec 64) :=
.seq body767_1 body767_4

def body767_6 : Prog (BitVec 64) :=
.seq body767_0 body767_5

def body767_7 : Prog (BitVec 64) :=
.seq body767_0 body767_1

def body767_8 : Prog (BitVec 64) :=
.seq body767_7 body767_2

def body767_9 : Prog (BitVec 64) :=
.seq body767_8 body767_3

def originalData767 : Decl (BitVec 64) :=
.function { name := "g2_set_inf", inline := false, exported := false, params := [("r", Flapjack.Shape.one)], body := body767_6, returnShape := (Flapjack.Shape.one) }
def simplifiedData767 : Decl (BitVec 64) :=
.function { name := "g2_set_inf", inline := false, exported := false, params := [("r", Flapjack.Shape.one)], body := body767_9, returnShape := (Flapjack.Shape.one) }
def original767 := Pancake.PanLang.declToHOL originalData767
def simplified767 := Pancake.PanLang.declToHOL simplifiedData767
end InitECandidate.Proofs.FrontendStages.Declarations
