import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify425
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body441_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_be32"
  [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "v")]

def body441_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 4#64],
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "v")]

def body441_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 12#64],
    Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "v")]

def body441_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "a")

def body441_4 : Prog (BitVec 64) :=
.seq body441_2 body441_3

def body441_5 : Prog (BitVec 64) :=
.seq body441_1 body441_4

def body441_6 : Prog (BitVec 64) :=
.seq body441_0 body441_5

def body441_7 : Prog (BitVec 64) :=
.dec ("a") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 240#64]) body441_6

def body441_8 : Prog (BitVec 64) :=
.seq body441_0 body441_1

def body441_9 : Prog (BitVec 64) :=
.seq body441_8 body441_2

def body441_10 : Prog (BitVec 64) :=
.seq body441_9 body441_3

def body441_11 : Prog (BitVec 64) :=
.dec ("a") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 240#64]) body441_10

def originalData441 : Decl (BitVec 64) :=
.function { name := "to_address_masked", inline := false, exported := false, params := [("v", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body441_7, returnShape := (Flapjack.Shape.one) }
def simplifiedData441 : Decl (BitVec 64) :=
.function { name := "to_address_masked", inline := false, exported := false, params := [("v", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body441_11, returnShape := (Flapjack.Shape.one) }
def original441 := Pancake.PanLang.declToHOL originalData441
def simplified441 := Pancake.PanLang.declToHOL simplifiedData441
end InitECandidate.Proofs.FrontendStages.Declarations
