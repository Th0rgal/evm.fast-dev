import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify841
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body857_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_be32"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "hi4"]

def body857_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 4#64],
    Flapjack.Exp.var Flapjack.VarKind.local "mid8"]

def body857_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 12#64],
    Flapjack.Exp.var Flapjack.VarKind.local "lo8"]

def body857_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body857_4 : Prog (BitVec 64) :=
.seq body857_2 body857_3

def body857_5 : Prog (BitVec 64) :=
.seq body857_1 body857_4

def body857_6 : Prog (BitVec 64) :=
.seq body857_0 body857_5

def body857_7 : Prog (BitVec 64) :=
.seq body857_0 body857_1

def body857_8 : Prog (BitVec 64) :=
.seq body857_7 body857_2

def body857_9 : Prog (BitVec 64) :=
.seq body857_8 body857_3

def originalData857 : Decl (BitVec 64) :=
.function { name := "addr_from_words", inline := false, exported := false, params := [("out", Flapjack.Shape.one), ("hi4", Flapjack.Shape.one), ("mid8", Flapjack.Shape.one), ("lo8", Flapjack.Shape.one)], body := body857_6, returnShape := (Flapjack.Shape.one) }
def simplifiedData857 : Decl (BitVec 64) :=
.function { name := "addr_from_words", inline := false, exported := false, params := [("out", Flapjack.Shape.one), ("hi4", Flapjack.Shape.one), ("mid8", Flapjack.Shape.one), ("lo8", Flapjack.Shape.one)], body := body857_9, returnShape := (Flapjack.Shape.one) }
def original857 := Pancake.PanLang.declToHOL originalData857
def simplified857 := Pancake.PanLang.declToHOL simplifiedData857
end InitECandidate.Proofs.FrontendStages.Declarations
