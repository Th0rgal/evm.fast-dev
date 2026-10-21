import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify341
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body357_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.global "sk_buf", Flapjack.Exp.var Flapjack.VarKind.local "addr",
    Flapjack.Exp.const 20#64]

def body357_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "sk_buf", Flapjack.Exp.const 20#64],
    Flapjack.Exp.var Flapjack.VarKind.local "key", Flapjack.Exp.const 32#64]

def body357_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.global "sk_buf")

def body357_3 : Prog (BitVec 64) :=
.seq body357_1 body357_2

def body357_4 : Prog (BitVec 64) :=
.seq body357_0 body357_3

def body357_5 : Prog (BitVec 64) :=
.seq body357_0 body357_1

def body357_6 : Prog (BitVec 64) :=
.seq body357_5 body357_2

def originalData357 : Decl (BitVec 64) :=
.function { name := "sk_make", inline := false, exported := false, params := [("addr", Flapjack.Shape.one), ("key", Flapjack.Shape.one)], body := body357_4, returnShape := (Flapjack.Shape.one) }
def simplifiedData357 : Decl (BitVec 64) :=
.function { name := "sk_make", inline := false, exported := false, params := [("addr", Flapjack.Shape.one), ("key", Flapjack.Shape.one)], body := body357_6, returnShape := (Flapjack.Shape.one) }
def original357 := Pancake.PanLang.declToHOL originalData357
def simplified357 := Pancake.PanLang.declToHOL simplifiedData357
end InitECandidate.Proofs.FrontendStages.Declarations
