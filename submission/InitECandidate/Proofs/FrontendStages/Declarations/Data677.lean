import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify661
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body677_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body677_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "i")

def body677_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body677_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64)) body677_1 body677_2

def body677_4 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("is_zero_bytes") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "a",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 32#64]],
  Flapjack.Exp.const 32#64]) body677_3

def body677_5 : Prog (BitVec 64) :=
.seq body677_0 body677_4

def body677_6 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "i")) body677_5

def body677_7 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.const 0#64, Flapjack.Exp.const 1#64])

def body677_8 : Prog (BitVec 64) :=
.seq body677_6 body677_7

def body677_9 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "n") body677_8

def originalData677 : Decl (BitVec 64) :=
.function { name := "fq_poly_deg", inline := false, exported := false, params := [("a", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body677_9, returnShape := (Flapjack.Shape.one) }
def simplifiedData677 : Decl (BitVec 64) :=
.function { name := "fq_poly_deg", inline := false, exported := false, params := [("a", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body677_9, returnShape := (Flapjack.Shape.one) }
def original677 := Pancake.PanLang.declToHOL originalData677
def simplified677 := Pancake.PanLang.declToHOL simplifiedData677
end InitECandidate.Proofs.FrontendStages.Declarations
