import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify209
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body225_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body225_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "w")

def body225_2 : Prog (BitVec 64) :=
.seq body225_0 body225_1

def body225_3 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("rlp_encode_bytes") ([Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.var Flapjack.VarKind.local "tmp",
  Flapjack.Exp.var Flapjack.VarKind.local "n"]) body225_2

def body225_4 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("u256_to_be_min") ([Flapjack.Exp.var Flapjack.VarKind.local "v", Flapjack.Exp.var Flapjack.VarKind.local "tmp"]) body225_3

def body225_5 : Prog (BitVec 64) :=
.decCall ("tmp") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body225_4

def body225_6 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body225_5

def originalData225 : Decl (BitVec 64) :=
.function { name := "rlp_put_u256", inline := false, exported := false, params := [("dst", Flapjack.Shape.one),
  ("v", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body225_6, returnShape := (Flapjack.Shape.one) }
def simplifiedData225 : Decl (BitVec 64) :=
.function { name := "rlp_put_u256", inline := false, exported := false, params := [("dst", Flapjack.Shape.one),
  ("v", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body225_6, returnShape := (Flapjack.Shape.one) }
def original225 := Pancake.PanLang.declToHOL originalData225
def simplified225 := Pancake.PanLang.declToHOL simplifiedData225
end InitECandidate.Proofs.FrontendStages.Declarations
