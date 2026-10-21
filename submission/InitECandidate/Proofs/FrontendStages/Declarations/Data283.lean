import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify267
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body283_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "fb" (Flapjack.Exp.loadByte (Flapjack.Exp.var Flapjack.VarKind.local "p"))

def body283_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body283_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "n")) body283_0 body283_1

def body283_3 : Prog (BitVec 64) :=
Flapjack.Prog.call none "rlp_bytes_encoded_len"
  [Flapjack.Exp.var Flapjack.VarKind.local "fb", Flapjack.Exp.var Flapjack.VarKind.local "n"]

def body283_4 : Prog (BitVec 64) :=
.seq body283_2 body283_3

def body283_5 : Prog (BitVec 64) :=
.dec ("fb") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body283_4

def originalData283 : Decl (BitVec 64) :=
.function { name := "rlp_value_encoded_len", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body283_5, returnShape := (Flapjack.Shape.one) }
def simplifiedData283 : Decl (BitVec 64) :=
.function { name := "rlp_value_encoded_len", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body283_5, returnShape := (Flapjack.Shape.one) }
def original283 := Pancake.PanLang.declToHOL originalData283
def simplified283 := Pancake.PanLang.declToHOL simplifiedData283
end InitECandidate.Proofs.FrontendStages.Declarations
