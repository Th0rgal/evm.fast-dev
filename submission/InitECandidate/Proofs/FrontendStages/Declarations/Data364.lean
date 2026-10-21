import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify348
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body364_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.global "empty_trie_root")

def body364_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body364_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "a") (Flapjack.Exp.const 1#64)) body364_0 body364_1

def body364_3 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 40#64]))

def body364_4 : Prog (BitVec 64) :=
.seq body364_2 body364_3

def body364_5 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("ws_get_account_optional") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body364_4

def originalData364 : Decl (BitVec 64) :=
.function { name := "ws_storage_root_of", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body364_5, returnShape := (Flapjack.Shape.one) }
def simplifiedData364 : Decl (BitVec 64) :=
.function { name := "ws_storage_root_of", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body364_5, returnShape := (Flapjack.Shape.one) }
def original364 := Pancake.PanLang.declToHOL originalData364
def simplified364 := Pancake.PanLang.declToHOL simplifiedData364
end InitECandidate.Proofs.FrontendStages.Declarations
