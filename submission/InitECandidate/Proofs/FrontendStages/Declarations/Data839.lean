import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify823
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body839_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.global "empty_trie_root")

def body839_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body839_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "has") (Flapjack.Exp.const 0#64)) body839_0 body839_1

def body839_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "r")

def body839_4 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.one) ("ws_storage_root_of") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body839_3

def body839_5 : Prog (BitVec 64) :=
.seq body839_2 body839_4

def body839_6 : Prog (BitVec 64) :=
.decCall ("has") (Flapjack.Shape.one) ("htab_has") ([Flapjack.Exp.var Flapjack.VarKind.local "cache", Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body839_5

def originalData839 : Decl (BitVec 64) :=
.function { name := "cache_get_root", inline := false, exported := false, params := [("cache", Flapjack.Shape.one), ("addr", Flapjack.Shape.one)], body := body839_6, returnShape := (Flapjack.Shape.one) }
def simplifiedData839 : Decl (BitVec 64) :=
.function { name := "cache_get_root", inline := false, exported := false, params := [("cache", Flapjack.Shape.one), ("addr", Flapjack.Shape.one)], body := body839_6, returnShape := (Flapjack.Shape.one) }
def original839 := Pancake.PanLang.declToHOL originalData839
def simplified839 := Pancake.PanLang.declToHOL simplifiedData839
end InitECandidate.Proofs.FrontendStages.Declarations
