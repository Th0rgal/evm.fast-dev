import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify347
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body363_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body363_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body363_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "leaf"))
  (Flapjack.Exp.const 0#64)) body363_0 body363_1

def body363_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "decode_account_from_leaf"
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "leaf"),
    Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "leaf"), Flapjack.Exp.var Flapjack.VarKind.local "a"]

def body363_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "a")

def body363_5 : Prog (BitVec 64) :=
.seq body363_3 body363_4

def body363_6 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 56#64]) body363_5

def body363_7 : Prog (BitVec 64) :=
.seq body363_2 body363_6

def body363_8 : Prog (BitVec 64) :=
.decCall ("leaf") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("ws_account_leaf") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body363_7

def originalData363 : Decl (BitVec 64) :=
.function { name := "ws_get_account_optional", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body363_8, returnShape := (Flapjack.Shape.one) }
def simplifiedData363 : Decl (BitVec 64) :=
.function { name := "ws_get_account_optional", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body363_8, returnShape := (Flapjack.Shape.one) }
def original363 := Pancake.PanLang.declToHOL originalData363
def simplified363 := Pancake.PanLang.declToHOL simplifiedData363
end InitECandidate.Proofs.FrontendStages.Declarations
