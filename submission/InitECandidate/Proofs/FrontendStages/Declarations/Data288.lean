import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify272
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body288_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.global "empty_trie_root",
    Flapjack.Exp.const 32#64]

def body288_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body288_2 : Prog (BitVec 64) :=
.seq body288_0 body288_1

def body288_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body288_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "root") (Flapjack.Exp.const 0#64)) body288_2 body288_3

def body288_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 32#64]

def body288_6 : Prog (BitVec 64) :=
.seq body288_5 body288_1

def body288_7 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("node_hash") ([Flapjack.Exp.var Flapjack.VarKind.local "root"]) body288_6

def body288_8 : Prog (BitVec 64) :=
.seq body288_4 body288_7

def body288_9 : Prog (BitVec 64) :=
.dec ("root") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 0#64])) body288_8

def originalData288 : Decl (BitVec 64) :=
.function { name := "mpt_root", inline := false, exported := false, params := [("m", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body288_9, returnShape := (Flapjack.Shape.one) }
def simplifiedData288 : Decl (BitVec 64) :=
.function { name := "mpt_root", inline := false, exported := false, params := [("m", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body288_9, returnShape := (Flapjack.Shape.one) }
def original288 := Pancake.PanLang.declToHOL originalData288
def simplified288 := Pancake.PanLang.declToHOL simplifiedData288
end InitECandidate.Proofs.FrontendStages.Declarations
