import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify342
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body358_0 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "nonce")

def body358_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "balance")

def body358_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.var Flapjack.VarKind.global "empty_trie_root")

def body358_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "code_hash")

def body358_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "a")

def body358_5 : Prog (BitVec 64) :=
.seq body358_3 body358_4

def body358_6 : Prog (BitVec 64) :=
.seq body358_2 body358_5

def body358_7 : Prog (BitVec 64) :=
.seq body358_1 body358_6

def body358_8 : Prog (BitVec 64) :=
.seq body358_0 body358_7

def body358_9 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 56#64]) body358_8

def body358_10 : Prog (BitVec 64) :=
.seq body358_0 body358_1

def body358_11 : Prog (BitVec 64) :=
.seq body358_10 body358_2

def body358_12 : Prog (BitVec 64) :=
.seq body358_11 body358_3

def body358_13 : Prog (BitVec 64) :=
.seq body358_12 body358_4

def body358_14 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 56#64]) body358_13

def originalData358 : Decl (BitVec 64) :=
.function { name := "acct_new", inline := false, exported := false, params := [("nonce", Flapjack.Shape.one),
  ("balance", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("code_hash", Flapjack.Shape.one)], body := body358_9, returnShape := (Flapjack.Shape.one) }
def simplifiedData358 : Decl (BitVec 64) :=
.function { name := "acct_new", inline := false, exported := false, params := [("nonce", Flapjack.Shape.one),
  ("balance", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("code_hash", Flapjack.Shape.one)], body := body358_14, returnShape := (Flapjack.Shape.one) }
def original358 := Pancake.PanLang.declToHOL originalData358
def simplified358 := Pancake.PanLang.declToHOL simplifiedData358
end InitECandidate.Proofs.FrontendStages.Declarations
