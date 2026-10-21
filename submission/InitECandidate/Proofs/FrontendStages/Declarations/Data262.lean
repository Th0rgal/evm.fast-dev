import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify246
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body262_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body262_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body262_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "is_empty") (Flapjack.Exp.const 0#64)) body262_0 body262_1

def body262_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 1#64]

def body262_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "r"))
  (Flapjack.Exp.const 0#64)) body262_3 body262_1

def body262_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.var Flapjack.VarKind.local "root_hash",
    Flapjack.Exp.const 32#64]

def body262_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "h")

def body262_7 : Prog (BitVec 64) :=
.seq body262_5 body262_6

def body262_8 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body262_7

def body262_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "nd") (Flapjack.Exp.const 0#64)) body262_8 body262_1

def body262_10 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "nd")

def body262_11 : Prog (BitVec 64) :=
.seq body262_9 body262_10

def body262_12 : Prog (BitVec 64) :=
.decCall ("nd") (Flapjack.Shape.one) ("_decode_witness_node") ([Flapjack.Exp.var Flapjack.VarKind.local "db", Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "r"),
  Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "r")]) body262_11

def body262_13 : Prog (BitVec 64) :=
.seq body262_4 body262_12

def body262_14 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("nodedb_lookup") ([Flapjack.Exp.var Flapjack.VarKind.local "db", Flapjack.Exp.var Flapjack.VarKind.local "root_hash"]) body262_13

def body262_15 : Prog (BitVec 64) :=
.seq body262_2 body262_14

def body262_16 : Prog (BitVec 64) :=
.decCall ("is_empty") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.var Flapjack.VarKind.local "root_hash", Flapjack.Exp.var Flapjack.VarKind.global "empty_trie_root",
  Flapjack.Exp.const 32#64]) body262_15

def originalData262 : Decl (BitVec 64) :=
.function { name := "decode_witness_to_mpt", inline := false, exported := false, params := [("db", Flapjack.Shape.one), ("root_hash", Flapjack.Shape.one)], body := body262_16, returnShape := (Flapjack.Shape.one) }
def simplifiedData262 : Decl (BitVec 64) :=
.function { name := "decode_witness_to_mpt", inline := false, exported := false, params := [("db", Flapjack.Shape.one), ("root_hash", Flapjack.Shape.one)], body := body262_16, returnShape := (Flapjack.Shape.one) }
def original262 := Pancake.PanLang.declToHOL originalData262
def simplified262 := Pancake.PanLang.declToHOL simplifiedData262
end InitECandidate.Proofs.FrontendStages.Declarations
