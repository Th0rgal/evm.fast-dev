import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data262
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate246
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody262_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody262_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody262_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "is_empty") (Flapjack.Exp.const 0#64)) globalBody262_0 globalBody262_1

def globalBody262_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 1#64]

def globalBody262_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "r"))
  (Flapjack.Exp.const 0#64)) globalBody262_3 globalBody262_1

def globalBody262_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.var Flapjack.VarKind.local "root_hash",
    Flapjack.Exp.const 32#64]

def globalBody262_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "h")

def globalBody262_7 : Prog (BitVec 64) :=
.seq globalBody262_5 globalBody262_6

def globalBody262_8 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) globalBody262_7

def globalBody262_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "nd") (Flapjack.Exp.const 0#64)) globalBody262_8 globalBody262_1

def globalBody262_10 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "nd")

def globalBody262_11 : Prog (BitVec 64) :=
.seq globalBody262_9 globalBody262_10

def globalBody262_12 : Prog (BitVec 64) :=
.decCall ("nd") (Flapjack.Shape.one) ("_decode_witness_node") ([Flapjack.Exp.var Flapjack.VarKind.local "db", Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "r"),
  Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "r")]) globalBody262_11

def globalBody262_13 : Prog (BitVec 64) :=
.seq globalBody262_4 globalBody262_12

def globalBody262_14 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("nodedb_lookup") ([Flapjack.Exp.var Flapjack.VarKind.local "db", Flapjack.Exp.var Flapjack.VarKind.local "root_hash"]) globalBody262_13

def globalBody262_15 : Prog (BitVec 64) :=
.seq globalBody262_2 globalBody262_14

def globalBody262_16 : Prog (BitVec 64) :=
.decCall ("is_empty") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.var Flapjack.VarKind.local "root_hash",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 128#64]),
  Flapjack.Exp.const 32#64]) globalBody262_15

def globalData262 : Decl (BitVec 64) :=
.function { name := "decode_witness_to_mpt", inline := false, exported := false, params := [("db", Flapjack.Shape.one), ("root_hash", Flapjack.Shape.one)], body := globalBody262_16, returnShape := (Flapjack.Shape.one) }
def globalOutput262 := Pancake.PanLang.declToHOL globalData262
end InitECandidate.Proofs.FrontendStages.Declarations
