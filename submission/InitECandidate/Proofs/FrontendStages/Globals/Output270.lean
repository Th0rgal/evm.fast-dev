import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data270
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate254
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody270_0 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "vptr")

def globalBody270_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "vlen")

def globalBody270_2 : Prog (BitVec 64) :=
.seq globalBody270_0 globalBody270_1

def globalBody270_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "node")

def globalBody270_4 : Prog (BitVec 64) :=
.seq globalBody270_2 globalBody270_3

def globalBody270_5 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody270_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) globalBody270_4 globalBody270_5

def globalBody270_7 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.var Flapjack.VarKind.local "ek", Flapjack.Exp.var Flapjack.VarKind.local "rk",
  Flapjack.Exp.var Flapjack.VarKind.local "el"]) globalBody270_6

def globalBody270_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "el")
  (Flapjack.Exp.var Flapjack.VarKind.local "rl")) globalBody270_7 globalBody270_5

def globalBody270_9 : Prog (BitVec 64) :=
Flapjack.Prog.call none "node_new_ext"
  [Flapjack.Exp.var Flapjack.VarKind.local "ek", Flapjack.Exp.var Flapjack.VarKind.local "pl",
    Flapjack.Exp.var Flapjack.VarKind.local "br"]

def globalBody270_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "pl")) globalBody270_9 globalBody270_5

def globalBody270_11 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "br")

def globalBody270_12 : Prog (BitVec 64) :=
.seq globalBody270_10 globalBody270_11

def globalBody270_13 : Prog (BitVec 64) :=
.decCall ("br") (Flapjack.Shape.one) ("_create_branch_from_two_leaves") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "ek", Flapjack.Exp.var Flapjack.VarKind.local "pl"],
  Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "el", Flapjack.Exp.var Flapjack.VarKind.local "pl"],
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 48#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 56#64]),
  Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "rk", Flapjack.Exp.var Flapjack.VarKind.local "pl"],
  Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "rl", Flapjack.Exp.var Flapjack.VarKind.local "pl"],
  Flapjack.Exp.var Flapjack.VarKind.local "vptr", Flapjack.Exp.var Flapjack.VarKind.local "vlen"]) globalBody270_12

def globalBody270_14 : Prog (BitVec 64) :=
.decCall ("pl") (Flapjack.Shape.one) ("common_prefix_length") ([Flapjack.Exp.var Flapjack.VarKind.local "ek", Flapjack.Exp.var Flapjack.VarKind.local "el",
  Flapjack.Exp.var Flapjack.VarKind.local "rk", Flapjack.Exp.var Flapjack.VarKind.local "rl"]) globalBody270_13

def globalBody270_15 : Prog (BitVec 64) :=
.seq globalBody270_8 globalBody270_14

def globalBody270_16 : Prog (BitVec 64) :=
.dec ("el") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 40#64])) globalBody270_15

def globalBody270_17 : Prog (BitVec 64) :=
.dec ("ek") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 32#64])) globalBody270_16

def globalData270 : Decl (BitVec 64) :=
.function { name := "_insert_into_leaf", inline := false, exported := false, params := [("node", Flapjack.Shape.one), ("rk", Flapjack.Shape.one), ("rl", Flapjack.Shape.one), ("vptr", Flapjack.Shape.one),
  ("vlen", Flapjack.Shape.one)], body := globalBody270_17, returnShape := (Flapjack.Shape.one) }
def globalOutput270 := Pancake.PanLang.declToHOL globalData270
end InitECandidate.Proofs.FrontendStages.Declarations
