import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify261
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body277_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "root"), none)) "_mpt_delete_node"
  [Flapjack.Exp.var Flapjack.VarKind.local "root", Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "nk"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "nk"), Flapjack.Exp.const 0#64]

def body277_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "root"), none)) "_mpt_insert_node"
  [Flapjack.Exp.var Flapjack.VarKind.local "root", Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "nk"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "nk"), Flapjack.Exp.const 0#64,
    Flapjack.Exp.var Flapjack.VarKind.local "vptr", Flapjack.Exp.var Flapjack.VarKind.local "vlen"]

def body277_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "vptr") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "vlen") (Flapjack.Exp.const 0#64)])) body277_0 body277_1

def body277_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "root")

def body277_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body277_5 : Prog (BitVec 64) :=
.seq body277_3 body277_4

def body277_6 : Prog (BitVec 64) :=
.seq body277_2 body277_5

def body277_7 : Prog (BitVec 64) :=
.dec ("root") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 0#64])) body277_6

def body277_8 : Prog (BitVec 64) :=
.decCall ("nk") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("mpt_nibble_key") ([Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.var Flapjack.VarKind.local "key",
  Flapjack.Exp.var Flapjack.VarKind.local "klen"]) body277_7

def body277_9 : Prog (BitVec 64) :=
.seq body277_2 body277_3

def body277_10 : Prog (BitVec 64) :=
.seq body277_9 body277_4

def body277_11 : Prog (BitVec 64) :=
.dec ("root") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 0#64])) body277_10

def body277_12 : Prog (BitVec 64) :=
.decCall ("nk") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("mpt_nibble_key") ([Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.var Flapjack.VarKind.local "key",
  Flapjack.Exp.var Flapjack.VarKind.local "klen"]) body277_11

def originalData277 : Decl (BitVec 64) :=
.function { name := "mpt_set", inline := false, exported := false, params := [("m", Flapjack.Shape.one), ("key", Flapjack.Shape.one), ("klen", Flapjack.Shape.one), ("vptr", Flapjack.Shape.one),
  ("vlen", Flapjack.Shape.one)], body := body277_8, returnShape := (Flapjack.Shape.one) }
def simplifiedData277 : Decl (BitVec 64) :=
.function { name := "mpt_set", inline := false, exported := false, params := [("m", Flapjack.Shape.one), ("key", Flapjack.Shape.one), ("klen", Flapjack.Shape.one), ("vptr", Flapjack.Shape.one),
  ("vlen", Flapjack.Shape.one)], body := body277_12, returnShape := (Flapjack.Shape.one) }
def original277 := Pancake.PanLang.declToHOL originalData277
def simplified277 := Pancake.PanLang.declToHOL simplifiedData277
end InitECandidate.Proofs.FrontendStages.Declarations
