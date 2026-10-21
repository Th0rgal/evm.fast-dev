import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify251
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body267_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.var Flapjack.VarKind.local "key", Flapjack.Exp.var Flapjack.VarKind.local "klen",
    Flapjack.Exp.var Flapjack.VarKind.global "mpt_hash_scratch"]

def body267_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "key_to_nibbles"
  [Flapjack.Exp.var Flapjack.VarKind.global "mpt_hash_scratch", Flapjack.Exp.const 32#64,
    Flapjack.Exp.var Flapjack.VarKind.local "nb"]

def body267_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rStruct [Flapjack.Exp.var Flapjack.VarKind.local "nb", Flapjack.Exp.const 64#64])

def body267_3 : Prog (BitVec 64) :=
.seq body267_1 body267_2

def body267_4 : Prog (BitVec 64) :=
.decCall ("nb") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) body267_3

def body267_5 : Prog (BitVec 64) :=
.seq body267_0 body267_4

def body267_6 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body267_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 8#64]))
  (Flapjack.Exp.const 0#64)) body267_5 body267_6

def body267_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "key_to_nibbles"
  [Flapjack.Exp.var Flapjack.VarKind.local "key", Flapjack.Exp.var Flapjack.VarKind.local "klen",
    Flapjack.Exp.var Flapjack.VarKind.local "nb2"]

def body267_9 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.var Flapjack.VarKind.local "nb2",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "klen"]])

def body267_10 : Prog (BitVec 64) :=
.seq body267_8 body267_9

def body267_11 : Prog (BitVec 64) :=
.decCall ("nb2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "klen"]]) body267_10

def body267_12 : Prog (BitVec 64) :=
.seq body267_7 body267_11

def originalData267 : Decl (BitVec 64) :=
.function { name := "mpt_nibble_key", inline := false, exported := false, params := [("m", Flapjack.Shape.one), ("key", Flapjack.Shape.one), ("klen", Flapjack.Shape.one)], body := body267_12, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData267 : Decl (BitVec 64) :=
.function { name := "mpt_nibble_key", inline := false, exported := false, params := [("m", Flapjack.Shape.one), ("key", Flapjack.Shape.one), ("klen", Flapjack.Shape.one)], body := body267_12, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def original267 := Pancake.PanLang.declToHOL originalData267
def simplified267 := Pancake.PanLang.declToHOL simplifiedData267
end InitECandidate.Proofs.FrontendStages.Declarations
