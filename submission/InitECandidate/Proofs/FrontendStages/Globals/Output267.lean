import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data267
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate251
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody267_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.var Flapjack.VarKind.local "key", Flapjack.Exp.var Flapjack.VarKind.local "klen",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 152#64])]

def globalBody267_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "key_to_nibbles"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 152#64]),
    Flapjack.Exp.const 32#64, Flapjack.Exp.var Flapjack.VarKind.local "nb"]

def globalBody267_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rStruct [Flapjack.Exp.var Flapjack.VarKind.local "nb", Flapjack.Exp.const 64#64])

def globalBody267_3 : Prog (BitVec 64) :=
.seq globalBody267_1 globalBody267_2

def globalBody267_4 : Prog (BitVec 64) :=
.decCall ("nb") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) globalBody267_3

def globalBody267_5 : Prog (BitVec 64) :=
.seq globalBody267_0 globalBody267_4

def globalBody267_6 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody267_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 8#64]))
  (Flapjack.Exp.const 0#64)) globalBody267_5 globalBody267_6

def globalBody267_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "key_to_nibbles"
  [Flapjack.Exp.var Flapjack.VarKind.local "key", Flapjack.Exp.var Flapjack.VarKind.local "klen",
    Flapjack.Exp.var Flapjack.VarKind.local "nb2"]

def globalBody267_9 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.var Flapjack.VarKind.local "nb2",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "klen"]])

def globalBody267_10 : Prog (BitVec 64) :=
.seq globalBody267_8 globalBody267_9

def globalBody267_11 : Prog (BitVec 64) :=
.decCall ("nb2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "klen"]]) globalBody267_10

def globalBody267_12 : Prog (BitVec 64) :=
.seq globalBody267_7 globalBody267_11

def globalData267 : Decl (BitVec 64) :=
.function { name := "mpt_nibble_key", inline := false, exported := false, params := [("m", Flapjack.Shape.one), ("key", Flapjack.Shape.one), ("klen", Flapjack.Shape.one)], body := globalBody267_12, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def globalOutput267 := Pancake.PanLang.declToHOL globalData267
end InitECandidate.Proofs.FrontendStages.Declarations
