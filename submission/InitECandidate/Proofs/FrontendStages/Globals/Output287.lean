import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data287
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate271
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody287_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "cached")

def globalBody287_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody287_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "cached") (Flapjack.Exp.const 0#64)) globalBody287_0 globalBody287_1

def globalBody287_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "r"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "r"), Flapjack.Exp.var Flapjack.VarKind.local "h"]

def globalBody287_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "h")

def globalBody287_5 : Prog (BitVec 64) :=
.seq globalBody287_3 globalBody287_4

def globalBody287_6 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "h")

def globalBody287_7 : Prog (BitVec 64) :=
.seq globalBody287_5 globalBody287_6

def globalBody287_8 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) globalBody287_7

def globalBody287_9 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("node_rlp") ([Flapjack.Exp.var Flapjack.VarKind.local "node"]) globalBody287_8

def globalBody287_10 : Prog (BitVec 64) :=
.seq globalBody287_2 globalBody287_9

def globalBody287_11 : Prog (BitVec 64) :=
.dec ("cached") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 24#64])) globalBody287_10

def globalData287 : Decl (BitVec 64) :=
.function { name := "node_hash", inline := false, exported := false, params := [("node", Flapjack.Shape.one)], body := globalBody287_11, returnShape := (Flapjack.Shape.one) }
def globalOutput287 := Pancake.PanLang.declToHOL globalData287
end InitECandidate.Proofs.FrontendStages.Declarations
