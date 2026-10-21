import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data288
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate272
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody288_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "out",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 128#64]),
    Flapjack.Exp.const 32#64]

def globalBody288_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody288_2 : Prog (BitVec 64) :=
.seq globalBody288_0 globalBody288_1

def globalBody288_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody288_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "root") (Flapjack.Exp.const 0#64)) globalBody288_2 globalBody288_3

def globalBody288_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 32#64]

def globalBody288_6 : Prog (BitVec 64) :=
.seq globalBody288_5 globalBody288_1

def globalBody288_7 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("node_hash") ([Flapjack.Exp.var Flapjack.VarKind.local "root"]) globalBody288_6

def globalBody288_8 : Prog (BitVec 64) :=
.seq globalBody288_4 globalBody288_7

def globalBody288_9 : Prog (BitVec 64) :=
.dec ("root") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 0#64])) globalBody288_8

def globalData288 : Decl (BitVec 64) :=
.function { name := "mpt_root", inline := false, exported := false, params := [("m", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := globalBody288_9, returnShape := (Flapjack.Shape.one) }
def globalOutput288 := Pancake.PanLang.declToHOL globalData288
end InitECandidate.Proofs.FrontendStages.Declarations
