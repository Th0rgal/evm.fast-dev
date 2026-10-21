import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data778
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate762
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody778_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
        Flapjack.Exp.const 1344#64],
    Flapjack.Exp.const 4#64]

def globalBody778_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody778_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "inf")

def globalBody778_3 : Prog (BitVec 64) :=
.seq globalBody778_1 globalBody778_2

def globalBody778_4 : Prog (BitVec 64) :=
.decCall ("inf") (Flapjack.Shape.one) ("g2_is_inf") ([Flapjack.Exp.var Flapjack.VarKind.local "t"]) globalBody778_3

def globalBody778_5 : Prog (BitVec 64) :=
.seq globalBody778_0 globalBody778_4

def globalBody778_6 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) globalBody778_5

def globalBody778_7 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody778_6

def globalData778 : Decl (BitVec 64) :=
.function { name := "g2_subgroup_check", inline := false, exported := false, params := [("p", Flapjack.Shape.one)], body := globalBody778_7, returnShape := (Flapjack.Shape.one) }
def globalOutput778 := Pancake.PanLang.declToHOL globalData778
end InitECandidate.Proofs.FrontendStages.Declarations
