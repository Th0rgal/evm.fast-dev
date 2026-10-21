import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data766
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate750
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody766_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
        Flapjack.Exp.const 1344#64],
    Flapjack.Exp.const 4#64]

def globalBody766_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody766_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "inf")

def globalBody766_3 : Prog (BitVec 64) :=
.seq globalBody766_1 globalBody766_2

def globalBody766_4 : Prog (BitVec 64) :=
.decCall ("inf") (Flapjack.Shape.one) ("g1_is_inf") ([Flapjack.Exp.var Flapjack.VarKind.local "t"]) globalBody766_3

def globalBody766_5 : Prog (BitVec 64) :=
.seq globalBody766_0 globalBody766_4

def globalBody766_6 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) globalBody766_5

def globalBody766_7 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody766_6

def globalData766 : Decl (BitVec 64) :=
.function { name := "g1_subgroup_check", inline := false, exported := false, params := [("p", Flapjack.Shape.one)], body := globalBody766_7, returnShape := (Flapjack.Shape.one) }
def globalOutput766 := Pancake.PanLang.declToHOL globalData766
end InitECandidate.Proofs.FrontendStages.Declarations
