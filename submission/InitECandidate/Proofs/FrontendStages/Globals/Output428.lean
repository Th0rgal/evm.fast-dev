import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data428
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate412
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody428_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "sort_elems"
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "k"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "k"), Flapjack.Exp.const 32#64,
    Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "tmp"]

def globalBody428_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "k")

def globalBody428_2 : Prog (BitVec 64) :=
.seq globalBody428_0 globalBody428_1

def globalBody428_3 : Prog (BitVec 64) :=
.decCall ("k") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_keys") ([Flapjack.Exp.var Flapjack.VarKind.local "t"]) globalBody428_2

def globalData428 : Decl (BitVec 64) :=
.function { name := "sorted_keys32", inline := false, exported := false, params := [("t", Flapjack.Shape.one), ("tmp", Flapjack.Shape.one)], body := globalBody428_3, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def globalOutput428 := Pancake.PanLang.declToHOL globalData428
end InitECandidate.Proofs.FrontendStages.Declarations
