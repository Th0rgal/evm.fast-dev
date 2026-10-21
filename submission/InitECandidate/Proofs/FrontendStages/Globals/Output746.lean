import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data746
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate730
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody746_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_set_one" [Flapjack.Exp.var Flapjack.VarKind.local "one"]

def globalBody746_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody746_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "e")

def globalBody746_3 : Prog (BitVec 64) :=
.seq globalBody746_1 globalBody746_2

def globalBody746_4 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "one", Flapjack.Exp.const 576#64]) globalBody746_3

def globalBody746_5 : Prog (BitVec 64) :=
.seq globalBody746_0 globalBody746_4

def globalBody746_6 : Prog (BitVec 64) :=
.decCall ("one") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 576#64]) globalBody746_5

def globalBody746_7 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody746_6

def globalData746 : Decl (BitVec 64) :=
.function { name := "fp12_is_one", inline := false, exported := false, params := [("a", Flapjack.Shape.one)], body := globalBody746_7, returnShape := (Flapjack.Shape.one) }
def globalOutput746 := Pancake.PanLang.declToHOL globalData746
end InitECandidate.Proofs.FrontendStages.Declarations
