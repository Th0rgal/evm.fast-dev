import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data659
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate641
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody659_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.var Flapjack.VarKind.local "a"]

def globalBody659_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody659_2 : Prog (BitVec 64) :=
.seq globalBody659_0 globalBody659_1

def globalBody659_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody659_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "fld") (Flapjack.Exp.const 12#64)) globalBody659_2 globalBody659_3

def globalBody659_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "d",
    Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "a"]

def globalBody659_6 : Prog (BitVec 64) :=
.seq globalBody659_4 globalBody659_5

def globalBody659_7 : Prog (BitVec 64) :=
.seq globalBody659_6 globalBody659_1

def globalData659 : Decl (BitVec 64) :=
.function { name := "fe_sqr", inline := false, exported := false, params := [("fld", Flapjack.Shape.one), ("d", Flapjack.Shape.one), ("a", Flapjack.Shape.one)], body := globalBody659_7, returnShape := (Flapjack.Shape.one) }
def globalOutput659 := Pancake.PanLang.declToHOL globalData659
end InitECandidate.Proofs.FrontendStages.Declarations
