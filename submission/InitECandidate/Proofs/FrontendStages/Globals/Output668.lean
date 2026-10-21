import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data668
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate652
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody668_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_set_one"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "pt"]

def globalBody668_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_set_one"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "pt", Flapjack.Exp.var Flapjack.VarKind.local "esz"]]

def globalBody668_2 : Prog (BitVec 64) :=
.seq globalBody668_0 globalBody668_1

def globalBody668_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_set_zero"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "pt",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]]

def globalBody668_4 : Prog (BitVec 64) :=
.seq globalBody668_2 globalBody668_3

def globalBody668_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody668_6 : Prog (BitVec 64) :=
.seq globalBody668_4 globalBody668_5

def globalBody668_7 : Prog (BitVec 64) :=
.dec ("esz") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.const 32#64]) globalBody668_6

def globalData668 : Decl (BitVec 64) :=
.function { name := "ecp_set_inf", inline := false, exported := false, params := [("fld", Flapjack.Shape.one), ("pt", Flapjack.Shape.one)], body := globalBody668_7, returnShape := (Flapjack.Shape.one) }
def globalOutput668 := Pancake.PanLang.declToHOL globalData668
end InitECandidate.Proofs.FrontendStages.Declarations
