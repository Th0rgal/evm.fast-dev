import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify396
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body412_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 8#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "slot", Flapjack.Exp.const 1#64]

def body412_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body412_2 : Prog (BitVec 64) :=
.seq body412_0 body412_1

def body412_3 : Prog (BitVec 64) :=
.decCall ("ad") (Flapjack.Shape.one) ("bal_ensure_account") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body412_2

def originalData412 : Decl (BitVec 64) :=
.function { name := "add_storage_read", inline := false, exported := false, params := [("addr", Flapjack.Shape.one), ("slot", Flapjack.Shape.one)], body := body412_3, returnShape := (Flapjack.Shape.one) }
def simplifiedData412 : Decl (BitVec 64) :=
.function { name := "add_storage_read", inline := false, exported := false, params := [("addr", Flapjack.Shape.one), ("slot", Flapjack.Shape.one)], body := body412_3, returnShape := (Flapjack.Shape.one) }
def original412 := Pancake.PanLang.declToHOL originalData412
def simplified412 := Pancake.PanLang.declToHOL simplifiedData412
end InitECandidate.Proofs.FrontendStages.Declarations
