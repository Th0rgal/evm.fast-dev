import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data880
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate864
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody880_0 : Prog (BitVec 64) :=
Flapjack.Prog.call
  (some
    (none,
      some
        ("MptErr", "e",
          Flapjack.Prog.seq
            (Flapjack.Prog.shMemStore Flapjack.OpSize.op8
              (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.const 2688614400#64, Flapjack.Exp.const 70#64])
              (Flapjack.Exp.var Flapjack.VarKind.local "e"))
            (Flapjack.Prog.raise "Fail" (Flapjack.Exp.const 4#64)))))
  "attempt_l3" [Flapjack.Exp.var Flapjack.VarKind.local "si"]

def globalBody880_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody880_2 : Prog (BitVec 64) :=
.seq globalBody880_0 globalBody880_1

def globalBody880_3 : Prog (BitVec 64) :=
.dec ("e") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody880_2

def globalData880 : Decl (BitVec 64) :=
.function { name := "attempt_l4", inline := false, exported := false, params := [("si", Flapjack.Shape.one)], body := globalBody880_3, returnShape := (Flapjack.Shape.one) }
def globalOutput880 := Pancake.PanLang.declToHOL globalData880
end InitECandidate.Proofs.FrontendStages.Declarations
