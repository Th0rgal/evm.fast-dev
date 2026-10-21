import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data877
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate861
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody877_0 : Prog (BitVec 64) :=
Flapjack.Prog.call
  (some
    (none,
      some
        ("BlockErr", "e",
          Flapjack.Prog.seq
            (Flapjack.Prog.shMemStore Flapjack.OpSize.op8
              (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.const 2688614400#64, Flapjack.Exp.const 70#64])
              (Flapjack.Exp.var Flapjack.VarKind.local "e"))
            (Flapjack.Prog.raise "Fail" (Flapjack.Exp.const 1#64)))))
  "run_attempt" [Flapjack.Exp.var Flapjack.VarKind.local "si"]

def globalBody877_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody877_2 : Prog (BitVec 64) :=
.seq globalBody877_0 globalBody877_1

def globalBody877_3 : Prog (BitVec 64) :=
.dec ("e") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody877_2

def globalData877 : Decl (BitVec 64) :=
.function { name := "attempt_l1", inline := false, exported := false, params := [("si", Flapjack.Shape.one)], body := globalBody877_3, returnShape := (Flapjack.Shape.one) }
def globalOutput877 := Pancake.PanLang.declToHOL globalData877
end InitECandidate.Proofs.FrontendStages.Declarations
