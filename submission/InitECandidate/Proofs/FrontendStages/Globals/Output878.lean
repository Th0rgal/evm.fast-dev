import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data878
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate862
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody878_0 : Prog (BitVec 64) :=
Flapjack.Prog.call
  (some
    (none,
      some
        ("HdrErr", "e",
          Flapjack.Prog.seq
            (Flapjack.Prog.shMemStore Flapjack.OpSize.op8
              (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.const 2688614400#64, Flapjack.Exp.const 70#64])
              (Flapjack.Exp.var Flapjack.VarKind.local "e"))
            (Flapjack.Prog.raise "Fail" (Flapjack.Exp.const 2#64)))))
  "attempt_l1" [Flapjack.Exp.var Flapjack.VarKind.local "si"]

def globalBody878_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody878_2 : Prog (BitVec 64) :=
.seq globalBody878_0 globalBody878_1

def globalBody878_3 : Prog (BitVec 64) :=
.dec ("e") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody878_2

def globalData878 : Decl (BitVec 64) :=
.function { name := "attempt_l2", inline := false, exported := false, params := [("si", Flapjack.Shape.one)], body := globalBody878_3, returnShape := (Flapjack.Shape.one) }
def globalOutput878 := Pancake.PanLang.declToHOL globalData878
end InitECandidate.Proofs.FrontendStages.Declarations
