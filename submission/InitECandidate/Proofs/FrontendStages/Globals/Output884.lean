import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data884
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate868
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody884_0 : Prog (BitVec 64) :=
Flapjack.Prog.call
  (some
    (none,
      some
        ("Fail", "e",
          Flapjack.Prog.seq (Flapjack.Prog.assign Flapjack.VarKind.local "ok" (Flapjack.Exp.const 0#64))
            (Flapjack.Prog.store (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 536#64])
              (Flapjack.Exp.var Flapjack.VarKind.local "e")))))
  "attempt_l7" [Flapjack.Exp.var Flapjack.VarKind.local "si"]

def globalBody884_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "ok")

def globalBody884_2 : Prog (BitVec 64) :=
.seq globalBody884_0 globalBody884_1

def globalBody884_3 : Prog (BitVec 64) :=
.dec ("ok") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) globalBody884_2

def globalBody884_4 : Prog (BitVec 64) :=
.dec ("e") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody884_3

def globalData884 : Decl (BitVec 64) :=
.function { name := "verify_stateless_new_payload", inline := false, exported := false, params := [("si", Flapjack.Shape.one)], body := globalBody884_4, returnShape := (Flapjack.Shape.one) }
def globalOutput884 := Pancake.PanLang.declToHOL globalData884
end InitECandidate.Proofs.FrontendStages.Declarations
