import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data879
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate863
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody879_0 : Prog (BitVec 64) :=
Flapjack.Prog.call
  (some
    (none,
      some
        ("RlpErr", "e",
          Flapjack.Prog.seq
            (Flapjack.Prog.shMemStore Flapjack.OpSize.op8
              (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.const 2688614400#64, Flapjack.Exp.const 70#64])
              (Flapjack.Exp.var Flapjack.VarKind.local "e"))
            (Flapjack.Prog.raise "Fail" (Flapjack.Exp.const 3#64)))))
  "attempt_l2" [Flapjack.Exp.var Flapjack.VarKind.local "si"]

def globalBody879_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody879_2 : Prog (BitVec 64) :=
.seq globalBody879_0 globalBody879_1

def globalBody879_3 : Prog (BitVec 64) :=
.dec ("e") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody879_2

def globalData879 : Decl (BitVec 64) :=
.function { name := "attempt_l3", inline := false, exported := false, params := [("si", Flapjack.Shape.one)], body := globalBody879_3, returnShape := (Flapjack.Shape.one) }
def globalOutput879 := Pancake.PanLang.declToHOL globalData879
end InitECandidate.Proofs.FrontendStages.Declarations
