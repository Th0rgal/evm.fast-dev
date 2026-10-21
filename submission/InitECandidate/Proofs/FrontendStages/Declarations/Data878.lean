import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify862
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body878_0 : Prog (BitVec 64) :=
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

def body878_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body878_2 : Prog (BitVec 64) :=
.seq body878_0 body878_1

def body878_3 : Prog (BitVec 64) :=
.dec ("e") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body878_2

def originalData878 : Decl (BitVec 64) :=
.function { name := "attempt_l2", inline := false, exported := false, params := [("si", Flapjack.Shape.one)], body := body878_3, returnShape := (Flapjack.Shape.one) }
def simplifiedData878 : Decl (BitVec 64) :=
.function { name := "attempt_l2", inline := false, exported := false, params := [("si", Flapjack.Shape.one)], body := body878_3, returnShape := (Flapjack.Shape.one) }
def original878 := Pancake.PanLang.declToHOL originalData878
def simplified878 := Pancake.PanLang.declToHOL simplifiedData878
end InitECandidate.Proofs.FrontendStages.Declarations
