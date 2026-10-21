import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify863
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body879_0 : Prog (BitVec 64) :=
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

def body879_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body879_2 : Prog (BitVec 64) :=
.seq body879_0 body879_1

def body879_3 : Prog (BitVec 64) :=
.dec ("e") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body879_2

def originalData879 : Decl (BitVec 64) :=
.function { name := "attempt_l3", inline := false, exported := false, params := [("si", Flapjack.Shape.one)], body := body879_3, returnShape := (Flapjack.Shape.one) }
def simplifiedData879 : Decl (BitVec 64) :=
.function { name := "attempt_l3", inline := false, exported := false, params := [("si", Flapjack.Shape.one)], body := body879_3, returnShape := (Flapjack.Shape.one) }
def original879 := Pancake.PanLang.declToHOL originalData879
def simplified879 := Pancake.PanLang.declToHOL simplifiedData879
end InitECandidate.Proofs.FrontendStages.Declarations
