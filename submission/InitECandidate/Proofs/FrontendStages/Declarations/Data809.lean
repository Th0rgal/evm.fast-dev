import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify793
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body809_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 519#64)

def body809_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body809_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 128#64) (Flapjack.Exp.var Flapjack.VarKind.local "k")) body809_0 body809_1

def body809_3 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount",
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 1#64],
            Flapjack.Exp.const 8#64]]))

def body809_4 : Prog (BitVec 64) :=
.seq body809_2 body809_3

def originalData809 : Decl (BitVec 64) :=
.function { name := "bls_g1_msm_discount", inline := false, exported := false, params := [("k", Flapjack.Shape.one)], body := body809_4, returnShape := (Flapjack.Shape.one) }
def simplifiedData809 : Decl (BitVec 64) :=
.function { name := "bls_g1_msm_discount", inline := false, exported := false, params := [("k", Flapjack.Shape.one)], body := body809_4, returnShape := (Flapjack.Shape.one) }
def original809 := Pancake.PanLang.declToHOL originalData809
def simplified809 := Pancake.PanLang.declToHOL simplifiedData809
end InitECandidate.Proofs.FrontendStages.Declarations
