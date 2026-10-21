import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify563
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body579_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "state_restore"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.global "cur_cont", Flapjack.Exp.const 24#64])]

def body579_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body579_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 160#64]))
  (Flapjack.Exp.const 0#64)) body579_0 body579_1

def body579_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body579_4 : Prog (BitVec 64) :=
.seq body579_2 body579_3

def originalData579 : Decl (BitVec 64) :=
.function { name := "frame_epilogue", inline := false, exported := false, params := [], body := body579_4, returnShape := (Flapjack.Shape.one) }
def simplifiedData579 : Decl (BitVec 64) :=
.function { name := "frame_epilogue", inline := false, exported := false, params := [], body := body579_4, returnShape := (Flapjack.Shape.one) }
def original579 := Pancake.PanLang.declToHOL originalData579
def simplified579 := Pancake.PanLang.declToHOL simplifiedData579
end InitECandidate.Proofs.FrontendStages.Declarations
