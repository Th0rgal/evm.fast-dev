import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify754
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body770_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "p"]

def body770_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 192#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 192#64]]

def body770_2 : Prog (BitVec 64) :=
.seq body770_0 body770_1

def body770_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body770_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "r")
  (Flapjack.Exp.var Flapjack.VarKind.local "p")) body770_2 body770_3

def body770_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_neg"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 96#64]]

def body770_6 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body770_7 : Prog (BitVec 64) :=
.seq body770_5 body770_6

def body770_8 : Prog (BitVec 64) :=
.seq body770_4 body770_7

def body770_9 : Prog (BitVec 64) :=
.seq body770_4 body770_5

def body770_10 : Prog (BitVec 64) :=
.seq body770_9 body770_6

def originalData770 : Decl (BitVec 64) :=
.function { name := "g2_neg", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("p", Flapjack.Shape.one)], body := body770_8, returnShape := (Flapjack.Shape.one) }
def simplifiedData770 : Decl (BitVec 64) :=
.function { name := "g2_neg", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("p", Flapjack.Shape.one)], body := body770_10, returnShape := (Flapjack.Shape.one) }
def original770 := Pancake.PanLang.declToHOL originalData770
def simplified770 := Pancake.PanLang.declToHOL simplifiedData770
end InitECandidate.Proofs.FrontendStages.Declarations
