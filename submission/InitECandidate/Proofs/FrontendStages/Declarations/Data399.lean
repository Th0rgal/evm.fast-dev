import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify383
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body399_0 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bs", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.const 1#64)

def body399_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bs", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "offset")

def body399_2 : Prog (BitVec 64) :=
.seq body399_0 body399_1

def body399_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body399_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bs", Flapjack.Exp.const 64#64]))
  (Flapjack.Exp.var Flapjack.VarKind.local "offset")) body399_1 body399_3

def body399_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bs", Flapjack.Exp.const 56#64]))
  (Flapjack.Exp.const 0#64)) body399_2 body399_4

def body399_6 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body399_7 : Prog (BitVec 64) :=
.seq body399_5 body399_6

def originalData399 : Decl (BitVec 64) :=
.function { name := "track_ancestor_access", inline := false, exported := false, params := [("offset", Flapjack.Shape.one)], body := body399_7, returnShape := (Flapjack.Shape.one) }
def simplifiedData399 : Decl (BitVec 64) :=
.function { name := "track_ancestor_access", inline := false, exported := false, params := [("offset", Flapjack.Shape.one)], body := body399_7, returnShape := (Flapjack.Shape.one) }
def original399 := Pancake.PanLang.declToHOL originalData399
def simplified399 := Pancake.PanLang.declToHOL simplifiedData399
end InitECandidate.Proofs.FrontendStages.Declarations
