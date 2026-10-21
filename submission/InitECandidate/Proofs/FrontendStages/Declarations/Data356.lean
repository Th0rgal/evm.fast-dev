import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify340
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body356_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.global "journal_n"
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.global "journal_n", Flapjack.Exp.const 1#64])

def body356_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.var Flapjack.VarKind.local "key",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 24#64])]

def body356_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_del"
  [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.var Flapjack.VarKind.local "key"]

def body356_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 16#64]))
  (Flapjack.Exp.const 0#64)) body356_1 body356_2

def body356_4 : Prog (BitVec 64) :=
.dec ("key") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 8#64])) body356_3

def body356_5 : Prog (BitVec 64) :=
.dec ("t") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "r")) body356_4

def body356_6 : Prog (BitVec 64) :=
.dec ("r") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.global "journal",
    Flapjack.Exp.panOp Flapjack.PanOp.mul
      [Flapjack.Exp.var Flapjack.VarKind.global "journal_n", Flapjack.Exp.const 32#64]]) body356_5

def body356_7 : Prog (BitVec 64) :=
.seq body356_0 body356_6

def body356_8 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "snap")
  (Flapjack.Exp.var Flapjack.VarKind.global "journal_n")) body356_7

def body356_9 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body356_10 : Prog (BitVec 64) :=
.seq body356_8 body356_9

def originalData356 : Decl (BitVec 64) :=
.function { name := "state_restore", inline := false, exported := false, params := [("snap", Flapjack.Shape.one)], body := body356_10, returnShape := (Flapjack.Shape.one) }
def simplifiedData356 : Decl (BitVec 64) :=
.function { name := "state_restore", inline := false, exported := false, params := [("snap", Flapjack.Shape.one)], body := body356_10, returnShape := (Flapjack.Shape.one) }
def original356 := Pancake.PanLang.declToHOL originalData356
def simplified356 := Pancake.PanLang.declToHOL simplifiedData356
end InitECandidate.Proofs.FrontendStages.Declarations
