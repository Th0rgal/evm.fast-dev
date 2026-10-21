import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify392
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body408_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "bal_accounts"), none)) "htab_new"
  [Flapjack.Exp.const 20#64, Flapjack.Exp.const 64#64]

def body408_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "bal_idx_accts"), none)) "htab_new"
  [Flapjack.Exp.const 28#64, Flapjack.Exp.const 64#64]

def body408_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "bal_idx_stor"), none)) "htab_new"
  [Flapjack.Exp.const 60#64, Flapjack.Exp.const 64#64]

def body408_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "bal_key_buf"), none)) "alloc" [Flapjack.Exp.const 64#64]

def body408_4 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.global "bal_index" (Flapjack.Exp.const 0#64)

def body408_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body408_6 : Prog (BitVec 64) :=
.seq body408_4 body408_5

def body408_7 : Prog (BitVec 64) :=
.seq body408_3 body408_6

def body408_8 : Prog (BitVec 64) :=
.seq body408_2 body408_7

def body408_9 : Prog (BitVec 64) :=
.seq body408_1 body408_8

def body408_10 : Prog (BitVec 64) :=
.seq body408_0 body408_9

def body408_11 : Prog (BitVec 64) :=
.seq body408_0 body408_1

def body408_12 : Prog (BitVec 64) :=
.seq body408_11 body408_2

def body408_13 : Prog (BitVec 64) :=
.seq body408_12 body408_3

def body408_14 : Prog (BitVec 64) :=
.seq body408_13 body408_4

def body408_15 : Prog (BitVec 64) :=
.seq body408_14 body408_5

def originalData408 : Decl (BitVec 64) :=
.function { name := "bal_init", inline := false, exported := false, params := [], body := body408_10, returnShape := (Flapjack.Shape.one) }
def simplifiedData408 : Decl (BitVec 64) :=
.function { name := "bal_init", inline := false, exported := false, params := [], body := body408_15, returnShape := (Flapjack.Shape.one) }
def original408 := Pancake.PanLang.declToHOL originalData408
def simplified408 := Pancake.PanLang.declToHOL simplifiedData408
end InitECandidate.Proofs.FrontendStages.Declarations
