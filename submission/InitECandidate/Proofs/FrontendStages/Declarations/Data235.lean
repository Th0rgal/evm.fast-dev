import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify219
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body235_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body235_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body235_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.global "hdr_zero8") (Flapjack.Exp.const 0#64)) body235_0 body235_1

def body235_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "hdr_zero8"), none)) "alloc" [Flapjack.Exp.const 8#64]

def body235_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.global "hdr_zero8", Flapjack.Exp.const 8#64]

def body235_5 : Prog (BitVec 64) :=
.seq body235_4 body235_0

def body235_6 : Prog (BitVec 64) :=
.seq body235_3 body235_5

def body235_7 : Prog (BitVec 64) :=
.seq body235_2 body235_6

def body235_8 : Prog (BitVec 64) :=
.seq body235_2 body235_3

def body235_9 : Prog (BitVec 64) :=
.seq body235_8 body235_4

def body235_10 : Prog (BitVec 64) :=
.seq body235_9 body235_0

def originalData235 : Decl (BitVec 64) :=
.function { name := "header_init", inline := false, exported := false, params := [], body := body235_7, returnShape := (Flapjack.Shape.one) }
def simplifiedData235 : Decl (BitVec 64) :=
.function { name := "header_init", inline := false, exported := false, params := [], body := body235_10, returnShape := (Flapjack.Shape.one) }
def original235 := Pancake.PanLang.declToHOL originalData235
def simplified235 := Pancake.PanLang.declToHOL simplifiedData235
end InitECandidate.Proofs.FrontendStages.Declarations
