import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify595
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body611_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body611_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body611_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "j") (Flapjack.Exp.const 16#64)) body611_0 body611_1

def body611_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1518500249#64)

def body611_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "j") (Flapjack.Exp.const 32#64)) body611_3 body611_1

def body611_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1859775393#64)

def body611_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "j") (Flapjack.Exp.const 48#64)) body611_5 body611_1

def body611_7 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 2400959708#64)

def body611_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "j") (Flapjack.Exp.const 64#64)) body611_7 body611_1

def body611_9 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 2840853838#64)

def body611_10 : Prog (BitVec 64) :=
.seq body611_8 body611_9

def body611_11 : Prog (BitVec 64) :=
.seq body611_6 body611_10

def body611_12 : Prog (BitVec 64) :=
.seq body611_4 body611_11

def body611_13 : Prog (BitVec 64) :=
.seq body611_2 body611_12

def body611_14 : Prog (BitVec 64) :=
.seq body611_2 body611_4

def body611_15 : Prog (BitVec 64) :=
.seq body611_14 body611_6

def body611_16 : Prog (BitVec 64) :=
.seq body611_15 body611_8

def body611_17 : Prog (BitVec 64) :=
.seq body611_16 body611_9

def originalData611 : Decl (BitVec 64) :=
.function { name := "rmd_k", inline := false, exported := false, params := [("j", Flapjack.Shape.one)], body := body611_13, returnShape := (Flapjack.Shape.one) }
def simplifiedData611 : Decl (BitVec 64) :=
.function { name := "rmd_k", inline := false, exported := false, params := [("j", Flapjack.Shape.one)], body := body611_17, returnShape := (Flapjack.Shape.one) }
def original611 := Pancake.PanLang.declToHOL originalData611
def simplified611 := Pancake.PanLang.declToHOL simplifiedData611
end InitECandidate.Proofs.FrontendStages.Declarations
