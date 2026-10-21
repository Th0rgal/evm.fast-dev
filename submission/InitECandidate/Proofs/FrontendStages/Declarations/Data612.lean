import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify596
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body612_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1352829926#64)

def body612_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body612_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "j") (Flapjack.Exp.const 16#64)) body612_0 body612_1

def body612_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1548603684#64)

def body612_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "j") (Flapjack.Exp.const 32#64)) body612_3 body612_1

def body612_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1836072691#64)

def body612_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "j") (Flapjack.Exp.const 48#64)) body612_5 body612_1

def body612_7 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 2053994217#64)

def body612_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "j") (Flapjack.Exp.const 64#64)) body612_7 body612_1

def body612_9 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body612_10 : Prog (BitVec 64) :=
.seq body612_8 body612_9

def body612_11 : Prog (BitVec 64) :=
.seq body612_6 body612_10

def body612_12 : Prog (BitVec 64) :=
.seq body612_4 body612_11

def body612_13 : Prog (BitVec 64) :=
.seq body612_2 body612_12

def body612_14 : Prog (BitVec 64) :=
.seq body612_2 body612_4

def body612_15 : Prog (BitVec 64) :=
.seq body612_14 body612_6

def body612_16 : Prog (BitVec 64) :=
.seq body612_15 body612_8

def body612_17 : Prog (BitVec 64) :=
.seq body612_16 body612_9

def originalData612 : Decl (BitVec 64) :=
.function { name := "rmd_kp", inline := false, exported := false, params := [("j", Flapjack.Shape.one)], body := body612_13, returnShape := (Flapjack.Shape.one) }
def simplifiedData612 : Decl (BitVec 64) :=
.function { name := "rmd_kp", inline := false, exported := false, params := [("j", Flapjack.Shape.one)], body := body612_17, returnShape := (Flapjack.Shape.one) }
def original612 := Pancake.PanLang.declToHOL originalData612
def simplified612 := Pancake.PanLang.declToHOL simplifiedData612
end InitECandidate.Proofs.FrontendStages.Declarations
