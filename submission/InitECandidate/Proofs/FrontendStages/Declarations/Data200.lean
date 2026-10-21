import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify184
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body200_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_fail" [Flapjack.Exp.const 30#64]

def body200_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body200_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "qr"))
  (Flapjack.Exp.const 0#64)) body200_0 body200_1

def body200_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_fail" [Flapjack.Exp.const 31#64]

def body200_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "lim")
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "qr"))) body200_3 body200_1

def body200_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "qr"))

def body200_6 : Prog (BitVec 64) :=
.seq body200_4 body200_5

def body200_7 : Prog (BitVec 64) :=
.seq body200_2 body200_6

def body200_8 : Prog (BitVec 64) :=
.decCall ("qr") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("udivmod") ([Flapjack.Exp.var Flapjack.VarKind.local "len", Flapjack.Exp.var Flapjack.VarKind.local "sz"]) body200_7

def body200_9 : Prog (BitVec 64) :=
.seq body200_2 body200_4

def body200_10 : Prog (BitVec 64) :=
.seq body200_9 body200_5

def body200_11 : Prog (BitVec 64) :=
.decCall ("qr") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("udivmod") ([Flapjack.Exp.var Flapjack.VarKind.local "len", Flapjack.Exp.var Flapjack.VarKind.local "sz"]) body200_10

def originalData200 : Decl (BitVec 64) :=
.function { name := "ssz_fixed_list_count", inline := false, exported := false, params := [("len", Flapjack.Shape.one), ("sz", Flapjack.Shape.one), ("lim", Flapjack.Shape.one)], body := body200_8, returnShape := (Flapjack.Shape.one) }
def simplifiedData200 : Decl (BitVec 64) :=
.function { name := "ssz_fixed_list_count", inline := false, exported := false, params := [("len", Flapjack.Shape.one), ("sz", Flapjack.Shape.one), ("lim", Flapjack.Shape.one)], body := body200_11, returnShape := (Flapjack.Shape.one) }
def original200 := Pancake.PanLang.declToHOL originalData200
def simplified200 := Pancake.PanLang.declToHOL simplifiedData200
end InitECandidate.Proofs.FrontendStages.Declarations
