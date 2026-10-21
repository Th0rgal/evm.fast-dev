import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify211
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body227_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "e"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "e"), Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body227_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body227_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body227_3 : Prog (BitVec 64) :=
.seq body227_1 body227_2

def body227_4 : Prog (BitVec 64) :=
.seq body227_0 body227_3

def body227_5 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("encode_header") ([Flapjack.Exp.var Flapjack.VarKind.local "h"]) body227_4

def body227_6 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body227_5

def body227_7 : Prog (BitVec 64) :=
.seq body227_0 body227_1

def body227_8 : Prog (BitVec 64) :=
.seq body227_7 body227_2

def body227_9 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("encode_header") ([Flapjack.Exp.var Flapjack.VarKind.local "h"]) body227_8

def body227_10 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body227_9

def originalData227 : Decl (BitVec 64) :=
.function { name := "header_hash", inline := false, exported := false, params := [("h", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body227_6, returnShape := (Flapjack.Shape.one) }
def simplifiedData227 : Decl (BitVec 64) :=
.function { name := "header_hash", inline := false, exported := false, params := [("h", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body227_10, returnShape := (Flapjack.Shape.one) }
def original227 := Pancake.PanLang.declToHOL originalData227
def simplified227 := Pancake.PanLang.declToHOL simplifiedData227
end InitECandidate.Proofs.FrontendStages.Declarations
