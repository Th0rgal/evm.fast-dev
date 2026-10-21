import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify312
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body328_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "e"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "e"), Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body328_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body328_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body328_3 : Prog (BitVec 64) :=
.seq body328_1 body328_2

def body328_4 : Prog (BitVec 64) :=
.seq body328_0 body328_3

def body328_5 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("tx_encode_generic") ([Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.var Flapjack.VarKind.local "mode",
  Flapjack.Exp.var Flapjack.VarKind.local "chain_id"]) body328_4

def body328_6 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body328_5

def body328_7 : Prog (BitVec 64) :=
.seq body328_0 body328_1

def body328_8 : Prog (BitVec 64) :=
.seq body328_7 body328_2

def body328_9 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("tx_encode_generic") ([Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.var Flapjack.VarKind.local "mode",
  Flapjack.Exp.var Flapjack.VarKind.local "chain_id"]) body328_8

def body328_10 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body328_9

def originalData328 : Decl (BitVec 64) :=
.function { name := "tx_signing_hash_mode", inline := false, exported := false, params := [("tx", Flapjack.Shape.one), ("mode", Flapjack.Shape.one), ("chain_id", Flapjack.Shape.one),
  ("out", Flapjack.Shape.one)], body := body328_6, returnShape := (Flapjack.Shape.one) }
def simplifiedData328 : Decl (BitVec 64) :=
.function { name := "tx_signing_hash_mode", inline := false, exported := false, params := [("tx", Flapjack.Shape.one), ("mode", Flapjack.Shape.one), ("chain_id", Flapjack.Shape.one),
  ("out", Flapjack.Shape.one)], body := body328_10, returnShape := (Flapjack.Shape.one) }
def original328 := Pancake.PanLang.declToHOL originalData328
def simplified328 := Pancake.PanLang.declToHOL simplifiedData328
end InitECandidate.Proofs.FrontendStages.Declarations
