import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify245
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body261_0 : Prog (BitVec 64) :=
Flapjack.Prog.call
  (some
    (some (Flapjack.VarKind.local, "nd"),
      some
        ("RlpErr", "e",
          Flapjack.Prog.seq
            (Flapjack.Prog.call (some (none, none)) "scratch_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"])
            (Flapjack.Prog.raise "RlpErr" (Flapjack.Exp.var Flapjack.VarKind.local "e")))))
  "_decode_witness_node_mpt"
  [Flapjack.Exp.var Flapjack.VarKind.local "db", Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body261_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "scratch_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body261_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "nd")

def body261_3 : Prog (BitVec 64) :=
.seq body261_1 body261_2

def body261_4 : Prog (BitVec 64) :=
.seq body261_0 body261_3

def body261_5 : Prog (BitVec 64) :=
.dec ("nd") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body261_4

def body261_6 : Prog (BitVec 64) :=
.dec ("e") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body261_5

def body261_7 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("scratch_mark") ([]) body261_6

def body261_8 : Prog (BitVec 64) :=
.seq body261_0 body261_1

def body261_9 : Prog (BitVec 64) :=
.seq body261_8 body261_2

def body261_10 : Prog (BitVec 64) :=
.dec ("nd") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body261_9

def body261_11 : Prog (BitVec 64) :=
.dec ("e") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body261_10

def body261_12 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("scratch_mark") ([]) body261_11

def originalData261 : Decl (BitVec 64) :=
.function { name := "_decode_witness_node", inline := false, exported := false, params := [("db", Flapjack.Shape.one), ("p", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body261_7, returnShape := (Flapjack.Shape.one) }
def simplifiedData261 : Decl (BitVec 64) :=
.function { name := "_decode_witness_node", inline := false, exported := false, params := [("db", Flapjack.Shape.one), ("p", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body261_12, returnShape := (Flapjack.Shape.one) }
def original261 := Pancake.PanLang.declToHOL originalData261
def simplified261 := Pancake.PanLang.declToHOL simplifiedData261
end InitECandidate.Proofs.FrontendStages.Declarations
