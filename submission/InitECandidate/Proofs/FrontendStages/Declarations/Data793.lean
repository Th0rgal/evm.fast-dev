import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify777
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body793_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "swu_g2"
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "t"]

def body793_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "iso_map_g2"
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "p"]

def body793_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 1632#64],
    Flapjack.Exp.const 10#64]

def body793_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body793_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body793_5 : Prog (BitVec 64) :=
.seq body793_3 body793_4

def body793_6 : Prog (BitVec 64) :=
.seq body793_2 body793_5

def body793_7 : Prog (BitVec 64) :=
.seq body793_1 body793_6

def body793_8 : Prog (BitVec 64) :=
.seq body793_0 body793_7

def body793_9 : Prog (BitVec 64) :=
.decCall ("p") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) body793_8

def body793_10 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body793_9

def body793_11 : Prog (BitVec 64) :=
.seq body793_0 body793_1

def body793_12 : Prog (BitVec 64) :=
.seq body793_11 body793_2

def body793_13 : Prog (BitVec 64) :=
.seq body793_12 body793_3

def body793_14 : Prog (BitVec 64) :=
.seq body793_13 body793_4

def body793_15 : Prog (BitVec 64) :=
.decCall ("p") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) body793_14

def body793_16 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body793_15

def originalData793 : Decl (BitVec 64) :=
.function { name := "map_fp2_to_g2", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("t", Flapjack.Shape.one)], body := body793_10, returnShape := (Flapjack.Shape.one) }
def simplifiedData793 : Decl (BitVec 64) :=
.function { name := "map_fp2_to_g2", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("t", Flapjack.Shape.one)], body := body793_16, returnShape := (Flapjack.Shape.one) }
def original793 := Pancake.PanLang.declToHOL originalData793
def simplified793 := Pancake.PanLang.declToHOL simplifiedData793
end InitECandidate.Proofs.FrontendStages.Declarations
