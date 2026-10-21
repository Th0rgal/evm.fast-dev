import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify772
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body788_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "swu_g1"
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "t"]

def body788_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "iso_map_g1"
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "p"]

def body788_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 1624#64],
    Flapjack.Exp.const 1#64]

def body788_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body788_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body788_5 : Prog (BitVec 64) :=
.seq body788_3 body788_4

def body788_6 : Prog (BitVec 64) :=
.seq body788_2 body788_5

def body788_7 : Prog (BitVec 64) :=
.seq body788_1 body788_6

def body788_8 : Prog (BitVec 64) :=
.seq body788_0 body788_7

def body788_9 : Prog (BitVec 64) :=
.decCall ("p") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) body788_8

def body788_10 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body788_9

def body788_11 : Prog (BitVec 64) :=
.seq body788_0 body788_1

def body788_12 : Prog (BitVec 64) :=
.seq body788_11 body788_2

def body788_13 : Prog (BitVec 64) :=
.seq body788_12 body788_3

def body788_14 : Prog (BitVec 64) :=
.seq body788_13 body788_4

def body788_15 : Prog (BitVec 64) :=
.decCall ("p") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) body788_14

def body788_16 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body788_15

def originalData788 : Decl (BitVec 64) :=
.function { name := "map_fp_to_g1", inline := false, exported := false, params := [("r", Flapjack.Shape.one),
  ("t",
    Flapjack.Shape.comb
      [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
        Flapjack.Shape.one])], body := body788_10, returnShape := (Flapjack.Shape.one) }
def simplifiedData788 : Decl (BitVec 64) :=
.function { name := "map_fp_to_g1", inline := false, exported := false, params := [("r", Flapjack.Shape.one),
  ("t",
    Flapjack.Shape.comb
      [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
        Flapjack.Shape.one])], body := body788_16, returnShape := (Flapjack.Shape.one) }
def original788 := Pancake.PanLang.declToHOL originalData788
def simplified788 := Pancake.PanLang.declToHOL simplifiedData788
end InitECandidate.Proofs.FrontendStages.Declarations
