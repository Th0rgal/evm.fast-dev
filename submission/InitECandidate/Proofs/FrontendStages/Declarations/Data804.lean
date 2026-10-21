import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify788
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body804_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body804_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body804_2 : Prog (BitVec 64) :=
.seq body804_0 body804_1

def body804_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body804_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 0#64)) body804_2 body804_3

def body804_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "map_fp_to_g1"
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "tv"]

def body804_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_encode"
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body804_7 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body804_8 : Prog (BitVec 64) :=
.seq body804_0 body804_7

def body804_9 : Prog (BitVec 64) :=
.seq body804_6 body804_8

def body804_10 : Prog (BitVec 64) :=
.seq body804_5 body804_9

def body804_11 : Prog (BitVec 64) :=
.dec ("tv") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "t")) body804_10

def body804_12 : Prog (BitVec 64) :=
.seq body804_4 body804_11

def body804_13 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("bls_fp_decode64") ([Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.var Flapjack.VarKind.local "t"]) body804_12

def body804_14 : Prog (BitVec 64) :=
.decCall ("p") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) body804_13

def body804_15 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 48#64]) body804_14

def body804_16 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body804_15

def body804_17 : Prog (BitVec 64) :=
.seq body804_5 body804_6

def body804_18 : Prog (BitVec 64) :=
.seq body804_17 body804_0

def body804_19 : Prog (BitVec 64) :=
.seq body804_18 body804_7

def body804_20 : Prog (BitVec 64) :=
.dec ("tv") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "t")) body804_19

def body804_21 : Prog (BitVec 64) :=
.seq body804_4 body804_20

def body804_22 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("bls_fp_decode64") ([Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.var Flapjack.VarKind.local "t"]) body804_21

def body804_23 : Prog (BitVec 64) :=
.decCall ("p") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) body804_22

def body804_24 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 48#64]) body804_23

def body804_25 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body804_24

def originalData804 : Decl (BitVec 64) :=
.function { name := "bls_map_fp_to_g1_exec", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body804_16, returnShape := (Flapjack.Shape.one) }
def simplifiedData804 : Decl (BitVec 64) :=
.function { name := "bls_map_fp_to_g1_exec", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body804_25, returnShape := (Flapjack.Shape.one) }
def original804 := Pancake.PanLang.declToHOL originalData804
def simplified804 := Pancake.PanLang.declToHOL simplifiedData804
end InitECandidate.Proofs.FrontendStages.Declarations
