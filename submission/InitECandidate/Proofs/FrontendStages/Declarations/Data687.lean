import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify671
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body687_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body687_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body687_2 : Prog (BitVec 64) :=
.seq body687_0 body687_1

def body687_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body687_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "e0") (Flapjack.Exp.const 0#64)) body687_2 body687_3

def body687_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_mul"
  [Flapjack.Exp.const 1#64, Flapjack.Exp.var Flapjack.VarKind.local "p0", Flapjack.Exp.var Flapjack.VarKind.local "p0",
    Flapjack.Exp.var Flapjack.VarKind.local "n"]

def body687_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bn254_g1_to_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p0", Flapjack.Exp.var Flapjack.VarKind.local "out64"]

def body687_7 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body687_8 : Prog (BitVec 64) :=
.seq body687_0 body687_7

def body687_9 : Prog (BitVec 64) :=
.seq body687_6 body687_8

def body687_10 : Prog (BitVec 64) :=
.seq body687_5 body687_9

def body687_11 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "in96", Flapjack.Exp.const 64#64],
  Flapjack.Exp.const 32#64]) body687_10

def body687_12 : Prog (BitVec 64) :=
.seq body687_4 body687_11

def body687_13 : Prog (BitVec 64) :=
.decCall ("e0") (Flapjack.Shape.one) ("bn254_parse_g1") ([Flapjack.Exp.var Flapjack.VarKind.local "in96", Flapjack.Exp.var Flapjack.VarKind.local "p0"]) body687_12

def body687_14 : Prog (BitVec 64) :=
.decCall ("p0") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body687_13

def body687_15 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body687_14

def body687_16 : Prog (BitVec 64) :=
.seq body687_5 body687_6

def body687_17 : Prog (BitVec 64) :=
.seq body687_16 body687_0

def body687_18 : Prog (BitVec 64) :=
.seq body687_17 body687_7

def body687_19 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "in96", Flapjack.Exp.const 64#64],
  Flapjack.Exp.const 32#64]) body687_18

def body687_20 : Prog (BitVec 64) :=
.seq body687_4 body687_19

def body687_21 : Prog (BitVec 64) :=
.decCall ("e0") (Flapjack.Shape.one) ("bn254_parse_g1") ([Flapjack.Exp.var Flapjack.VarKind.local "in96", Flapjack.Exp.var Flapjack.VarKind.local "p0"]) body687_20

def body687_22 : Prog (BitVec 64) :=
.decCall ("p0") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body687_21

def body687_23 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body687_22

def originalData687 : Decl (BitVec 64) :=
.function { name := "bn254_g1_mul", inline := false, exported := false, params := [("in96", Flapjack.Shape.one), ("out64", Flapjack.Shape.one)], body := body687_15, returnShape := (Flapjack.Shape.one) }
def simplifiedData687 : Decl (BitVec 64) :=
.function { name := "bn254_g1_mul", inline := false, exported := false, params := [("in96", Flapjack.Shape.one), ("out64", Flapjack.Shape.one)], body := body687_23, returnShape := (Flapjack.Shape.one) }
def original687 := Pancake.PanLang.declToHOL originalData687
def simplified687 := Pancake.PanLang.declToHOL simplifiedData687
end InitECandidate.Proofs.FrontendStages.Declarations
