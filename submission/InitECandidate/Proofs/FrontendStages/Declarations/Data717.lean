import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify701
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body717_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 16#64]

def body717_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bls_fp_to_be48"
  [Flapjack.Exp.var Flapjack.VarKind.local "c",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 16#64]]

def body717_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body717_3 : Prog (BitVec 64) :=
.seq body717_1 body717_2

def body717_4 : Prog (BitVec 64) :=
.seq body717_0 body717_3

def body717_5 : Prog (BitVec 64) :=
.decCall ("c") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_from_mont") ([Flapjack.Exp.var Flapjack.VarKind.local "m"]) body717_4

def body717_6 : Prog (BitVec 64) :=
.dec ("m") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "a")) body717_5

def body717_7 : Prog (BitVec 64) :=
.seq body717_0 body717_1

def body717_8 : Prog (BitVec 64) :=
.seq body717_7 body717_2

def body717_9 : Prog (BitVec 64) :=
.decCall ("c") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_from_mont") ([Flapjack.Exp.var Flapjack.VarKind.local "m"]) body717_8

def body717_10 : Prog (BitVec 64) :=
.dec ("m") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "a")) body717_9

def originalData717 : Decl (BitVec 64) :=
.function { name := "bls_fp_encode64", inline := false, exported := false, params := [("a", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body717_6, returnShape := (Flapjack.Shape.one) }
def simplifiedData717 : Decl (BitVec 64) :=
.function { name := "bls_fp_encode64", inline := false, exported := false, params := [("a", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body717_10, returnShape := (Flapjack.Shape.one) }
def original717 := Pancake.PanLang.declToHOL originalData717
def simplified717 := Pancake.PanLang.declToHOL simplifiedData717
end InitECandidate.Proofs.FrontendStages.Declarations
