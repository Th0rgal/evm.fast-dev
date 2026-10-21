import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify699
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body715_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_be64"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "a")]

def body715_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 8#64],
    Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "a")]

def body715_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 16#64],
    Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "a")]

def body715_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 24#64],
    Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "a")]

def body715_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 32#64],
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "a")]

def body715_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 40#64],
    Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "a")]

def body715_6 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body715_7 : Prog (BitVec 64) :=
.seq body715_5 body715_6

def body715_8 : Prog (BitVec 64) :=
.seq body715_4 body715_7

def body715_9 : Prog (BitVec 64) :=
.seq body715_3 body715_8

def body715_10 : Prog (BitVec 64) :=
.seq body715_2 body715_9

def body715_11 : Prog (BitVec 64) :=
.seq body715_1 body715_10

def body715_12 : Prog (BitVec 64) :=
.seq body715_0 body715_11

def body715_13 : Prog (BitVec 64) :=
.seq body715_0 body715_1

def body715_14 : Prog (BitVec 64) :=
.seq body715_13 body715_2

def body715_15 : Prog (BitVec 64) :=
.seq body715_14 body715_3

def body715_16 : Prog (BitVec 64) :=
.seq body715_15 body715_4

def body715_17 : Prog (BitVec 64) :=
.seq body715_16 body715_5

def body715_18 : Prog (BitVec 64) :=
.seq body715_17 body715_6

def originalData715 : Decl (BitVec 64) :=
.function { name := "bls_fp_to_be48", inline := false, exported := false, params := [("a",
    Flapjack.Shape.comb
      [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
        Flapjack.Shape.one]),
  ("out", Flapjack.Shape.one)], body := body715_12, returnShape := (Flapjack.Shape.one) }
def simplifiedData715 : Decl (BitVec 64) :=
.function { name := "bls_fp_to_be48", inline := false, exported := false, params := [("a",
    Flapjack.Shape.comb
      [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
        Flapjack.Shape.one]),
  ("out", Flapjack.Shape.one)], body := body715_18, returnShape := (Flapjack.Shape.one) }
def original715 := Pancake.PanLang.declToHOL originalData715
def simplified715 := Pancake.PanLang.declToHOL simplifiedData715
end InitECandidate.Proofs.FrontendStages.Declarations
