import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify807
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body823_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.const 600#64,
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 120#64, Flapjack.Exp.var Flapjack.VarKind.local "w"]]]

def body823_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 12#64]

def body823_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ripemd160"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 88#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 12#64]]

def body823_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "out")

def body823_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 128#64])
  (Flapjack.Exp.const 32#64)

def body823_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body823_6 : Prog (BitVec 64) :=
.seq body823_4 body823_5

def body823_7 : Prog (BitVec 64) :=
.seq body823_3 body823_6

def body823_8 : Prog (BitVec 64) :=
.seq body823_2 body823_7

def body823_9 : Prog (BitVec 64) :=
.seq body823_1 body823_8

def body823_10 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body823_9

def body823_11 : Prog (BitVec 64) :=
.seq body823_0 body823_10

def body823_12 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("words_of") ([Flapjack.Exp.var Flapjack.VarKind.local "n"]) body823_11

def body823_13 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 96#64])) body823_12

def body823_14 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body823_13

def body823_15 : Prog (BitVec 64) :=
.seq body823_1 body823_2

def body823_16 : Prog (BitVec 64) :=
.seq body823_15 body823_3

def body823_17 : Prog (BitVec 64) :=
.seq body823_16 body823_4

def body823_18 : Prog (BitVec 64) :=
.seq body823_17 body823_5

def body823_19 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body823_18

def body823_20 : Prog (BitVec 64) :=
.seq body823_0 body823_19

def body823_21 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("words_of") ([Flapjack.Exp.var Flapjack.VarKind.local "n"]) body823_20

def body823_22 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 96#64])) body823_21

def body823_23 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body823_22

def originalData823 : Decl (BitVec 64) :=
.function { name := "pre_ripemd160", inline := false, exported := false, params := [], body := body823_14, returnShape := (Flapjack.Shape.one) }
def simplifiedData823 : Decl (BitVec 64) :=
.function { name := "pre_ripemd160", inline := false, exported := false, params := [], body := body823_23, returnShape := (Flapjack.Shape.one) }
def original823 := Pancake.PanLang.declToHOL originalData823
def simplified823 := Pancake.PanLang.declToHOL simplifiedData823
end InitECandidate.Proofs.FrontendStages.Declarations
