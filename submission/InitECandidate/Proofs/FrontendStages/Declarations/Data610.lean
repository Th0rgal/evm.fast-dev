import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify594
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body610_0 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.op Flapjack.BinOp.xor
    [Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "y",
      Flapjack.Exp.var Flapjack.VarKind.local "z"])

def body610_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body610_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "j") (Flapjack.Exp.const 16#64)) body610_0 body610_1

def body610_3 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.op Flapjack.BinOp.and
        [Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "y"],
      Flapjack.Exp.op Flapjack.BinOp.and
        [Flapjack.Exp.op Flapjack.BinOp.xor
            [Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.const 4294967295#64],
          Flapjack.Exp.var Flapjack.VarKind.local "z"]])

def body610_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "j") (Flapjack.Exp.const 32#64)) body610_3 body610_1

def body610_5 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.op Flapjack.BinOp.xor
    [Flapjack.Exp.op Flapjack.BinOp.or
        [Flapjack.Exp.var Flapjack.VarKind.local "x",
          Flapjack.Exp.op Flapjack.BinOp.xor
            [Flapjack.Exp.var Flapjack.VarKind.local "y", Flapjack.Exp.const 4294967295#64]],
      Flapjack.Exp.var Flapjack.VarKind.local "z"])

def body610_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "j") (Flapjack.Exp.const 48#64)) body610_5 body610_1

def body610_7 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.op Flapjack.BinOp.and
        [Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "z"],
      Flapjack.Exp.op Flapjack.BinOp.and
        [Flapjack.Exp.var Flapjack.VarKind.local "y",
          Flapjack.Exp.op Flapjack.BinOp.xor
            [Flapjack.Exp.var Flapjack.VarKind.local "z", Flapjack.Exp.const 4294967295#64]]])

def body610_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "j") (Flapjack.Exp.const 64#64)) body610_7 body610_1

def body610_9 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.op Flapjack.BinOp.xor
    [Flapjack.Exp.var Flapjack.VarKind.local "x",
      Flapjack.Exp.op Flapjack.BinOp.or
        [Flapjack.Exp.var Flapjack.VarKind.local "y",
          Flapjack.Exp.op Flapjack.BinOp.xor
            [Flapjack.Exp.var Flapjack.VarKind.local "z", Flapjack.Exp.const 4294967295#64]]])

def body610_10 : Prog (BitVec 64) :=
.seq body610_8 body610_9

def body610_11 : Prog (BitVec 64) :=
.seq body610_6 body610_10

def body610_12 : Prog (BitVec 64) :=
.seq body610_4 body610_11

def body610_13 : Prog (BitVec 64) :=
.seq body610_2 body610_12

def body610_14 : Prog (BitVec 64) :=
.seq body610_2 body610_4

def body610_15 : Prog (BitVec 64) :=
.seq body610_14 body610_6

def body610_16 : Prog (BitVec 64) :=
.seq body610_15 body610_8

def body610_17 : Prog (BitVec 64) :=
.seq body610_16 body610_9

def originalData610 : Decl (BitVec 64) :=
.function { name := "rmd_f", inline := false, exported := false, params := [("j", Flapjack.Shape.one), ("x", Flapjack.Shape.one), ("y", Flapjack.Shape.one), ("z", Flapjack.Shape.one)], body := body610_13, returnShape := (Flapjack.Shape.one) }
def simplifiedData610 : Decl (BitVec 64) :=
.function { name := "rmd_f", inline := false, exported := false, params := [("j", Flapjack.Shape.one), ("x", Flapjack.Shape.one), ("y", Flapjack.Shape.one), ("z", Flapjack.Shape.one)], body := body610_17, returnShape := (Flapjack.Shape.one) }
def original610 := Pancake.PanLang.declToHOL originalData610
def simplified610 := Pancake.PanLang.declToHOL simplifiedData610
end InitECandidate.Proofs.FrontendStages.Declarations
