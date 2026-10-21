import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify497
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body513_0 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "pa") (Flapjack.Exp.var Flapjack.VarKind.local "b")

def body513_1 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "pb") (Flapjack.Exp.var Flapjack.VarKind.local "a")

def body513_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body513_3 : Prog (BitVec 64) :=
.seq body513_1 body513_2

def body513_4 : Prog (BitVec 64) :=
.seq body513_0 body513_3

def body513_5 : Prog (BitVec 64) :=
.dec ("b") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "pb")) body513_4

def body513_6 : Prog (BitVec 64) :=
.dec ("a") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "pa")) body513_5

def body513_7 : Prog (BitVec 64) :=
.dec ("pb") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "stk",
    Flapjack.Exp.panOp Flapjack.PanOp.mul
      [Flapjack.Exp.op Flapjack.BinOp.sub
          [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "sp", Flapjack.Exp.const 1#64],
            Flapjack.Exp.var Flapjack.VarKind.local "j"],
        Flapjack.Exp.const 32#64]]) body513_6

def body513_8 : Prog (BitVec 64) :=
.dec ("pa") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "stk",
    Flapjack.Exp.panOp Flapjack.PanOp.mul
      [Flapjack.Exp.op Flapjack.BinOp.sub
          [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "sp", Flapjack.Exp.const 1#64],
            Flapjack.Exp.var Flapjack.VarKind.local "i"],
        Flapjack.Exp.const 32#64]]) body513_7

def body513_9 : Prog (BitVec 64) :=
.dec ("stk") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 8#64])) body513_8

def body513_10 : Prog (BitVec 64) :=
.dec ("sp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 16#64])) body513_9

def body513_11 : Prog (BitVec 64) :=
.seq body513_0 body513_1

def body513_12 : Prog (BitVec 64) :=
.seq body513_11 body513_2

def body513_13 : Prog (BitVec 64) :=
.dec ("b") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "pb")) body513_12

def body513_14 : Prog (BitVec 64) :=
.dec ("a") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "pa")) body513_13

def body513_15 : Prog (BitVec 64) :=
.dec ("pb") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "stk",
    Flapjack.Exp.panOp Flapjack.PanOp.mul
      [Flapjack.Exp.op Flapjack.BinOp.sub
          [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "sp", Flapjack.Exp.const 1#64],
            Flapjack.Exp.var Flapjack.VarKind.local "j"],
        Flapjack.Exp.const 32#64]]) body513_14

def body513_16 : Prog (BitVec 64) :=
.dec ("pa") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "stk",
    Flapjack.Exp.panOp Flapjack.PanOp.mul
      [Flapjack.Exp.op Flapjack.BinOp.sub
          [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "sp", Flapjack.Exp.const 1#64],
            Flapjack.Exp.var Flapjack.VarKind.local "i"],
        Flapjack.Exp.const 32#64]]) body513_15

def body513_17 : Prog (BitVec 64) :=
.dec ("stk") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 8#64])) body513_16

def body513_18 : Prog (BitVec 64) :=
.dec ("sp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 16#64])) body513_17

def originalData513 : Decl (BitVec 64) :=
.function { name := "stack_swap_positions", inline := false, exported := false, params := [("i", Flapjack.Shape.one), ("j", Flapjack.Shape.one)], body := body513_10, returnShape := (Flapjack.Shape.one) }
def simplifiedData513 : Decl (BitVec 64) :=
.function { name := "stack_swap_positions", inline := false, exported := false, params := [("i", Flapjack.Shape.one), ("j", Flapjack.Shape.one)], body := body513_18, returnShape := (Flapjack.Shape.one) }
def original513 := Pancake.PanLang.declToHOL originalData513
def simplified513 := Pancake.PanLang.declToHOL simplifiedData513
end InitECandidate.Proofs.FrontendStages.Declarations
