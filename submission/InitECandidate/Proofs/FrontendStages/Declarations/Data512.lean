import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify496
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body512_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 3#64]

def body512_1 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 2#64)

def body512_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body512_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "item")
  (Flapjack.Exp.var Flapjack.VarKind.local "sp")) body512_1 body512_2

def body512_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push" [Flapjack.Exp.var Flapjack.VarKind.local "v"]

def body512_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body512_6 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body512_7 : Prog (BitVec 64) :=
.seq body512_5 body512_6

def body512_8 : Prog (BitVec 64) :=
.seq body512_4 body512_7

def body512_9 : Prog (BitVec 64) :=
.dec ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 8#64]),
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.sub
            [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "sp", Flapjack.Exp.const 1#64],
              Flapjack.Exp.var Flapjack.VarKind.local "item"],
          Flapjack.Exp.const 32#64]])) body512_8

def body512_10 : Prog (BitVec 64) :=
.seq body512_3 body512_9

def body512_11 : Prog (BitVec 64) :=
.dec ("sp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 16#64])) body512_10

def body512_12 : Prog (BitVec 64) :=
.seq body512_0 body512_11

def body512_13 : Prog (BitVec 64) :=
.seq body512_4 body512_5

def body512_14 : Prog (BitVec 64) :=
.seq body512_13 body512_6

def body512_15 : Prog (BitVec 64) :=
.dec ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 8#64]),
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.sub
            [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "sp", Flapjack.Exp.const 1#64],
              Flapjack.Exp.var Flapjack.VarKind.local "item"],
          Flapjack.Exp.const 32#64]])) body512_14

def body512_16 : Prog (BitVec 64) :=
.seq body512_3 body512_15

def body512_17 : Prog (BitVec 64) :=
.dec ("sp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 16#64])) body512_16

def body512_18 : Prog (BitVec 64) :=
.seq body512_0 body512_17

def originalData512 : Decl (BitVec 64) :=
.function { name := "op_dup", inline := false, exported := false, params := [("item", Flapjack.Shape.one)], body := body512_12, returnShape := (Flapjack.Shape.one) }
def simplifiedData512 : Decl (BitVec 64) :=
.function { name := "op_dup", inline := false, exported := false, params := [("item", Flapjack.Shape.one)], body := body512_18, returnShape := (Flapjack.Shape.one) }
def original512 := Pancake.PanLang.declToHOL originalData512
def simplified512 := Pancake.PanLang.declToHOL simplifiedData512
end InitECandidate.Proofs.FrontendStages.Declarations
