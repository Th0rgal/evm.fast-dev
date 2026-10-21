import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify501
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body517_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 3#64]

def body517_1 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 2#64)

def body517_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body517_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 16#64]))
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body517_1 body517_2

def body517_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push" [Flapjack.Exp.var Flapjack.VarKind.local "v"]

def body517_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 2#64]

def body517_6 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body517_7 : Prog (BitVec 64) :=
.seq body517_5 body517_6

def body517_8 : Prog (BitVec 64) :=
.seq body517_4 body517_7

def body517_9 : Prog (BitVec 64) :=
.dec ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 8#64]),
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.sub
            [Flapjack.Exp.var Flapjack.VarKind.local "sp", Flapjack.Exp.var Flapjack.VarKind.local "n"],
          Flapjack.Exp.const 32#64]])) body517_8

def body517_10 : Prog (BitVec 64) :=
.dec ("sp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 16#64])) body517_9

def body517_11 : Prog (BitVec 64) :=
.seq body517_3 body517_10

def body517_12 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("decode_single") ([Flapjack.Exp.var Flapjack.VarKind.local "imm"]) body517_11

def body517_13 : Prog (BitVec 64) :=
.decCall ("imm") (Flapjack.Shape.one) ("code_imm") ([]) body517_12

def body517_14 : Prog (BitVec 64) :=
.seq body517_0 body517_13

def body517_15 : Prog (BitVec 64) :=
.seq body517_4 body517_5

def body517_16 : Prog (BitVec 64) :=
.seq body517_15 body517_6

def body517_17 : Prog (BitVec 64) :=
.dec ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 8#64]),
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.sub
            [Flapjack.Exp.var Flapjack.VarKind.local "sp", Flapjack.Exp.var Flapjack.VarKind.local "n"],
          Flapjack.Exp.const 32#64]])) body517_16

def body517_18 : Prog (BitVec 64) :=
.dec ("sp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 16#64])) body517_17

def body517_19 : Prog (BitVec 64) :=
.seq body517_3 body517_18

def body517_20 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("decode_single") ([Flapjack.Exp.var Flapjack.VarKind.local "imm"]) body517_19

def body517_21 : Prog (BitVec 64) :=
.decCall ("imm") (Flapjack.Shape.one) ("code_imm") ([]) body517_20

def body517_22 : Prog (BitVec 64) :=
.seq body517_0 body517_21

def originalData517 : Decl (BitVec 64) :=
.function { name := "op_dupn", inline := false, exported := false, params := [], body := body517_14, returnShape := (Flapjack.Shape.one) }
def simplifiedData517 : Decl (BitVec 64) :=
.function { name := "op_dupn", inline := false, exported := false, params := [], body := body517_22, returnShape := (Flapjack.Shape.one) }
def original517 := Pancake.PanLang.declToHOL originalData517
def simplified517 := Pancake.PanLang.declToHOL simplifiedData517
end InitECandidate.Proofs.FrontendStages.Declarations
