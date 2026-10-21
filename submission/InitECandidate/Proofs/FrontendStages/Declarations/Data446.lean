import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify430
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body446_0 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 72#64])
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "sgl", Flapjack.Exp.var Flapjack.VarKind.local "amount"])

def body446_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body446_2 : Prog (BitVec 64) :=
.seq body446_0 body446_1

def body446_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body446_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "sgl")
  (Flapjack.Exp.var Flapjack.VarKind.local "amount")) body446_2 body446_3

def body446_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 72#64])
  (Flapjack.Exp.const 0#64)

def body446_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "gl", Flapjack.Exp.var Flapjack.VarKind.local "rem"])

def body446_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 192#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 192#64]),
      Flapjack.Exp.var Flapjack.VarKind.local "rem"])

def body446_8 : Prog (BitVec 64) :=
.seq body446_7 body446_1

def body446_9 : Prog (BitVec 64) :=
.seq body446_6 body446_8

def body446_10 : Prog (BitVec 64) :=
.seq body446_5 body446_9

def body446_11 : Prog (BitVec 64) :=
.dec ("rem") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "amount", Flapjack.Exp.var Flapjack.VarKind.local "sgl"]) body446_10

def body446_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "tot")
  (Flapjack.Exp.var Flapjack.VarKind.local "amount")) body446_11 body446_3

def body446_13 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 4#64)

def body446_14 : Prog (BitVec 64) :=
.seq body446_13 body446_1

def body446_15 : Prog (BitVec 64) :=
.seq body446_12 body446_14

def body446_16 : Prog (BitVec 64) :=
.decCall ("tot") (Flapjack.Shape.one) ("add_sat") ([Flapjack.Exp.var Flapjack.VarKind.local "sgl", Flapjack.Exp.var Flapjack.VarKind.local "gl"]) body446_15

def body446_17 : Prog (BitVec 64) :=
.seq body446_4 body446_16

def body446_18 : Prog (BitVec 64) :=
.dec ("gl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 64#64])) body446_17

def body446_19 : Prog (BitVec 64) :=
.dec ("sgl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 72#64])) body446_18

def body446_20 : Prog (BitVec 64) :=
.seq body446_5 body446_6

def body446_21 : Prog (BitVec 64) :=
.seq body446_20 body446_7

def body446_22 : Prog (BitVec 64) :=
.seq body446_21 body446_1

def body446_23 : Prog (BitVec 64) :=
.dec ("rem") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "amount", Flapjack.Exp.var Flapjack.VarKind.local "sgl"]) body446_22

def body446_24 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "tot")
  (Flapjack.Exp.var Flapjack.VarKind.local "amount")) body446_23 body446_3

def body446_25 : Prog (BitVec 64) :=
.seq body446_24 body446_13

def body446_26 : Prog (BitVec 64) :=
.seq body446_25 body446_1

def body446_27 : Prog (BitVec 64) :=
.decCall ("tot") (Flapjack.Shape.one) ("add_sat") ([Flapjack.Exp.var Flapjack.VarKind.local "sgl", Flapjack.Exp.var Flapjack.VarKind.local "gl"]) body446_26

def body446_28 : Prog (BitVec 64) :=
.seq body446_4 body446_27

def body446_29 : Prog (BitVec 64) :=
.dec ("gl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 64#64])) body446_28

def body446_30 : Prog (BitVec 64) :=
.dec ("sgl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 72#64])) body446_29

def originalData446 : Decl (BitVec 64) :=
.function { name := "charge_state_gas", inline := false, exported := false, params := [("amount", Flapjack.Shape.one)], body := body446_19, returnShape := (Flapjack.Shape.one) }
def simplifiedData446 : Decl (BitVec 64) :=
.function { name := "charge_state_gas", inline := false, exported := false, params := [("amount", Flapjack.Shape.one)], body := body446_30, returnShape := (Flapjack.Shape.one) }
def original446 := Pancake.PanLang.declToHOL originalData446
def simplified446 := Pancake.PanLang.declToHOL simplifiedData446
end InitECandidate.Proofs.FrontendStages.Declarations
