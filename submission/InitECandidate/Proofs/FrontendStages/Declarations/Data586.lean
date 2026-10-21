import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify570
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body586_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 11#64)

def body586_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body586_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.loadByte (Flapjack.Exp.var Flapjack.VarKind.local "code"))
  (Flapjack.Exp.const 239#64)) body586_0 body586_1

def body586_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "n")) body586_2 body586_1

def body586_4 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 4#64)

def body586_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 65536#64) (Flapjack.Exp.var Flapjack.VarKind.local "n")) body586_4 body586_1

def body586_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas"
  [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 6#64, Flapjack.Exp.var Flapjack.VarKind.local "w"]]

def body586_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_state_gas"
  [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 1530#64]]

def body586_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "stored_code", Flapjack.Exp.var Flapjack.VarKind.local "code",
    Flapjack.Exp.var Flapjack.VarKind.local "n"]

def body586_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "set_code"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 32#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "stored_code", Flapjack.Exp.var Flapjack.VarKind.local "n"]

def body586_10 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body586_11 : Prog (BitVec 64) :=
.seq body586_9 body586_10

def body586_12 : Prog (BitVec 64) :=
.seq body586_8 body586_11

def body586_13 : Prog (BitVec 64) :=
.decCall ("stored_code") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 8#64]]) body586_12

def body586_14 : Prog (BitVec 64) :=
.seq body586_7 body586_13

def body586_15 : Prog (BitVec 64) :=
.seq body586_6 body586_14

def body586_16 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("words_of") ([Flapjack.Exp.var Flapjack.VarKind.local "n"]) body586_15

def body586_17 : Prog (BitVec 64) :=
.seq body586_5 body586_16

def body586_18 : Prog (BitVec 64) :=
.seq body586_3 body586_17

def body586_19 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 128#64])) body586_18

def body586_20 : Prog (BitVec 64) :=
.dec ("code") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 120#64])) body586_19

def body586_21 : Prog (BitVec 64) :=
.seq body586_3 body586_5

def body586_22 : Prog (BitVec 64) :=
.seq body586_6 body586_7

def body586_23 : Prog (BitVec 64) :=
.seq body586_8 body586_9

def body586_24 : Prog (BitVec 64) :=
.seq body586_23 body586_10

def body586_25 : Prog (BitVec 64) :=
.decCall ("stored_code") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 8#64]]) body586_24

def body586_26 : Prog (BitVec 64) :=
.seq body586_22 body586_25

def body586_27 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("words_of") ([Flapjack.Exp.var Flapjack.VarKind.local "n"]) body586_26

def body586_28 : Prog (BitVec 64) :=
.seq body586_21 body586_27

def body586_29 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 128#64])) body586_28

def body586_30 : Prog (BitVec 64) :=
.dec ("code") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 120#64])) body586_29

def originalData586 : Decl (BitVec 64) :=
.function { name := "create_finish", inline := false, exported := false, params := [("msg", Flapjack.Shape.one), ("child", Flapjack.Shape.one)], body := body586_20, returnShape := (Flapjack.Shape.one) }
def simplifiedData586 : Decl (BitVec 64) :=
.function { name := "create_finish", inline := false, exported := false, params := [("msg", Flapjack.Shape.one), ("child", Flapjack.Shape.one)], body := body586_30, returnShape := (Flapjack.Shape.one) }
def original586 := Pancake.PanLang.declToHOL originalData586
def simplified586 := Pancake.PanLang.declToHOL simplifiedData586
end InitECandidate.Proofs.FrontendStages.Declarations
