import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify568
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body584_0 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body584_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "set_delegation" []

def body584_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 200#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "used")

def body584_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 72#64]))

def body584_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 192#64])
  (Flapjack.Exp.const 0#64)

def body584_5 : Prog (BitVec 64) :=
.seq body584_3 body584_4

def body584_6 : Prog (BitVec 64) :=
.seq body584_2 body584_5

def body584_7 : Prog (BitVec 64) :=
.decCall ("used") (Flapjack.Shape.one) ("frame_state_gas_used") ([Flapjack.Exp.var Flapjack.VarKind.global "ev"]) body584_6

def body584_8 : Prog (BitVec 64) :=
.seq body584_1 body584_7

def body584_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 152#64]))
  (Flapjack.Exp.const 0#64)) body584_8 body584_0

def body584_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "prepare_dispatch" []

def body584_11 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body584_12 : Prog (BitVec 64) :=
.seq body584_0 body584_11

def body584_13 : Prog (BitVec 64) :=
.seq body584_10 body584_12

def body584_14 : Prog (BitVec 64) :=
.seq body584_0 body584_13

def body584_15 : Prog (BitVec 64) :=
.seq body584_9 body584_14

def body584_16 : Prog (BitVec 64) :=
.dec ("te") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 8#64])) body584_15

def body584_17 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body584_16

def body584_18 : Prog (BitVec 64) :=
.seq body584_0 body584_17

def body584_19 : Prog (BitVec 64) :=
.seq body584_2 body584_3

def body584_20 : Prog (BitVec 64) :=
.seq body584_19 body584_4

def body584_21 : Prog (BitVec 64) :=
.decCall ("used") (Flapjack.Shape.one) ("frame_state_gas_used") ([Flapjack.Exp.var Flapjack.VarKind.global "ev"]) body584_20

def body584_22 : Prog (BitVec 64) :=
.seq body584_1 body584_21

def body584_23 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 152#64]))
  (Flapjack.Exp.const 0#64)) body584_22 body584_0

def body584_24 : Prog (BitVec 64) :=
.seq body584_23 body584_10

def body584_25 : Prog (BitVec 64) :=
.seq body584_24 body584_11

def body584_26 : Prog (BitVec 64) :=
.dec ("te") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 8#64])) body584_25

def body584_27 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body584_26

def originalData584 : Decl (BitVec 64) :=
.function { name := "depth0_prepare", inline := false, exported := false, params := [], body := body584_18, returnShape := (Flapjack.Shape.one) }
def simplifiedData584 : Decl (BitVec 64) :=
.function { name := "depth0_prepare", inline := false, exported := false, params := [], body := body584_27, returnShape := (Flapjack.Shape.one) }
def original584 := Pancake.PanLang.declToHOL originalData584
def simplified584 := Pancake.PanLang.declToHOL simplifiedData584
end InitECandidate.Proofs.FrontendStages.Declarations
