import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify561
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body577_0 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body577_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "move_ether"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 16#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 32#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "v"]

def body577_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "emit_transfer_log"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 16#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 32#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "v"]

def body577_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "same") (Flapjack.Exp.const 0#64)) body577_2 body577_0

def body577_4 : Prog (BitVec 64) :=
.decCall ("same") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 16#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 32#64]),
  Flapjack.Exp.const 20#64]) body577_3

def body577_5 : Prog (BitVec 64) :=
.seq body577_1 body577_4

def body577_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64)) body577_5 body577_0

def body577_7 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "v"]) body577_6

def body577_8 : Prog (BitVec 64) :=
.dec ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 56#64])) body577_7

def body577_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 136#64]))
  (Flapjack.Exp.const 0#64)) body577_8 body577_0

def body577_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "run_precompile" [Flapjack.Exp.var Flapjack.VarKind.local "pi"]

def body577_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 168#64]))
  (Flapjack.Exp.const 0#64)) body577_10 body577_0

def body577_12 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body577_13 : Prog (BitVec 64) :=
.seq body577_11 body577_12

def body577_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "pi") (Flapjack.Exp.const 0#64)) body577_13 body577_0

def body577_15 : Prog (BitVec 64) :=
.decCall ("pi") (Flapjack.Shape.one) ("precompile_index") ([Flapjack.Exp.var Flapjack.VarKind.local "ca"]) body577_14

def body577_16 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "ca") (Flapjack.Exp.const 0#64)) body577_15 body577_0

def body577_17 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body577_18 : Prog (BitVec 64) :=
.seq body577_0 body577_17

def body577_19 : Prog (BitVec 64) :=
.seq body577_16 body577_18

def body577_20 : Prog (BitVec 64) :=
.dec ("ca") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 104#64])) body577_19

def body577_21 : Prog (BitVec 64) :=
.seq body577_9 body577_20

def body577_22 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body577_21

def body577_23 : Prog (BitVec 64) :=
.seq body577_0 body577_22

def body577_24 : Prog (BitVec 64) :=
.seq body577_16 body577_17

def body577_25 : Prog (BitVec 64) :=
.dec ("ca") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 104#64])) body577_24

def body577_26 : Prog (BitVec 64) :=
.seq body577_9 body577_25

def body577_27 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body577_26

def originalData577 : Decl (BitVec 64) :=
.function { name := "frame_prologue", inline := false, exported := false, params := [], body := body577_23, returnShape := (Flapjack.Shape.one) }
def simplifiedData577 : Decl (BitVec 64) :=
.function { name := "frame_prologue", inline := false, exported := false, params := [], body := body577_27, returnShape := (Flapjack.Shape.one) }
def original577 := Pancake.PanLang.declToHOL originalData577
def simplified577 := Pancake.PanLang.declToHOL simplifiedData577
end InitECandidate.Proofs.FrontendStages.Declarations
