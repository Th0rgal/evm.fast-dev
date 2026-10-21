import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify565
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body581_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "done" (Flapjack.Exp.const 1#64)

def body581_1 : Prog (BitVec 64) :=
Flapjack.Prog.call
  (some
    (none,
      some
        ("EvmErr", "err",
          Flapjack.Prog.call (some (none, none)) "frame_exception" [Flapjack.Exp.var Flapjack.VarKind.local "err"])))
  "op_dispatch"
  [Flapjack.Exp.loadByte
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.load Flapjack.Shape.one
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 48#64]),
          Flapjack.Exp.var Flapjack.VarKind.local "pc"])]

def body581_2 : Prog (BitVec 64) :=
.dec ("err") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body581_1

def body581_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "pc")
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 56#64]))) body581_0 body581_2

def body581_4 : Prog (BitVec 64) :=
.dec ("pc") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 0#64])) body581_3

def body581_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 104#64]))
  (Flapjack.Exp.const 0#64)) body581_0 body581_4

def body581_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.global "cur_cont", Flapjack.Exp.const 32#64]))
  (Flapjack.Exp.const 0#64)) body581_0 body581_5

def body581_7 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body581_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "frame_epilogue" []

def body581_9 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.global "ev"
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "cur_cont", Flapjack.Exp.const 0#64]))

def body581_10 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.global "cur_cont"
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "cur_cont", Flapjack.Exp.const 8#64]))

def body581_11 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "go" (Flapjack.Exp.const 0#64)

def body581_12 : Prog (BitVec 64) :=
.seq body581_10 body581_11

def body581_13 : Prog (BitVec 64) :=
.seq body581_9 body581_12

def body581_14 : Prog (BitVec 64) :=
Flapjack.Prog.call
  (some
    (none,
      some
        ("EvmErr", "err2",
          Flapjack.Prog.call (some (none, none)) "frame_exception" [Flapjack.Exp.var Flapjack.VarKind.local "err2"])))
  "finish_child" []

def body581_15 : Prog (BitVec 64) :=
.dec ("err2") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body581_14

def body581_16 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.global "cur_cont", Flapjack.Exp.const 16#64]))
  (Flapjack.Exp.const 0#64)) body581_13 body581_15

def body581_17 : Prog (BitVec 64) :=
.seq body581_8 body581_16

def body581_18 : Prog (BitVec 64) :=
.seq body581_7 body581_17

def body581_19 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "done") (Flapjack.Exp.const 0#64)) body581_18 body581_7

def body581_20 : Prog (BitVec 64) :=
.seq body581_6 body581_19

def body581_21 : Prog (BitVec 64) :=
.dec ("done") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body581_20

def body581_22 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "go") (Flapjack.Exp.const 0#64)) body581_21

def body581_23 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body581_24 : Prog (BitVec 64) :=
.seq body581_22 body581_23

def body581_25 : Prog (BitVec 64) :=
.dec ("go") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) body581_24

def body581_26 : Prog (BitVec 64) :=
.seq body581_9 body581_10

def body581_27 : Prog (BitVec 64) :=
.seq body581_26 body581_11

def body581_28 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.global "cur_cont", Flapjack.Exp.const 16#64]))
  (Flapjack.Exp.const 0#64)) body581_27 body581_15

def body581_29 : Prog (BitVec 64) :=
.seq body581_8 body581_28

def body581_30 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "done") (Flapjack.Exp.const 0#64)) body581_29 body581_7

def body581_31 : Prog (BitVec 64) :=
.seq body581_6 body581_30

def body581_32 : Prog (BitVec 64) :=
.dec ("done") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body581_31

def body581_33 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "go") (Flapjack.Exp.const 0#64)) body581_32

def body581_34 : Prog (BitVec 64) :=
.seq body581_33 body581_23

def body581_35 : Prog (BitVec 64) :=
.dec ("go") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) body581_34

def originalData581 : Decl (BitVec 64) :=
.function { name := "run_frames", inline := false, exported := false, params := [], body := body581_25, returnShape := (Flapjack.Shape.one) }
def simplifiedData581 : Decl (BitVec 64) :=
.function { name := "run_frames", inline := false, exported := false, params := [], body := body581_35, returnShape := (Flapjack.Shape.one) }
def original581 := Pancake.PanLang.declToHOL originalData581
def simplified581 := Pancake.PanLang.declToHOL simplifiedData581
end InitECandidate.Proofs.FrontendStages.Declarations
