import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data581
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate565
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody581_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "done" (Flapjack.Exp.const 1#64)

def globalBody581_1 : Prog (BitVec 64) :=
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
              [Flapjack.Exp.load Flapjack.Shape.one
                  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
                Flapjack.Exp.const 48#64]),
          Flapjack.Exp.var Flapjack.VarKind.local "pc"])]

def globalBody581_2 : Prog (BitVec 64) :=
.dec ("err") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody581_1

def globalBody581_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "pc")
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
        Flapjack.Exp.const 56#64]))) globalBody581_0 globalBody581_2

def globalBody581_4 : Prog (BitVec 64) :=
.dec ("pc") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 0#64])) globalBody581_3

def globalBody581_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
        Flapjack.Exp.const 104#64]))
  (Flapjack.Exp.const 0#64)) globalBody581_0 globalBody581_4

def globalBody581_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 288#64]),
        Flapjack.Exp.const 32#64]))
  (Flapjack.Exp.const 0#64)) globalBody581_0 globalBody581_5

def globalBody581_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "frame_epilogue" []

def globalBody581_8 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 288#64]),
        Flapjack.Exp.const 0#64]))

def globalBody581_9 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 288#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 288#64]),
        Flapjack.Exp.const 8#64]))

def globalBody581_10 : Prog (BitVec 64) :=
.seq globalBody581_8 globalBody581_9

def globalBody581_11 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "go" (Flapjack.Exp.const 0#64)

def globalBody581_12 : Prog (BitVec 64) :=
.seq globalBody581_10 globalBody581_11

def globalBody581_13 : Prog (BitVec 64) :=
Flapjack.Prog.call
  (some
    (none,
      some
        ("EvmErr", "err2",
          Flapjack.Prog.call (some (none, none)) "frame_exception" [Flapjack.Exp.var Flapjack.VarKind.local "err2"])))
  "finish_child" []

def globalBody581_14 : Prog (BitVec 64) :=
.dec ("err2") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody581_13

def globalBody581_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 288#64]),
        Flapjack.Exp.const 16#64]))
  (Flapjack.Exp.const 0#64)) globalBody581_12 globalBody581_14

def globalBody581_16 : Prog (BitVec 64) :=
.seq globalBody581_7 globalBody581_15

def globalBody581_17 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody581_18 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "done") (Flapjack.Exp.const 0#64)) globalBody581_16 globalBody581_17

def globalBody581_19 : Prog (BitVec 64) :=
.seq globalBody581_6 globalBody581_18

def globalBody581_20 : Prog (BitVec 64) :=
.dec ("done") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody581_19

def globalBody581_21 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "go") (Flapjack.Exp.const 0#64)) globalBody581_20

def globalBody581_22 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody581_23 : Prog (BitVec 64) :=
.seq globalBody581_21 globalBody581_22

def globalBody581_24 : Prog (BitVec 64) :=
.dec ("go") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) globalBody581_23

def globalData581 : Decl (BitVec 64) :=
.function { name := "run_frames", inline := false, exported := false, params := [], body := globalBody581_24, returnShape := (Flapjack.Shape.one) }
def globalOutput581 := Pancake.PanLang.declToHOL globalData581
end InitECandidate.Proofs.FrontendStages.Declarations
