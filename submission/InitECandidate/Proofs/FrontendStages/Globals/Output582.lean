import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data582
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate566
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody582_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "csnap"), none)) "state_snapshot" []

def globalBody582_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "destroy_storage" [Flapjack.Exp.var Flapjack.VarKind.local "target"]

def globalBody582_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mark_account_created" [Flapjack.Exp.var Flapjack.VarKind.local "target"]

def globalBody582_3 : Prog (BitVec 64) :=
.seq globalBody582_1 globalBody582_2

def globalBody582_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "increment_nonce" [Flapjack.Exp.var Flapjack.VarKind.local "target"]

def globalBody582_5 : Prog (BitVec 64) :=
.seq globalBody582_3 globalBody582_4

def globalBody582_6 : Prog (BitVec 64) :=
.dec ("target") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cm", Flapjack.Exp.const 32#64])) globalBody582_5

def globalBody582_7 : Prog (BitVec 64) :=
.seq globalBody582_0 globalBody582_6

def globalBody582_8 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody582_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "kind") (Flapjack.Exp.const 2#64)) globalBody582_7 globalBody582_8

def globalBody582_10 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 7#64)

def globalBody582_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 1024#64)
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cm", Flapjack.Exp.const 128#64]))) globalBody582_10 globalBody582_8

def globalBody582_12 : Prog (BitVec 64) :=
.seq globalBody582_9 globalBody582_11

def globalBody582_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "frame_open"
  [Flapjack.Exp.var Flapjack.VarKind.local "cm", Flapjack.Exp.var Flapjack.VarKind.local "kind"]

def globalBody582_14 : Prog (BitVec 64) :=
.seq globalBody582_12 globalBody582_13

def globalBody582_15 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 288#64]),
      Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "snapshot")

def globalBody582_16 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 288#64]),
      Flapjack.Exp.const 96#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "csnap")

def globalBody582_17 : Prog (BitVec 64) :=
.seq globalBody582_15 globalBody582_16

def globalBody582_18 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 288#64]),
      Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "child_mark")

def globalBody582_19 : Prog (BitVec 64) :=
.seq globalBody582_17 globalBody582_18

def globalBody582_20 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 288#64]),
      Flapjack.Exp.const 56#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "child_mem_mark")

def globalBody582_21 : Prog (BitVec 64) :=
.seq globalBody582_19 globalBody582_20

def globalBody582_22 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 288#64]),
      Flapjack.Exp.const 64#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "new_account_charged")

def globalBody582_23 : Prog (BitVec 64) :=
.seq globalBody582_21 globalBody582_22

def globalBody582_24 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 288#64]),
      Flapjack.Exp.const 72#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "out_start")

def globalBody582_25 : Prog (BitVec 64) :=
.seq globalBody582_23 globalBody582_24

def globalBody582_26 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 288#64]),
      Flapjack.Exp.const 80#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "out_size")

def globalBody582_27 : Prog (BitVec 64) :=
.seq globalBody582_25 globalBody582_26

def globalBody582_28 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 288#64]),
      Flapjack.Exp.const 88#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "contract_address")

def globalBody582_29 : Prog (BitVec 64) :=
.seq globalBody582_27 globalBody582_28

def globalBody582_30 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "frame_start" []

def globalBody582_31 : Prog (BitVec 64) :=
.seq globalBody582_29 globalBody582_30

def globalBody582_32 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody582_33 : Prog (BitVec 64) :=
.seq globalBody582_31 globalBody582_32

def globalBody582_34 : Prog (BitVec 64) :=
.decCall ("snapshot") (Flapjack.Shape.one) ("state_snapshot") ([]) globalBody582_33

def globalBody582_35 : Prog (BitVec 64) :=
.seq globalBody582_14 globalBody582_34

def globalBody582_36 : Prog (BitVec 64) :=
.dec ("csnap") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody582_35

def globalData582 : Decl (BitVec 64) :=
.function { name := "start_child", inline := false, exported := false, params := [("cm", Flapjack.Shape.one), ("kind", Flapjack.Shape.one), ("child_mark", Flapjack.Shape.one),
  ("child_mem_mark", Flapjack.Shape.one), ("new_account_charged", Flapjack.Shape.one),
  ("out_start", Flapjack.Shape.one), ("out_size", Flapjack.Shape.one), ("contract_address", Flapjack.Shape.one)], body := globalBody582_36, returnShape := (Flapjack.Shape.one) }
def globalOutput582 := Pancake.PanLang.declToHOL globalData582
end InitECandidate.Proofs.FrontendStages.Declarations
