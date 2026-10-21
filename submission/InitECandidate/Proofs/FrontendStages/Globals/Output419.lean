import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data419
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate398
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody419_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_le64"
  [Flapjack.Exp.var Flapjack.VarKind.local "kb",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 224#64])]

def globalBody419_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "kb", Flapjack.Exp.const 8#64],
    Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 20#64]

def globalBody419_2 : Prog (BitVec 64) :=
.seq globalBody419_0 globalBody419_1

def globalBody419_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "m"))

def globalBody419_4 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody419_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "m"))
  (Flapjack.Exp.const 0#64)) globalBody419_3 globalBody419_4

def globalBody419_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 80#64]

def globalBody419_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 48#64],
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 136#64]),
    Flapjack.Exp.const 32#64]

def globalBody419_8 : Prog (BitVec 64) :=
.seq globalBody419_6 globalBody419_7

def globalBody419_9 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "rec") (Flapjack.Exp.const 1#64)

def globalBody419_10 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pre", Flapjack.Exp.const 0#64]))

def globalBody419_11 : Prog (BitVec 64) :=
.seq globalBody419_9 globalBody419_10

def globalBody419_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pre", Flapjack.Exp.const 8#64]))

def globalBody419_13 : Prog (BitVec 64) :=
.seq globalBody419_11 globalBody419_12

def globalBody419_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 48#64],
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pre", Flapjack.Exp.const 48#64]),
    Flapjack.Exp.const 32#64]

def globalBody419_15 : Prog (BitVec 64) :=
.seq globalBody419_13 globalBody419_14

def globalBody419_16 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "pre") (Flapjack.Exp.const 1#64)) globalBody419_15 globalBody419_4

def globalBody419_17 : Prog (BitVec 64) :=
.seq globalBody419_8 globalBody419_16

def globalBody419_18 : Prog (BitVec 64) :=
.seq globalBody419_17 globalBody419_0

def globalBody419_19 : Prog (BitVec 64) :=
.seq globalBody419_18 globalBody419_1

def globalBody419_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 232#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "kb", Flapjack.Exp.var Flapjack.VarKind.local "rec"]

def globalBody419_21 : Prog (BitVec 64) :=
.seq globalBody419_19 globalBody419_20

def globalBody419_22 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "rec")

def globalBody419_23 : Prog (BitVec 64) :=
.seq globalBody419_21 globalBody419_22

def globalBody419_24 : Prog (BitVec 64) :=
.decCall ("rec") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 80#64]) globalBody419_23

def globalBody419_25 : Prog (BitVec 64) :=
.decCall ("pre") (Flapjack.Shape.one) ("get_pre_tx_account") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) globalBody419_24

def globalBody419_26 : Prog (BitVec 64) :=
.seq globalBody419_5 globalBody419_25

def globalBody419_27 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 232#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "kb"]) globalBody419_26

def globalBody419_28 : Prog (BitVec 64) :=
.seq globalBody419_2 globalBody419_27

def globalBody419_29 : Prog (BitVec 64) :=
.dec ("kb") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 248#64])) globalBody419_28

def globalData419 : Decl (BitVec 64) :=
.function { name := "idx_start_account", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := globalBody419_29, returnShape := (Flapjack.Shape.one) }
def globalOutput419 := Pancake.PanLang.declToHOL globalData419
end InitECandidate.Proofs.FrontendStages.Declarations
