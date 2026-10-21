import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data591
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate575
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody591_0 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pm", Flapjack.Exp.const 0#64]))

def globalBody591_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pm", Flapjack.Exp.const 8#64]))

def globalBody591_2 : Prog (BitVec 64) :=
.seq globalBody591_0 globalBody591_1

def globalBody591_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "caller")

def globalBody591_4 : Prog (BitVec 64) :=
.seq globalBody591_2 globalBody591_3

def globalBody591_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "target")

def globalBody591_6 : Prog (BitVec 64) :=
.seq globalBody591_4 globalBody591_5

def globalBody591_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "current_target")

def globalBody591_8 : Prog (BitVec 64) :=
.seq globalBody591_6 globalBody591_7

def globalBody591_9 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "gas")

def globalBody591_10 : Prog (BitVec 64) :=
.seq globalBody591_8 globalBody591_9

def globalBody591_11 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "reservoir")

def globalBody591_12 : Prog (BitVec 64) :=
.seq globalBody591_10 globalBody591_11

def globalBody591_13 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "value")

def globalBody591_14 : Prog (BitVec 64) :=
.seq globalBody591_12 globalBody591_13

def globalBody591_15 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 88#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "data")

def globalBody591_16 : Prog (BitVec 64) :=
.seq globalBody591_14 globalBody591_15

def globalBody591_17 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "data_n")

def globalBody591_18 : Prog (BitVec 64) :=
.seq globalBody591_16 globalBody591_17

def globalBody591_19 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 104#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "code_address")

def globalBody591_20 : Prog (BitVec 64) :=
.seq globalBody591_18 globalBody591_19

def globalBody591_21 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 112#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "code")

def globalBody591_22 : Prog (BitVec 64) :=
.seq globalBody591_20 globalBody591_21

def globalBody591_23 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "code_n")

def globalBody591_24 : Prog (BitVec 64) :=
.seq globalBody591_22 globalBody591_23

def globalBody591_25 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 128#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pm", Flapjack.Exp.const 128#64]),
      Flapjack.Exp.const 1#64])

def globalBody591_26 : Prog (BitVec 64) :=
.seq globalBody591_24 globalBody591_25

def globalBody591_27 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 136#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "transfer")

def globalBody591_28 : Prog (BitVec 64) :=
.seq globalBody591_26 globalBody591_27

def globalBody591_29 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "stat" (Flapjack.Exp.const 1#64)

def globalBody591_30 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody591_31 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pm", Flapjack.Exp.const 144#64]))
  (Flapjack.Exp.const 0#64)) globalBody591_29 globalBody591_30

def globalBody591_32 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 144#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "stat")

def globalBody591_33 : Prog (BitVec 64) :=
.seq globalBody591_31 globalBody591_32

def globalBody591_34 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 152#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
        Flapjack.Exp.const 168#64]))

def globalBody591_35 : Prog (BitVec 64) :=
.seq globalBody591_33 globalBody591_34

def globalBody591_36 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 160#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
        Flapjack.Exp.const 176#64]))

def globalBody591_37 : Prog (BitVec 64) :=
.seq globalBody591_35 globalBody591_36

def globalBody591_38 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 168#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "disable_pre")

def globalBody591_39 : Prog (BitVec 64) :=
.seq globalBody591_37 globalBody591_38

def globalBody591_40 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "m")

def globalBody591_41 : Prog (BitVec 64) :=
.seq globalBody591_39 globalBody591_40

def globalBody591_42 : Prog (BitVec 64) :=
.dec ("stat") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "is_static") globalBody591_41

def globalBody591_43 : Prog (BitVec 64) :=
.seq globalBody591_28 globalBody591_42

def globalBody591_44 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.one) ("msg_new_scratch") ([]) globalBody591_43

def globalBody591_45 : Prog (BitVec 64) :=
.dec ("pm") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 112#64])) globalBody591_44

def globalData591 : Decl (BitVec 64) :=
.function { name := "child_message", inline := false, exported := false, params := [("caller", Flapjack.Shape.one), ("target", Flapjack.Shape.one), ("current_target", Flapjack.Shape.one),
  ("gas", Flapjack.Shape.one), ("reservoir", Flapjack.Shape.one),
  ("value", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("data", Flapjack.Shape.one), ("data_n", Flapjack.Shape.one), ("code_address", Flapjack.Shape.one),
  ("code", Flapjack.Shape.one), ("code_n", Flapjack.Shape.one), ("transfer", Flapjack.Shape.one),
  ("is_static", Flapjack.Shape.one), ("disable_pre", Flapjack.Shape.one)], body := globalBody591_45, returnShape := (Flapjack.Shape.one) }
def globalOutput591 := Pancake.PanLang.declToHOL globalData591
end InitECandidate.Proofs.FrontendStages.Declarations
