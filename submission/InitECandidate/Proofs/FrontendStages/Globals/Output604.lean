import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data604
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate588
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody604_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 96#64]

def globalBody604_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.const 12#64)

def globalBody604_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 48#64]))

def globalBody604_3 : Prog (BitVec 64) :=
.seq globalBody604_1 globalBody604_2

def globalBody604_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 40#64]))

def globalBody604_5 : Prog (BitVec 64) :=
.seq globalBody604_3 globalBody604_4

def globalBody604_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 264#64]))

def globalBody604_7 : Prog (BitVec 64) :=
.seq globalBody604_5 globalBody604_6

def globalBody604_8 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "out")

def globalBody604_9 : Prog (BitVec 64) :=
.seq globalBody604_7 globalBody604_8

def globalBody604_10 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody604_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "dep") (Flapjack.Exp.const 0#64)) globalBody604_9 globalBody604_10

def globalBody604_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "frame"), none)) "process_create_message"
  [Flapjack.Exp.var Flapjack.VarKind.local "msg"]

def globalBody604_13 : Prog (BitVec 64) :=
.seq globalBody604_11 globalBody604_12

def globalBody604_14 : Prog (BitVec 64) :=
.decCall ("dep") (Flapjack.Shape.one) ("account_deployable") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 32#64])]) globalBody604_13

def globalBody604_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "frame"), none)) "process_message"
  [Flapjack.Exp.var Flapjack.VarKind.local "msg"]

def globalBody604_16 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 24#64]))
  (Flapjack.Exp.const 0#64)) globalBody604_14 globalBody604_15

def globalBody604_17 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 64#64]))

def globalBody604_18 : Prog (BitVec 64) :=
.seq globalBody604_16 globalBody604_17

def globalBody604_19 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 160#64]))

def globalBody604_20 : Prog (BitVec 64) :=
.seq globalBody604_18 globalBody604_19

def globalBody604_21 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 120#64]))

def globalBody604_22 : Prog (BitVec 64) :=
.seq globalBody604_20 globalBody604_21

def globalBody604_23 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 128#64]))

def globalBody604_24 : Prog (BitVec 64) :=
.seq globalBody604_22 globalBody604_23

def globalBody604_25 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 72#64]))

def globalBody604_26 : Prog (BitVec 64) :=
.seq globalBody604_24 globalBody604_25

def globalBody604_27 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 184#64]))

def globalBody604_28 : Prog (BitVec 64) :=
.seq globalBody604_26 globalBody604_27

def globalBody604_29 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 72#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "fsg",
      Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 200#64])])

def globalBody604_30 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 88#64]))

def globalBody604_31 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 136#64]))

def globalBody604_32 : Prog (BitVec 64) :=
.seq globalBody604_30 globalBody604_31

def globalBody604_33 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "rc" (Flapjack.Exp.const 0#64)

def globalBody604_34 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "rc") (Flapjack.Exp.const 0#64)) globalBody604_33 globalBody604_10

def globalBody604_35 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "rc")

def globalBody604_36 : Prog (BitVec 64) :=
.seq globalBody604_34 globalBody604_35

def globalBody604_37 : Prog (BitVec 64) :=
.dec ("rc") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 96#64])) globalBody604_36

def globalBody604_38 : Prog (BitVec 64) :=
.seq globalBody604_32 globalBody604_37

def globalBody604_39 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 160#64]))
  (Flapjack.Exp.const 0#64)) globalBody604_38 globalBody604_10

def globalBody604_40 : Prog (BitVec 64) :=
.seq globalBody604_29 globalBody604_39

def globalBody604_41 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 80#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 208#64]))

def globalBody604_42 : Prog (BitVec 64) :=
.seq globalBody604_40 globalBody604_41

def globalBody604_43 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 88#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 224#64]))

def globalBody604_44 : Prog (BitVec 64) :=
.seq globalBody604_42 globalBody604_43

def globalBody604_45 : Prog (BitVec 64) :=
.seq globalBody604_44 globalBody604_8

def globalBody604_46 : Prog (BitVec 64) :=
.decCall ("fsg") (Flapjack.Shape.one) ("frame_state_gas_used") ([Flapjack.Exp.var Flapjack.VarKind.local "frame"]) globalBody604_45

def globalBody604_47 : Prog (BitVec 64) :=
.seq globalBody604_28 globalBody604_46

def globalBody604_48 : Prog (BitVec 64) :=
.dec ("frame") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody604_47

def globalBody604_49 : Prog (BitVec 64) :=
.seq globalBody604_0 globalBody604_48

def globalBody604_50 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) globalBody604_49

def globalData604 : Decl (BitVec 64) :=
.function { name := "process_message_call", inline := false, exported := false, params := [("msg", Flapjack.Shape.one)], body := globalBody604_50, returnShape := (Flapjack.Shape.one) }
def globalOutput604 := Pancake.PanLang.declToHOL globalData604
end InitECandidate.Proofs.FrontendStages.Declarations
