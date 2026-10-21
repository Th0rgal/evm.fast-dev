import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data867
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate834
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody867_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "state_fresh_tx" []

def globalBody867_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 304#64]))

def globalBody867_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "target")

def globalBody867_3 : Prog (BitVec 64) :=
.seq globalBody867_1 globalBody867_2

def globalBody867_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 408#64]),
        Flapjack.Exp.const 48#64]))

def globalBody867_5 : Prog (BitVec 64) :=
.seq globalBody867_3 globalBody867_4

def globalBody867_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 80#64])
  (Flapjack.Exp.const 30000000#64)

def globalBody867_7 : Prog (BitVec 64) :=
.seq globalBody867_5 globalBody867_6

def globalBody867_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 88#64])
  (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 97920#64, Flapjack.Exp.const 16#64])

def globalBody867_9 : Prog (BitVec 64) :=
.seq globalBody867_7 globalBody867_8

def globalBody867_10 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 408#64]))

def globalBody867_11 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "te")

def globalBody867_12 : Prog (BitVec 64) :=
.seq globalBody867_10 globalBody867_11

def globalBody867_13 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 304#64]))

def globalBody867_14 : Prog (BitVec 64) :=
.seq globalBody867_12 globalBody867_13

def globalBody867_15 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "target")

def globalBody867_16 : Prog (BitVec 64) :=
.seq globalBody867_14 globalBody867_15

def globalBody867_17 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "target")

def globalBody867_18 : Prog (BitVec 64) :=
.seq globalBody867_16 globalBody867_17

def globalBody867_19 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.const 30000000#64)

def globalBody867_20 : Prog (BitVec 64) :=
.seq globalBody867_18 globalBody867_19

def globalBody867_21 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 97920#64, Flapjack.Exp.const 16#64])

def globalBody867_22 : Prog (BitVec 64) :=
.seq globalBody867_20 globalBody867_21

def globalBody867_23 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 88#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "data")

def globalBody867_24 : Prog (BitVec 64) :=
.seq globalBody867_22 globalBody867_23

def globalBody867_25 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "data_n")

def globalBody867_26 : Prog (BitVec 64) :=
.seq globalBody867_24 globalBody867_25

def globalBody867_27 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 104#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "target")

def globalBody867_28 : Prog (BitVec 64) :=
.seq globalBody867_26 globalBody867_27

def globalBody867_29 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 112#64])
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "code"))

def globalBody867_30 : Prog (BitVec 64) :=
.seq globalBody867_28 globalBody867_29

def globalBody867_31 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "code"))

def globalBody867_32 : Prog (BitVec 64) :=
.seq globalBody867_30 globalBody867_31

def globalBody867_33 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 152#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "aa")

def globalBody867_34 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 160#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "ak")

def globalBody867_35 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "incorporate_tx_into_block" []

def globalBody867_36 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "system_ret",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 40#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "system_ret_n"]

def globalBody867_37 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "system_ret")

def globalBody867_38 : Prog (BitVec 64) :=
.seq globalBody867_36 globalBody867_37

def globalBody867_39 : Prog (BitVec 64) :=
.decCall ("system_ret") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "system_ret_n", Flapjack.Exp.const 8#64]]) globalBody867_38

def globalBody867_40 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody867_41 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "system_ret_n")) globalBody867_39 globalBody867_40

def globalBody867_42 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "scratch_release" [Flapjack.Exp.var Flapjack.VarKind.local "system_mark"]

def globalBody867_43 : Prog (BitVec 64) :=
.seq globalBody867_41 globalBody867_42

def globalBody867_44 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "frame_mem_release"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 88#64])]

def globalBody867_45 : Prog (BitVec 64) :=
.seq globalBody867_43 globalBody867_44

def globalBody867_46 : Prog (BitVec 64) :=
.dec ("system_ret_n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 48#64])) globalBody867_45

def globalBody867_47 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "system_mark") (Flapjack.Exp.const 0#64)) globalBody867_46 globalBody867_40

def globalBody867_48 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "out")

def globalBody867_49 : Prog (BitVec 64) :=
.seq globalBody867_47 globalBody867_48

def globalBody867_50 : Prog (BitVec 64) :=
.dec ("system_mark") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 80#64])) globalBody867_49

def globalBody867_51 : Prog (BitVec 64) :=
.seq globalBody867_35 globalBody867_50

def globalBody867_52 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("process_message_call") ([Flapjack.Exp.var Flapjack.VarKind.local "m"]) globalBody867_51

def globalBody867_53 : Prog (BitVec 64) :=
.seq globalBody867_34 globalBody867_52

def globalBody867_54 : Prog (BitVec 64) :=
.decCall ("ak") (Flapjack.Shape.one) ("htab_new") ([Flapjack.Exp.const 52#64, Flapjack.Exp.const 8#64]) globalBody867_53

def globalBody867_55 : Prog (BitVec 64) :=
.seq globalBody867_33 globalBody867_54

def globalBody867_56 : Prog (BitVec 64) :=
.decCall ("aa") (Flapjack.Shape.one) ("htab_new") ([Flapjack.Exp.const 20#64, Flapjack.Exp.const 8#64]) globalBody867_55

def globalBody867_57 : Prog (BitVec 64) :=
.seq globalBody867_32 globalBody867_56

def globalBody867_58 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.one) ("msg_new") ([]) globalBody867_57

def globalBody867_59 : Prog (BitVec 64) :=
.seq globalBody867_9 globalBody867_58

def globalBody867_60 : Prog (BitVec 64) :=
.decCall ("te") (Flapjack.Shape.one) ("te_new") ([]) globalBody867_59

def globalBody867_61 : Prog (BitVec 64) :=
.decCall ("code") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("ext_code_of") ([Flapjack.Exp.var Flapjack.VarKind.local "target"]) globalBody867_60

def globalBody867_62 : Prog (BitVec 64) :=
.seq globalBody867_0 globalBody867_61

def globalData867 : Decl (BitVec 64) :=
.function { name := "process_unchecked_system_transaction", inline := false, exported := false, params := [("target", Flapjack.Shape.one), ("data", Flapjack.Shape.one), ("data_n", Flapjack.Shape.one)], body := globalBody867_62, returnShape := (Flapjack.Shape.one) }
def globalOutput867 := Pancake.PanLang.declToHOL globalData867
end InitECandidate.Proofs.FrontendStages.Declarations
