import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data464
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate448
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody464_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 280#64]

def globalBody464_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 208#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "stack_mark")

def globalBody464_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "stk")

def globalBody464_3 : Prog (BitVec 64) :=
.seq globalBody464_1 globalBody464_2

def globalBody464_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 232#64])
  (Flapjack.Exp.const 32#64)

def globalBody464_5 : Prog (BitVec 64) :=
.seq globalBody464_3 globalBody464_4

def globalBody464_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 224#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "mem_mark")

def globalBody464_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "mem")

def globalBody464_8 : Prog (BitVec 64) :=
.seq globalBody464_6 globalBody464_7

def globalBody464_9 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.const 1024#64)

def globalBody464_10 : Prog (BitVec 64) :=
.seq globalBody464_8 globalBody464_9

def globalBody464_11 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 112#64]))

def globalBody464_12 : Prog (BitVec 64) :=
.seq globalBody464_10 globalBody464_11

def globalBody464_13 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 120#64]))

def globalBody464_14 : Prog (BitVec 64) :=
.seq globalBody464_12 globalBody464_13

def globalBody464_15 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 40#64]))

def globalBody464_16 : Prog (BitVec 64) :=
.seq globalBody464_14 globalBody464_15

def globalBody464_17 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 72#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 48#64]))

def globalBody464_18 : Prog (BitVec 64) :=
.seq globalBody464_16 globalBody464_17

def globalBody464_19 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 80#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "jd")

def globalBody464_20 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 88#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "logs")

def globalBody464_21 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 104#64])
  (Flapjack.Exp.const 1#64)

def globalBody464_22 : Prog (BitVec 64) :=
.seq globalBody464_20 globalBody464_21

def globalBody464_23 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 112#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "msg")

def globalBody464_24 : Prog (BitVec 64) :=
.seq globalBody464_22 globalBody464_23

def globalBody464_25 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 136#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "del")

def globalBody464_26 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 168#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 152#64]))

def globalBody464_27 : Prog (BitVec 64) :=
.seq globalBody464_25 globalBody464_26

def globalBody464_28 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 176#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 160#64]))

def globalBody464_29 : Prog (BitVec 64) :=
.seq globalBody464_27 globalBody464_28

def globalBody464_30 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 264#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "acc_n")

def globalBody464_31 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "acc_n"), none)) "htab_count"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 160#64])]

def globalBody464_32 : Prog (BitVec 64) :=
.seq globalBody464_30 globalBody464_31

def globalBody464_33 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 272#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "acc_n")

def globalBody464_34 : Prog (BitVec 64) :=
.seq globalBody464_32 globalBody464_33

def globalBody464_35 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 264#64]))

def globalBody464_36 : Prog (BitVec 64) :=
.seq globalBody464_34 globalBody464_35

def globalBody464_37 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 144#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 264#64]))

def globalBody464_38 : Prog (BitVec 64) :=
.seq globalBody464_36 globalBody464_37

def globalBody464_39 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 216#64])
  (Flapjack.Exp.const 0#64)

def globalBody464_40 : Prog (BitVec 64) :=
.seq globalBody464_38 globalBody464_39

def globalBody464_41 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "e")

def globalBody464_42 : Prog (BitVec 64) :=
.seq globalBody464_40 globalBody464_41

def globalBody464_43 : Prog (BitVec 64) :=
.decCall ("acc_n") (Flapjack.Shape.one) ("htab_count") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 152#64])]) globalBody464_42

def globalBody464_44 : Prog (BitVec 64) :=
.seq globalBody464_29 globalBody464_43

def globalBody464_45 : Prog (BitVec 64) :=
.decCall ("del") (Flapjack.Shape.one) ("htab_new_scratch") ([Flapjack.Exp.const 20#64, Flapjack.Exp.const 4#64]) globalBody464_44

def globalBody464_46 : Prog (BitVec 64) :=
.seq globalBody464_24 globalBody464_45

def globalBody464_47 : Prog (BitVec 64) :=
.decCall ("logs") (Flapjack.Shape.one) ("lst_new_scratch") ([Flapjack.Exp.const 8#64, Flapjack.Exp.const 4#64]) globalBody464_46

def globalBody464_48 : Prog (BitVec 64) :=
.seq globalBody464_19 globalBody464_47

def globalBody464_49 : Prog (BitVec 64) :=
.decCall ("jd") (Flapjack.Shape.one) ("compute_jumpdests") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 112#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 120#64])]) globalBody464_48

def globalBody464_50 : Prog (BitVec 64) :=
.seq globalBody464_18 globalBody464_49

def globalBody464_51 : Prog (BitVec 64) :=
.decCall ("mem") (Flapjack.Shape.one) ("frame_mem_alloc") ([Flapjack.Exp.const 1024#64]) globalBody464_50

def globalBody464_52 : Prog (BitVec 64) :=
.seq globalBody464_5 globalBody464_51

def globalBody464_53 : Prog (BitVec 64) :=
.decCall ("stk") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 32#64, Flapjack.Exp.const 32#64]]) globalBody464_52

def globalBody464_54 : Prog (BitVec 64) :=
.seq globalBody464_0 globalBody464_53

def globalBody464_55 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.const 280#64]) globalBody464_54

def globalBody464_56 : Prog (BitVec 64) :=
.decCall ("mem_mark") (Flapjack.Shape.one) ("frame_mem_mark") ([]) globalBody464_55

def globalBody464_57 : Prog (BitVec 64) :=
.decCall ("stack_mark") (Flapjack.Shape.one) ("scratch_mark") ([]) globalBody464_56

def globalData464 : Decl (BitVec 64) :=
.function { name := "frame_new", inline := false, exported := false, params := [("msg", Flapjack.Shape.one)], body := globalBody464_57, returnShape := (Flapjack.Shape.one) }
def globalOutput464 := Pancake.PanLang.declToHOL globalData464
end InitECandidate.Proofs.FrontendStages.Declarations
