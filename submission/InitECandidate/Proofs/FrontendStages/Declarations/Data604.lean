import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify588
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body604_0 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body604_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 96#64]

def body604_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.const 12#64)

def body604_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 48#64]))

def body604_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 40#64]))

def body604_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.var Flapjack.VarKind.global "evm_empty")

def body604_6 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "out")

def body604_7 : Prog (BitVec 64) :=
.seq body604_5 body604_6

def body604_8 : Prog (BitVec 64) :=
.seq body604_4 body604_7

def body604_9 : Prog (BitVec 64) :=
.seq body604_3 body604_8

def body604_10 : Prog (BitVec 64) :=
.seq body604_2 body604_9

def body604_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "dep") (Flapjack.Exp.const 0#64)) body604_10 body604_0

def body604_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "frame"), none)) "process_create_message"
  [Flapjack.Exp.var Flapjack.VarKind.local "msg"]

def body604_13 : Prog (BitVec 64) :=
.seq body604_11 body604_12

def body604_14 : Prog (BitVec 64) :=
.decCall ("dep") (Flapjack.Shape.one) ("account_deployable") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 32#64])]) body604_13

def body604_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "frame"), none)) "process_message"
  [Flapjack.Exp.var Flapjack.VarKind.local "msg"]

def body604_16 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 24#64]))
  (Flapjack.Exp.const 0#64)) body604_14 body604_15

def body604_17 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 64#64]))

def body604_18 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 160#64]))

def body604_19 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 120#64]))

def body604_20 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 128#64]))

def body604_21 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 72#64]))

def body604_22 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 184#64]))

def body604_23 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 72#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "fsg",
      Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 200#64])])

def body604_24 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 88#64]))

def body604_25 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 136#64]))

def body604_26 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "rc" (Flapjack.Exp.const 0#64)

def body604_27 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "rc") (Flapjack.Exp.const 0#64)) body604_26 body604_0

def body604_28 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "rc")

def body604_29 : Prog (BitVec 64) :=
.seq body604_27 body604_28

def body604_30 : Prog (BitVec 64) :=
.dec ("rc") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 96#64])) body604_29

def body604_31 : Prog (BitVec 64) :=
.seq body604_25 body604_30

def body604_32 : Prog (BitVec 64) :=
.seq body604_24 body604_31

def body604_33 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 160#64]))
  (Flapjack.Exp.const 0#64)) body604_32 body604_0

def body604_34 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 80#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 208#64]))

def body604_35 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 88#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 224#64]))

def body604_36 : Prog (BitVec 64) :=
.seq body604_35 body604_6

def body604_37 : Prog (BitVec 64) :=
.seq body604_34 body604_36

def body604_38 : Prog (BitVec 64) :=
.seq body604_33 body604_37

def body604_39 : Prog (BitVec 64) :=
.seq body604_23 body604_38

def body604_40 : Prog (BitVec 64) :=
.decCall ("fsg") (Flapjack.Shape.one) ("frame_state_gas_used") ([Flapjack.Exp.var Flapjack.VarKind.local "frame"]) body604_39

def body604_41 : Prog (BitVec 64) :=
.seq body604_22 body604_40

def body604_42 : Prog (BitVec 64) :=
.seq body604_21 body604_41

def body604_43 : Prog (BitVec 64) :=
.seq body604_20 body604_42

def body604_44 : Prog (BitVec 64) :=
.seq body604_19 body604_43

def body604_45 : Prog (BitVec 64) :=
.seq body604_18 body604_44

def body604_46 : Prog (BitVec 64) :=
.seq body604_17 body604_45

def body604_47 : Prog (BitVec 64) :=
.seq body604_16 body604_46

def body604_48 : Prog (BitVec 64) :=
.dec ("frame") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body604_47

def body604_49 : Prog (BitVec 64) :=
.seq body604_1 body604_48

def body604_50 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body604_49

def body604_51 : Prog (BitVec 64) :=
.seq body604_0 body604_50

def body604_52 : Prog (BitVec 64) :=
.seq body604_2 body604_3

def body604_53 : Prog (BitVec 64) :=
.seq body604_52 body604_4

def body604_54 : Prog (BitVec 64) :=
.seq body604_53 body604_5

def body604_55 : Prog (BitVec 64) :=
.seq body604_54 body604_6

def body604_56 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "dep") (Flapjack.Exp.const 0#64)) body604_55 body604_0

def body604_57 : Prog (BitVec 64) :=
.seq body604_56 body604_12

def body604_58 : Prog (BitVec 64) :=
.decCall ("dep") (Flapjack.Shape.one) ("account_deployable") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 32#64])]) body604_57

def body604_59 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 24#64]))
  (Flapjack.Exp.const 0#64)) body604_58 body604_15

def body604_60 : Prog (BitVec 64) :=
.seq body604_59 body604_17

def body604_61 : Prog (BitVec 64) :=
.seq body604_60 body604_18

def body604_62 : Prog (BitVec 64) :=
.seq body604_61 body604_19

def body604_63 : Prog (BitVec 64) :=
.seq body604_62 body604_20

def body604_64 : Prog (BitVec 64) :=
.seq body604_63 body604_21

def body604_65 : Prog (BitVec 64) :=
.seq body604_64 body604_22

def body604_66 : Prog (BitVec 64) :=
.seq body604_24 body604_25

def body604_67 : Prog (BitVec 64) :=
.seq body604_66 body604_30

def body604_68 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "frame", Flapjack.Exp.const 160#64]))
  (Flapjack.Exp.const 0#64)) body604_67 body604_0

def body604_69 : Prog (BitVec 64) :=
.seq body604_23 body604_68

def body604_70 : Prog (BitVec 64) :=
.seq body604_69 body604_34

def body604_71 : Prog (BitVec 64) :=
.seq body604_70 body604_35

def body604_72 : Prog (BitVec 64) :=
.seq body604_71 body604_6

def body604_73 : Prog (BitVec 64) :=
.decCall ("fsg") (Flapjack.Shape.one) ("frame_state_gas_used") ([Flapjack.Exp.var Flapjack.VarKind.local "frame"]) body604_72

def body604_74 : Prog (BitVec 64) :=
.seq body604_65 body604_73

def body604_75 : Prog (BitVec 64) :=
.dec ("frame") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body604_74

def body604_76 : Prog (BitVec 64) :=
.seq body604_1 body604_75

def body604_77 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body604_76

def originalData604 : Decl (BitVec 64) :=
.function { name := "process_message_call", inline := false, exported := false, params := [("msg", Flapjack.Shape.one)], body := body604_51, returnShape := (Flapjack.Shape.one) }
def simplifiedData604 : Decl (BitVec 64) :=
.function { name := "process_message_call", inline := false, exported := false, params := [("msg", Flapjack.Shape.one)], body := body604_77, returnShape := (Flapjack.Shape.one) }
def original604 := Pancake.PanLang.declToHOL originalData604
def simplified604 := Pancake.PanLang.declToHOL simplifiedData604
end InitECandidate.Proofs.FrontendStages.Declarations
