import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify575
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body591_0 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pm", Flapjack.Exp.const 0#64]))

def body591_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pm", Flapjack.Exp.const 8#64]))

def body591_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "caller")

def body591_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "target")

def body591_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "current_target")

def body591_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "gas")

def body591_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "reservoir")

def body591_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "value")

def body591_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 88#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "data")

def body591_9 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "data_n")

def body591_10 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 104#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "code_address")

def body591_11 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 112#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "code")

def body591_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "code_n")

def body591_13 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 128#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pm", Flapjack.Exp.const 128#64]),
      Flapjack.Exp.const 1#64])

def body591_14 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 136#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "transfer")

def body591_15 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "stat" (Flapjack.Exp.const 1#64)

def body591_16 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body591_17 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pm", Flapjack.Exp.const 144#64]))
  (Flapjack.Exp.const 0#64)) body591_15 body591_16

def body591_18 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 144#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "stat")

def body591_19 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 152#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 168#64]))

def body591_20 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 160#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 176#64]))

def body591_21 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 168#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "disable_pre")

def body591_22 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "m")

def body591_23 : Prog (BitVec 64) :=
.seq body591_21 body591_22

def body591_24 : Prog (BitVec 64) :=
.seq body591_20 body591_23

def body591_25 : Prog (BitVec 64) :=
.seq body591_19 body591_24

def body591_26 : Prog (BitVec 64) :=
.seq body591_18 body591_25

def body591_27 : Prog (BitVec 64) :=
.seq body591_17 body591_26

def body591_28 : Prog (BitVec 64) :=
.dec ("stat") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "is_static") body591_27

def body591_29 : Prog (BitVec 64) :=
.seq body591_14 body591_28

def body591_30 : Prog (BitVec 64) :=
.seq body591_13 body591_29

def body591_31 : Prog (BitVec 64) :=
.seq body591_12 body591_30

def body591_32 : Prog (BitVec 64) :=
.seq body591_11 body591_31

def body591_33 : Prog (BitVec 64) :=
.seq body591_10 body591_32

def body591_34 : Prog (BitVec 64) :=
.seq body591_9 body591_33

def body591_35 : Prog (BitVec 64) :=
.seq body591_8 body591_34

def body591_36 : Prog (BitVec 64) :=
.seq body591_7 body591_35

def body591_37 : Prog (BitVec 64) :=
.seq body591_6 body591_36

def body591_38 : Prog (BitVec 64) :=
.seq body591_5 body591_37

def body591_39 : Prog (BitVec 64) :=
.seq body591_4 body591_38

def body591_40 : Prog (BitVec 64) :=
.seq body591_3 body591_39

def body591_41 : Prog (BitVec 64) :=
.seq body591_2 body591_40

def body591_42 : Prog (BitVec 64) :=
.seq body591_1 body591_41

def body591_43 : Prog (BitVec 64) :=
.seq body591_0 body591_42

def body591_44 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.one) ("msg_new_scratch") ([]) body591_43

def body591_45 : Prog (BitVec 64) :=
.dec ("pm") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body591_44

def body591_46 : Prog (BitVec 64) :=
.seq body591_0 body591_1

def body591_47 : Prog (BitVec 64) :=
.seq body591_46 body591_2

def body591_48 : Prog (BitVec 64) :=
.seq body591_47 body591_3

def body591_49 : Prog (BitVec 64) :=
.seq body591_48 body591_4

def body591_50 : Prog (BitVec 64) :=
.seq body591_49 body591_5

def body591_51 : Prog (BitVec 64) :=
.seq body591_50 body591_6

def body591_52 : Prog (BitVec 64) :=
.seq body591_51 body591_7

def body591_53 : Prog (BitVec 64) :=
.seq body591_52 body591_8

def body591_54 : Prog (BitVec 64) :=
.seq body591_53 body591_9

def body591_55 : Prog (BitVec 64) :=
.seq body591_54 body591_10

def body591_56 : Prog (BitVec 64) :=
.seq body591_55 body591_11

def body591_57 : Prog (BitVec 64) :=
.seq body591_56 body591_12

def body591_58 : Prog (BitVec 64) :=
.seq body591_57 body591_13

def body591_59 : Prog (BitVec 64) :=
.seq body591_58 body591_14

def body591_60 : Prog (BitVec 64) :=
.seq body591_17 body591_18

def body591_61 : Prog (BitVec 64) :=
.seq body591_60 body591_19

def body591_62 : Prog (BitVec 64) :=
.seq body591_61 body591_20

def body591_63 : Prog (BitVec 64) :=
.seq body591_62 body591_21

def body591_64 : Prog (BitVec 64) :=
.seq body591_63 body591_22

def body591_65 : Prog (BitVec 64) :=
.dec ("stat") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "is_static") body591_64

def body591_66 : Prog (BitVec 64) :=
.seq body591_59 body591_65

def body591_67 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.one) ("msg_new_scratch") ([]) body591_66

def body591_68 : Prog (BitVec 64) :=
.dec ("pm") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body591_67

def originalData591 : Decl (BitVec 64) :=
.function { name := "child_message", inline := false, exported := false, params := [("caller", Flapjack.Shape.one), ("target", Flapjack.Shape.one), ("current_target", Flapjack.Shape.one),
  ("gas", Flapjack.Shape.one), ("reservoir", Flapjack.Shape.one),
  ("value", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("data", Flapjack.Shape.one), ("data_n", Flapjack.Shape.one), ("code_address", Flapjack.Shape.one),
  ("code", Flapjack.Shape.one), ("code_n", Flapjack.Shape.one), ("transfer", Flapjack.Shape.one),
  ("is_static", Flapjack.Shape.one), ("disable_pre", Flapjack.Shape.one)], body := body591_45, returnShape := (Flapjack.Shape.one) }
def simplifiedData591 : Decl (BitVec 64) :=
.function { name := "child_message", inline := false, exported := false, params := [("caller", Flapjack.Shape.one), ("target", Flapjack.Shape.one), ("current_target", Flapjack.Shape.one),
  ("gas", Flapjack.Shape.one), ("reservoir", Flapjack.Shape.one),
  ("value", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("data", Flapjack.Shape.one), ("data_n", Flapjack.Shape.one), ("code_address", Flapjack.Shape.one),
  ("code", Flapjack.Shape.one), ("code_n", Flapjack.Shape.one), ("transfer", Flapjack.Shape.one),
  ("is_static", Flapjack.Shape.one), ("disable_pre", Flapjack.Shape.one)], body := body591_68, returnShape := (Flapjack.Shape.one) }
def original591 := Pancake.PanLang.declToHOL originalData591
def simplified591 := Pancake.PanLang.declToHOL simplifiedData591
end InitECandidate.Proofs.FrontendStages.Declarations
