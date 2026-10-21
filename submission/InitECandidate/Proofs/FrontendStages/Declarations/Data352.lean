import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify336
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body352_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "ts"), none)) "alloc" [Flapjack.Exp.const 72#64]

def body352_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ts", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.global "bs")

def body352_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ts", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "t")

def body352_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "t"), none)) "htab_new"
  [Flapjack.Exp.const 20#64, Flapjack.Exp.const 64#64]

def body352_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ts", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "t")

def body352_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "t"), none)) "htab_new"
  [Flapjack.Exp.const 52#64, Flapjack.Exp.const 64#64]

def body352_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ts", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "t")

def body352_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "t"), none)) "htab_new"
  [Flapjack.Exp.const 20#64, Flapjack.Exp.const 16#64]

def body352_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ts", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "t")

def body352_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "t"), none)) "htab_new"
  [Flapjack.Exp.const 52#64, Flapjack.Exp.const 16#64]

def body352_10 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ts", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "t")

def body352_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "t"), none)) "htab_new"
  [Flapjack.Exp.const 32#64, Flapjack.Exp.const 16#64]

def body352_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ts", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "t")

def body352_13 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ts", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "t")

def body352_14 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ts", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "t")

def body352_15 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.global "journal_n" (Flapjack.Exp.const 0#64)

def body352_16 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body352_17 : Prog (BitVec 64) :=
.seq body352_15 body352_16

def body352_18 : Prog (BitVec 64) :=
.seq body352_14 body352_17

def body352_19 : Prog (BitVec 64) :=
.seq body352_9 body352_18

def body352_20 : Prog (BitVec 64) :=
.seq body352_13 body352_19

def body352_21 : Prog (BitVec 64) :=
.seq body352_7 body352_20

def body352_22 : Prog (BitVec 64) :=
.seq body352_12 body352_21

def body352_23 : Prog (BitVec 64) :=
.seq body352_11 body352_22

def body352_24 : Prog (BitVec 64) :=
.seq body352_10 body352_23

def body352_25 : Prog (BitVec 64) :=
.seq body352_9 body352_24

def body352_26 : Prog (BitVec 64) :=
.seq body352_8 body352_25

def body352_27 : Prog (BitVec 64) :=
.seq body352_7 body352_26

def body352_28 : Prog (BitVec 64) :=
.seq body352_6 body352_27

def body352_29 : Prog (BitVec 64) :=
.seq body352_5 body352_28

def body352_30 : Prog (BitVec 64) :=
.seq body352_4 body352_29

def body352_31 : Prog (BitVec 64) :=
.seq body352_3 body352_30

def body352_32 : Prog (BitVec 64) :=
.seq body352_2 body352_31

def body352_33 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("htab_new") ([Flapjack.Exp.const 20#64, Flapjack.Exp.const 64#64]) body352_32

def body352_34 : Prog (BitVec 64) :=
.seq body352_1 body352_33

def body352_35 : Prog (BitVec 64) :=
.seq body352_0 body352_34

def body352_36 : Prog (BitVec 64) :=
.seq body352_0 body352_1

def body352_37 : Prog (BitVec 64) :=
.seq body352_2 body352_3

def body352_38 : Prog (BitVec 64) :=
.seq body352_37 body352_4

def body352_39 : Prog (BitVec 64) :=
.seq body352_38 body352_5

def body352_40 : Prog (BitVec 64) :=
.seq body352_39 body352_6

def body352_41 : Prog (BitVec 64) :=
.seq body352_40 body352_7

def body352_42 : Prog (BitVec 64) :=
.seq body352_41 body352_8

def body352_43 : Prog (BitVec 64) :=
.seq body352_42 body352_9

def body352_44 : Prog (BitVec 64) :=
.seq body352_43 body352_10

def body352_45 : Prog (BitVec 64) :=
.seq body352_44 body352_11

def body352_46 : Prog (BitVec 64) :=
.seq body352_45 body352_12

def body352_47 : Prog (BitVec 64) :=
.seq body352_46 body352_7

def body352_48 : Prog (BitVec 64) :=
.seq body352_47 body352_13

def body352_49 : Prog (BitVec 64) :=
.seq body352_48 body352_9

def body352_50 : Prog (BitVec 64) :=
.seq body352_49 body352_14

def body352_51 : Prog (BitVec 64) :=
.seq body352_50 body352_15

def body352_52 : Prog (BitVec 64) :=
.seq body352_51 body352_16

def body352_53 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("htab_new") ([Flapjack.Exp.const 20#64, Flapjack.Exp.const 64#64]) body352_52

def body352_54 : Prog (BitVec 64) :=
.seq body352_36 body352_53

def originalData352 : Decl (BitVec 64) :=
.function { name := "state_fresh_tx", inline := false, exported := false, params := [], body := body352_35, returnShape := (Flapjack.Shape.one) }
def simplifiedData352 : Decl (BitVec 64) :=
.function { name := "state_fresh_tx", inline := false, exported := false, params := [], body := body352_54, returnShape := (Flapjack.Shape.one) }
def original352 := Pancake.PanLang.declToHOL originalData352
def simplified352 := Pancake.PanLang.declToHOL simplifiedData352
end InitECandidate.Proofs.FrontendStages.Declarations
