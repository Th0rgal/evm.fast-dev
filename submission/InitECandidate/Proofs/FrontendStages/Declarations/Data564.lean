import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify548
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body564_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body564_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body564_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64)) body564_0 body564_1

def body564_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "log", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.global "vm_system_address")

def body564_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "topics", Flapjack.Exp.var Flapjack.VarKind.global "transfer_topic",
    Flapjack.Exp.const 32#64]

def body564_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "topics", Flapjack.Exp.const 32#64],
    Flapjack.Exp.const 12#64]

def body564_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "topics", Flapjack.Exp.const 44#64],
    Flapjack.Exp.var Flapjack.VarKind.local "sender", Flapjack.Exp.const 20#64]

def body564_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "topics", Flapjack.Exp.const 64#64],
    Flapjack.Exp.const 12#64]

def body564_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "topics", Flapjack.Exp.const 76#64],
    Flapjack.Exp.var Flapjack.VarKind.local "recipient", Flapjack.Exp.const 20#64]

def body564_9 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "log", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "topics")

def body564_10 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "log", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.const 3#64)

def body564_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "u256_to_be32"
  [Flapjack.Exp.var Flapjack.VarKind.local "amount", Flapjack.Exp.var Flapjack.VarKind.local "data"]

def body564_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "log", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "data")

def body564_13 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "log", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.const 32#64)

def body564_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "log_append"
  [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.var Flapjack.VarKind.local "log"]

def body564_15 : Prog (BitVec 64) :=
.seq body564_14 body564_0

def body564_16 : Prog (BitVec 64) :=
.seq body564_13 body564_15

def body564_17 : Prog (BitVec 64) :=
.seq body564_12 body564_16

def body564_18 : Prog (BitVec 64) :=
.seq body564_11 body564_17

def body564_19 : Prog (BitVec 64) :=
.decCall ("data") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body564_18

def body564_20 : Prog (BitVec 64) :=
.seq body564_10 body564_19

def body564_21 : Prog (BitVec 64) :=
.seq body564_9 body564_20

def body564_22 : Prog (BitVec 64) :=
.seq body564_8 body564_21

def body564_23 : Prog (BitVec 64) :=
.seq body564_7 body564_22

def body564_24 : Prog (BitVec 64) :=
.seq body564_6 body564_23

def body564_25 : Prog (BitVec 64) :=
.seq body564_5 body564_24

def body564_26 : Prog (BitVec 64) :=
.seq body564_4 body564_25

def body564_27 : Prog (BitVec 64) :=
.decCall ("topics") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body564_26

def body564_28 : Prog (BitVec 64) :=
.seq body564_3 body564_27

def body564_29 : Prog (BitVec 64) :=
.decCall ("log") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 40#64]) body564_28

def body564_30 : Prog (BitVec 64) :=
.seq body564_2 body564_29

def body564_31 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "amount"]) body564_30

def body564_32 : Prog (BitVec 64) :=
.seq body564_4 body564_5

def body564_33 : Prog (BitVec 64) :=
.seq body564_32 body564_6

def body564_34 : Prog (BitVec 64) :=
.seq body564_33 body564_7

def body564_35 : Prog (BitVec 64) :=
.seq body564_34 body564_8

def body564_36 : Prog (BitVec 64) :=
.seq body564_35 body564_9

def body564_37 : Prog (BitVec 64) :=
.seq body564_36 body564_10

def body564_38 : Prog (BitVec 64) :=
.seq body564_11 body564_12

def body564_39 : Prog (BitVec 64) :=
.seq body564_38 body564_13

def body564_40 : Prog (BitVec 64) :=
.seq body564_39 body564_14

def body564_41 : Prog (BitVec 64) :=
.seq body564_40 body564_0

def body564_42 : Prog (BitVec 64) :=
.decCall ("data") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body564_41

def body564_43 : Prog (BitVec 64) :=
.seq body564_37 body564_42

def body564_44 : Prog (BitVec 64) :=
.decCall ("topics") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body564_43

def body564_45 : Prog (BitVec 64) :=
.seq body564_3 body564_44

def body564_46 : Prog (BitVec 64) :=
.decCall ("log") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 40#64]) body564_45

def body564_47 : Prog (BitVec 64) :=
.seq body564_2 body564_46

def body564_48 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "amount"]) body564_47

def originalData564 : Decl (BitVec 64) :=
.function { name := "emit_transfer_log", inline := false, exported := false, params := [("sender", Flapjack.Shape.one), ("recipient", Flapjack.Shape.one),
  ("amount", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body564_31, returnShape := (Flapjack.Shape.one) }
def simplifiedData564 : Decl (BitVec 64) :=
.function { name := "emit_transfer_log", inline := false, exported := false, params := [("sender", Flapjack.Shape.one), ("recipient", Flapjack.Shape.one),
  ("amount", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body564_48, returnShape := (Flapjack.Shape.one) }
def original564 := Pancake.PanLang.declToHOL originalData564
def simplified564 := Pancake.PanLang.declToHOL simplifiedData564
end InitECandidate.Proofs.FrontendStages.Declarations
