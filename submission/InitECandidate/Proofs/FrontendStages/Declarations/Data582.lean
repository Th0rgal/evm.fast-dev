import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify566
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body582_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "csnap"), none)) "state_snapshot" []

def body582_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "destroy_storage" [Flapjack.Exp.var Flapjack.VarKind.local "target"]

def body582_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mark_account_created" [Flapjack.Exp.var Flapjack.VarKind.local "target"]

def body582_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "increment_nonce" [Flapjack.Exp.var Flapjack.VarKind.local "target"]

def body582_4 : Prog (BitVec 64) :=
.seq body582_2 body582_3

def body582_5 : Prog (BitVec 64) :=
.seq body582_1 body582_4

def body582_6 : Prog (BitVec 64) :=
.dec ("target") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cm", Flapjack.Exp.const 32#64])) body582_5

def body582_7 : Prog (BitVec 64) :=
.seq body582_0 body582_6

def body582_8 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body582_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "kind") (Flapjack.Exp.const 2#64)) body582_7 body582_8

def body582_10 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 7#64)

def body582_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 1024#64)
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cm", Flapjack.Exp.const 128#64]))) body582_10 body582_8

def body582_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "frame_open"
  [Flapjack.Exp.var Flapjack.VarKind.local "cm", Flapjack.Exp.var Flapjack.VarKind.local "kind"]

def body582_13 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "cur_cont", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "snapshot")

def body582_14 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "cur_cont", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "csnap")

def body582_15 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "cur_cont", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "child_mark")

def body582_16 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "cur_cont", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "child_mem_mark")

def body582_17 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "cur_cont", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "new_account_charged")

def body582_18 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "cur_cont", Flapjack.Exp.const 72#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "out_start")

def body582_19 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "cur_cont", Flapjack.Exp.const 80#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "out_size")

def body582_20 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "cur_cont", Flapjack.Exp.const 88#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "contract_address")

def body582_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "frame_start" []

def body582_22 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body582_23 : Prog (BitVec 64) :=
.seq body582_21 body582_22

def body582_24 : Prog (BitVec 64) :=
.seq body582_20 body582_23

def body582_25 : Prog (BitVec 64) :=
.seq body582_19 body582_24

def body582_26 : Prog (BitVec 64) :=
.seq body582_18 body582_25

def body582_27 : Prog (BitVec 64) :=
.seq body582_17 body582_26

def body582_28 : Prog (BitVec 64) :=
.seq body582_16 body582_27

def body582_29 : Prog (BitVec 64) :=
.seq body582_15 body582_28

def body582_30 : Prog (BitVec 64) :=
.seq body582_14 body582_29

def body582_31 : Prog (BitVec 64) :=
.seq body582_13 body582_30

def body582_32 : Prog (BitVec 64) :=
.decCall ("snapshot") (Flapjack.Shape.one) ("state_snapshot") ([]) body582_31

def body582_33 : Prog (BitVec 64) :=
.seq body582_8 body582_32

def body582_34 : Prog (BitVec 64) :=
.seq body582_8 body582_33

def body582_35 : Prog (BitVec 64) :=
.seq body582_12 body582_34

def body582_36 : Prog (BitVec 64) :=
.seq body582_8 body582_35

def body582_37 : Prog (BitVec 64) :=
.seq body582_11 body582_36

def body582_38 : Prog (BitVec 64) :=
.seq body582_9 body582_37

def body582_39 : Prog (BitVec 64) :=
.dec ("csnap") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body582_38

def body582_40 : Prog (BitVec 64) :=
.seq body582_1 body582_2

def body582_41 : Prog (BitVec 64) :=
.seq body582_40 body582_3

def body582_42 : Prog (BitVec 64) :=
.dec ("target") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cm", Flapjack.Exp.const 32#64])) body582_41

def body582_43 : Prog (BitVec 64) :=
.seq body582_0 body582_42

def body582_44 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "kind") (Flapjack.Exp.const 2#64)) body582_43 body582_8

def body582_45 : Prog (BitVec 64) :=
.seq body582_44 body582_11

def body582_46 : Prog (BitVec 64) :=
.seq body582_45 body582_12

def body582_47 : Prog (BitVec 64) :=
.seq body582_13 body582_14

def body582_48 : Prog (BitVec 64) :=
.seq body582_47 body582_15

def body582_49 : Prog (BitVec 64) :=
.seq body582_48 body582_16

def body582_50 : Prog (BitVec 64) :=
.seq body582_49 body582_17

def body582_51 : Prog (BitVec 64) :=
.seq body582_50 body582_18

def body582_52 : Prog (BitVec 64) :=
.seq body582_51 body582_19

def body582_53 : Prog (BitVec 64) :=
.seq body582_52 body582_20

def body582_54 : Prog (BitVec 64) :=
.seq body582_53 body582_21

def body582_55 : Prog (BitVec 64) :=
.seq body582_54 body582_22

def body582_56 : Prog (BitVec 64) :=
.decCall ("snapshot") (Flapjack.Shape.one) ("state_snapshot") ([]) body582_55

def body582_57 : Prog (BitVec 64) :=
.seq body582_46 body582_56

def body582_58 : Prog (BitVec 64) :=
.dec ("csnap") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body582_57

def originalData582 : Decl (BitVec 64) :=
.function { name := "start_child", inline := false, exported := false, params := [("cm", Flapjack.Shape.one), ("kind", Flapjack.Shape.one), ("child_mark", Flapjack.Shape.one),
  ("child_mem_mark", Flapjack.Shape.one), ("new_account_charged", Flapjack.Shape.one),
  ("out_start", Flapjack.Shape.one), ("out_size", Flapjack.Shape.one), ("contract_address", Flapjack.Shape.one)], body := body582_39, returnShape := (Flapjack.Shape.one) }
def simplifiedData582 : Decl (BitVec 64) :=
.function { name := "start_child", inline := false, exported := false, params := [("cm", Flapjack.Shape.one), ("kind", Flapjack.Shape.one), ("child_mark", Flapjack.Shape.one),
  ("child_mem_mark", Flapjack.Shape.one), ("new_account_charged", Flapjack.Shape.one),
  ("out_start", Flapjack.Shape.one), ("out_size", Flapjack.Shape.one), ("contract_address", Flapjack.Shape.one)], body := body582_58, returnShape := (Flapjack.Shape.one) }
def original582 := Pancake.PanLang.declToHOL originalData582
def simplified582 := Pancake.PanLang.declToHOL simplifiedData582
end InitECandidate.Proofs.FrontendStages.Declarations
