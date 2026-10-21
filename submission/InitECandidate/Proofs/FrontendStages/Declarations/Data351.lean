import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify335
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body351_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "ws"), none)) "alloc" [Flapjack.Exp.const 40#64]

def body351_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ws", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "nodedb")

def body351_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ws", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "state_root")

def body351_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ws", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "codedb")

def body351_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ws", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "root")

def body351_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ws", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "t")

def body351_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "bs"), none)) "alloc" [Flapjack.Exp.const 80#64]

def body351_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bs", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.global "ws")

def body351_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "t"), none)) "htab_new"
  [Flapjack.Exp.const 20#64, Flapjack.Exp.const 256#64]

def body351_9 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bs", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "t")

def body351_10 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bs", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "t")

def body351_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "t"), none)) "htab_new"
  [Flapjack.Exp.const 52#64, Flapjack.Exp.const 256#64]

def body351_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bs", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "t")

def body351_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "t"), none)) "htab_new"
  [Flapjack.Exp.const 20#64, Flapjack.Exp.const 64#64]

def body351_14 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bs", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "t")

def body351_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "t"), none)) "htab_new"
  [Flapjack.Exp.const 52#64, Flapjack.Exp.const 64#64]

def body351_16 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bs", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "t")

def body351_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "t"), none)) "htab_new"
  [Flapjack.Exp.const 32#64, Flapjack.Exp.const 64#64]

def body351_18 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bs", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "t")

def body351_19 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bs", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.const 0#64)

def body351_20 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bs", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.const 0#64)

def body351_21 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bs", Flapjack.Exp.const 72#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "t")

def body351_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "sk_buf"), none)) "alloc" [Flapjack.Exp.const 64#64]

def body351_23 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.global "journal_cap" (Flapjack.Exp.const 524288#64)

def body351_24 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "journal"), none)) "alloc"
  [Flapjack.Exp.panOp Flapjack.PanOp.mul
      [Flapjack.Exp.var Flapjack.VarKind.global "journal_cap", Flapjack.Exp.const 32#64]]

def body351_25 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.global "journal_n" (Flapjack.Exp.const 0#64)

def body351_26 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.global "ts" (Flapjack.Exp.const 0#64)

def body351_27 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body351_28 : Prog (BitVec 64) :=
.seq body351_26 body351_27

def body351_29 : Prog (BitVec 64) :=
.seq body351_25 body351_28

def body351_30 : Prog (BitVec 64) :=
.seq body351_24 body351_29

def body351_31 : Prog (BitVec 64) :=
.seq body351_23 body351_30

def body351_32 : Prog (BitVec 64) :=
.seq body351_22 body351_31

def body351_33 : Prog (BitVec 64) :=
.seq body351_21 body351_32

def body351_34 : Prog (BitVec 64) :=
.seq body351_8 body351_33

def body351_35 : Prog (BitVec 64) :=
.seq body351_20 body351_34

def body351_36 : Prog (BitVec 64) :=
.seq body351_19 body351_35

def body351_37 : Prog (BitVec 64) :=
.seq body351_18 body351_36

def body351_38 : Prog (BitVec 64) :=
.seq body351_17 body351_37

def body351_39 : Prog (BitVec 64) :=
.seq body351_16 body351_38

def body351_40 : Prog (BitVec 64) :=
.seq body351_15 body351_39

def body351_41 : Prog (BitVec 64) :=
.seq body351_14 body351_40

def body351_42 : Prog (BitVec 64) :=
.seq body351_13 body351_41

def body351_43 : Prog (BitVec 64) :=
.seq body351_12 body351_42

def body351_44 : Prog (BitVec 64) :=
.seq body351_11 body351_43

def body351_45 : Prog (BitVec 64) :=
.seq body351_10 body351_44

def body351_46 : Prog (BitVec 64) :=
.seq body351_8 body351_45

def body351_47 : Prog (BitVec 64) :=
.seq body351_9 body351_46

def body351_48 : Prog (BitVec 64) :=
.seq body351_8 body351_47

def body351_49 : Prog (BitVec 64) :=
.seq body351_7 body351_48

def body351_50 : Prog (BitVec 64) :=
.seq body351_6 body351_49

def body351_51 : Prog (BitVec 64) :=
.seq body351_5 body351_50

def body351_52 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("htab_new") ([Flapjack.Exp.const 32#64, Flapjack.Exp.const 64#64]) body351_51

def body351_53 : Prog (BitVec 64) :=
.seq body351_4 body351_52

def body351_54 : Prog (BitVec 64) :=
.decCall ("root") (Flapjack.Shape.one) ("decode_witness_to_mpt") ([Flapjack.Exp.var Flapjack.VarKind.local "nodedb", Flapjack.Exp.var Flapjack.VarKind.local "state_root"]) body351_53

def body351_55 : Prog (BitVec 64) :=
.seq body351_3 body351_54

def body351_56 : Prog (BitVec 64) :=
.seq body351_2 body351_55

def body351_57 : Prog (BitVec 64) :=
.seq body351_1 body351_56

def body351_58 : Prog (BitVec 64) :=
.seq body351_0 body351_57

def body351_59 : Prog (BitVec 64) :=
.seq body351_0 body351_1

def body351_60 : Prog (BitVec 64) :=
.seq body351_59 body351_2

def body351_61 : Prog (BitVec 64) :=
.seq body351_60 body351_3

def body351_62 : Prog (BitVec 64) :=
.seq body351_5 body351_6

def body351_63 : Prog (BitVec 64) :=
.seq body351_62 body351_7

def body351_64 : Prog (BitVec 64) :=
.seq body351_63 body351_8

def body351_65 : Prog (BitVec 64) :=
.seq body351_64 body351_9

def body351_66 : Prog (BitVec 64) :=
.seq body351_65 body351_8

def body351_67 : Prog (BitVec 64) :=
.seq body351_66 body351_10

def body351_68 : Prog (BitVec 64) :=
.seq body351_67 body351_11

def body351_69 : Prog (BitVec 64) :=
.seq body351_68 body351_12

def body351_70 : Prog (BitVec 64) :=
.seq body351_69 body351_13

def body351_71 : Prog (BitVec 64) :=
.seq body351_70 body351_14

def body351_72 : Prog (BitVec 64) :=
.seq body351_71 body351_15

def body351_73 : Prog (BitVec 64) :=
.seq body351_72 body351_16

def body351_74 : Prog (BitVec 64) :=
.seq body351_73 body351_17

def body351_75 : Prog (BitVec 64) :=
.seq body351_74 body351_18

def body351_76 : Prog (BitVec 64) :=
.seq body351_75 body351_19

def body351_77 : Prog (BitVec 64) :=
.seq body351_76 body351_20

def body351_78 : Prog (BitVec 64) :=
.seq body351_77 body351_8

def body351_79 : Prog (BitVec 64) :=
.seq body351_78 body351_21

def body351_80 : Prog (BitVec 64) :=
.seq body351_79 body351_22

def body351_81 : Prog (BitVec 64) :=
.seq body351_80 body351_23

def body351_82 : Prog (BitVec 64) :=
.seq body351_81 body351_24

def body351_83 : Prog (BitVec 64) :=
.seq body351_82 body351_25

def body351_84 : Prog (BitVec 64) :=
.seq body351_83 body351_26

def body351_85 : Prog (BitVec 64) :=
.seq body351_84 body351_27

def body351_86 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("htab_new") ([Flapjack.Exp.const 32#64, Flapjack.Exp.const 64#64]) body351_85

def body351_87 : Prog (BitVec 64) :=
.seq body351_4 body351_86

def body351_88 : Prog (BitVec 64) :=
.decCall ("root") (Flapjack.Shape.one) ("decode_witness_to_mpt") ([Flapjack.Exp.var Flapjack.VarKind.local "nodedb", Flapjack.Exp.var Flapjack.VarKind.local "state_root"]) body351_87

def body351_89 : Prog (BitVec 64) :=
.seq body351_61 body351_88

def originalData351 : Decl (BitVec 64) :=
.function { name := "state_init", inline := false, exported := false, params := [("nodedb", Flapjack.Shape.one), ("state_root", Flapjack.Shape.one), ("codedb", Flapjack.Shape.one)], body := body351_58, returnShape := (Flapjack.Shape.one) }
def simplifiedData351 : Decl (BitVec 64) :=
.function { name := "state_init", inline := false, exported := false, params := [("nodedb", Flapjack.Shape.one), ("state_root", Flapjack.Shape.one), ("codedb", Flapjack.Shape.one)], body := body351_89, returnShape := (Flapjack.Shape.one) }
def original351 := Pancake.PanLang.declToHOL originalData351
def simplified351 := Pancake.PanLang.declToHOL simplifiedData351
end InitECandidate.Proofs.FrontendStages.Declarations
