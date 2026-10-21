import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify448
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body464_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 280#64]

def body464_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 208#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "stack_mark")

def body464_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "stk")

def body464_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 232#64])
  (Flapjack.Exp.const 32#64)

def body464_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 224#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "mem_mark")

def body464_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "mem")

def body464_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.const 1024#64)

def body464_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 112#64]))

def body464_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 120#64]))

def body464_9 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 40#64]))

def body464_10 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 72#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 48#64]))

def body464_11 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 80#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "jd")

def body464_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 88#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "logs")

def body464_13 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 104#64])
  (Flapjack.Exp.const 1#64)

def body464_14 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 112#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "msg")

def body464_15 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 136#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "del")

def body464_16 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 168#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 152#64]))

def body464_17 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 176#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 160#64]))

def body464_18 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 264#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "acc_n")

def body464_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "acc_n"), none)) "htab_count"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 160#64])]

def body464_20 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 272#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "acc_n")

def body464_21 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.var Flapjack.VarKind.global "evm_empty")

def body464_22 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 144#64])
  (Flapjack.Exp.var Flapjack.VarKind.global "evm_empty")

def body464_23 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 216#64])
  (Flapjack.Exp.const 0#64)

def body464_24 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "e")

def body464_25 : Prog (BitVec 64) :=
.seq body464_23 body464_24

def body464_26 : Prog (BitVec 64) :=
.seq body464_22 body464_25

def body464_27 : Prog (BitVec 64) :=
.seq body464_21 body464_26

def body464_28 : Prog (BitVec 64) :=
.seq body464_20 body464_27

def body464_29 : Prog (BitVec 64) :=
.seq body464_19 body464_28

def body464_30 : Prog (BitVec 64) :=
.seq body464_18 body464_29

def body464_31 : Prog (BitVec 64) :=
.decCall ("acc_n") (Flapjack.Shape.one) ("htab_count") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 152#64])]) body464_30

def body464_32 : Prog (BitVec 64) :=
.seq body464_17 body464_31

def body464_33 : Prog (BitVec 64) :=
.seq body464_16 body464_32

def body464_34 : Prog (BitVec 64) :=
.seq body464_15 body464_33

def body464_35 : Prog (BitVec 64) :=
.decCall ("del") (Flapjack.Shape.one) ("htab_new_scratch") ([Flapjack.Exp.const 20#64, Flapjack.Exp.const 4#64]) body464_34

def body464_36 : Prog (BitVec 64) :=
.seq body464_14 body464_35

def body464_37 : Prog (BitVec 64) :=
.seq body464_13 body464_36

def body464_38 : Prog (BitVec 64) :=
.seq body464_12 body464_37

def body464_39 : Prog (BitVec 64) :=
.decCall ("logs") (Flapjack.Shape.one) ("lst_new_scratch") ([Flapjack.Exp.const 8#64, Flapjack.Exp.const 4#64]) body464_38

def body464_40 : Prog (BitVec 64) :=
.seq body464_11 body464_39

def body464_41 : Prog (BitVec 64) :=
.decCall ("jd") (Flapjack.Shape.one) ("compute_jumpdests") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 112#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 120#64])]) body464_40

def body464_42 : Prog (BitVec 64) :=
.seq body464_10 body464_41

def body464_43 : Prog (BitVec 64) :=
.seq body464_9 body464_42

def body464_44 : Prog (BitVec 64) :=
.seq body464_8 body464_43

def body464_45 : Prog (BitVec 64) :=
.seq body464_7 body464_44

def body464_46 : Prog (BitVec 64) :=
.seq body464_6 body464_45

def body464_47 : Prog (BitVec 64) :=
.seq body464_5 body464_46

def body464_48 : Prog (BitVec 64) :=
.seq body464_4 body464_47

def body464_49 : Prog (BitVec 64) :=
.decCall ("mem") (Flapjack.Shape.one) ("frame_mem_alloc") ([Flapjack.Exp.const 1024#64]) body464_48

def body464_50 : Prog (BitVec 64) :=
.seq body464_3 body464_49

def body464_51 : Prog (BitVec 64) :=
.seq body464_2 body464_50

def body464_52 : Prog (BitVec 64) :=
.seq body464_1 body464_51

def body464_53 : Prog (BitVec 64) :=
.decCall ("stk") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 32#64, Flapjack.Exp.const 32#64]]) body464_52

def body464_54 : Prog (BitVec 64) :=
.seq body464_0 body464_53

def body464_55 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.const 280#64]) body464_54

def body464_56 : Prog (BitVec 64) :=
.decCall ("mem_mark") (Flapjack.Shape.one) ("frame_mem_mark") ([]) body464_55

def body464_57 : Prog (BitVec 64) :=
.decCall ("stack_mark") (Flapjack.Shape.one) ("scratch_mark") ([]) body464_56

def body464_58 : Prog (BitVec 64) :=
.seq body464_1 body464_2

def body464_59 : Prog (BitVec 64) :=
.seq body464_58 body464_3

def body464_60 : Prog (BitVec 64) :=
.seq body464_4 body464_5

def body464_61 : Prog (BitVec 64) :=
.seq body464_60 body464_6

def body464_62 : Prog (BitVec 64) :=
.seq body464_61 body464_7

def body464_63 : Prog (BitVec 64) :=
.seq body464_62 body464_8

def body464_64 : Prog (BitVec 64) :=
.seq body464_63 body464_9

def body464_65 : Prog (BitVec 64) :=
.seq body464_64 body464_10

def body464_66 : Prog (BitVec 64) :=
.seq body464_12 body464_13

def body464_67 : Prog (BitVec 64) :=
.seq body464_66 body464_14

def body464_68 : Prog (BitVec 64) :=
.seq body464_15 body464_16

def body464_69 : Prog (BitVec 64) :=
.seq body464_68 body464_17

def body464_70 : Prog (BitVec 64) :=
.seq body464_18 body464_19

def body464_71 : Prog (BitVec 64) :=
.seq body464_70 body464_20

def body464_72 : Prog (BitVec 64) :=
.seq body464_71 body464_21

def body464_73 : Prog (BitVec 64) :=
.seq body464_72 body464_22

def body464_74 : Prog (BitVec 64) :=
.seq body464_73 body464_23

def body464_75 : Prog (BitVec 64) :=
.seq body464_74 body464_24

def body464_76 : Prog (BitVec 64) :=
.decCall ("acc_n") (Flapjack.Shape.one) ("htab_count") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 152#64])]) body464_75

def body464_77 : Prog (BitVec 64) :=
.seq body464_69 body464_76

def body464_78 : Prog (BitVec 64) :=
.decCall ("del") (Flapjack.Shape.one) ("htab_new_scratch") ([Flapjack.Exp.const 20#64, Flapjack.Exp.const 4#64]) body464_77

def body464_79 : Prog (BitVec 64) :=
.seq body464_67 body464_78

def body464_80 : Prog (BitVec 64) :=
.decCall ("logs") (Flapjack.Shape.one) ("lst_new_scratch") ([Flapjack.Exp.const 8#64, Flapjack.Exp.const 4#64]) body464_79

def body464_81 : Prog (BitVec 64) :=
.seq body464_11 body464_80

def body464_82 : Prog (BitVec 64) :=
.decCall ("jd") (Flapjack.Shape.one) ("compute_jumpdests") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 112#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 120#64])]) body464_81

def body464_83 : Prog (BitVec 64) :=
.seq body464_65 body464_82

def body464_84 : Prog (BitVec 64) :=
.decCall ("mem") (Flapjack.Shape.one) ("frame_mem_alloc") ([Flapjack.Exp.const 1024#64]) body464_83

def body464_85 : Prog (BitVec 64) :=
.seq body464_59 body464_84

def body464_86 : Prog (BitVec 64) :=
.decCall ("stk") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 32#64, Flapjack.Exp.const 32#64]]) body464_85

def body464_87 : Prog (BitVec 64) :=
.seq body464_0 body464_86

def body464_88 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.const 280#64]) body464_87

def body464_89 : Prog (BitVec 64) :=
.decCall ("mem_mark") (Flapjack.Shape.one) ("frame_mem_mark") ([]) body464_88

def body464_90 : Prog (BitVec 64) :=
.decCall ("stack_mark") (Flapjack.Shape.one) ("scratch_mark") ([]) body464_89

def originalData464 : Decl (BitVec 64) :=
.function { name := "frame_new", inline := false, exported := false, params := [("msg", Flapjack.Shape.one)], body := body464_57, returnShape := (Flapjack.Shape.one) }
def simplifiedData464 : Decl (BitVec 64) :=
.function { name := "frame_new", inline := false, exported := false, params := [("msg", Flapjack.Shape.one)], body := body464_90, returnShape := (Flapjack.Shape.one) }
def original464 := Pancake.PanLang.declToHOL originalData464
def simplified464 := Pancake.PanLang.declToHOL simplifiedData464
end InitECandidate.Proofs.FrontendStages.Declarations
