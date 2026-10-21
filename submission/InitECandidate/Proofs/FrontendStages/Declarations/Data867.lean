import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify851
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body867_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "state_fresh_tx" []

def body867_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.global "vm_system_address")

def body867_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "target")

def body867_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 48#64]))

def body867_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 80#64])
  (Flapjack.Exp.const 30000000#64)

def body867_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 88#64])
  (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 97920#64, Flapjack.Exp.const 16#64])

def body867_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.global "be")

def body867_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "te")

def body867_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.global "vm_system_address")

def body867_9 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "target")

def body867_10 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "target")

def body867_11 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.const 30000000#64)

def body867_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 97920#64, Flapjack.Exp.const 16#64])

def body867_13 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 88#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "data")

def body867_14 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "data_n")

def body867_15 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 104#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "target")

def body867_16 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 112#64])
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "code"))

def body867_17 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "code"))

def body867_18 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 152#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "aa")

def body867_19 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 160#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "ak")

def body867_20 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body867_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "incorporate_tx_into_block" []

def body867_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "system_ret",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 40#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "system_ret_n"]

def body867_23 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "system_ret")

def body867_24 : Prog (BitVec 64) :=
.seq body867_22 body867_23

def body867_25 : Prog (BitVec 64) :=
.decCall ("system_ret") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "system_ret_n", Flapjack.Exp.const 8#64]]) body867_24

def body867_26 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "system_ret_n")) body867_25 body867_20

def body867_27 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "scratch_release" [Flapjack.Exp.var Flapjack.VarKind.local "system_mark"]

def body867_28 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "frame_mem_release"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 88#64])]

def body867_29 : Prog (BitVec 64) :=
.seq body867_27 body867_28

def body867_30 : Prog (BitVec 64) :=
.seq body867_26 body867_29

def body867_31 : Prog (BitVec 64) :=
.dec ("system_ret_n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 48#64])) body867_30

def body867_32 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "system_mark") (Flapjack.Exp.const 0#64)) body867_31 body867_20

def body867_33 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "out")

def body867_34 : Prog (BitVec 64) :=
.seq body867_32 body867_33

def body867_35 : Prog (BitVec 64) :=
.dec ("system_mark") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 80#64])) body867_34

def body867_36 : Prog (BitVec 64) :=
.seq body867_21 body867_35

def body867_37 : Prog (BitVec 64) :=
.seq body867_20 body867_36

def body867_38 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("process_message_call") ([Flapjack.Exp.var Flapjack.VarKind.local "m"]) body867_37

def body867_39 : Prog (BitVec 64) :=
.seq body867_20 body867_38

def body867_40 : Prog (BitVec 64) :=
.seq body867_19 body867_39

def body867_41 : Prog (BitVec 64) :=
.decCall ("ak") (Flapjack.Shape.one) ("htab_new") ([Flapjack.Exp.const 52#64, Flapjack.Exp.const 8#64]) body867_40

def body867_42 : Prog (BitVec 64) :=
.seq body867_18 body867_41

def body867_43 : Prog (BitVec 64) :=
.decCall ("aa") (Flapjack.Shape.one) ("htab_new") ([Flapjack.Exp.const 20#64, Flapjack.Exp.const 8#64]) body867_42

def body867_44 : Prog (BitVec 64) :=
.seq body867_17 body867_43

def body867_45 : Prog (BitVec 64) :=
.seq body867_16 body867_44

def body867_46 : Prog (BitVec 64) :=
.seq body867_15 body867_45

def body867_47 : Prog (BitVec 64) :=
.seq body867_14 body867_46

def body867_48 : Prog (BitVec 64) :=
.seq body867_13 body867_47

def body867_49 : Prog (BitVec 64) :=
.seq body867_12 body867_48

def body867_50 : Prog (BitVec 64) :=
.seq body867_11 body867_49

def body867_51 : Prog (BitVec 64) :=
.seq body867_10 body867_50

def body867_52 : Prog (BitVec 64) :=
.seq body867_9 body867_51

def body867_53 : Prog (BitVec 64) :=
.seq body867_8 body867_52

def body867_54 : Prog (BitVec 64) :=
.seq body867_7 body867_53

def body867_55 : Prog (BitVec 64) :=
.seq body867_6 body867_54

def body867_56 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.one) ("msg_new") ([]) body867_55

def body867_57 : Prog (BitVec 64) :=
.seq body867_5 body867_56

def body867_58 : Prog (BitVec 64) :=
.seq body867_4 body867_57

def body867_59 : Prog (BitVec 64) :=
.seq body867_3 body867_58

def body867_60 : Prog (BitVec 64) :=
.seq body867_2 body867_59

def body867_61 : Prog (BitVec 64) :=
.seq body867_1 body867_60

def body867_62 : Prog (BitVec 64) :=
.decCall ("te") (Flapjack.Shape.one) ("te_new") ([]) body867_61

def body867_63 : Prog (BitVec 64) :=
.decCall ("code") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("ext_code_of") ([Flapjack.Exp.var Flapjack.VarKind.local "target"]) body867_62

def body867_64 : Prog (BitVec 64) :=
.seq body867_0 body867_63

def body867_65 : Prog (BitVec 64) :=
.seq body867_1 body867_2

def body867_66 : Prog (BitVec 64) :=
.seq body867_65 body867_3

def body867_67 : Prog (BitVec 64) :=
.seq body867_66 body867_4

def body867_68 : Prog (BitVec 64) :=
.seq body867_67 body867_5

def body867_69 : Prog (BitVec 64) :=
.seq body867_6 body867_7

def body867_70 : Prog (BitVec 64) :=
.seq body867_69 body867_8

def body867_71 : Prog (BitVec 64) :=
.seq body867_70 body867_9

def body867_72 : Prog (BitVec 64) :=
.seq body867_71 body867_10

def body867_73 : Prog (BitVec 64) :=
.seq body867_72 body867_11

def body867_74 : Prog (BitVec 64) :=
.seq body867_73 body867_12

def body867_75 : Prog (BitVec 64) :=
.seq body867_74 body867_13

def body867_76 : Prog (BitVec 64) :=
.seq body867_75 body867_14

def body867_77 : Prog (BitVec 64) :=
.seq body867_76 body867_15

def body867_78 : Prog (BitVec 64) :=
.seq body867_77 body867_16

def body867_79 : Prog (BitVec 64) :=
.seq body867_78 body867_17

def body867_80 : Prog (BitVec 64) :=
.seq body867_26 body867_27

def body867_81 : Prog (BitVec 64) :=
.seq body867_80 body867_28

def body867_82 : Prog (BitVec 64) :=
.dec ("system_ret_n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 48#64])) body867_81

def body867_83 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "system_mark") (Flapjack.Exp.const 0#64)) body867_82 body867_20

def body867_84 : Prog (BitVec 64) :=
.seq body867_83 body867_33

def body867_85 : Prog (BitVec 64) :=
.dec ("system_mark") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 80#64])) body867_84

def body867_86 : Prog (BitVec 64) :=
.seq body867_21 body867_85

def body867_87 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("process_message_call") ([Flapjack.Exp.var Flapjack.VarKind.local "m"]) body867_86

def body867_88 : Prog (BitVec 64) :=
.seq body867_19 body867_87

def body867_89 : Prog (BitVec 64) :=
.decCall ("ak") (Flapjack.Shape.one) ("htab_new") ([Flapjack.Exp.const 52#64, Flapjack.Exp.const 8#64]) body867_88

def body867_90 : Prog (BitVec 64) :=
.seq body867_18 body867_89

def body867_91 : Prog (BitVec 64) :=
.decCall ("aa") (Flapjack.Shape.one) ("htab_new") ([Flapjack.Exp.const 20#64, Flapjack.Exp.const 8#64]) body867_90

def body867_92 : Prog (BitVec 64) :=
.seq body867_79 body867_91

def body867_93 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.one) ("msg_new") ([]) body867_92

def body867_94 : Prog (BitVec 64) :=
.seq body867_68 body867_93

def body867_95 : Prog (BitVec 64) :=
.decCall ("te") (Flapjack.Shape.one) ("te_new") ([]) body867_94

def body867_96 : Prog (BitVec 64) :=
.decCall ("code") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("ext_code_of") ([Flapjack.Exp.var Flapjack.VarKind.local "target"]) body867_95

def body867_97 : Prog (BitVec 64) :=
.seq body867_0 body867_96

def originalData867 : Decl (BitVec 64) :=
.function { name := "process_unchecked_system_transaction", inline := false, exported := false, params := [("target", Flapjack.Shape.one), ("data", Flapjack.Shape.one), ("data_n", Flapjack.Shape.one)], body := body867_64, returnShape := (Flapjack.Shape.one) }
def simplifiedData867 : Decl (BitVec 64) :=
.function { name := "process_unchecked_system_transaction", inline := false, exported := false, params := [("target", Flapjack.Shape.one), ("data", Flapjack.Shape.one), ("data_n", Flapjack.Shape.one)], body := body867_97, returnShape := (Flapjack.Shape.one) }
def original867 := Pancake.PanLang.declToHOL originalData867
def simplified867 := Pancake.PanLang.declToHOL simplifiedData867
end InitECandidate.Proofs.FrontendStages.Declarations
