import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify858
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body874_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.var Flapjack.VarKind.local "dep",
    Flapjack.Exp.var Flapjack.VarKind.local "dep_n"]

def body874_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "dep" (Flapjack.Exp.var Flapjack.VarKind.local "nd")

def body874_2 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "dep_cap"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "dep_cap", Flapjack.Exp.const 2#64],
      Flapjack.Exp.const 1024#64])

def body874_3 : Prog (BitVec 64) :=
.seq body874_1 body874_2

def body874_4 : Prog (BitVec 64) :=
.seq body874_0 body874_3

def body874_5 : Prog (BitVec 64) :=
.decCall ("nd") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "dep_cap", Flapjack.Exp.const 2#64],
      Flapjack.Exp.const 1024#64]]) body874_4

def body874_6 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body874_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "dep_cap")
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "dep_n", Flapjack.Exp.const 192#64])) body874_5 body874_6

def body874_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "extract_deposit_data"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "log", Flapjack.Exp.const 24#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "log", Flapjack.Exp.const 32#64]),
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "dep", Flapjack.Exp.var Flapjack.VarKind.local "dep_n"]]

def body874_9 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "dep_n"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "dep_n", Flapjack.Exp.const 192#64])

def body874_10 : Prog (BitVec 64) :=
.seq body874_8 body874_9

def body874_11 : Prog (BitVec 64) :=
.seq body874_7 body874_10

def body874_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "sig") (Flapjack.Exp.const 0#64)) body874_11 body874_6

def body874_13 : Prog (BitVec 64) :=
.decCall ("sig") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "log", Flapjack.Exp.const 8#64]),
  Flapjack.Exp.var Flapjack.VarKind.global "deposit_event_signature_hash", Flapjack.Exp.const 32#64]) body874_12

def body874_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "log", Flapjack.Exp.const 16#64]))) body874_13 body874_6

def body874_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "isdep") (Flapjack.Exp.const 0#64)) body874_14 body874_6

def body874_16 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "j"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 1#64])

def body874_17 : Prog (BitVec 64) :=
.seq body874_15 body874_16

def body874_18 : Prog (BitVec 64) :=
.decCall ("isdep") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "log", Flapjack.Exp.const 0#64]),
  Flapjack.Exp.var Flapjack.VarKind.global "deposit_contract_address", Flapjack.Exp.const 20#64]) body874_17

def body874_19 : Prog (BitVec 64) :=
.dec ("log") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "lp",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 8#64]])) body874_18

def body874_20 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "j")
  (Flapjack.Exp.var Flapjack.VarKind.local "nl")) body874_19

def body874_21 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body874_22 : Prog (BitVec 64) :=
.seq body874_20 body874_21

def body874_23 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body874_22

def body874_24 : Prog (BitVec 64) :=
.dec ("lp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "logs", Flapjack.Exp.const 0#64])) body874_23

def body874_25 : Prog (BitVec 64) :=
.dec ("nl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "logs", Flapjack.Exp.const 8#64])) body874_24

def body874_26 : Prog (BitVec 64) :=
.dec ("logs") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "rp",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]])) body874_25

def body874_27 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "nr")) body874_26

def body874_28 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "requests_append"
  [Flapjack.Exp.const 0#64, Flapjack.Exp.var Flapjack.VarKind.local "dep",
    Flapjack.Exp.var Flapjack.VarKind.local "dep_n"]

def body874_29 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "dep_n")) body874_28 body874_6

def body874_30 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "requests_append"
  [Flapjack.Exp.const 1#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "o1", Flapjack.Exp.const 40#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "o1", Flapjack.Exp.const 48#64])]

def body874_31 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "o1", Flapjack.Exp.const 48#64]))) body874_30 body874_6

def body874_32 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "requests_append"
  [Flapjack.Exp.const 2#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "o2", Flapjack.Exp.const 40#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "o2", Flapjack.Exp.const 48#64])]

def body874_33 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "o2", Flapjack.Exp.const 48#64]))) body874_32 body874_6

def body874_34 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "requests_append"
  [Flapjack.Exp.const 3#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "o3", Flapjack.Exp.const 40#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "o3", Flapjack.Exp.const 48#64])]

def body874_35 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "o3", Flapjack.Exp.const 48#64]))) body874_34 body874_6

def body874_36 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "requests_append"
  [Flapjack.Exp.const 4#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "o4", Flapjack.Exp.const 40#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "o4", Flapjack.Exp.const 48#64])]

def body874_37 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "o4", Flapjack.Exp.const 48#64]))) body874_36 body874_6

def body874_38 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body874_39 : Prog (BitVec 64) :=
.seq body874_37 body874_38

def body874_40 : Prog (BitVec 64) :=
.decCall ("o4") (Flapjack.Shape.one) ("process_checked_system_transaction") ([Flapjack.Exp.var Flapjack.VarKind.global "builder_exit_address"]) body874_39

def body874_41 : Prog (BitVec 64) :=
.seq body874_35 body874_40

def body874_42 : Prog (BitVec 64) :=
.decCall ("o3") (Flapjack.Shape.one) ("process_checked_system_transaction") ([Flapjack.Exp.var Flapjack.VarKind.global "builder_deposit_address"]) body874_41

def body874_43 : Prog (BitVec 64) :=
.seq body874_33 body874_42

def body874_44 : Prog (BitVec 64) :=
.decCall ("o2") (Flapjack.Shape.one) ("process_checked_system_transaction") ([Flapjack.Exp.var Flapjack.VarKind.global "consolidation_request_address"]) body874_43

def body874_45 : Prog (BitVec 64) :=
.seq body874_31 body874_44

def body874_46 : Prog (BitVec 64) :=
.decCall ("o1") (Flapjack.Shape.one) ("process_checked_system_transaction") ([Flapjack.Exp.var Flapjack.VarKind.global "withdrawal_request_address"]) body874_45

def body874_47 : Prog (BitVec 64) :=
.seq body874_29 body874_46

def body874_48 : Prog (BitVec 64) :=
.seq body874_27 body874_47

def body874_49 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body874_48

def body874_50 : Prog (BitVec 64) :=
.dec ("dep_cap") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body874_49

def body874_51 : Prog (BitVec 64) :=
.dec ("dep_n") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body874_50

def body874_52 : Prog (BitVec 64) :=
.decCall ("dep") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 8#64]) body874_51

def body874_53 : Prog (BitVec 64) :=
.dec ("rp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rls", Flapjack.Exp.const 0#64])) body874_52

def body874_54 : Prog (BitVec 64) :=
.dec ("nr") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rls", Flapjack.Exp.const 8#64])) body874_53

def body874_55 : Prog (BitVec 64) :=
.dec ("rls") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 72#64])) body874_54

def body874_56 : Prog (BitVec 64) :=
.seq body874_0 body874_1

def body874_57 : Prog (BitVec 64) :=
.seq body874_56 body874_2

def body874_58 : Prog (BitVec 64) :=
.decCall ("nd") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "dep_cap", Flapjack.Exp.const 2#64],
      Flapjack.Exp.const 1024#64]]) body874_57

def body874_59 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "dep_cap")
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "dep_n", Flapjack.Exp.const 192#64])) body874_58 body874_6

def body874_60 : Prog (BitVec 64) :=
.seq body874_59 body874_8

def body874_61 : Prog (BitVec 64) :=
.seq body874_60 body874_9

def body874_62 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "sig") (Flapjack.Exp.const 0#64)) body874_61 body874_6

def body874_63 : Prog (BitVec 64) :=
.decCall ("sig") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "log", Flapjack.Exp.const 8#64]),
  Flapjack.Exp.var Flapjack.VarKind.global "deposit_event_signature_hash", Flapjack.Exp.const 32#64]) body874_62

def body874_64 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "log", Flapjack.Exp.const 16#64]))) body874_63 body874_6

def body874_65 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "isdep") (Flapjack.Exp.const 0#64)) body874_64 body874_6

def body874_66 : Prog (BitVec 64) :=
.seq body874_65 body874_16

def body874_67 : Prog (BitVec 64) :=
.decCall ("isdep") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "log", Flapjack.Exp.const 0#64]),
  Flapjack.Exp.var Flapjack.VarKind.global "deposit_contract_address", Flapjack.Exp.const 20#64]) body874_66

def body874_68 : Prog (BitVec 64) :=
.dec ("log") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "lp",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 8#64]])) body874_67

def body874_69 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "j")
  (Flapjack.Exp.var Flapjack.VarKind.local "nl")) body874_68

def body874_70 : Prog (BitVec 64) :=
.seq body874_69 body874_21

def body874_71 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body874_70

def body874_72 : Prog (BitVec 64) :=
.dec ("lp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "logs", Flapjack.Exp.const 0#64])) body874_71

def body874_73 : Prog (BitVec 64) :=
.dec ("nl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "logs", Flapjack.Exp.const 8#64])) body874_72

def body874_74 : Prog (BitVec 64) :=
.dec ("logs") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "rp",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]])) body874_73

def body874_75 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "nr")) body874_74

def body874_76 : Prog (BitVec 64) :=
.seq body874_75 body874_29

def body874_77 : Prog (BitVec 64) :=
.seq body874_76 body874_46

def body874_78 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body874_77

def body874_79 : Prog (BitVec 64) :=
.dec ("dep_cap") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body874_78

def body874_80 : Prog (BitVec 64) :=
.dec ("dep_n") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body874_79

def body874_81 : Prog (BitVec 64) :=
.decCall ("dep") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 8#64]) body874_80

def body874_82 : Prog (BitVec 64) :=
.dec ("rp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rls", Flapjack.Exp.const 0#64])) body874_81

def body874_83 : Prog (BitVec 64) :=
.dec ("nr") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rls", Flapjack.Exp.const 8#64])) body874_82

def body874_84 : Prog (BitVec 64) :=
.dec ("rls") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 72#64])) body874_83

def originalData874 : Decl (BitVec 64) :=
.function { name := "process_general_purpose_requests", inline := false, exported := false, params := [], body := body874_55, returnShape := (Flapjack.Shape.one) }
def simplifiedData874 : Decl (BitVec 64) :=
.function { name := "process_general_purpose_requests", inline := false, exported := false, params := [], body := body874_84, returnShape := (Flapjack.Shape.one) }
def original874 := Pancake.PanLang.declToHOL originalData874
def simplified874 := Pancake.PanLang.declToHOL simplifiedData874
end InitECandidate.Proofs.FrontendStages.Declarations
