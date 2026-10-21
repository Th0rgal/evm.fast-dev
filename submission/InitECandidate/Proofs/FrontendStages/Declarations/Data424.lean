import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify408
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body424_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "post_bal"
  (Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "post", Flapjack.Exp.const 8#64]))

def body424_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "post_nonce"
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "post", Flapjack.Exp.const 0#64]))

def body424_2 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "post_ch"
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "post", Flapjack.Exp.const 48#64]))

def body424_3 : Prog (BitVec 64) :=
.seq body424_1 body424_2

def body424_4 : Prog (BitVec 64) :=
.seq body424_0 body424_3

def body424_5 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body424_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "post") (Flapjack.Exp.const 1#64)) body424_4 body424_5

def body424_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "add_balance_change"
  [Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.var Flapjack.VarKind.local "idx",
    Flapjack.Exp.var Flapjack.VarKind.local "post_bal"]

def body424_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bal_remove_change"
  [Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 16#64, Flapjack.Exp.const 40#64,
    Flapjack.Exp.var Flapjack.VarKind.local "idx"]

def body424_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) body424_7 body424_8

def body424_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "add_nonce_change"
  [Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.var Flapjack.VarKind.local "idx",
    Flapjack.Exp.var Flapjack.VarKind.local "post_nonce"]

def body424_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bal_remove_change"
  [Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 24#64, Flapjack.Exp.const 16#64,
    Flapjack.Exp.var Flapjack.VarKind.local "idx"]

def body424_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "pre_nonce")
  (Flapjack.Exp.var Flapjack.VarKind.local "post_nonce")) body424_10 body424_11

def body424_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "eq"), none)) "memeq"
  [Flapjack.Exp.var Flapjack.VarKind.local "pre_ch", Flapjack.Exp.var Flapjack.VarKind.local "post_ch",
    Flapjack.Exp.const 32#64]

def body424_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "add_code_change"
  [Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.var Flapjack.VarKind.local "idx",
    Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "code"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "code")]

def body424_15 : Prog (BitVec 64) :=
.decCall ("code") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("get_code") ([Flapjack.Exp.var Flapjack.VarKind.local "post_ch", Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body424_14

def body424_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bal_remove_change"
  [Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 32#64, Flapjack.Exp.const 24#64,
    Flapjack.Exp.var Flapjack.VarKind.local "idx"]

def body424_17 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) body424_15 body424_16

def body424_18 : Prog (BitVec 64) :=
.seq body424_13 body424_17

def body424_19 : Prog (BitVec 64) :=
.seq body424_12 body424_18

def body424_20 : Prog (BitVec 64) :=
.seq body424_9 body424_19

def body424_21 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "pre_bal", Flapjack.Exp.var Flapjack.VarKind.local "post_bal"]) body424_20

def body424_22 : Prog (BitVec 64) :=
.seq body424_6 body424_21

def body424_23 : Prog (BitVec 64) :=
.dec ("post_ch") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.global "empty_code_hash") body424_22

def body424_24 : Prog (BitVec 64) :=
.dec ("post_nonce") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body424_23

def body424_25 : Prog (BitVec 64) :=
.dec ("post_bal") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body424_24

def body424_26 : Prog (BitVec 64) :=
.dec ("pre_ch") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pre", Flapjack.Exp.const 48#64]) body424_25

def body424_27 : Prog (BitVec 64) :=
.dec ("pre_nonce") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pre", Flapjack.Exp.const 8#64])) body424_26

def body424_28 : Prog (BitVec 64) :=
.dec ("pre_bal") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pre", Flapjack.Exp.const 16#64])) body424_27

def body424_29 : Prog (BitVec 64) :=
.decCall ("pre") (Flapjack.Shape.one) ("idx_start_account") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body424_28

def body424_30 : Prog (BitVec 64) :=
.dec ("post") (Flapjack.Shape.one) (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "s")) body424_29

def body424_31 : Prog (BitVec 64) :=
.dec ("addr") (Flapjack.Shape.one) (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s")) body424_30

def body424_32 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "s"))
  (Flapjack.Exp.const 0#64)) body424_31 body424_5

def body424_33 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body424_34 : Prog (BitVec 64) :=
.seq body424_32 body424_33

def body424_35 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_item") ([Flapjack.Exp.var Flapjack.VarKind.local "aw", Flapjack.Exp.var Flapjack.VarKind.local "i"]) body424_34

def body424_36 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "cap")) body424_35

def body424_37 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "cap"
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "outer", Flapjack.Exp.const 24#64]))

def body424_38 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i" (Flapjack.Exp.const 0#64)

def body424_39 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "add_storage_write"
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s2"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "e"), Flapjack.Exp.var Flapjack.VarKind.local "idx",
    Flapjack.Exp.var Flapjack.VarKind.local "post_v"]

def body424_40 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "remove_storage_write"
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s2"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "e"), Flapjack.Exp.var Flapjack.VarKind.local "idx"]

def body424_41 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq2") (Flapjack.Exp.const 0#64)) body424_39 body424_40

def body424_42 : Prog (BitVec 64) :=
.decCall ("eq2") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "pre_v", Flapjack.Exp.var Flapjack.VarKind.local "post_v"]) body424_41

def body424_43 : Prog (BitVec 64) :=
.dec ("post_v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "e"))) body424_42

def body424_44 : Prog (BitVec 64) :=
.decCall ("pre_v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("idx_start_storage") ([Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s2"),
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "e")]) body424_43

def body424_45 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "e"))
  (Flapjack.Exp.const 0#64)) body424_44 body424_5

def body424_46 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "j"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 1#64])

def body424_47 : Prog (BitVec 64) :=
.seq body424_45 body424_46

def body424_48 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_item") ([Flapjack.Exp.var Flapjack.VarKind.local "inner", Flapjack.Exp.var Flapjack.VarKind.local "j"]) body424_47

def body424_49 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "j")
  (Flapjack.Exp.var Flapjack.VarKind.local "icap")) body424_48

def body424_50 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body424_49

def body424_51 : Prog (BitVec 64) :=
.dec ("icap") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "inner", Flapjack.Exp.const 24#64])) body424_50

def body424_52 : Prog (BitVec 64) :=
.dec ("inner") (Flapjack.Shape.one) (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "s2")) body424_51

def body424_53 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "s2"))
  (Flapjack.Exp.const 0#64)) body424_52 body424_5

def body424_54 : Prog (BitVec 64) :=
.seq body424_53 body424_33

def body424_55 : Prog (BitVec 64) :=
.decCall ("s2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_item") ([Flapjack.Exp.var Flapjack.VarKind.local "outer", Flapjack.Exp.var Flapjack.VarKind.local "i"]) body424_54

def body424_56 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "cap")) body424_55

def body424_57 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body424_58 : Prog (BitVec 64) :=
.seq body424_56 body424_57

def body424_59 : Prog (BitVec 64) :=
.seq body424_38 body424_58

def body424_60 : Prog (BitVec 64) :=
.seq body424_37 body424_59

def body424_61 : Prog (BitVec 64) :=
.dec ("outer") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ts", Flapjack.Exp.const 32#64])) body424_60

def body424_62 : Prog (BitVec 64) :=
.seq body424_36 body424_61

def body424_63 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body424_62

def body424_64 : Prog (BitVec 64) :=
.dec ("cap") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "aw", Flapjack.Exp.const 24#64])) body424_63

def body424_65 : Prog (BitVec 64) :=
.dec ("aw") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ts", Flapjack.Exp.const 16#64])) body424_64

def body424_66 : Prog (BitVec 64) :=
.dec ("idx") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.global "bal_index") body424_65

def body424_67 : Prog (BitVec 64) :=
.seq body424_0 body424_1

def body424_68 : Prog (BitVec 64) :=
.seq body424_67 body424_2

def body424_69 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "post") (Flapjack.Exp.const 1#64)) body424_68 body424_5

def body424_70 : Prog (BitVec 64) :=
.seq body424_9 body424_12

def body424_71 : Prog (BitVec 64) :=
.seq body424_70 body424_13

def body424_72 : Prog (BitVec 64) :=
.seq body424_71 body424_17

def body424_73 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "pre_bal", Flapjack.Exp.var Flapjack.VarKind.local "post_bal"]) body424_72

def body424_74 : Prog (BitVec 64) :=
.seq body424_69 body424_73

def body424_75 : Prog (BitVec 64) :=
.dec ("post_ch") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.global "empty_code_hash") body424_74

def body424_76 : Prog (BitVec 64) :=
.dec ("post_nonce") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body424_75

def body424_77 : Prog (BitVec 64) :=
.dec ("post_bal") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body424_76

def body424_78 : Prog (BitVec 64) :=
.dec ("pre_ch") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pre", Flapjack.Exp.const 48#64]) body424_77

def body424_79 : Prog (BitVec 64) :=
.dec ("pre_nonce") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pre", Flapjack.Exp.const 8#64])) body424_78

def body424_80 : Prog (BitVec 64) :=
.dec ("pre_bal") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pre", Flapjack.Exp.const 16#64])) body424_79

def body424_81 : Prog (BitVec 64) :=
.decCall ("pre") (Flapjack.Shape.one) ("idx_start_account") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body424_80

def body424_82 : Prog (BitVec 64) :=
.dec ("post") (Flapjack.Shape.one) (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "s")) body424_81

def body424_83 : Prog (BitVec 64) :=
.dec ("addr") (Flapjack.Shape.one) (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s")) body424_82

def body424_84 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "s"))
  (Flapjack.Exp.const 0#64)) body424_83 body424_5

def body424_85 : Prog (BitVec 64) :=
.seq body424_84 body424_33

def body424_86 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_item") ([Flapjack.Exp.var Flapjack.VarKind.local "aw", Flapjack.Exp.var Flapjack.VarKind.local "i"]) body424_85

def body424_87 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "cap")) body424_86

def body424_88 : Prog (BitVec 64) :=
.seq body424_37 body424_38

def body424_89 : Prog (BitVec 64) :=
.seq body424_88 body424_56

def body424_90 : Prog (BitVec 64) :=
.seq body424_89 body424_57

def body424_91 : Prog (BitVec 64) :=
.dec ("outer") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ts", Flapjack.Exp.const 32#64])) body424_90

def body424_92 : Prog (BitVec 64) :=
.seq body424_87 body424_91

def body424_93 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body424_92

def body424_94 : Prog (BitVec 64) :=
.dec ("cap") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "aw", Flapjack.Exp.const 24#64])) body424_93

def body424_95 : Prog (BitVec 64) :=
.dec ("aw") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ts", Flapjack.Exp.const 16#64])) body424_94

def body424_96 : Prog (BitVec 64) :=
.dec ("idx") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.global "bal_index") body424_95

def originalData424 : Decl (BitVec 64) :=
.function { name := "update_builder_from_tx", inline := false, exported := false, params := [], body := body424_66, returnShape := (Flapjack.Shape.one) }
def simplifiedData424 : Decl (BitVec 64) :=
.function { name := "update_builder_from_tx", inline := false, exported := false, params := [], body := body424_96, returnShape := (Flapjack.Shape.one) }
def original424 := Pancake.PanLang.declToHOL originalData424
def simplified424 := Pancake.PanLang.declToHOL simplifiedData424
end InitECandidate.Proofs.FrontendStages.Declarations
