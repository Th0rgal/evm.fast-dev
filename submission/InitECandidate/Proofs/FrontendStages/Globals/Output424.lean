import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data424
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate408
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody424_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "post_bal"
  (Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "post", Flapjack.Exp.const 8#64]))

def globalBody424_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "post_nonce"
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "post", Flapjack.Exp.const 0#64]))

def globalBody424_2 : Prog (BitVec 64) :=
.seq globalBody424_0 globalBody424_1

def globalBody424_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "post_ch"
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "post", Flapjack.Exp.const 48#64]))

def globalBody424_4 : Prog (BitVec 64) :=
.seq globalBody424_2 globalBody424_3

def globalBody424_5 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody424_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "post") (Flapjack.Exp.const 1#64)) globalBody424_4 globalBody424_5

def globalBody424_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "add_balance_change"
  [Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.var Flapjack.VarKind.local "idx",
    Flapjack.Exp.var Flapjack.VarKind.local "post_bal"]

def globalBody424_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bal_remove_change"
  [Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 16#64, Flapjack.Exp.const 40#64,
    Flapjack.Exp.var Flapjack.VarKind.local "idx"]

def globalBody424_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) globalBody424_7 globalBody424_8

def globalBody424_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "add_nonce_change"
  [Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.var Flapjack.VarKind.local "idx",
    Flapjack.Exp.var Flapjack.VarKind.local "post_nonce"]

def globalBody424_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bal_remove_change"
  [Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 24#64, Flapjack.Exp.const 16#64,
    Flapjack.Exp.var Flapjack.VarKind.local "idx"]

def globalBody424_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "pre_nonce")
  (Flapjack.Exp.var Flapjack.VarKind.local "post_nonce")) globalBody424_10 globalBody424_11

def globalBody424_13 : Prog (BitVec 64) :=
.seq globalBody424_9 globalBody424_12

def globalBody424_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "eq"), none)) "memeq"
  [Flapjack.Exp.var Flapjack.VarKind.local "pre_ch", Flapjack.Exp.var Flapjack.VarKind.local "post_ch",
    Flapjack.Exp.const 32#64]

def globalBody424_15 : Prog (BitVec 64) :=
.seq globalBody424_13 globalBody424_14

def globalBody424_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "add_code_change"
  [Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.var Flapjack.VarKind.local "idx",
    Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "code"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "code")]

def globalBody424_17 : Prog (BitVec 64) :=
.decCall ("code") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("get_code") ([Flapjack.Exp.var Flapjack.VarKind.local "post_ch", Flapjack.Exp.var Flapjack.VarKind.local "addr"]) globalBody424_16

def globalBody424_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bal_remove_change"
  [Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 32#64, Flapjack.Exp.const 24#64,
    Flapjack.Exp.var Flapjack.VarKind.local "idx"]

def globalBody424_19 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) globalBody424_17 globalBody424_18

def globalBody424_20 : Prog (BitVec 64) :=
.seq globalBody424_15 globalBody424_19

def globalBody424_21 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "pre_bal", Flapjack.Exp.var Flapjack.VarKind.local "post_bal"]) globalBody424_20

def globalBody424_22 : Prog (BitVec 64) :=
.seq globalBody424_6 globalBody424_21

def globalBody424_23 : Prog (BitVec 64) :=
.dec ("post_ch") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 136#64])) globalBody424_22

def globalBody424_24 : Prog (BitVec 64) :=
.dec ("post_nonce") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody424_23

def globalBody424_25 : Prog (BitVec 64) :=
.dec ("post_bal") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) globalBody424_24

def globalBody424_26 : Prog (BitVec 64) :=
.dec ("pre_ch") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pre", Flapjack.Exp.const 48#64]) globalBody424_25

def globalBody424_27 : Prog (BitVec 64) :=
.dec ("pre_nonce") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pre", Flapjack.Exp.const 8#64])) globalBody424_26

def globalBody424_28 : Prog (BitVec 64) :=
.dec ("pre_bal") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pre", Flapjack.Exp.const 16#64])) globalBody424_27

def globalBody424_29 : Prog (BitVec 64) :=
.decCall ("pre") (Flapjack.Shape.one) ("idx_start_account") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) globalBody424_28

def globalBody424_30 : Prog (BitVec 64) :=
.dec ("post") (Flapjack.Shape.one) (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "s")) globalBody424_29

def globalBody424_31 : Prog (BitVec 64) :=
.dec ("addr") (Flapjack.Shape.one) (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s")) globalBody424_30

def globalBody424_32 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "s"))
  (Flapjack.Exp.const 0#64)) globalBody424_31 globalBody424_5

def globalBody424_33 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody424_34 : Prog (BitVec 64) :=
.seq globalBody424_32 globalBody424_33

def globalBody424_35 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_item") ([Flapjack.Exp.var Flapjack.VarKind.local "aw", Flapjack.Exp.var Flapjack.VarKind.local "i"]) globalBody424_34

def globalBody424_36 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "cap")) globalBody424_35

def globalBody424_37 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "cap"
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "outer", Flapjack.Exp.const 24#64]))

def globalBody424_38 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i" (Flapjack.Exp.const 0#64)

def globalBody424_39 : Prog (BitVec 64) :=
.seq globalBody424_37 globalBody424_38

def globalBody424_40 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "add_storage_write"
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s2"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "e"), Flapjack.Exp.var Flapjack.VarKind.local "idx",
    Flapjack.Exp.var Flapjack.VarKind.local "post_v"]

def globalBody424_41 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "remove_storage_write"
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s2"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "e"), Flapjack.Exp.var Flapjack.VarKind.local "idx"]

def globalBody424_42 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq2") (Flapjack.Exp.const 0#64)) globalBody424_40 globalBody424_41

def globalBody424_43 : Prog (BitVec 64) :=
.decCall ("eq2") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "pre_v", Flapjack.Exp.var Flapjack.VarKind.local "post_v"]) globalBody424_42

def globalBody424_44 : Prog (BitVec 64) :=
.dec ("post_v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "e"))) globalBody424_43

def globalBody424_45 : Prog (BitVec 64) :=
.decCall ("pre_v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("idx_start_storage") ([Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s2"),
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "e")]) globalBody424_44

def globalBody424_46 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "e"))
  (Flapjack.Exp.const 0#64)) globalBody424_45 globalBody424_5

def globalBody424_47 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "j"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 1#64])

def globalBody424_48 : Prog (BitVec 64) :=
.seq globalBody424_46 globalBody424_47

def globalBody424_49 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_item") ([Flapjack.Exp.var Flapjack.VarKind.local "inner", Flapjack.Exp.var Flapjack.VarKind.local "j"]) globalBody424_48

def globalBody424_50 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "j")
  (Flapjack.Exp.var Flapjack.VarKind.local "icap")) globalBody424_49

def globalBody424_51 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody424_50

def globalBody424_52 : Prog (BitVec 64) :=
.dec ("icap") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "inner", Flapjack.Exp.const 24#64])) globalBody424_51

def globalBody424_53 : Prog (BitVec 64) :=
.dec ("inner") (Flapjack.Shape.one) (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "s2")) globalBody424_52

def globalBody424_54 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "s2"))
  (Flapjack.Exp.const 0#64)) globalBody424_53 globalBody424_5

def globalBody424_55 : Prog (BitVec 64) :=
.seq globalBody424_54 globalBody424_33

def globalBody424_56 : Prog (BitVec 64) :=
.decCall ("s2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_item") ([Flapjack.Exp.var Flapjack.VarKind.local "outer", Flapjack.Exp.var Flapjack.VarKind.local "i"]) globalBody424_55

def globalBody424_57 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "cap")) globalBody424_56

def globalBody424_58 : Prog (BitVec 64) :=
.seq globalBody424_39 globalBody424_57

def globalBody424_59 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody424_60 : Prog (BitVec 64) :=
.seq globalBody424_58 globalBody424_59

def globalBody424_61 : Prog (BitVec 64) :=
.dec ("outer") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 184#64]),
      Flapjack.Exp.const 32#64])) globalBody424_60

def globalBody424_62 : Prog (BitVec 64) :=
.seq globalBody424_36 globalBody424_61

def globalBody424_63 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody424_62

def globalBody424_64 : Prog (BitVec 64) :=
.dec ("cap") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "aw", Flapjack.Exp.const 24#64])) globalBody424_63

def globalBody424_65 : Prog (BitVec 64) :=
.dec ("aw") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 184#64]),
      Flapjack.Exp.const 16#64])) globalBody424_64

def globalBody424_66 : Prog (BitVec 64) :=
.dec ("idx") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 224#64])) globalBody424_65

def globalData424 : Decl (BitVec 64) :=
.function { name := "update_builder_from_tx", inline := false, exported := false, params := [], body := globalBody424_66, returnShape := (Flapjack.Shape.one) }
def globalOutput424 := Pancake.PanLang.declToHOL globalData424
end InitECandidate.Proofs.FrontendStages.Declarations
