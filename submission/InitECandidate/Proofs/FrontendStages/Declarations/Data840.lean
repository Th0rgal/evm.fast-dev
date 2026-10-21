import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify824
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body840_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "cache", Flapjack.Exp.var Flapjack.VarKind.local "addr",
    Flapjack.Exp.const 1#64]

def body840_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body840_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "has") (Flapjack.Exp.const 0#64)) body840_0 body840_1

def body840_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "enc",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "vbuf", Flapjack.Exp.const 40#64],
    Flapjack.Exp.var Flapjack.VarKind.local "w"]

def body840_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "mpt", Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "e"),
    Flapjack.Exp.const 32#64, Flapjack.Exp.var Flapjack.VarKind.local "enc",
    Flapjack.Exp.var Flapjack.VarKind.local "w"]

def body840_5 : Prog (BitVec 64) :=
.seq body840_3 body840_4

def body840_6 : Prog (BitVec 64) :=
.decCall ("enc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 40#64]) body840_5

def body840_7 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("rlp_encode_bytes") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "vbuf", Flapjack.Exp.const 8#64, Flapjack.Exp.const 32#64],
  Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "vbuf", Flapjack.Exp.const 8#64],
  Flapjack.Exp.var Flapjack.VarKind.local "n"]) body840_6

def body840_8 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("u256_to_be_min") ([Flapjack.Exp.var Flapjack.VarKind.local "v",
  Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "vbuf", Flapjack.Exp.const 8#64]]) body840_7

def body840_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "pass") (Flapjack.Exp.const 0#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64))]) body840_8 body840_1

def body840_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "mpt", Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "e"),
    Flapjack.Exp.const 32#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]

def body840_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "pass") (Flapjack.Exp.const 1#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64))]) body840_10 body840_1

def body840_12 : Prog (BitVec 64) :=
.seq body840_9 body840_11

def body840_13 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "v"]) body840_12

def body840_14 : Prog (BitVec 64) :=
.dec ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "e"))) body840_13

def body840_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "e"))
  (Flapjack.Exp.const 0#64)) body840_14 body840_1

def body840_16 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "j"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 1#64])

def body840_17 : Prog (BitVec 64) :=
.seq body840_15 body840_16

def body840_18 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_item") ([Flapjack.Exp.var Flapjack.VarKind.local "inner", Flapjack.Exp.var Flapjack.VarKind.local "j"]) body840_17

def body840_19 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "j")
  (Flapjack.Exp.var Flapjack.VarKind.local "icount")) body840_18

def body840_20 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pass"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pass", Flapjack.Exp.const 1#64])

def body840_21 : Prog (BitVec 64) :=
.seq body840_19 body840_20

def body840_22 : Prog (BitVec 64) :=
.dec ("icount") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "inner", Flapjack.Exp.const 24#64])) body840_21

def body840_23 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body840_22

def body840_24 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "pass") (Flapjack.Exp.const 2#64)) body840_23

def body840_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_root"
  [Flapjack.Exp.var Flapjack.VarKind.local "mpt", Flapjack.Exp.var Flapjack.VarKind.local "root"]

def body840_26 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "new_roots", Flapjack.Exp.var Flapjack.VarKind.local "addr",
    Flapjack.Exp.var Flapjack.VarKind.local "root"]

def body840_27 : Prog (BitVec 64) :=
.seq body840_25 body840_26

def body840_28 : Prog (BitVec 64) :=
.decCall ("root") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body840_27

def body840_29 : Prog (BitVec 64) :=
.seq body840_24 body840_28

def body840_30 : Prog (BitVec 64) :=
.dec ("pass") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body840_29

def body840_31 : Prog (BitVec 64) :=
.decCall ("vbuf") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body840_30

def body840_32 : Prog (BitVec 64) :=
.decCall ("mpt") (Flapjack.Shape.one) ("mpt_from_witness") ([Flapjack.Exp.var Flapjack.VarKind.local "nodedb", Flapjack.Exp.var Flapjack.VarKind.local "old_root",
  Flapjack.Exp.const 1#64]) body840_31

def body840_33 : Prog (BitVec 64) :=
.decCall ("old_root") (Flapjack.Shape.one) ("ws_storage_root_of") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body840_32

def body840_34 : Prog (BitVec 64) :=
.seq body840_2 body840_33

def body840_35 : Prog (BitVec 64) :=
.decCall ("has") (Flapjack.Shape.one) ("htab_has") ([Flapjack.Exp.var Flapjack.VarKind.local "cache", Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body840_34

def body840_36 : Prog (BitVec 64) :=
.dec ("inner") (Flapjack.Shape.one) (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "s")) body840_35

def body840_37 : Prog (BitVec 64) :=
.dec ("addr") (Flapjack.Shape.one) (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s")) body840_36

def body840_38 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "s"))
  (Flapjack.Exp.const 0#64)) body840_37 body840_1

def body840_39 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body840_40 : Prog (BitVec 64) :=
.seq body840_38 body840_39

def body840_41 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_item") ([Flapjack.Exp.var Flapjack.VarKind.local "sw", Flapjack.Exp.var Flapjack.VarKind.local "i"]) body840_40

def body840_42 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "cap")) body840_41

def body840_43 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i" (Flapjack.Exp.const 0#64)

def body840_44 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "cache",
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s2"), Flapjack.Exp.const 1#64]

def body840_45 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "sr" (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "nr"))

def body840_46 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "nr"))
  (Flapjack.Exp.const 0#64)) body840_45 body840_1

def body840_47 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "state_mpt",
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s2"), Flapjack.Exp.const 20#64,
    Flapjack.Exp.var Flapjack.VarKind.local "enc", Flapjack.Exp.var Flapjack.VarKind.local "n"]

def body840_48 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("encode_account") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 0#64]),
  Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 8#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "sr",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 48#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "enc"]) body840_47

def body840_49 : Prog (BitVec 64) :=
.decCall ("enc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 128#64]) body840_48

def body840_50 : Prog (BitVec 64) :=
.seq body840_46 body840_49

def body840_51 : Prog (BitVec 64) :=
.dec ("sr") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.global "empty_trie_root") body840_50

def body840_52 : Prog (BitVec 64) :=
.decCall ("nr") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.var Flapjack.VarKind.local "new_roots",
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s2")]) body840_51

def body840_53 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "a") (Flapjack.Exp.const 1#64)) body840_52 body840_1

def body840_54 : Prog (BitVec 64) :=
.seq body840_44 body840_53

def body840_55 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("ws_get_account_optional") ([Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s2")]) body840_54

def body840_56 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "inaw") (Flapjack.Exp.const 0#64)) body840_55 body840_1

def body840_57 : Prog (BitVec 64) :=
.decCall ("inaw") (Flapjack.Shape.one) ("htab_has") ([Flapjack.Exp.var Flapjack.VarKind.local "aw", Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s2")]) body840_56

def body840_58 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "s2"))
  (Flapjack.Exp.const 0#64)) body840_57 body840_1

def body840_59 : Prog (BitVec 64) :=
.seq body840_58 body840_39

def body840_60 : Prog (BitVec 64) :=
.decCall ("s2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_item") ([Flapjack.Exp.var Flapjack.VarKind.local "sw", Flapjack.Exp.var Flapjack.VarKind.local "i"]) body840_59

def body840_61 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "cap")) body840_60

def body840_62 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "state_mpt", Flapjack.Exp.var Flapjack.VarKind.local "addr3",
    Flapjack.Exp.const 20#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]

def body840_63 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "sr2"
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "nr2"))

def body840_64 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "sr2"), none)) "cache_get_root"
  [Flapjack.Exp.var Flapjack.VarKind.local "cache", Flapjack.Exp.var Flapjack.VarKind.local "addr3"]

def body840_65 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "nr2"))
  (Flapjack.Exp.const 0#64)) body840_63 body840_64

def body840_66 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "state_mpt", Flapjack.Exp.var Flapjack.VarKind.local "addr3",
    Flapjack.Exp.const 20#64, Flapjack.Exp.var Flapjack.VarKind.local "enc2",
    Flapjack.Exp.var Flapjack.VarKind.local "n2"]

def body840_67 : Prog (BitVec 64) :=
.decCall ("n2") (Flapjack.Shape.one) ("encode_account") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "acct", Flapjack.Exp.const 0#64]),
  Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "acct", Flapjack.Exp.const 8#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "sr2",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "acct", Flapjack.Exp.const 48#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "enc2"]) body840_66

def body840_68 : Prog (BitVec 64) :=
.decCall ("enc2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 128#64]) body840_67

def body840_69 : Prog (BitVec 64) :=
.seq body840_65 body840_68

def body840_70 : Prog (BitVec 64) :=
.dec ("sr2") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body840_69

def body840_71 : Prog (BitVec 64) :=
.decCall ("nr2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.var Flapjack.VarKind.local "new_roots", Flapjack.Exp.var Flapjack.VarKind.local "addr3"]) body840_70

def body840_72 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "acct") (Flapjack.Exp.const 1#64)) body840_62 body840_71

def body840_73 : Prog (BitVec 64) :=
.dec ("acct") (Flapjack.Shape.one) (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "s3")) body840_72

def body840_74 : Prog (BitVec 64) :=
.dec ("addr3") (Flapjack.Shape.one) (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s3")) body840_73

def body840_75 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "s3"))
  (Flapjack.Exp.const 0#64)) body840_74 body840_1

def body840_76 : Prog (BitVec 64) :=
.seq body840_75 body840_39

def body840_77 : Prog (BitVec 64) :=
.decCall ("s3") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_item") ([Flapjack.Exp.var Flapjack.VarKind.local "aw", Flapjack.Exp.var Flapjack.VarKind.local "i"]) body840_76

def body840_78 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "acap")) body840_77

def body840_79 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_root"
  [Flapjack.Exp.var Flapjack.VarKind.local "state_mpt", Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body840_80 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body840_81 : Prog (BitVec 64) :=
.seq body840_79 body840_80

def body840_82 : Prog (BitVec 64) :=
.seq body840_78 body840_81

def body840_83 : Prog (BitVec 64) :=
.seq body840_43 body840_82

def body840_84 : Prog (BitVec 64) :=
.dec ("acap") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "aw", Flapjack.Exp.const 24#64])) body840_83

def body840_85 : Prog (BitVec 64) :=
.seq body840_61 body840_84

def body840_86 : Prog (BitVec 64) :=
.seq body840_43 body840_85

def body840_87 : Prog (BitVec 64) :=
.decCall ("state_mpt") (Flapjack.Shape.one) ("mpt_from_witness") ([Flapjack.Exp.var Flapjack.VarKind.local "nodedb",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ws", Flapjack.Exp.const 8#64]),
  Flapjack.Exp.const 1#64]) body840_86

def body840_88 : Prog (BitVec 64) :=
.seq body840_42 body840_87

def body840_89 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body840_88

def body840_90 : Prog (BitVec 64) :=
.dec ("cap") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "sw", Flapjack.Exp.const 24#64])) body840_89

def body840_91 : Prog (BitVec 64) :=
.dec ("nodedb") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ws", Flapjack.Exp.const 0#64])) body840_90

def body840_92 : Prog (BitVec 64) :=
.dec ("aw") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bs", Flapjack.Exp.const 16#64])) body840_91

def body840_93 : Prog (BitVec 64) :=
.dec ("sw") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bs", Flapjack.Exp.const 32#64])) body840_92

def body840_94 : Prog (BitVec 64) :=
.decCall ("new_roots") (Flapjack.Shape.one) ("htab_new") ([Flapjack.Exp.const 20#64, Flapjack.Exp.const 64#64]) body840_93

def body840_95 : Prog (BitVec 64) :=
.decCall ("cache") (Flapjack.Shape.one) ("htab_copy") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bs", Flapjack.Exp.const 72#64])]) body840_94

def body840_96 : Prog (BitVec 64) :=
.seq body840_43 body840_61

def body840_97 : Prog (BitVec 64) :=
.seq body840_43 body840_78

def body840_98 : Prog (BitVec 64) :=
.seq body840_97 body840_79

def body840_99 : Prog (BitVec 64) :=
.seq body840_98 body840_80

def body840_100 : Prog (BitVec 64) :=
.dec ("acap") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "aw", Flapjack.Exp.const 24#64])) body840_99

def body840_101 : Prog (BitVec 64) :=
.seq body840_96 body840_100

def body840_102 : Prog (BitVec 64) :=
.decCall ("state_mpt") (Flapjack.Shape.one) ("mpt_from_witness") ([Flapjack.Exp.var Flapjack.VarKind.local "nodedb",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ws", Flapjack.Exp.const 8#64]),
  Flapjack.Exp.const 1#64]) body840_101

def body840_103 : Prog (BitVec 64) :=
.seq body840_42 body840_102

def body840_104 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body840_103

def body840_105 : Prog (BitVec 64) :=
.dec ("cap") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "sw", Flapjack.Exp.const 24#64])) body840_104

def body840_106 : Prog (BitVec 64) :=
.dec ("nodedb") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ws", Flapjack.Exp.const 0#64])) body840_105

def body840_107 : Prog (BitVec 64) :=
.dec ("aw") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bs", Flapjack.Exp.const 16#64])) body840_106

def body840_108 : Prog (BitVec 64) :=
.dec ("sw") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bs", Flapjack.Exp.const 32#64])) body840_107

def body840_109 : Prog (BitVec 64) :=
.decCall ("new_roots") (Flapjack.Shape.one) ("htab_new") ([Flapjack.Exp.const 20#64, Flapjack.Exp.const 64#64]) body840_108

def body840_110 : Prog (BitVec 64) :=
.decCall ("cache") (Flapjack.Shape.one) ("htab_copy") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bs", Flapjack.Exp.const 72#64])]) body840_109

def originalData840 : Decl (BitVec 64) :=
.function { name := "compute_state_root", inline := false, exported := false, params := [("out", Flapjack.Shape.one)], body := body840_95, returnShape := (Flapjack.Shape.one) }
def simplifiedData840 : Decl (BitVec 64) :=
.function { name := "compute_state_root", inline := false, exported := false, params := [("out", Flapjack.Shape.one)], body := body840_110, returnShape := (Flapjack.Shape.one) }
def original840 := Pancake.PanLang.declToHOL originalData840
def simplified840 := Pancake.PanLang.declToHOL simplifiedData840
end InitECandidate.Proofs.FrontendStages.Declarations
