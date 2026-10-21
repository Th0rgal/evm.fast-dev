import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data840
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate824
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody840_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "cache", Flapjack.Exp.var Flapjack.VarKind.local "addr",
    Flapjack.Exp.const 1#64]

def globalBody840_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody840_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "has") (Flapjack.Exp.const 0#64)) globalBody840_0 globalBody840_1

def globalBody840_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "enc",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "vbuf", Flapjack.Exp.const 40#64],
    Flapjack.Exp.var Flapjack.VarKind.local "w"]

def globalBody840_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "mpt", Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "e"),
    Flapjack.Exp.const 32#64, Flapjack.Exp.var Flapjack.VarKind.local "enc",
    Flapjack.Exp.var Flapjack.VarKind.local "w"]

def globalBody840_5 : Prog (BitVec 64) :=
.seq globalBody840_3 globalBody840_4

def globalBody840_6 : Prog (BitVec 64) :=
.decCall ("enc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 40#64]) globalBody840_5

def globalBody840_7 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("rlp_encode_bytes") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "vbuf", Flapjack.Exp.const 8#64, Flapjack.Exp.const 32#64],
  Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "vbuf", Flapjack.Exp.const 8#64],
  Flapjack.Exp.var Flapjack.VarKind.local "n"]) globalBody840_6

def globalBody840_8 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("u256_to_be_min") ([Flapjack.Exp.var Flapjack.VarKind.local "v",
  Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "vbuf", Flapjack.Exp.const 8#64]]) globalBody840_7

def globalBody840_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "pass") (Flapjack.Exp.const 0#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64))]) globalBody840_8 globalBody840_1

def globalBody840_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "mpt", Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "e"),
    Flapjack.Exp.const 32#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]

def globalBody840_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "pass") (Flapjack.Exp.const 1#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64))]) globalBody840_10 globalBody840_1

def globalBody840_12 : Prog (BitVec 64) :=
.seq globalBody840_9 globalBody840_11

def globalBody840_13 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "v"]) globalBody840_12

def globalBody840_14 : Prog (BitVec 64) :=
.dec ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "e"))) globalBody840_13

def globalBody840_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "e"))
  (Flapjack.Exp.const 0#64)) globalBody840_14 globalBody840_1

def globalBody840_16 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "j"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 1#64])

def globalBody840_17 : Prog (BitVec 64) :=
.seq globalBody840_15 globalBody840_16

def globalBody840_18 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_item") ([Flapjack.Exp.var Flapjack.VarKind.local "inner", Flapjack.Exp.var Flapjack.VarKind.local "j"]) globalBody840_17

def globalBody840_19 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "j")
  (Flapjack.Exp.var Flapjack.VarKind.local "icount")) globalBody840_18

def globalBody840_20 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pass"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pass", Flapjack.Exp.const 1#64])

def globalBody840_21 : Prog (BitVec 64) :=
.seq globalBody840_19 globalBody840_20

def globalBody840_22 : Prog (BitVec 64) :=
.dec ("icount") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "inner", Flapjack.Exp.const 24#64])) globalBody840_21

def globalBody840_23 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody840_22

def globalBody840_24 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "pass") (Flapjack.Exp.const 2#64)) globalBody840_23

def globalBody840_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_root"
  [Flapjack.Exp.var Flapjack.VarKind.local "mpt", Flapjack.Exp.var Flapjack.VarKind.local "root"]

def globalBody840_26 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "new_roots", Flapjack.Exp.var Flapjack.VarKind.local "addr",
    Flapjack.Exp.var Flapjack.VarKind.local "root"]

def globalBody840_27 : Prog (BitVec 64) :=
.seq globalBody840_25 globalBody840_26

def globalBody840_28 : Prog (BitVec 64) :=
.decCall ("root") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) globalBody840_27

def globalBody840_29 : Prog (BitVec 64) :=
.seq globalBody840_24 globalBody840_28

def globalBody840_30 : Prog (BitVec 64) :=
.dec ("pass") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody840_29

def globalBody840_31 : Prog (BitVec 64) :=
.decCall ("vbuf") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) globalBody840_30

def globalBody840_32 : Prog (BitVec 64) :=
.decCall ("mpt") (Flapjack.Shape.one) ("mpt_from_witness") ([Flapjack.Exp.var Flapjack.VarKind.local "nodedb", Flapjack.Exp.var Flapjack.VarKind.local "old_root",
  Flapjack.Exp.const 1#64]) globalBody840_31

def globalBody840_33 : Prog (BitVec 64) :=
.decCall ("old_root") (Flapjack.Shape.one) ("ws_storage_root_of") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) globalBody840_32

def globalBody840_34 : Prog (BitVec 64) :=
.seq globalBody840_2 globalBody840_33

def globalBody840_35 : Prog (BitVec 64) :=
.decCall ("has") (Flapjack.Shape.one) ("htab_has") ([Flapjack.Exp.var Flapjack.VarKind.local "cache", Flapjack.Exp.var Flapjack.VarKind.local "addr"]) globalBody840_34

def globalBody840_36 : Prog (BitVec 64) :=
.dec ("inner") (Flapjack.Shape.one) (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "s")) globalBody840_35

def globalBody840_37 : Prog (BitVec 64) :=
.dec ("addr") (Flapjack.Shape.one) (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s")) globalBody840_36

def globalBody840_38 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "s"))
  (Flapjack.Exp.const 0#64)) globalBody840_37 globalBody840_1

def globalBody840_39 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody840_40 : Prog (BitVec 64) :=
.seq globalBody840_38 globalBody840_39

def globalBody840_41 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_item") ([Flapjack.Exp.var Flapjack.VarKind.local "sw", Flapjack.Exp.var Flapjack.VarKind.local "i"]) globalBody840_40

def globalBody840_42 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "cap")) globalBody840_41

def globalBody840_43 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i" (Flapjack.Exp.const 0#64)

def globalBody840_44 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "cache",
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s2"), Flapjack.Exp.const 1#64]

def globalBody840_45 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "sr" (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "nr"))

def globalBody840_46 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "nr"))
  (Flapjack.Exp.const 0#64)) globalBody840_45 globalBody840_1

def globalBody840_47 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "state_mpt",
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s2"), Flapjack.Exp.const 20#64,
    Flapjack.Exp.var Flapjack.VarKind.local "enc", Flapjack.Exp.var Flapjack.VarKind.local "n"]

def globalBody840_48 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("encode_account") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 0#64]),
  Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 8#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "sr",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 48#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "enc"]) globalBody840_47

def globalBody840_49 : Prog (BitVec 64) :=
.decCall ("enc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 128#64]) globalBody840_48

def globalBody840_50 : Prog (BitVec 64) :=
.seq globalBody840_46 globalBody840_49

def globalBody840_51 : Prog (BitVec 64) :=
.dec ("sr") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 128#64])) globalBody840_50

def globalBody840_52 : Prog (BitVec 64) :=
.decCall ("nr") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.var Flapjack.VarKind.local "new_roots",
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s2")]) globalBody840_51

def globalBody840_53 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "a") (Flapjack.Exp.const 1#64)) globalBody840_52 globalBody840_1

def globalBody840_54 : Prog (BitVec 64) :=
.seq globalBody840_44 globalBody840_53

def globalBody840_55 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("ws_get_account_optional") ([Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s2")]) globalBody840_54

def globalBody840_56 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "inaw") (Flapjack.Exp.const 0#64)) globalBody840_55 globalBody840_1

def globalBody840_57 : Prog (BitVec 64) :=
.decCall ("inaw") (Flapjack.Shape.one) ("htab_has") ([Flapjack.Exp.var Flapjack.VarKind.local "aw", Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s2")]) globalBody840_56

def globalBody840_58 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "s2"))
  (Flapjack.Exp.const 0#64)) globalBody840_57 globalBody840_1

def globalBody840_59 : Prog (BitVec 64) :=
.seq globalBody840_58 globalBody840_39

def globalBody840_60 : Prog (BitVec 64) :=
.decCall ("s2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_item") ([Flapjack.Exp.var Flapjack.VarKind.local "sw", Flapjack.Exp.var Flapjack.VarKind.local "i"]) globalBody840_59

def globalBody840_61 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "cap")) globalBody840_60

def globalBody840_62 : Prog (BitVec 64) :=
.seq globalBody840_43 globalBody840_61

def globalBody840_63 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "state_mpt", Flapjack.Exp.var Flapjack.VarKind.local "addr3",
    Flapjack.Exp.const 20#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]

def globalBody840_64 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "sr2"
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "nr2"))

def globalBody840_65 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "sr2"), none)) "cache_get_root"
  [Flapjack.Exp.var Flapjack.VarKind.local "cache", Flapjack.Exp.var Flapjack.VarKind.local "addr3"]

def globalBody840_66 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "nr2"))
  (Flapjack.Exp.const 0#64)) globalBody840_64 globalBody840_65

def globalBody840_67 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "state_mpt", Flapjack.Exp.var Flapjack.VarKind.local "addr3",
    Flapjack.Exp.const 20#64, Flapjack.Exp.var Flapjack.VarKind.local "enc2",
    Flapjack.Exp.var Flapjack.VarKind.local "n2"]

def globalBody840_68 : Prog (BitVec 64) :=
.decCall ("n2") (Flapjack.Shape.one) ("encode_account") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "acct", Flapjack.Exp.const 0#64]),
  Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "acct", Flapjack.Exp.const 8#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "sr2",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "acct", Flapjack.Exp.const 48#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "enc2"]) globalBody840_67

def globalBody840_69 : Prog (BitVec 64) :=
.decCall ("enc2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 128#64]) globalBody840_68

def globalBody840_70 : Prog (BitVec 64) :=
.seq globalBody840_66 globalBody840_69

def globalBody840_71 : Prog (BitVec 64) :=
.dec ("sr2") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody840_70

def globalBody840_72 : Prog (BitVec 64) :=
.decCall ("nr2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.var Flapjack.VarKind.local "new_roots", Flapjack.Exp.var Flapjack.VarKind.local "addr3"]) globalBody840_71

def globalBody840_73 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "acct") (Flapjack.Exp.const 1#64)) globalBody840_63 globalBody840_72

def globalBody840_74 : Prog (BitVec 64) :=
.dec ("acct") (Flapjack.Shape.one) (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "s3")) globalBody840_73

def globalBody840_75 : Prog (BitVec 64) :=
.dec ("addr3") (Flapjack.Shape.one) (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "s3")) globalBody840_74

def globalBody840_76 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "s3"))
  (Flapjack.Exp.const 0#64)) globalBody840_75 globalBody840_1

def globalBody840_77 : Prog (BitVec 64) :=
.seq globalBody840_76 globalBody840_39

def globalBody840_78 : Prog (BitVec 64) :=
.decCall ("s3") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_item") ([Flapjack.Exp.var Flapjack.VarKind.local "aw", Flapjack.Exp.var Flapjack.VarKind.local "i"]) globalBody840_77

def globalBody840_79 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "acap")) globalBody840_78

def globalBody840_80 : Prog (BitVec 64) :=
.seq globalBody840_43 globalBody840_79

def globalBody840_81 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_root"
  [Flapjack.Exp.var Flapjack.VarKind.local "state_mpt", Flapjack.Exp.var Flapjack.VarKind.local "out"]

def globalBody840_82 : Prog (BitVec 64) :=
.seq globalBody840_80 globalBody840_81

def globalBody840_83 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody840_84 : Prog (BitVec 64) :=
.seq globalBody840_82 globalBody840_83

def globalBody840_85 : Prog (BitVec 64) :=
.dec ("acap") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "aw", Flapjack.Exp.const 24#64])) globalBody840_84

def globalBody840_86 : Prog (BitVec 64) :=
.seq globalBody840_62 globalBody840_85

def globalBody840_87 : Prog (BitVec 64) :=
.decCall ("state_mpt") (Flapjack.Shape.one) ("mpt_from_witness") ([Flapjack.Exp.var Flapjack.VarKind.local "nodedb",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 168#64]),
        Flapjack.Exp.const 8#64]),
  Flapjack.Exp.const 1#64]) globalBody840_86

def globalBody840_88 : Prog (BitVec 64) :=
.seq globalBody840_42 globalBody840_87

def globalBody840_89 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody840_88

def globalBody840_90 : Prog (BitVec 64) :=
.dec ("cap") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "sw", Flapjack.Exp.const 24#64])) globalBody840_89

def globalBody840_91 : Prog (BitVec 64) :=
.dec ("nodedb") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 168#64]),
      Flapjack.Exp.const 0#64])) globalBody840_90

def globalBody840_92 : Prog (BitVec 64) :=
.dec ("aw") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 176#64]),
      Flapjack.Exp.const 16#64])) globalBody840_91

def globalBody840_93 : Prog (BitVec 64) :=
.dec ("sw") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 176#64]),
      Flapjack.Exp.const 32#64])) globalBody840_92

def globalBody840_94 : Prog (BitVec 64) :=
.decCall ("new_roots") (Flapjack.Shape.one) ("htab_new") ([Flapjack.Exp.const 20#64, Flapjack.Exp.const 64#64]) globalBody840_93

def globalBody840_95 : Prog (BitVec 64) :=
.decCall ("cache") (Flapjack.Shape.one) ("htab_copy") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 176#64]),
        Flapjack.Exp.const 72#64])]) globalBody840_94

def globalData840 : Decl (BitVec 64) :=
.function { name := "compute_state_root", inline := false, exported := false, params := [("out", Flapjack.Shape.one)], body := globalBody840_95, returnShape := (Flapjack.Shape.one) }
def globalOutput840 := Pancake.PanLang.declToHOL globalData840
end InitECandidate.Proofs.FrontendStages.Declarations
