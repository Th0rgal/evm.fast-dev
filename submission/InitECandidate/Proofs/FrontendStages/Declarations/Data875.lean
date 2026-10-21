import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify859
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body875_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "bo"), none)) "alloc" [Flapjack.Exp.const 88#64]

def body875_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 88#64]

def body875_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "txs")

def body875_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "rcs")

def body875_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "logs")

def body875_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "reqs")

def body875_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 72#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "rls")

def body875_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 80#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "ntx")

def body875_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bal_init" []

def body875_9 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body875_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "process_unchecked_system_transaction"
  [Flapjack.Exp.var Flapjack.VarKind.global "beacon_roots_address",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 24#64]),
    Flapjack.Exp.const 32#64]

def body875_11 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "lasth"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "block_hashes",
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.sub
            [Flapjack.Exp.var Flapjack.VarKind.global "block_hashes_n", Flapjack.Exp.const 1#64],
          Flapjack.Exp.const 32#64]])

def body875_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.var Flapjack.VarKind.global "block_hashes_n")) body875_11 body875_9

def body875_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "process_unchecked_system_transaction"
  [Flapjack.Exp.var Flapjack.VarKind.global "history_storage_address", Flapjack.Exp.var Flapjack.VarKind.local "lasth",
    Flapjack.Exp.const 32#64]

def body875_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "state_fresh_tx" []

def body875_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "track_ancestor_access" [Flapjack.Exp.const 1#64]

def body875_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "process_transaction"
  [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.var Flapjack.VarKind.local "i"]

def body875_17 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body875_18 : Prog (BitVec 64) :=
.seq body875_9 body875_17

def body875_19 : Prog (BitVec 64) :=
.seq body875_16 body875_18

def body875_20 : Prog (BitVec 64) :=
.seq body875_9 body875_19

def body875_21 : Prog (BitVec 64) :=
.decCall ("tx") (Flapjack.Shape.one) ("decode_transaction") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "ptxs",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64]]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "ptxs",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64],
        Flapjack.Exp.const 8#64])]) body875_20

def body875_22 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "ntx")) body875_21

def body875_23 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.global "bal_index"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ntx", Flapjack.Exp.const 1#64])

def body875_24 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "process_withdrawals" [Flapjack.Exp.var Flapjack.VarKind.local "pl"]

def body875_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "process_general_purpose_requests" []

def body875_26 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "validate_block_access_list_gas_limit"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 8#64])]

def body875_27 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "compute_state_root" [Flapjack.Exp.var Flapjack.VarKind.local "root"]

def body875_28 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "build_mpt_indexed"
  [Flapjack.Exp.var Flapjack.VarKind.local "txs", Flapjack.Exp.var Flapjack.VarKind.local "ntx",
    Flapjack.Exp.var Flapjack.VarKind.local "txroot"]

def body875_29 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "build_mpt_indexed"
  [Flapjack.Exp.var Flapjack.VarKind.local "rcs", Flapjack.Exp.var Flapjack.VarKind.local "ntx",
    Flapjack.Exp.var Flapjack.VarKind.local "rroot"]

def body875_30 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "logs_bloom"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 40#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "bloom"]

def body875_31 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "build_mpt_indexed"
  [Flapjack.Exp.var Flapjack.VarKind.global "wd_rlp_slices",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 56#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "wroot"]

def body875_32 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "compute_requests_hash"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 56#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 64#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "rqh"]

def body875_33 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "bal"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "bal"),
    Flapjack.Exp.var Flapjack.VarKind.local "balh"]

def body875_34 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 110#64)

def body875_35 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "bgu")
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 112#64]))) body875_34 body875_9

def body875_36 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 111#64)

def body875_37 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) body875_36 body875_9

def body875_38 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "eq"), none)) "memeq"
  [Flapjack.Exp.var Flapjack.VarKind.local "root",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 32#64]),
    Flapjack.Exp.const 32#64]

def body875_39 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 112#64)

def body875_40 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) body875_39 body875_9

def body875_41 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "eq"), none)) "memeq"
  [Flapjack.Exp.var Flapjack.VarKind.local "rroot",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 48#64]),
    Flapjack.Exp.const 32#64]

def body875_42 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 113#64)

def body875_43 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) body875_42 body875_9

def body875_44 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "eq"), none)) "memeq"
  [Flapjack.Exp.var Flapjack.VarKind.local "bloom",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 56#64]),
    Flapjack.Exp.const 256#64]

def body875_45 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 114#64)

def body875_46 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) body875_45 body875_9

def body875_47 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "eq"), none)) "memeq"
  [Flapjack.Exp.var Flapjack.VarKind.local "wroot",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 192#64]),
    Flapjack.Exp.const 32#64]

def body875_48 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 115#64)

def body875_49 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) body875_48 body875_9

def body875_50 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 116#64)

def body875_51 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 48#64]))
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 200#64]))) body875_50 body875_9

def body875_52 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "eq"), none)) "memeq"
  [Flapjack.Exp.var Flapjack.VarKind.local "rqh",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 224#64]),
    Flapjack.Exp.const 32#64]

def body875_53 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 117#64)

def body875_54 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) body875_53 body875_9

def body875_55 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "eq"), none)) "memeq"
  [Flapjack.Exp.var Flapjack.VarKind.local "balh",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 232#64]),
    Flapjack.Exp.const 32#64]

def body875_56 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 118#64)

def body875_57 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) body875_56 body875_9

def body875_58 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body875_59 : Prog (BitVec 64) :=
.seq body875_57 body875_58

def body875_60 : Prog (BitVec 64) :=
.seq body875_55 body875_59

def body875_61 : Prog (BitVec 64) :=
.seq body875_54 body875_60

def body875_62 : Prog (BitVec 64) :=
.seq body875_52 body875_61

def body875_63 : Prog (BitVec 64) :=
.seq body875_51 body875_62

def body875_64 : Prog (BitVec 64) :=
.seq body875_49 body875_63

def body875_65 : Prog (BitVec 64) :=
.seq body875_47 body875_64

def body875_66 : Prog (BitVec 64) :=
.seq body875_46 body875_65

def body875_67 : Prog (BitVec 64) :=
.seq body875_44 body875_66

def body875_68 : Prog (BitVec 64) :=
.seq body875_43 body875_67

def body875_69 : Prog (BitVec 64) :=
.seq body875_41 body875_68

def body875_70 : Prog (BitVec 64) :=
.seq body875_40 body875_69

def body875_71 : Prog (BitVec 64) :=
.seq body875_38 body875_70

def body875_72 : Prog (BitVec 64) :=
.seq body875_37 body875_71

def body875_73 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.var Flapjack.VarKind.local "txroot",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 40#64]),
  Flapjack.Exp.const 32#64]) body875_72

def body875_74 : Prog (BitVec 64) :=
.seq body875_35 body875_73

def body875_75 : Prog (BitVec 64) :=
.decCall ("bgu") (Flapjack.Shape.one) ("max") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 0#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 8#64])]) body875_74

def body875_76 : Prog (BitVec 64) :=
.seq body875_33 body875_75

def body875_77 : Prog (BitVec 64) :=
.decCall ("balh") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body875_76

def body875_78 : Prog (BitVec 64) :=
.seq body875_32 body875_77

def body875_79 : Prog (BitVec 64) :=
.decCall ("rqh") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body875_78

def body875_80 : Prog (BitVec 64) :=
.seq body875_31 body875_79

def body875_81 : Prog (BitVec 64) :=
.decCall ("wroot") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body875_80

def body875_82 : Prog (BitVec 64) :=
.seq body875_30 body875_81

def body875_83 : Prog (BitVec 64) :=
.decCall ("bloom") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 256#64]) body875_82

def body875_84 : Prog (BitVec 64) :=
.seq body875_29 body875_83

def body875_85 : Prog (BitVec 64) :=
.decCall ("rroot") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body875_84

def body875_86 : Prog (BitVec 64) :=
.seq body875_28 body875_85

def body875_87 : Prog (BitVec 64) :=
.decCall ("txroot") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body875_86

def body875_88 : Prog (BitVec 64) :=
.seq body875_9 body875_87

def body875_89 : Prog (BitVec 64) :=
.seq body875_27 body875_88

def body875_90 : Prog (BitVec 64) :=
.decCall ("root") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body875_89

def body875_91 : Prog (BitVec 64) :=
.seq body875_9 body875_90

def body875_92 : Prog (BitVec 64) :=
.seq body875_26 body875_91

def body875_93 : Prog (BitVec 64) :=
.decCall ("bal") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("build_block_access_list_rlp") ([]) body875_92

def body875_94 : Prog (BitVec 64) :=
.seq body875_9 body875_93

def body875_95 : Prog (BitVec 64) :=
.seq body875_25 body875_94

def body875_96 : Prog (BitVec 64) :=
.seq body875_9 body875_95

def body875_97 : Prog (BitVec 64) :=
.seq body875_24 body875_96

def body875_98 : Prog (BitVec 64) :=
.seq body875_9 body875_97

def body875_99 : Prog (BitVec 64) :=
.seq body875_23 body875_98

def body875_100 : Prog (BitVec 64) :=
.seq body875_22 body875_99

def body875_101 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body875_100

def body875_102 : Prog (BitVec 64) :=
.dec ("ptxs") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 32#64])) body875_101

def body875_103 : Prog (BitVec 64) :=
.seq body875_15 body875_102

def body875_104 : Prog (BitVec 64) :=
.seq body875_14 body875_103

def body875_105 : Prog (BitVec 64) :=
.seq body875_9 body875_104

def body875_106 : Prog (BitVec 64) :=
.seq body875_13 body875_105

def body875_107 : Prog (BitVec 64) :=
.seq body875_12 body875_106

def body875_108 : Prog (BitVec 64) :=
.dec ("lasth") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.global "zero32") body875_107

def body875_109 : Prog (BitVec 64) :=
.seq body875_10 body875_108

def body875_110 : Prog (BitVec 64) :=
.seq body875_9 body875_109

def body875_111 : Prog (BitVec 64) :=
.seq body875_8 body875_110

def body875_112 : Prog (BitVec 64) :=
.seq body875_7 body875_111

def body875_113 : Prog (BitVec 64) :=
.seq body875_6 body875_112

def body875_114 : Prog (BitVec 64) :=
.decCall ("rls") (Flapjack.Shape.one) ("lst_new") ([Flapjack.Exp.const 8#64, Flapjack.Exp.const 16#64]) body875_113

def body875_115 : Prog (BitVec 64) :=
.seq body875_5 body875_114

def body875_116 : Prog (BitVec 64) :=
.decCall ("reqs") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 8#64, Flapjack.Exp.const 16#64]]) body875_115

def body875_117 : Prog (BitVec 64) :=
.seq body875_4 body875_116

def body875_118 : Prog (BitVec 64) :=
.decCall ("logs") (Flapjack.Shape.one) ("lst_new") ([Flapjack.Exp.const 8#64, Flapjack.Exp.const 16#64]) body875_117

def body875_119 : Prog (BitVec 64) :=
.seq body875_3 body875_118

def body875_120 : Prog (BitVec 64) :=
.decCall ("rcs") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "ntx", Flapjack.Exp.const 16#64],
      Flapjack.Exp.const 16#64]]) body875_119

def body875_121 : Prog (BitVec 64) :=
.seq body875_2 body875_120

def body875_122 : Prog (BitVec 64) :=
.decCall ("txs") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "ntx", Flapjack.Exp.const 16#64],
      Flapjack.Exp.const 16#64]]) body875_121

def body875_123 : Prog (BitVec 64) :=
.seq body875_1 body875_122

def body875_124 : Prog (BitVec 64) :=
.seq body875_0 body875_123

def body875_125 : Prog (BitVec 64) :=
.dec ("ntx") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 40#64])) body875_124

def body875_126 : Prog (BitVec 64) :=
.dec ("pl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 0#64])) body875_125

def body875_127 : Prog (BitVec 64) :=
.seq body875_0 body875_1

def body875_128 : Prog (BitVec 64) :=
.seq body875_6 body875_7

def body875_129 : Prog (BitVec 64) :=
.seq body875_128 body875_8

def body875_130 : Prog (BitVec 64) :=
.seq body875_129 body875_10

def body875_131 : Prog (BitVec 64) :=
.seq body875_12 body875_13

def body875_132 : Prog (BitVec 64) :=
.seq body875_131 body875_14

def body875_133 : Prog (BitVec 64) :=
.seq body875_132 body875_15

def body875_134 : Prog (BitVec 64) :=
.seq body875_16 body875_17

def body875_135 : Prog (BitVec 64) :=
.decCall ("tx") (Flapjack.Shape.one) ("decode_transaction") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "ptxs",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64]]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "ptxs",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64],
        Flapjack.Exp.const 8#64])]) body875_134

def body875_136 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "ntx")) body875_135

def body875_137 : Prog (BitVec 64) :=
.seq body875_136 body875_23

def body875_138 : Prog (BitVec 64) :=
.seq body875_137 body875_24

def body875_139 : Prog (BitVec 64) :=
.seq body875_138 body875_25

def body875_140 : Prog (BitVec 64) :=
.seq body875_37 body875_38

def body875_141 : Prog (BitVec 64) :=
.seq body875_140 body875_40

def body875_142 : Prog (BitVec 64) :=
.seq body875_141 body875_41

def body875_143 : Prog (BitVec 64) :=
.seq body875_142 body875_43

def body875_144 : Prog (BitVec 64) :=
.seq body875_143 body875_44

def body875_145 : Prog (BitVec 64) :=
.seq body875_144 body875_46

def body875_146 : Prog (BitVec 64) :=
.seq body875_145 body875_47

def body875_147 : Prog (BitVec 64) :=
.seq body875_146 body875_49

def body875_148 : Prog (BitVec 64) :=
.seq body875_147 body875_51

def body875_149 : Prog (BitVec 64) :=
.seq body875_148 body875_52

def body875_150 : Prog (BitVec 64) :=
.seq body875_149 body875_54

def body875_151 : Prog (BitVec 64) :=
.seq body875_150 body875_55

def body875_152 : Prog (BitVec 64) :=
.seq body875_151 body875_57

def body875_153 : Prog (BitVec 64) :=
.seq body875_152 body875_58

def body875_154 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.var Flapjack.VarKind.local "txroot",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 40#64]),
  Flapjack.Exp.const 32#64]) body875_153

def body875_155 : Prog (BitVec 64) :=
.seq body875_35 body875_154

def body875_156 : Prog (BitVec 64) :=
.decCall ("bgu") (Flapjack.Shape.one) ("max") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 0#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bo", Flapjack.Exp.const 8#64])]) body875_155

def body875_157 : Prog (BitVec 64) :=
.seq body875_33 body875_156

def body875_158 : Prog (BitVec 64) :=
.decCall ("balh") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body875_157

def body875_159 : Prog (BitVec 64) :=
.seq body875_32 body875_158

def body875_160 : Prog (BitVec 64) :=
.decCall ("rqh") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body875_159

def body875_161 : Prog (BitVec 64) :=
.seq body875_31 body875_160

def body875_162 : Prog (BitVec 64) :=
.decCall ("wroot") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body875_161

def body875_163 : Prog (BitVec 64) :=
.seq body875_30 body875_162

def body875_164 : Prog (BitVec 64) :=
.decCall ("bloom") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 256#64]) body875_163

def body875_165 : Prog (BitVec 64) :=
.seq body875_29 body875_164

def body875_166 : Prog (BitVec 64) :=
.decCall ("rroot") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body875_165

def body875_167 : Prog (BitVec 64) :=
.seq body875_28 body875_166

def body875_168 : Prog (BitVec 64) :=
.decCall ("txroot") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body875_167

def body875_169 : Prog (BitVec 64) :=
.seq body875_27 body875_168

def body875_170 : Prog (BitVec 64) :=
.decCall ("root") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body875_169

def body875_171 : Prog (BitVec 64) :=
.seq body875_26 body875_170

def body875_172 : Prog (BitVec 64) :=
.decCall ("bal") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("build_block_access_list_rlp") ([]) body875_171

def body875_173 : Prog (BitVec 64) :=
.seq body875_139 body875_172

def body875_174 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body875_173

def body875_175 : Prog (BitVec 64) :=
.dec ("ptxs") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 32#64])) body875_174

def body875_176 : Prog (BitVec 64) :=
.seq body875_133 body875_175

def body875_177 : Prog (BitVec 64) :=
.dec ("lasth") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.global "zero32") body875_176

def body875_178 : Prog (BitVec 64) :=
.seq body875_130 body875_177

def body875_179 : Prog (BitVec 64) :=
.decCall ("rls") (Flapjack.Shape.one) ("lst_new") ([Flapjack.Exp.const 8#64, Flapjack.Exp.const 16#64]) body875_178

def body875_180 : Prog (BitVec 64) :=
.seq body875_5 body875_179

def body875_181 : Prog (BitVec 64) :=
.decCall ("reqs") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 8#64, Flapjack.Exp.const 16#64]]) body875_180

def body875_182 : Prog (BitVec 64) :=
.seq body875_4 body875_181

def body875_183 : Prog (BitVec 64) :=
.decCall ("logs") (Flapjack.Shape.one) ("lst_new") ([Flapjack.Exp.const 8#64, Flapjack.Exp.const 16#64]) body875_182

def body875_184 : Prog (BitVec 64) :=
.seq body875_3 body875_183

def body875_185 : Prog (BitVec 64) :=
.decCall ("rcs") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "ntx", Flapjack.Exp.const 16#64],
      Flapjack.Exp.const 16#64]]) body875_184

def body875_186 : Prog (BitVec 64) :=
.seq body875_2 body875_185

def body875_187 : Prog (BitVec 64) :=
.decCall ("txs") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "ntx", Flapjack.Exp.const 16#64],
      Flapjack.Exp.const 16#64]]) body875_186

def body875_188 : Prog (BitVec 64) :=
.seq body875_127 body875_187

def body875_189 : Prog (BitVec 64) :=
.dec ("ntx") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 40#64])) body875_188

def body875_190 : Prog (BitVec 64) :=
.dec ("pl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 0#64])) body875_189

def originalData875 : Decl (BitVec 64) :=
.function { name := "execute_block", inline := false, exported := false, params := [("si", Flapjack.Shape.one), ("hdr", Flapjack.Shape.one)], body := body875_126, returnShape := (Flapjack.Shape.one) }
def simplifiedData875 : Decl (BitVec 64) :=
.function { name := "execute_block", inline := false, exported := false, params := [("si", Flapjack.Shape.one), ("hdr", Flapjack.Shape.one)], body := body875_190, returnShape := (Flapjack.Shape.one) }
def original875 := Pancake.PanLang.declToHOL originalData875
def simplified875 := Pancake.PanLang.declToHOL simplifiedData875
end InitECandidate.Proofs.FrontendStages.Declarations
