import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify860
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body876_0 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body876_1 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 3#64)

def body876_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "nh") (Flapjack.Exp.const 0#64)) body876_1 body876_0

def body876_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.global "block_hashes"
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "vh"))

def body876_4 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.global "block_hashes_n" (Flapjack.Exp.var Flapjack.VarKind.local "nh")

def body876_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "state_init"
  [Flapjack.Exp.var Flapjack.VarKind.local "nodedb",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "parent", Flapjack.Exp.const 32#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "codedb"]

def body876_6 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 4#64)

def body876_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "txs",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64],
        Flapjack.Exp.const 8#64]))
  (Flapjack.Exp.const 0#64)) body876_6 body876_0

def body876_8 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body876_9 : Prog (BitVec 64) :=
.seq body876_7 body876_8

def body876_10 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "ntx")) body876_9

def body876_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "header_hash"
  [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.var Flapjack.VarKind.local "bh"]

def body876_12 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 5#64)

def body876_13 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) body876_12 body876_0

def body876_14 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 6#64)

def body876_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "vvh") (Flapjack.Exp.const 0#64)) body876_14 body876_0

def body876_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "validate_header"
  [Flapjack.Exp.var Flapjack.VarKind.local "parent", Flapjack.Exp.var Flapjack.VarKind.local "hdr"]

def body876_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "be"), none)) "alloc" [Flapjack.Exp.const 120#64]

def body876_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 120#64]

def body876_19 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 88#64]))

def body876_20 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 104#64]))

def body876_21 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.global "block_hashes")

def body876_22 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.global "block_hashes_n")

def body876_23 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 24#64]))

def body876_24 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 96#64]))

def body876_25 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 160#64]))

def body876_26 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 80#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 120#64]))

def body876_27 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 88#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 144#64]))

def body876_28 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 208#64]))

def body876_29 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 104#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 216#64]))

def body876_30 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "be", Flapjack.Exp.const 112#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 240#64]))

def body876_31 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "execute_block"
  [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.var Flapjack.VarKind.local "hdr"]

def body876_32 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body876_33 : Prog (BitVec 64) :=
.seq body876_0 body876_32

def body876_34 : Prog (BitVec 64) :=
.seq body876_31 body876_33

def body876_35 : Prog (BitVec 64) :=
.seq body876_0 body876_34

def body876_36 : Prog (BitVec 64) :=
.seq body876_30 body876_35

def body876_37 : Prog (BitVec 64) :=
.seq body876_29 body876_36

def body876_38 : Prog (BitVec 64) :=
.seq body876_28 body876_37

def body876_39 : Prog (BitVec 64) :=
.seq body876_27 body876_38

def body876_40 : Prog (BitVec 64) :=
.seq body876_26 body876_39

def body876_41 : Prog (BitVec 64) :=
.seq body876_25 body876_40

def body876_42 : Prog (BitVec 64) :=
.seq body876_24 body876_41

def body876_43 : Prog (BitVec 64) :=
.seq body876_23 body876_42

def body876_44 : Prog (BitVec 64) :=
.seq body876_22 body876_43

def body876_45 : Prog (BitVec 64) :=
.seq body876_21 body876_44

def body876_46 : Prog (BitVec 64) :=
.seq body876_20 body876_45

def body876_47 : Prog (BitVec 64) :=
.seq body876_19 body876_46

def body876_48 : Prog (BitVec 64) :=
.seq body876_18 body876_47

def body876_49 : Prog (BitVec 64) :=
.seq body876_17 body876_48

def body876_50 : Prog (BitVec 64) :=
.seq body876_0 body876_49

def body876_51 : Prog (BitVec 64) :=
.seq body876_16 body876_50

def body876_52 : Prog (BitVec 64) :=
.seq body876_0 body876_51

def body876_53 : Prog (BitVec 64) :=
.seq body876_15 body876_52

def body876_54 : Prog (BitVec 64) :=
.seq body876_0 body876_53

def body876_55 : Prog (BitVec 64) :=
.decCall ("vvh") (Flapjack.Shape.one) ("is_valid_versioned_hashes") ([Flapjack.Exp.var Flapjack.VarKind.local "si"]) body876_54

def body876_56 : Prog (BitVec 64) :=
.seq body876_0 body876_55

def body876_57 : Prog (BitVec 64) :=
.seq body876_13 body876_56

def body876_58 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.var Flapjack.VarKind.local "bh",
  Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 0#64]),
      Flapjack.Exp.const 472#64],
  Flapjack.Exp.const 32#64]) body876_57

def body876_59 : Prog (BitVec 64) :=
.seq body876_11 body876_58

def body876_60 : Prog (BitVec 64) :=
.decCall ("bh") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body876_59

def body876_61 : Prog (BitVec 64) :=
.seq body876_0 body876_60

def body876_62 : Prog (BitVec 64) :=
.decCall ("hdr") (Flapjack.Shape.one) ("payload_header") ([Flapjack.Exp.var Flapjack.VarKind.local "si"]) body876_61

def body876_63 : Prog (BitVec 64) :=
.seq body876_0 body876_62

def body876_64 : Prog (BitVec 64) :=
.seq body876_10 body876_63

def body876_65 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body876_64

def body876_66 : Prog (BitVec 64) :=
.dec ("ntx") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 40#64])) body876_65

def body876_67 : Prog (BitVec 64) :=
.dec ("txs") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 32#64])) body876_66

def body876_68 : Prog (BitVec 64) :=
.seq body876_0 body876_67

def body876_69 : Prog (BitVec 64) :=
.seq body876_5 body876_68

def body876_70 : Prog (BitVec 64) :=
.decCall ("codedb") (Flapjack.Shape.one) ("nodedb_build") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 56#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 64#64])]) body876_69

def body876_71 : Prog (BitVec 64) :=
.decCall ("nodedb") (Flapjack.Shape.one) ("nodedb_build") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 40#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 48#64])]) body876_70

def body876_72 : Prog (BitVec 64) :=
.seq body876_0 body876_71

def body876_73 : Prog (BitVec 64) :=
.seq body876_4 body876_72

def body876_74 : Prog (BitVec 64) :=
.seq body876_3 body876_73

def body876_75 : Prog (BitVec 64) :=
.dec ("parent") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "vh"),
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "nh", Flapjack.Exp.const 1#64],
          Flapjack.Exp.const 8#64]])) body876_74

def body876_76 : Prog (BitVec 64) :=
.seq body876_2 body876_75

def body876_77 : Prog (BitVec 64) :=
.dec ("nh") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 80#64])) body876_76

def body876_78 : Prog (BitVec 64) :=
.decCall ("vh") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("validate_headers") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 72#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 80#64])]) body876_77

def body876_79 : Prog (BitVec 64) :=
.seq body876_0 body876_78

def body876_80 : Prog (BitVec 64) :=
.dec ("pl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 0#64])) body876_79

def body876_81 : Prog (BitVec 64) :=
.seq body876_3 body876_4

def body876_82 : Prog (BitVec 64) :=
.seq body876_15 body876_16

def body876_83 : Prog (BitVec 64) :=
.seq body876_82 body876_17

def body876_84 : Prog (BitVec 64) :=
.seq body876_83 body876_18

def body876_85 : Prog (BitVec 64) :=
.seq body876_84 body876_19

def body876_86 : Prog (BitVec 64) :=
.seq body876_85 body876_20

def body876_87 : Prog (BitVec 64) :=
.seq body876_86 body876_21

def body876_88 : Prog (BitVec 64) :=
.seq body876_87 body876_22

def body876_89 : Prog (BitVec 64) :=
.seq body876_88 body876_23

def body876_90 : Prog (BitVec 64) :=
.seq body876_89 body876_24

def body876_91 : Prog (BitVec 64) :=
.seq body876_90 body876_25

def body876_92 : Prog (BitVec 64) :=
.seq body876_91 body876_26

def body876_93 : Prog (BitVec 64) :=
.seq body876_92 body876_27

def body876_94 : Prog (BitVec 64) :=
.seq body876_93 body876_28

def body876_95 : Prog (BitVec 64) :=
.seq body876_94 body876_29

def body876_96 : Prog (BitVec 64) :=
.seq body876_95 body876_30

def body876_97 : Prog (BitVec 64) :=
.seq body876_96 body876_31

def body876_98 : Prog (BitVec 64) :=
.seq body876_97 body876_32

def body876_99 : Prog (BitVec 64) :=
.decCall ("vvh") (Flapjack.Shape.one) ("is_valid_versioned_hashes") ([Flapjack.Exp.var Flapjack.VarKind.local "si"]) body876_98

def body876_100 : Prog (BitVec 64) :=
.seq body876_13 body876_99

def body876_101 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.var Flapjack.VarKind.local "bh",
  Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 0#64]),
      Flapjack.Exp.const 472#64],
  Flapjack.Exp.const 32#64]) body876_100

def body876_102 : Prog (BitVec 64) :=
.seq body876_11 body876_101

def body876_103 : Prog (BitVec 64) :=
.decCall ("bh") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body876_102

def body876_104 : Prog (BitVec 64) :=
.decCall ("hdr") (Flapjack.Shape.one) ("payload_header") ([Flapjack.Exp.var Flapjack.VarKind.local "si"]) body876_103

def body876_105 : Prog (BitVec 64) :=
.seq body876_10 body876_104

def body876_106 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body876_105

def body876_107 : Prog (BitVec 64) :=
.dec ("ntx") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 40#64])) body876_106

def body876_108 : Prog (BitVec 64) :=
.dec ("txs") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 32#64])) body876_107

def body876_109 : Prog (BitVec 64) :=
.seq body876_5 body876_108

def body876_110 : Prog (BitVec 64) :=
.decCall ("codedb") (Flapjack.Shape.one) ("nodedb_build") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 56#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 64#64])]) body876_109

def body876_111 : Prog (BitVec 64) :=
.decCall ("nodedb") (Flapjack.Shape.one) ("nodedb_build") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 40#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 48#64])]) body876_110

def body876_112 : Prog (BitVec 64) :=
.seq body876_81 body876_111

def body876_113 : Prog (BitVec 64) :=
.dec ("parent") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "vh"),
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "nh", Flapjack.Exp.const 1#64],
          Flapjack.Exp.const 8#64]])) body876_112

def body876_114 : Prog (BitVec 64) :=
.seq body876_2 body876_113

def body876_115 : Prog (BitVec 64) :=
.dec ("nh") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 80#64])) body876_114

def body876_116 : Prog (BitVec 64) :=
.decCall ("vh") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("validate_headers") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 72#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 80#64])]) body876_115

def body876_117 : Prog (BitVec 64) :=
.dec ("pl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 0#64])) body876_116

def originalData876 : Decl (BitVec 64) :=
.function { name := "run_attempt", inline := false, exported := false, params := [("si", Flapjack.Shape.one)], body := body876_80, returnShape := (Flapjack.Shape.one) }
def simplifiedData876 : Decl (BitVec 64) :=
.function { name := "run_attempt", inline := false, exported := false, params := [("si", Flapjack.Shape.one)], body := body876_117, returnShape := (Flapjack.Shape.one) }
def original876 := Pancake.PanLang.declToHOL originalData876
def simplified876 := Pancake.PanLang.declToHOL simplifiedData876
end InitECandidate.Proofs.FrontendStages.Declarations
