import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify810
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body826_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "buffer_read"
  [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 0#64,
    Flapjack.Exp.const 96#64, Flapjack.Exp.var Flapjack.VarKind.local "hdr"]

def body826_1 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 4#64)

def body826_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body826_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 1024#64) (Flapjack.Exp.var Flapjack.VarKind.local "blen")) body826_1 body826_2

def body826_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 1024#64) (Flapjack.Exp.var Flapjack.VarKind.local "elen")) body826_1 body826_2

def body826_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 1024#64) (Flapjack.Exp.var Flapjack.VarKind.local "mlen")) body826_1 body826_2

def body826_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "buffer_read"
  [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.var Flapjack.VarKind.local "exp_start", Flapjack.Exp.var Flapjack.VarKind.local "hlen",
    Flapjack.Exp.var Flapjack.VarKind.local "hdr"]

def body826_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.var Flapjack.VarKind.local "cost"]

def body826_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "empty")

def body826_9 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 128#64])
  (Flapjack.Exp.const 0#64)

def body826_10 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body826_11 : Prog (BitVec 64) :=
.seq body826_9 body826_10

def body826_12 : Prog (BitVec 64) :=
.seq body826_8 body826_11

def body826_13 : Prog (BitVec 64) :=
.decCall ("empty") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 8#64]) body826_12

def body826_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "blen") (Flapjack.Exp.const 0#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "mlen") (Flapjack.Exp.const 0#64))]) body826_13 body826_2

def body826_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "buffer_read"
  [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.const 96#64, Flapjack.Exp.var Flapjack.VarKind.local "blen",
    Flapjack.Exp.var Flapjack.VarKind.local "bp"]

def body826_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "buffer_read"
  [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.var Flapjack.VarKind.local "exp_start", Flapjack.Exp.var Flapjack.VarKind.local "elen",
    Flapjack.Exp.var Flapjack.VarKind.local "ep"]

def body826_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "buffer_read"
  [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "exp_start", Flapjack.Exp.var Flapjack.VarKind.local "elen"],
    Flapjack.Exp.var Flapjack.VarKind.local "mlen", Flapjack.Exp.var Flapjack.VarKind.local "mp"]

def body826_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "modexp"
  [Flapjack.Exp.var Flapjack.VarKind.local "bp", Flapjack.Exp.var Flapjack.VarKind.local "blen",
    Flapjack.Exp.var Flapjack.VarKind.local "ep", Flapjack.Exp.var Flapjack.VarKind.local "elen",
    Flapjack.Exp.var Flapjack.VarKind.local "mp", Flapjack.Exp.var Flapjack.VarKind.local "mlen",
    Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body826_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body826_20 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "out")

def body826_21 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 128#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "mlen")

def body826_22 : Prog (BitVec 64) :=
.seq body826_21 body826_10

def body826_23 : Prog (BitVec 64) :=
.seq body826_20 body826_22

def body826_24 : Prog (BitVec 64) :=
.seq body826_19 body826_23

def body826_25 : Prog (BitVec 64) :=
.seq body826_18 body826_24

def body826_26 : Prog (BitVec 64) :=
.seq body826_17 body826_25

def body826_27 : Prog (BitVec 64) :=
.seq body826_16 body826_26

def body826_28 : Prog (BitVec 64) :=
.seq body826_15 body826_27

def body826_29 : Prog (BitVec 64) :=
.decCall ("mp") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "mlen", Flapjack.Exp.const 8#64]]) body826_28

def body826_30 : Prog (BitVec 64) :=
.decCall ("ep") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "elen", Flapjack.Exp.const 8#64]]) body826_29

def body826_31 : Prog (BitVec 64) :=
.decCall ("bp") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "blen", Flapjack.Exp.const 8#64]]) body826_30

def body826_32 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body826_31

def body826_33 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "mlen", Flapjack.Exp.const 8#64]]) body826_32

def body826_34 : Prog (BitVec 64) :=
.seq body826_14 body826_33

def body826_35 : Prog (BitVec 64) :=
.seq body826_7 body826_34

def body826_36 : Prog (BitVec 64) :=
.decCall ("cost") (Flapjack.Shape.one) ("modexp_gas") ([Flapjack.Exp.var Flapjack.VarKind.local "blen", Flapjack.Exp.var Flapjack.VarKind.local "mlen",
  Flapjack.Exp.var Flapjack.VarKind.local "elen", Flapjack.Exp.var Flapjack.VarKind.local "head"]) body826_35

def body826_37 : Prog (BitVec 64) :=
.decCall ("head") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.var Flapjack.VarKind.local "hlen"]) body826_36

def body826_38 : Prog (BitVec 64) :=
.seq body826_6 body826_37

def body826_39 : Prog (BitVec 64) :=
.decCall ("hlen") (Flapjack.Shape.one) ("min") ([Flapjack.Exp.const 32#64, Flapjack.Exp.var Flapjack.VarKind.local "elen"]) body826_38

def body826_40 : Prog (BitVec 64) :=
.dec ("exp_start") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.const 96#64, Flapjack.Exp.var Flapjack.VarKind.local "blen"]) body826_39

def body826_41 : Prog (BitVec 64) :=
.seq body826_5 body826_40

def body826_42 : Prog (BitVec 64) :=
.decCall ("mlen") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "ml"]) body826_41

def body826_43 : Prog (BitVec 64) :=
.decCall ("ml") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 64#64],
  Flapjack.Exp.const 32#64]) body826_42

def body826_44 : Prog (BitVec 64) :=
.seq body826_4 body826_43

def body826_45 : Prog (BitVec 64) :=
.decCall ("elen") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "el"]) body826_44

def body826_46 : Prog (BitVec 64) :=
.decCall ("el") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 32#64],
  Flapjack.Exp.const 32#64]) body826_45

def body826_47 : Prog (BitVec 64) :=
.seq body826_3 body826_46

def body826_48 : Prog (BitVec 64) :=
.decCall ("blen") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "bl"]) body826_47

def body826_49 : Prog (BitVec 64) :=
.decCall ("bl") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 32#64]) body826_48

def body826_50 : Prog (BitVec 64) :=
.seq body826_0 body826_49

def body826_51 : Prog (BitVec 64) :=
.dec ("hdr") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.global "pre_hdr_buf") body826_50

def body826_52 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 96#64])) body826_51

def body826_53 : Prog (BitVec 64) :=
.dec ("data") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 88#64])) body826_52

def body826_54 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body826_53

def body826_55 : Prog (BitVec 64) :=
.seq body826_8 body826_9

def body826_56 : Prog (BitVec 64) :=
.seq body826_55 body826_10

def body826_57 : Prog (BitVec 64) :=
.decCall ("empty") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 8#64]) body826_56

def body826_58 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "blen") (Flapjack.Exp.const 0#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "mlen") (Flapjack.Exp.const 0#64))]) body826_57 body826_2

def body826_59 : Prog (BitVec 64) :=
.seq body826_7 body826_58

def body826_60 : Prog (BitVec 64) :=
.seq body826_15 body826_16

def body826_61 : Prog (BitVec 64) :=
.seq body826_60 body826_17

def body826_62 : Prog (BitVec 64) :=
.seq body826_61 body826_18

def body826_63 : Prog (BitVec 64) :=
.seq body826_62 body826_19

def body826_64 : Prog (BitVec 64) :=
.seq body826_63 body826_20

def body826_65 : Prog (BitVec 64) :=
.seq body826_64 body826_21

def body826_66 : Prog (BitVec 64) :=
.seq body826_65 body826_10

def body826_67 : Prog (BitVec 64) :=
.decCall ("mp") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "mlen", Flapjack.Exp.const 8#64]]) body826_66

def body826_68 : Prog (BitVec 64) :=
.decCall ("ep") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "elen", Flapjack.Exp.const 8#64]]) body826_67

def body826_69 : Prog (BitVec 64) :=
.decCall ("bp") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "blen", Flapjack.Exp.const 8#64]]) body826_68

def body826_70 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body826_69

def body826_71 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "mlen", Flapjack.Exp.const 8#64]]) body826_70

def body826_72 : Prog (BitVec 64) :=
.seq body826_59 body826_71

def body826_73 : Prog (BitVec 64) :=
.decCall ("cost") (Flapjack.Shape.one) ("modexp_gas") ([Flapjack.Exp.var Flapjack.VarKind.local "blen", Flapjack.Exp.var Flapjack.VarKind.local "mlen",
  Flapjack.Exp.var Flapjack.VarKind.local "elen", Flapjack.Exp.var Flapjack.VarKind.local "head"]) body826_72

def body826_74 : Prog (BitVec 64) :=
.decCall ("head") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.var Flapjack.VarKind.local "hlen"]) body826_73

def body826_75 : Prog (BitVec 64) :=
.seq body826_6 body826_74

def body826_76 : Prog (BitVec 64) :=
.decCall ("hlen") (Flapjack.Shape.one) ("min") ([Flapjack.Exp.const 32#64, Flapjack.Exp.var Flapjack.VarKind.local "elen"]) body826_75

def body826_77 : Prog (BitVec 64) :=
.dec ("exp_start") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.const 96#64, Flapjack.Exp.var Flapjack.VarKind.local "blen"]) body826_76

def body826_78 : Prog (BitVec 64) :=
.seq body826_5 body826_77

def body826_79 : Prog (BitVec 64) :=
.decCall ("mlen") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "ml"]) body826_78

def body826_80 : Prog (BitVec 64) :=
.decCall ("ml") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 64#64],
  Flapjack.Exp.const 32#64]) body826_79

def body826_81 : Prog (BitVec 64) :=
.seq body826_4 body826_80

def body826_82 : Prog (BitVec 64) :=
.decCall ("elen") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "el"]) body826_81

def body826_83 : Prog (BitVec 64) :=
.decCall ("el") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 32#64],
  Flapjack.Exp.const 32#64]) body826_82

def body826_84 : Prog (BitVec 64) :=
.seq body826_3 body826_83

def body826_85 : Prog (BitVec 64) :=
.decCall ("blen") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "bl"]) body826_84

def body826_86 : Prog (BitVec 64) :=
.decCall ("bl") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 32#64]) body826_85

def body826_87 : Prog (BitVec 64) :=
.seq body826_0 body826_86

def body826_88 : Prog (BitVec 64) :=
.dec ("hdr") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.global "pre_hdr_buf") body826_87

def body826_89 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 96#64])) body826_88

def body826_90 : Prog (BitVec 64) :=
.dec ("data") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 88#64])) body826_89

def body826_91 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body826_90

def originalData826 : Decl (BitVec 64) :=
.function { name := "pre_modexp", inline := false, exported := false, params := [], body := body826_54, returnShape := (Flapjack.Shape.one) }
def simplifiedData826 : Decl (BitVec 64) :=
.function { name := "pre_modexp", inline := false, exported := false, params := [], body := body826_91, returnShape := (Flapjack.Shape.one) }
def original826 := Pancake.PanLang.declToHOL originalData826
def simplified826 := Pancake.PanLang.declToHOL simplifiedData826
end InitECandidate.Proofs.FrontendStages.Declarations
