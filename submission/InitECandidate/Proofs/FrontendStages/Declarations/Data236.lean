import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify220
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body236_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 20#64)

def body236_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body236_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 96#64]))
  (Flapjack.Exp.const 1#64)) body236_0 body236_1

def body236_3 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 21#64)

def body236_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 208#64]))
  (Flapjack.Exp.var Flapjack.VarKind.local "ebg")) body236_3 body236_1

def body236_5 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 22#64)

def body236_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 104#64]))
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 112#64]))) body236_5 body236_1

def body236_7 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 23#64)

def body236_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) body236_7 body236_1

def body236_9 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 24#64)

def body236_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "parent", Flapjack.Exp.const 120#64]))
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 120#64]))) body236_9 body236_1

def body236_11 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 25#64)

def body236_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 96#64]))
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "parent", Flapjack.Exp.const 96#64]),
      Flapjack.Exp.const 1#64])) body236_11 body236_1

def body236_13 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 26#64)

def body236_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 32#64)
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 136#64]))) body236_13 body236_1

def body236_15 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 27#64)

def body236_16 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "dz") (Flapjack.Exp.const 0#64)) body236_15 body236_1

def body236_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "eq"), none)) "memeq"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 152#64]),
    Flapjack.Exp.var Flapjack.VarKind.global "hdr_zero8", Flapjack.Exp.const 8#64]

def body236_18 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 28#64)

def body236_19 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) body236_18 body236_1

def body236_20 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "tmp") (Flapjack.Exp.const 192#64)

def body236_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp", Flapjack.Exp.const 1#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tmp", Flapjack.Exp.const 32#64]]

def body236_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "eq"), none)) "memeq"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 16#64]),
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tmp", Flapjack.Exp.const 32#64],
    Flapjack.Exp.const 32#64]

def body236_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body236_24 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 29#64)

def body236_25 : Prog (BitVec 64) :=
.seq body236_23 body236_24

def body236_26 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) body236_25 body236_1

def body236_27 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "header_hash"
  [Flapjack.Exp.var Flapjack.VarKind.local "parent", Flapjack.Exp.var Flapjack.VarKind.local "tmp"]

def body236_28 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "eq"), none)) "memeq"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 8#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "tmp", Flapjack.Exp.const 32#64]

def body236_29 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 30#64)

def body236_30 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) body236_29 body236_1

def body236_31 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body236_32 : Prog (BitVec 64) :=
.seq body236_30 body236_31

def body236_33 : Prog (BitVec 64) :=
.seq body236_23 body236_32

def body236_34 : Prog (BitVec 64) :=
.seq body236_28 body236_33

def body236_35 : Prog (BitVec 64) :=
.seq body236_27 body236_34

def body236_36 : Prog (BitVec 64) :=
.seq body236_26 body236_35

def body236_37 : Prog (BitVec 64) :=
.seq body236_22 body236_36

def body236_38 : Prog (BitVec 64) :=
.seq body236_21 body236_37

def body236_39 : Prog (BitVec 64) :=
.seq body236_20 body236_38

def body236_40 : Prog (BitVec 64) :=
.decCall ("tmp") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) body236_39

def body236_41 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body236_40

def body236_42 : Prog (BitVec 64) :=
.seq body236_19 body236_41

def body236_43 : Prog (BitVec 64) :=
.seq body236_17 body236_42

def body236_44 : Prog (BitVec 64) :=
.seq body236_16 body236_43

def body236_45 : Prog (BitVec 64) :=
.decCall ("dz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 64#64])]) body236_44

def body236_46 : Prog (BitVec 64) :=
.seq body236_14 body236_45

def body236_47 : Prog (BitVec 64) :=
.seq body236_12 body236_46

def body236_48 : Prog (BitVec 64) :=
.seq body236_10 body236_47

def body236_49 : Prog (BitVec 64) :=
.seq body236_8 body236_48

def body236_50 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "expected",
  Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 160#64])]) body236_49

def body236_51 : Prog (BitVec 64) :=
.decCall ("expected") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("calculate_base_fee_per_gas") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 104#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "parent", Flapjack.Exp.const 104#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "parent", Flapjack.Exp.const 112#64]),
  Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "parent", Flapjack.Exp.const 160#64])]) body236_50

def body236_52 : Prog (BitVec 64) :=
.seq body236_6 body236_51

def body236_53 : Prog (BitVec 64) :=
.seq body236_4 body236_52

def body236_54 : Prog (BitVec 64) :=
.decCall ("ebg") (Flapjack.Shape.one) ("calculate_excess_blob_gas") ([Flapjack.Exp.var Flapjack.VarKind.local "parent"]) body236_53

def body236_55 : Prog (BitVec 64) :=
.seq body236_2 body236_54

def body236_56 : Prog (BitVec 64) :=
.seq body236_4 body236_6

def body236_57 : Prog (BitVec 64) :=
.seq body236_8 body236_10

def body236_58 : Prog (BitVec 64) :=
.seq body236_57 body236_12

def body236_59 : Prog (BitVec 64) :=
.seq body236_58 body236_14

def body236_60 : Prog (BitVec 64) :=
.seq body236_16 body236_17

def body236_61 : Prog (BitVec 64) :=
.seq body236_60 body236_19

def body236_62 : Prog (BitVec 64) :=
.seq body236_20 body236_21

def body236_63 : Prog (BitVec 64) :=
.seq body236_62 body236_22

def body236_64 : Prog (BitVec 64) :=
.seq body236_63 body236_26

def body236_65 : Prog (BitVec 64) :=
.seq body236_64 body236_27

def body236_66 : Prog (BitVec 64) :=
.seq body236_65 body236_28

def body236_67 : Prog (BitVec 64) :=
.seq body236_66 body236_23

def body236_68 : Prog (BitVec 64) :=
.seq body236_67 body236_30

def body236_69 : Prog (BitVec 64) :=
.seq body236_68 body236_31

def body236_70 : Prog (BitVec 64) :=
.decCall ("tmp") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) body236_69

def body236_71 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body236_70

def body236_72 : Prog (BitVec 64) :=
.seq body236_61 body236_71

def body236_73 : Prog (BitVec 64) :=
.decCall ("dz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 64#64])]) body236_72

def body236_74 : Prog (BitVec 64) :=
.seq body236_59 body236_73

def body236_75 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "expected",
  Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 160#64])]) body236_74

def body236_76 : Prog (BitVec 64) :=
.decCall ("expected") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("calculate_base_fee_per_gas") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 104#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "parent", Flapjack.Exp.const 104#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "parent", Flapjack.Exp.const 112#64]),
  Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "parent", Flapjack.Exp.const 160#64])]) body236_75

def body236_77 : Prog (BitVec 64) :=
.seq body236_56 body236_76

def body236_78 : Prog (BitVec 64) :=
.decCall ("ebg") (Flapjack.Shape.one) ("calculate_excess_blob_gas") ([Flapjack.Exp.var Flapjack.VarKind.local "parent"]) body236_77

def body236_79 : Prog (BitVec 64) :=
.seq body236_2 body236_78

def originalData236 : Decl (BitVec 64) :=
.function { name := "validate_header", inline := false, exported := false, params := [("parent", Flapjack.Shape.one), ("h", Flapjack.Shape.one)], body := body236_55, returnShape := (Flapjack.Shape.one) }
def simplifiedData236 : Decl (BitVec 64) :=
.function { name := "validate_header", inline := false, exported := false, params := [("parent", Flapjack.Shape.one), ("h", Flapjack.Shape.one)], body := body236_79, returnShape := (Flapjack.Shape.one) }
def original236 := Pancake.PanLang.declToHOL originalData236
def simplified236 := Pancake.PanLang.declToHOL simplifiedData236
end InitECandidate.Proofs.FrontendStages.Declarations
