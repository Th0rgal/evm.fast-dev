import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify790
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body806_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "sha256"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 96#64],
    Flapjack.Exp.const 48#64, Flapjack.Exp.var Flapjack.VarKind.local "h"]

def body806_1 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "h") (Flapjack.Exp.const 1#64)

def body806_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body806_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body806_4 : Prog (BitVec 64) :=
.seq body806_2 body806_3

def body806_5 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body806_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "heq") (Flapjack.Exp.const 0#64)) body806_4 body806_5

def body806_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 0#64)) body806_4 body806_5

def body806_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "ok"), none)) "kzg_load_g1"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 144#64],
    Flapjack.Exp.var Flapjack.VarKind.local "pr"]

def body806_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "zlt") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ylt") (Flapjack.Exp.const 0#64)])) body806_4 body806_5

def body806_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "v") (Flapjack.Exp.const 0#64)) body806_3 body806_5

def body806_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 64#64]

def body806_12 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 30#64])
  (Flapjack.Exp.const 16#64)

def body806_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "u256_to_be32"
  [Flapjack.Exp.var Flapjack.VarKind.local "r",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 32#64]]

def body806_14 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body806_15 : Prog (BitVec 64) :=
.seq body806_13 body806_14

def body806_16 : Prog (BitVec 64) :=
.seq body806_12 body806_15

def body806_17 : Prog (BitVec 64) :=
.seq body806_11 body806_16

def body806_18 : Prog (BitVec 64) :=
.seq body806_10 body806_17

def body806_19 : Prog (BitVec 64) :=
.seq body806_2 body806_18

def body806_20 : Prog (BitVec 64) :=
.decCall ("v") (Flapjack.Shape.one) ("kzg_verify") ([Flapjack.Exp.var Flapjack.VarKind.local "c",
  Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 32#64],
  Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 64#64],
  Flapjack.Exp.var Flapjack.VarKind.local "pr"]) body806_19

def body806_21 : Prog (BitVec 64) :=
.seq body806_9 body806_20

def body806_22 : Prog (BitVec 64) :=
.decCall ("ylt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "y", Flapjack.Exp.var Flapjack.VarKind.local "r"]) body806_21

def body806_23 : Prog (BitVec 64) :=
.decCall ("zlt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "z", Flapjack.Exp.var Flapjack.VarKind.local "r"]) body806_22

def body806_24 : Prog (BitVec 64) :=
.dec ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 1344#64])) body806_23

def body806_25 : Prog (BitVec 64) :=
.decCall ("y") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 64#64],
  Flapjack.Exp.const 32#64]) body806_24

def body806_26 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 32#64],
  Flapjack.Exp.const 32#64]) body806_25

def body806_27 : Prog (BitVec 64) :=
.seq body806_7 body806_26

def body806_28 : Prog (BitVec 64) :=
.seq body806_8 body806_27

def body806_29 : Prog (BitVec 64) :=
.seq body806_7 body806_28

def body806_30 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("kzg_load_g1") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 96#64],
  Flapjack.Exp.var Flapjack.VarKind.local "c"]) body806_29

def body806_31 : Prog (BitVec 64) :=
.seq body806_6 body806_30

def body806_32 : Prog (BitVec 64) :=
.decCall ("heq") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 32#64]) body806_31

def body806_33 : Prog (BitVec 64) :=
.seq body806_1 body806_32

def body806_34 : Prog (BitVec 64) :=
.seq body806_0 body806_33

def body806_35 : Prog (BitVec 64) :=
.decCall ("pr") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) body806_34

def body806_36 : Prog (BitVec 64) :=
.decCall ("c") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) body806_35

def body806_37 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body806_36

def body806_38 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body806_37

def body806_39 : Prog (BitVec 64) :=
.seq body806_0 body806_1

def body806_40 : Prog (BitVec 64) :=
.seq body806_7 body806_8

def body806_41 : Prog (BitVec 64) :=
.seq body806_40 body806_7

def body806_42 : Prog (BitVec 64) :=
.seq body806_2 body806_10

def body806_43 : Prog (BitVec 64) :=
.seq body806_42 body806_11

def body806_44 : Prog (BitVec 64) :=
.seq body806_43 body806_12

def body806_45 : Prog (BitVec 64) :=
.seq body806_44 body806_13

def body806_46 : Prog (BitVec 64) :=
.seq body806_45 body806_14

def body806_47 : Prog (BitVec 64) :=
.decCall ("v") (Flapjack.Shape.one) ("kzg_verify") ([Flapjack.Exp.var Flapjack.VarKind.local "c",
  Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 32#64],
  Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 64#64],
  Flapjack.Exp.var Flapjack.VarKind.local "pr"]) body806_46

def body806_48 : Prog (BitVec 64) :=
.seq body806_9 body806_47

def body806_49 : Prog (BitVec 64) :=
.decCall ("ylt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "y", Flapjack.Exp.var Flapjack.VarKind.local "r"]) body806_48

def body806_50 : Prog (BitVec 64) :=
.decCall ("zlt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "z", Flapjack.Exp.var Flapjack.VarKind.local "r"]) body806_49

def body806_51 : Prog (BitVec 64) :=
.dec ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 1344#64])) body806_50

def body806_52 : Prog (BitVec 64) :=
.decCall ("y") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 64#64],
  Flapjack.Exp.const 32#64]) body806_51

def body806_53 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 32#64],
  Flapjack.Exp.const 32#64]) body806_52

def body806_54 : Prog (BitVec 64) :=
.seq body806_41 body806_53

def body806_55 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("kzg_load_g1") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 96#64],
  Flapjack.Exp.var Flapjack.VarKind.local "c"]) body806_54

def body806_56 : Prog (BitVec 64) :=
.seq body806_6 body806_55

def body806_57 : Prog (BitVec 64) :=
.decCall ("heq") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 32#64]) body806_56

def body806_58 : Prog (BitVec 64) :=
.seq body806_39 body806_57

def body806_59 : Prog (BitVec 64) :=
.decCall ("pr") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) body806_58

def body806_60 : Prog (BitVec 64) :=
.decCall ("c") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) body806_59

def body806_61 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body806_60

def body806_62 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body806_61

def originalData806 : Decl (BitVec 64) :=
.function { name := "kzg_point_evaluation_exec", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body806_38, returnShape := (Flapjack.Shape.one) }
def simplifiedData806 : Decl (BitVec 64) :=
.function { name := "kzg_point_evaluation_exec", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body806_62, returnShape := (Flapjack.Shape.one) }
def original806 := Pancake.PanLang.declToHOL originalData806
def simplified806 := Pancake.PanLang.declToHOL simplifiedData806
end InitECandidate.Proofs.FrontendStages.Declarations
