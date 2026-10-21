import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify667
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body683_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body683_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body683_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "xl") (Flapjack.Exp.const 0#64)) body683_0 body683_1

def body683_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "yl") (Flapjack.Exp.const 0#64)) body683_0 body683_1

def body683_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_set_inf"
  [Flapjack.Exp.const 1#64, Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body683_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body683_6 : Prog (BitVec 64) :=
.seq body683_4 body683_5

def body683_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.var Flapjack.VarKind.local "xz", Flapjack.Exp.var Flapjack.VarKind.local "yz"])
  (Flapjack.Exp.const 1#64)) body683_6 body683_1

def body683_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "x"), none)) "fq_to_mont"
  [Flapjack.Exp.var Flapjack.VarKind.local "x"]

def body683_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "y"), none)) "fq_to_mont"
  [Flapjack.Exp.var Flapjack.VarKind.local "y"]

def body683_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "r"), none)) "fq_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "x"]

def body683_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "r"), none)) "fq_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "r",
    Flapjack.Exp.rStruct
      [Flapjack.Exp.const 8797723225643362519#64, Flapjack.Exp.const 2263834496217719225#64,
        Flapjack.Exp.const 3696305541684646532#64, Flapjack.Exp.const 3035258219084094862#64]]

def body683_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) body683_0 body683_1

def body683_13 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "out") (Flapjack.Exp.var Flapjack.VarKind.local "x")

def body683_14 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "y")

def body683_15 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 15230403791020821917#64, Flapjack.Exp.const 754611498739239741#64,
      Flapjack.Exp.const 7381016538464732716#64, Flapjack.Exp.const 1011752739694698287#64])

def body683_16 : Prog (BitVec 64) :=
.seq body683_15 body683_5

def body683_17 : Prog (BitVec 64) :=
.seq body683_14 body683_16

def body683_18 : Prog (BitVec 64) :=
.seq body683_13 body683_17

def body683_19 : Prog (BitVec 64) :=
.seq body683_12 body683_18

def body683_20 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.var Flapjack.VarKind.local "r"]) body683_19

def body683_21 : Prog (BitVec 64) :=
.seq body683_11 body683_20

def body683_22 : Prog (BitVec 64) :=
.seq body683_10 body683_21

def body683_23 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "x"]) body683_22

def body683_24 : Prog (BitVec 64) :=
.decCall ("l") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "y", Flapjack.Exp.var Flapjack.VarKind.local "y"]) body683_23

def body683_25 : Prog (BitVec 64) :=
.seq body683_9 body683_24

def body683_26 : Prog (BitVec 64) :=
.seq body683_8 body683_25

def body683_27 : Prog (BitVec 64) :=
.seq body683_7 body683_26

def body683_28 : Prog (BitVec 64) :=
.decCall ("yz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "y"]) body683_27

def body683_29 : Prog (BitVec 64) :=
.decCall ("xz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "x"]) body683_28

def body683_30 : Prog (BitVec 64) :=
.seq body683_3 body683_29

def body683_31 : Prog (BitVec 64) :=
.decCall ("yl") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "y",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 4332616871279656263#64, Flapjack.Exp.const 10917124144477883021#64,
      Flapjack.Exp.const 13281191951274694749#64, Flapjack.Exp.const 3486998266802970665#64]]) body683_30

def body683_32 : Prog (BitVec 64) :=
.seq body683_2 body683_31

def body683_33 : Prog (BitVec 64) :=
.decCall ("xl") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "x",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 4332616871279656263#64, Flapjack.Exp.const 10917124144477883021#64,
      Flapjack.Exp.const 13281191951274694749#64, Flapjack.Exp.const 3486998266802970665#64]]) body683_32

def body683_34 : Prog (BitVec 64) :=
.decCall ("y") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 32#64],
  Flapjack.Exp.const 32#64]) body683_33

def body683_35 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 32#64]) body683_34

def body683_36 : Prog (BitVec 64) :=
.seq body683_7 body683_8

def body683_37 : Prog (BitVec 64) :=
.seq body683_36 body683_9

def body683_38 : Prog (BitVec 64) :=
.seq body683_10 body683_11

def body683_39 : Prog (BitVec 64) :=
.seq body683_12 body683_13

def body683_40 : Prog (BitVec 64) :=
.seq body683_39 body683_14

def body683_41 : Prog (BitVec 64) :=
.seq body683_40 body683_15

def body683_42 : Prog (BitVec 64) :=
.seq body683_41 body683_5

def body683_43 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.var Flapjack.VarKind.local "r"]) body683_42

def body683_44 : Prog (BitVec 64) :=
.seq body683_38 body683_43

def body683_45 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "x"]) body683_44

def body683_46 : Prog (BitVec 64) :=
.decCall ("l") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "y", Flapjack.Exp.var Flapjack.VarKind.local "y"]) body683_45

def body683_47 : Prog (BitVec 64) :=
.seq body683_37 body683_46

def body683_48 : Prog (BitVec 64) :=
.decCall ("yz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "y"]) body683_47

def body683_49 : Prog (BitVec 64) :=
.decCall ("xz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "x"]) body683_48

def body683_50 : Prog (BitVec 64) :=
.seq body683_3 body683_49

def body683_51 : Prog (BitVec 64) :=
.decCall ("yl") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "y",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 4332616871279656263#64, Flapjack.Exp.const 10917124144477883021#64,
      Flapjack.Exp.const 13281191951274694749#64, Flapjack.Exp.const 3486998266802970665#64]]) body683_50

def body683_52 : Prog (BitVec 64) :=
.seq body683_2 body683_51

def body683_53 : Prog (BitVec 64) :=
.decCall ("xl") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "x",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 4332616871279656263#64, Flapjack.Exp.const 10917124144477883021#64,
      Flapjack.Exp.const 13281191951274694749#64, Flapjack.Exp.const 3486998266802970665#64]]) body683_52

def body683_54 : Prog (BitVec 64) :=
.decCall ("y") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 32#64],
  Flapjack.Exp.const 32#64]) body683_53

def body683_55 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 32#64]) body683_54

def originalData683 : Decl (BitVec 64) :=
.function { name := "bn254_parse_g1", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body683_35, returnShape := (Flapjack.Shape.one) }
def simplifiedData683 : Decl (BitVec 64) :=
.function { name := "bn254_parse_g1", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body683_55, returnShape := (Flapjack.Shape.one) }
def original683 := Pancake.PanLang.declToHOL originalData683
def simplified683 := Pancake.PanLang.declToHOL simplifiedData683
end InitECandidate.Proofs.FrontendStages.Declarations
