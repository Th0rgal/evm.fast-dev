import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data683
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate667
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody683_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def globalBody683_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody683_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "xl") (Flapjack.Exp.const 0#64)) globalBody683_0 globalBody683_1

def globalBody683_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "yl") (Flapjack.Exp.const 0#64)) globalBody683_0 globalBody683_1

def globalBody683_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_set_inf"
  [Flapjack.Exp.const 1#64, Flapjack.Exp.var Flapjack.VarKind.local "out"]

def globalBody683_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody683_6 : Prog (BitVec 64) :=
.seq globalBody683_4 globalBody683_5

def globalBody683_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.var Flapjack.VarKind.local "xz", Flapjack.Exp.var Flapjack.VarKind.local "yz"])
  (Flapjack.Exp.const 1#64)) globalBody683_6 globalBody683_1

def globalBody683_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "x"), none)) "fq_to_mont"
  [Flapjack.Exp.var Flapjack.VarKind.local "x"]

def globalBody683_9 : Prog (BitVec 64) :=
.seq globalBody683_7 globalBody683_8

def globalBody683_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "y"), none)) "fq_to_mont"
  [Flapjack.Exp.var Flapjack.VarKind.local "y"]

def globalBody683_11 : Prog (BitVec 64) :=
.seq globalBody683_9 globalBody683_10

def globalBody683_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "r"), none)) "fq_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "x"]

def globalBody683_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "r"), none)) "fq_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "r",
    Flapjack.Exp.rStruct
      [Flapjack.Exp.const 8797723225643362519#64, Flapjack.Exp.const 2263834496217719225#64,
        Flapjack.Exp.const 3696305541684646532#64, Flapjack.Exp.const 3035258219084094862#64]]

def globalBody683_14 : Prog (BitVec 64) :=
.seq globalBody683_12 globalBody683_13

def globalBody683_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) globalBody683_0 globalBody683_1

def globalBody683_16 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "out") (Flapjack.Exp.var Flapjack.VarKind.local "x")

def globalBody683_17 : Prog (BitVec 64) :=
.seq globalBody683_15 globalBody683_16

def globalBody683_18 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "y")

def globalBody683_19 : Prog (BitVec 64) :=
.seq globalBody683_17 globalBody683_18

def globalBody683_20 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 15230403791020821917#64, Flapjack.Exp.const 754611498739239741#64,
      Flapjack.Exp.const 7381016538464732716#64, Flapjack.Exp.const 1011752739694698287#64])

def globalBody683_21 : Prog (BitVec 64) :=
.seq globalBody683_19 globalBody683_20

def globalBody683_22 : Prog (BitVec 64) :=
.seq globalBody683_21 globalBody683_5

def globalBody683_23 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.var Flapjack.VarKind.local "r"]) globalBody683_22

def globalBody683_24 : Prog (BitVec 64) :=
.seq globalBody683_14 globalBody683_23

def globalBody683_25 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "x"]) globalBody683_24

def globalBody683_26 : Prog (BitVec 64) :=
.decCall ("l") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "y", Flapjack.Exp.var Flapjack.VarKind.local "y"]) globalBody683_25

def globalBody683_27 : Prog (BitVec 64) :=
.seq globalBody683_11 globalBody683_26

def globalBody683_28 : Prog (BitVec 64) :=
.decCall ("yz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "y"]) globalBody683_27

def globalBody683_29 : Prog (BitVec 64) :=
.decCall ("xz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "x"]) globalBody683_28

def globalBody683_30 : Prog (BitVec 64) :=
.seq globalBody683_3 globalBody683_29

def globalBody683_31 : Prog (BitVec 64) :=
.decCall ("yl") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "y",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 4332616871279656263#64, Flapjack.Exp.const 10917124144477883021#64,
      Flapjack.Exp.const 13281191951274694749#64, Flapjack.Exp.const 3486998266802970665#64]]) globalBody683_30

def globalBody683_32 : Prog (BitVec 64) :=
.seq globalBody683_2 globalBody683_31

def globalBody683_33 : Prog (BitVec 64) :=
.decCall ("xl") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "x",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 4332616871279656263#64, Flapjack.Exp.const 10917124144477883021#64,
      Flapjack.Exp.const 13281191951274694749#64, Flapjack.Exp.const 3486998266802970665#64]]) globalBody683_32

def globalBody683_34 : Prog (BitVec 64) :=
.decCall ("y") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 32#64],
  Flapjack.Exp.const 32#64]) globalBody683_33

def globalBody683_35 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 32#64]) globalBody683_34

def globalData683 : Decl (BitVec 64) :=
.function { name := "bn254_parse_g1", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := globalBody683_35, returnShape := (Flapjack.Shape.one) }
def globalOutput683 := Pancake.PanLang.declToHOL globalData683
end InitECandidate.Proofs.FrontendStages.Declarations
