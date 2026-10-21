import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify213
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body229_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "acc"), none)) "u256_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "den"]

def body229_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "out"), none)) "u256_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def body229_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "trap_with" [Flapjack.Exp.const 3#64]

def body229_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body229_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "prod"),
      Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "prod"),
      Flapjack.Exp.rField 6 (Flapjack.Exp.var Flapjack.VarKind.local "prod"),
      Flapjack.Exp.rField 7 (Flapjack.Exp.var Flapjack.VarKind.local "prod")])
  (Flapjack.Exp.const 0#64)) body229_2 body229_3

def body229_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "di"), none)) "u256_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "di", Flapjack.Exp.var Flapjack.VarKind.local "den"]

def body229_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "acc"), none)) "u256_div"
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "di"]

def body229_7 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body229_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "nz"), none)) "u256_is_zero"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def body229_9 : Prog (BitVec 64) :=
.seq body229_7 body229_8

def body229_10 : Prog (BitVec 64) :=
.seq body229_6 body229_9

def body229_11 : Prog (BitVec 64) :=
.seq body229_5 body229_10

def body229_12 : Prog (BitVec 64) :=
.decCall ("di") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_word") ([Flapjack.Exp.var Flapjack.VarKind.local "i"]) body229_11

def body229_13 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "prod"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "prod"),
    Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "prod"),
    Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "prod")]) body229_12

def body229_14 : Prog (BitVec 64) :=
.seq body229_4 body229_13

def body229_15 : Prog (BitVec 64) :=
.decCall ("prod") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_mul_full") ([Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "num"]) body229_14

def body229_16 : Prog (BitVec 64) :=
.seq body229_1 body229_15

def body229_17 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "nz") (Flapjack.Exp.const 0#64)) body229_16

def body229_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "out"), none)) "u256_div"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "den"]

def body229_19 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "out")

def body229_20 : Prog (BitVec 64) :=
.seq body229_18 body229_19

def body229_21 : Prog (BitVec 64) :=
.seq body229_17 body229_20

def body229_22 : Prog (BitVec 64) :=
.decCall ("nz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "acc"]) body229_21

def body229_23 : Prog (BitVec 64) :=
.dec ("zero") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body229_22

def body229_24 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) body229_23

def body229_25 : Prog (BitVec 64) :=
.dec ("out") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body229_24

def body229_26 : Prog (BitVec 64) :=
.seq body229_0 body229_25

def body229_27 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_word") ([Flapjack.Exp.var Flapjack.VarKind.local "factor"]) body229_26

def body229_28 : Prog (BitVec 64) :=
.decCall ("num") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_word") ([Flapjack.Exp.var Flapjack.VarKind.local "numerator"]) body229_27

def body229_29 : Prog (BitVec 64) :=
.decCall ("den") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_word") ([Flapjack.Exp.var Flapjack.VarKind.local "denominator"]) body229_28

def body229_30 : Prog (BitVec 64) :=
.seq body229_5 body229_6

def body229_31 : Prog (BitVec 64) :=
.seq body229_30 body229_7

def body229_32 : Prog (BitVec 64) :=
.seq body229_31 body229_8

def body229_33 : Prog (BitVec 64) :=
.decCall ("di") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_word") ([Flapjack.Exp.var Flapjack.VarKind.local "i"]) body229_32

def body229_34 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "prod"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "prod"),
    Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "prod"),
    Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "prod")]) body229_33

def body229_35 : Prog (BitVec 64) :=
.seq body229_4 body229_34

def body229_36 : Prog (BitVec 64) :=
.decCall ("prod") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_mul_full") ([Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "num"]) body229_35

def body229_37 : Prog (BitVec 64) :=
.seq body229_1 body229_36

def body229_38 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "nz") (Flapjack.Exp.const 0#64)) body229_37

def body229_39 : Prog (BitVec 64) :=
.seq body229_38 body229_18

def body229_40 : Prog (BitVec 64) :=
.seq body229_39 body229_19

def body229_41 : Prog (BitVec 64) :=
.decCall ("nz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "acc"]) body229_40

def body229_42 : Prog (BitVec 64) :=
.dec ("zero") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body229_41

def body229_43 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) body229_42

def body229_44 : Prog (BitVec 64) :=
.dec ("out") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body229_43

def body229_45 : Prog (BitVec 64) :=
.seq body229_0 body229_44

def body229_46 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_word") ([Flapjack.Exp.var Flapjack.VarKind.local "factor"]) body229_45

def body229_47 : Prog (BitVec 64) :=
.decCall ("num") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_word") ([Flapjack.Exp.var Flapjack.VarKind.local "numerator"]) body229_46

def body229_48 : Prog (BitVec 64) :=
.decCall ("den") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_word") ([Flapjack.Exp.var Flapjack.VarKind.local "denominator"]) body229_47

def originalData229 : Decl (BitVec 64) :=
.function { name := "taylor_exponential", inline := false, exported := false, params := [("factor", Flapjack.Shape.one), ("numerator", Flapjack.Shape.one), ("denominator", Flapjack.Shape.one)], body := body229_29, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData229 : Decl (BitVec 64) :=
.function { name := "taylor_exponential", inline := false, exported := false, params := [("factor", Flapjack.Shape.one), ("numerator", Flapjack.Shape.one), ("denominator", Flapjack.Shape.one)], body := body229_48, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def original229 := Pancake.PanLang.declToHOL originalData229
def simplified229 := Pancake.PanLang.declToHOL simplifiedData229
end InitECandidate.Proofs.FrontendStages.Declarations
