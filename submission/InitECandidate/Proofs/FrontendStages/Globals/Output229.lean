import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data229
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate211
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody229_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "acc"), none)) "u256_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "den"]

def globalBody229_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "out"), none)) "u256_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def globalBody229_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "trap_with" [Flapjack.Exp.const 3#64]

def globalBody229_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody229_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "prod"),
      Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "prod"),
      Flapjack.Exp.rField 6 (Flapjack.Exp.var Flapjack.VarKind.local "prod"),
      Flapjack.Exp.rField 7 (Flapjack.Exp.var Flapjack.VarKind.local "prod")])
  (Flapjack.Exp.const 0#64)) globalBody229_2 globalBody229_3

def globalBody229_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "di"), none)) "u256_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "di", Flapjack.Exp.var Flapjack.VarKind.local "den"]

def globalBody229_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "acc"), none)) "u256_div"
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "di"]

def globalBody229_7 : Prog (BitVec 64) :=
.seq globalBody229_5 globalBody229_6

def globalBody229_8 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody229_9 : Prog (BitVec 64) :=
.seq globalBody229_7 globalBody229_8

def globalBody229_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "nz"), none)) "u256_is_zero"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def globalBody229_11 : Prog (BitVec 64) :=
.seq globalBody229_9 globalBody229_10

def globalBody229_12 : Prog (BitVec 64) :=
.decCall ("di") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_word") ([Flapjack.Exp.var Flapjack.VarKind.local "i"]) globalBody229_11

def globalBody229_13 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "prod"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "prod"),
    Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "prod"),
    Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "prod")]) globalBody229_12

def globalBody229_14 : Prog (BitVec 64) :=
.seq globalBody229_4 globalBody229_13

def globalBody229_15 : Prog (BitVec 64) :=
.decCall ("prod") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_mul_full") ([Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "num"]) globalBody229_14

def globalBody229_16 : Prog (BitVec 64) :=
.seq globalBody229_1 globalBody229_15

def globalBody229_17 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "nz") (Flapjack.Exp.const 0#64)) globalBody229_16

def globalBody229_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "out"), none)) "u256_div"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "den"]

def globalBody229_19 : Prog (BitVec 64) :=
.seq globalBody229_17 globalBody229_18

def globalBody229_20 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "out")

def globalBody229_21 : Prog (BitVec 64) :=
.seq globalBody229_19 globalBody229_20

def globalBody229_22 : Prog (BitVec 64) :=
.decCall ("nz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "acc"]) globalBody229_21

def globalBody229_23 : Prog (BitVec 64) :=
.dec ("zero") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) globalBody229_22

def globalBody229_24 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) globalBody229_23

def globalBody229_25 : Prog (BitVec 64) :=
.dec ("out") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) globalBody229_24

def globalBody229_26 : Prog (BitVec 64) :=
.seq globalBody229_0 globalBody229_25

def globalBody229_27 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_word") ([Flapjack.Exp.var Flapjack.VarKind.local "factor"]) globalBody229_26

def globalBody229_28 : Prog (BitVec 64) :=
.decCall ("num") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_word") ([Flapjack.Exp.var Flapjack.VarKind.local "numerator"]) globalBody229_27

def globalBody229_29 : Prog (BitVec 64) :=
.decCall ("den") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_word") ([Flapjack.Exp.var Flapjack.VarKind.local "denominator"]) globalBody229_28

def globalData229 : Decl (BitVec 64) :=
.function { name := "taylor_exponential", inline := false, exported := false, params := [("factor", Flapjack.Shape.one), ("numerator", Flapjack.Shape.one), ("denominator", Flapjack.Shape.one)], body := globalBody229_29, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def globalOutput229 := Pancake.PanLang.declToHOL globalData229
end InitECandidate.Proofs.FrontendStages.Declarations
