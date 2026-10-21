import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify622
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body638_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "p256_set_infinity" [Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body638_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body638_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "p256_ec_double" [Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body638_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "p256_ec_add_affine"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "ax",
    Flapjack.Exp.var Flapjack.VarKind.local "ay"]

def body638_4 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body638_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "bit1") (Flapjack.Exp.const 1#64)) body638_3 body638_4

def body638_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "p256_ec_add_affine"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "bx",
    Flapjack.Exp.var Flapjack.VarKind.local "by"]

def body638_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "bit2") (Flapjack.Exp.const 1#64)) body638_6 body638_4

def body638_8 : Prog (BitVec 64) :=
.decCall ("bit2") (Flapjack.Shape.one) ("u256_bit") ([Flapjack.Exp.var Flapjack.VarKind.local "k2", Flapjack.Exp.var Flapjack.VarKind.local "i"]) body638_7

def body638_9 : Prog (BitVec 64) :=
.seq body638_5 body638_8

def body638_10 : Prog (BitVec 64) :=
.decCall ("bit1") (Flapjack.Shape.one) ("u256_bit") ([Flapjack.Exp.var Flapjack.VarKind.local "k1", Flapjack.Exp.var Flapjack.VarKind.local "i"]) body638_9

def body638_11 : Prog (BitVec 64) :=
.seq body638_2 body638_10

def body638_12 : Prog (BitVec 64) :=
.seq body638_1 body638_11

def body638_13 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "i")) body638_12

def body638_14 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body638_15 : Prog (BitVec 64) :=
.seq body638_13 body638_14

def body638_16 : Prog (BitVec 64) :=
.decCall ("i") (Flapjack.Shape.one) ("max") ([Flapjack.Exp.var Flapjack.VarKind.local "len1", Flapjack.Exp.var Flapjack.VarKind.local "len2"]) body638_15

def body638_17 : Prog (BitVec 64) :=
.decCall ("len2") (Flapjack.Shape.one) ("u256_bit_length") ([Flapjack.Exp.var Flapjack.VarKind.local "k2"]) body638_16

def body638_18 : Prog (BitVec 64) :=
.decCall ("len1") (Flapjack.Shape.one) ("u256_bit_length") ([Flapjack.Exp.var Flapjack.VarKind.local "k1"]) body638_17

def body638_19 : Prog (BitVec 64) :=
.seq body638_0 body638_18

def body638_20 : Prog (BitVec 64) :=
.seq body638_1 body638_2

def body638_21 : Prog (BitVec 64) :=
.seq body638_20 body638_10

def body638_22 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "i")) body638_21

def body638_23 : Prog (BitVec 64) :=
.seq body638_22 body638_14

def body638_24 : Prog (BitVec 64) :=
.decCall ("i") (Flapjack.Shape.one) ("max") ([Flapjack.Exp.var Flapjack.VarKind.local "len1", Flapjack.Exp.var Flapjack.VarKind.local "len2"]) body638_23

def body638_25 : Prog (BitVec 64) :=
.decCall ("len2") (Flapjack.Shape.one) ("u256_bit_length") ([Flapjack.Exp.var Flapjack.VarKind.local "k2"]) body638_24

def body638_26 : Prog (BitVec 64) :=
.decCall ("len1") (Flapjack.Shape.one) ("u256_bit_length") ([Flapjack.Exp.var Flapjack.VarKind.local "k1"]) body638_25

def body638_27 : Prog (BitVec 64) :=
.seq body638_0 body638_26

def originalData638 : Decl (BitVec 64) :=
.function { name := "p256_ec_mul2", inline := false, exported := false, params := [("out", Flapjack.Shape.one),
  ("k1", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("ax", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("ay", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("k2", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("bx", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("by", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body638_19, returnShape := (Flapjack.Shape.one) }
def simplifiedData638 : Decl (BitVec 64) :=
.function { name := "p256_ec_mul2", inline := false, exported := false, params := [("out", Flapjack.Shape.one),
  ("k1", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("ax", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("ay", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("k2", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("bx", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("by", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body638_27, returnShape := (Flapjack.Shape.one) }
def original638 := Pancake.PanLang.declToHOL originalData638
def simplified638 := Pancake.PanLang.declToHOL simplifiedData638
end InitECandidate.Proofs.FrontendStages.Declarations
