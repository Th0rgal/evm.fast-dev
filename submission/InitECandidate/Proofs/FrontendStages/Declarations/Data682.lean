import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify666
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body682_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bn254_init" []

def body682_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_set_one"
  [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body682_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body682_3 : Prog (BitVec 64) :=
.seq body682_1 body682_2

def body682_4 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body682_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.var Flapjack.VarKind.local "qi", Flapjack.Exp.var Flapjack.VarKind.local "pi"])
  (Flapjack.Exp.const 1#64)) body682_3 body682_4

def body682_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_twist"
  [Flapjack.Exp.var Flapjack.VarKind.local "Q", Flapjack.Exp.var Flapjack.VarKind.local "q2"]

def body682_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_cast"
  [Flapjack.Exp.var Flapjack.VarKind.local "P", Flapjack.Exp.var Flapjack.VarKind.local "p1"]

def body682_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bn254_miller_raw"
  [Flapjack.Exp.var Flapjack.VarKind.local "fnum", Flapjack.Exp.var Flapjack.VarKind.local "fden",
    Flapjack.Exp.var Flapjack.VarKind.local "Q", Flapjack.Exp.var Flapjack.VarKind.local "P"]

def body682_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_inv"
  [Flapjack.Exp.var Flapjack.VarKind.local "fden", Flapjack.Exp.var Flapjack.VarKind.local "fden"]

def body682_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fnum", Flapjack.Exp.var Flapjack.VarKind.local "fnum",
    Flapjack.Exp.var Flapjack.VarKind.local "fden"]

def body682_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_pow_words"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "fnum",
    Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 44#64]

def body682_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body682_13 : Prog (BitVec 64) :=
.seq body682_12 body682_2

def body682_14 : Prog (BitVec 64) :=
.seq body682_11 body682_13

def body682_15 : Prog (BitVec 64) :=
.seq body682_10 body682_14

def body682_16 : Prog (BitVec 64) :=
.seq body682_9 body682_15

def body682_17 : Prog (BitVec 64) :=
.seq body682_8 body682_16

def body682_18 : Prog (BitVec 64) :=
.seq body682_7 body682_17

def body682_19 : Prog (BitVec 64) :=
.seq body682_6 body682_18

def body682_20 : Prog (BitVec 64) :=
.decCall ("fden") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 384#64]) body682_19

def body682_21 : Prog (BitVec 64) :=
.decCall ("fnum") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 384#64]) body682_20

def body682_22 : Prog (BitVec 64) :=
.decCall ("P") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 1152#64]) body682_21

def body682_23 : Prog (BitVec 64) :=
.decCall ("Q") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 1152#64]) body682_22

def body682_24 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body682_23

def body682_25 : Prog (BitVec 64) :=
.seq body682_5 body682_24

def body682_26 : Prog (BitVec 64) :=
.decCall ("pi") (Flapjack.Shape.one) ("ecp_is_inf") ([Flapjack.Exp.const 1#64, Flapjack.Exp.var Flapjack.VarKind.local "p1"]) body682_25

def body682_27 : Prog (BitVec 64) :=
.decCall ("qi") (Flapjack.Shape.one) ("ecp_is_inf") ([Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "q2"]) body682_26

def body682_28 : Prog (BitVec 64) :=
.seq body682_0 body682_27

def body682_29 : Prog (BitVec 64) :=
.seq body682_6 body682_7

def body682_30 : Prog (BitVec 64) :=
.seq body682_29 body682_8

def body682_31 : Prog (BitVec 64) :=
.seq body682_30 body682_9

def body682_32 : Prog (BitVec 64) :=
.seq body682_31 body682_10

def body682_33 : Prog (BitVec 64) :=
.seq body682_32 body682_11

def body682_34 : Prog (BitVec 64) :=
.seq body682_33 body682_12

def body682_35 : Prog (BitVec 64) :=
.seq body682_34 body682_2

def body682_36 : Prog (BitVec 64) :=
.decCall ("fden") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 384#64]) body682_35

def body682_37 : Prog (BitVec 64) :=
.decCall ("fnum") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 384#64]) body682_36

def body682_38 : Prog (BitVec 64) :=
.decCall ("P") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 1152#64]) body682_37

def body682_39 : Prog (BitVec 64) :=
.decCall ("Q") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 1152#64]) body682_38

def body682_40 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body682_39

def body682_41 : Prog (BitVec 64) :=
.seq body682_5 body682_40

def body682_42 : Prog (BitVec 64) :=
.decCall ("pi") (Flapjack.Shape.one) ("ecp_is_inf") ([Flapjack.Exp.const 1#64, Flapjack.Exp.var Flapjack.VarKind.local "p1"]) body682_41

def body682_43 : Prog (BitVec 64) :=
.decCall ("qi") (Flapjack.Shape.one) ("ecp_is_inf") ([Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "q2"]) body682_42

def body682_44 : Prog (BitVec 64) :=
.seq body682_0 body682_43

def originalData682 : Decl (BitVec 64) :=
.function { name := "bn254_pairing", inline := false, exported := false, params := [("out", Flapjack.Shape.one), ("q2", Flapjack.Shape.one), ("p1", Flapjack.Shape.one)], body := body682_28, returnShape := (Flapjack.Shape.one) }
def simplifiedData682 : Decl (BitVec 64) :=
.function { name := "bn254_pairing", inline := false, exported := false, params := [("out", Flapjack.Shape.one), ("q2", Flapjack.Shape.one), ("p1", Flapjack.Shape.one)], body := body682_44, returnShape := (Flapjack.Shape.one) }
def original682 := Pancake.PanLang.declToHOL originalData682
def simplified682 := Pancake.PanLang.declToHOL simplifiedData682
end InitECandidate.Proofs.FrontendStages.Declarations
