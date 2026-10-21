import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify766
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body782_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "rp", Flapjack.Exp.var Flapjack.VarKind.local "q"]

def body782_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rp", Flapjack.Exp.const 96#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 96#64]]

def body782_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_set_one"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rp", Flapjack.Exp.const 192#64]]

def body782_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_set_one" [Flapjack.Exp.var Flapjack.VarKind.local "f"]

def body782_4 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body782_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "f", Flapjack.Exp.var Flapjack.VarKind.local "f",
    Flapjack.Exp.var Flapjack.VarKind.local "f"]

def body782_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pair_doubling_step"
  [Flapjack.Exp.var Flapjack.VarKind.local "rp", Flapjack.Exp.var Flapjack.VarKind.local "co"]

def body782_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pair_ell"
  [Flapjack.Exp.var Flapjack.VarKind.local "f", Flapjack.Exp.var Flapjack.VarKind.local "co",
    Flapjack.Exp.var Flapjack.VarKind.local "px", Flapjack.Exp.var Flapjack.VarKind.local "py"]

def body782_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pair_addition_step"
  [Flapjack.Exp.var Flapjack.VarKind.local "rp", Flapjack.Exp.var Flapjack.VarKind.local "q",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 96#64],
    Flapjack.Exp.var Flapjack.VarKind.local "co"]

def body782_9 : Prog (BitVec 64) :=
.seq body782_8 body782_7

def body782_10 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body782_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "x")
        (Flapjack.Exp.var Flapjack.VarKind.local "i"),
      Flapjack.Exp.const 1#64])
  (Flapjack.Exp.const 1#64)) body782_9 body782_10

def body782_12 : Prog (BitVec 64) :=
.seq body782_7 body782_11

def body782_13 : Prog (BitVec 64) :=
.seq body782_6 body782_12

def body782_14 : Prog (BitVec 64) :=
.seq body782_5 body782_13

def body782_15 : Prog (BitVec 64) :=
.seq body782_4 body782_14

def body782_16 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "i")) body782_15

def body782_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_conj"
  [Flapjack.Exp.var Flapjack.VarKind.local "f", Flapjack.Exp.var Flapjack.VarKind.local "f"]

def body782_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body782_19 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body782_20 : Prog (BitVec 64) :=
.seq body782_18 body782_19

def body782_21 : Prog (BitVec 64) :=
.seq body782_17 body782_20

def body782_22 : Prog (BitVec 64) :=
.seq body782_16 body782_21

def body782_23 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 63#64) body782_22

def body782_24 : Prog (BitVec 64) :=
.dec ("x") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 1376#64])) body782_23

def body782_25 : Prog (BitVec 64) :=
.seq body782_3 body782_24

def body782_26 : Prog (BitVec 64) :=
.seq body782_2 body782_25

def body782_27 : Prog (BitVec 64) :=
.seq body782_1 body782_26

def body782_28 : Prog (BitVec 64) :=
.seq body782_0 body782_27

def body782_29 : Prog (BitVec 64) :=
.decCall ("co") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 96#64, Flapjack.Exp.const 3#64]]) body782_28

def body782_30 : Prog (BitVec 64) :=
.decCall ("rp") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) body782_29

def body782_31 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body782_30

def body782_32 : Prog (BitVec 64) :=
.seq body782_0 body782_1

def body782_33 : Prog (BitVec 64) :=
.seq body782_32 body782_2

def body782_34 : Prog (BitVec 64) :=
.seq body782_33 body782_3

def body782_35 : Prog (BitVec 64) :=
.seq body782_4 body782_5

def body782_36 : Prog (BitVec 64) :=
.seq body782_35 body782_6

def body782_37 : Prog (BitVec 64) :=
.seq body782_36 body782_7

def body782_38 : Prog (BitVec 64) :=
.seq body782_37 body782_11

def body782_39 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "i")) body782_38

def body782_40 : Prog (BitVec 64) :=
.seq body782_39 body782_17

def body782_41 : Prog (BitVec 64) :=
.seq body782_40 body782_18

def body782_42 : Prog (BitVec 64) :=
.seq body782_41 body782_19

def body782_43 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 63#64) body782_42

def body782_44 : Prog (BitVec 64) :=
.dec ("x") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 1376#64])) body782_43

def body782_45 : Prog (BitVec 64) :=
.seq body782_34 body782_44

def body782_46 : Prog (BitVec 64) :=
.decCall ("co") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 96#64, Flapjack.Exp.const 3#64]]) body782_45

def body782_47 : Prog (BitVec 64) :=
.decCall ("rp") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) body782_46

def body782_48 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body782_47

def originalData782 : Decl (BitVec 64) :=
.function { name := "pair_miller_loop", inline := false, exported := false, params := [("f", Flapjack.Shape.one),
  ("px",
    Flapjack.Shape.comb
      [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
        Flapjack.Shape.one]),
  ("py",
    Flapjack.Shape.comb
      [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
        Flapjack.Shape.one]),
  ("q", Flapjack.Shape.one)], body := body782_31, returnShape := (Flapjack.Shape.one) }
def simplifiedData782 : Decl (BitVec 64) :=
.function { name := "pair_miller_loop", inline := false, exported := false, params := [("f", Flapjack.Shape.one),
  ("px",
    Flapjack.Shape.comb
      [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
        Flapjack.Shape.one]),
  ("py",
    Flapjack.Shape.comb
      [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
        Flapjack.Shape.one]),
  ("q", Flapjack.Shape.one)], body := body782_48, returnShape := (Flapjack.Shape.one) }
def original782 := Pancake.PanLang.declToHOL originalData782
def simplified782 := Pancake.PanLang.declToHOL simplifiedData782
end InitECandidate.Proofs.FrontendStages.Declarations
