import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify639
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body655_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "e"
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 1#64])

def body655_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "c0"), none)) "fq_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "c0", Flapjack.Exp.var Flapjack.VarKind.local "t82"]

def body655_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 32#64]])
  (Flapjack.Exp.var Flapjack.VarKind.local "c0")

def body655_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "c6"), none)) "fq_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "c6", Flapjack.Exp.var Flapjack.VarKind.local "t18"]

def body655_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t",
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 6#64],
          Flapjack.Exp.const 32#64]])
  (Flapjack.Exp.var Flapjack.VarKind.local "c6")

def body655_5 : Prog (BitVec 64) :=
.seq body655_3 body655_4

def body655_6 : Prog (BitVec 64) :=
.dec ("c6") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t",
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 6#64],
          Flapjack.Exp.const 32#64]])) body655_5

def body655_7 : Prog (BitVec 64) :=
.seq body655_2 body655_6

def body655_8 : Prog (BitVec 64) :=
.seq body655_1 body655_7

def body655_9 : Prog (BitVec 64) :=
.dec ("c0") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 32#64]])) body655_8

def body655_10 : Prog (BitVec 64) :=
.decCall ("t18") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_mul_small") ([Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 18#64]) body655_9

def body655_11 : Prog (BitVec 64) :=
.decCall ("t82") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_mul_small") ([Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 82#64]) body655_10

def body655_12 : Prog (BitVec 64) :=
.dec ("top") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t",
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 12#64],
          Flapjack.Exp.const 32#64]])) body655_11

def body655_13 : Prog (BitVec 64) :=
.seq body655_0 body655_12

def body655_14 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "e")) body655_13

def body655_15 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body655_16 : Prog (BitVec 64) :=
.seq body655_14 body655_15

def body655_17 : Prog (BitVec 64) :=
.dec ("e") (Flapjack.Shape.one) (Flapjack.Exp.const 11#64) body655_16

def body655_18 : Prog (BitVec 64) :=
.seq body655_1 body655_2

def body655_19 : Prog (BitVec 64) :=
.seq body655_18 body655_6

def body655_20 : Prog (BitVec 64) :=
.dec ("c0") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 32#64]])) body655_19

def body655_21 : Prog (BitVec 64) :=
.decCall ("t18") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_mul_small") ([Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 18#64]) body655_20

def body655_22 : Prog (BitVec 64) :=
.decCall ("t82") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_mul_small") ([Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 82#64]) body655_21

def body655_23 : Prog (BitVec 64) :=
.dec ("top") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t",
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 12#64],
          Flapjack.Exp.const 32#64]])) body655_22

def body655_24 : Prog (BitVec 64) :=
.seq body655_0 body655_23

def body655_25 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "e")) body655_24

def body655_26 : Prog (BitVec 64) :=
.seq body655_25 body655_15

def body655_27 : Prog (BitVec 64) :=
.dec ("e") (Flapjack.Shape.one) (Flapjack.Exp.const 11#64) body655_26

def originalData655 : Decl (BitVec 64) :=
.function { name := "fq12_reduce", inline := false, exported := false, params := [("t", Flapjack.Shape.one)], body := body655_17, returnShape := (Flapjack.Shape.one) }
def simplifiedData655 : Decl (BitVec 64) :=
.function { name := "fq12_reduce", inline := false, exported := false, params := [("t", Flapjack.Shape.one)], body := body655_27, returnShape := (Flapjack.Shape.one) }
def original655 := Pancake.PanLang.declToHOL originalData655
def simplified655 := Pancake.PanLang.declToHOL simplifiedData655
end InitECandidate.Proofs.FrontendStages.Declarations
