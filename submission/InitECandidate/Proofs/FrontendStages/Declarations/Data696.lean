import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify680
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body696_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body696_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body696_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "a"))
  (Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "b"))) body696_0 body696_1

def body696_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body696_4 : Prog (BitVec 64) :=
.seq body696_2 body696_3

def body696_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "a"))
  (Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "b"))) body696_4 body696_1

def body696_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "a"))
  (Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "b"))) body696_0 body696_1

def body696_7 : Prog (BitVec 64) :=
.seq body696_6 body696_3

def body696_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "a"))
  (Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "b"))) body696_7 body696_1

def body696_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "a"))
  (Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "b"))) body696_0 body696_1

def body696_10 : Prog (BitVec 64) :=
.seq body696_9 body696_3

def body696_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "a"))
  (Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "b"))) body696_10 body696_1

def body696_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "a"))
  (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "b"))) body696_0 body696_1

def body696_13 : Prog (BitVec 64) :=
.seq body696_12 body696_3

def body696_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "a"))
  (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "b"))) body696_13 body696_1

def body696_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "a"))
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "b"))) body696_0 body696_1

def body696_16 : Prog (BitVec 64) :=
.seq body696_15 body696_3

def body696_17 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "a"))
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "b"))) body696_16 body696_1

def body696_18 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "a"))
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "b"))) body696_0 body696_1

def body696_19 : Prog (BitVec 64) :=
.seq body696_18 body696_3

def body696_20 : Prog (BitVec 64) :=
.seq body696_17 body696_19

def body696_21 : Prog (BitVec 64) :=
.seq body696_14 body696_20

def body696_22 : Prog (BitVec 64) :=
.seq body696_11 body696_21

def body696_23 : Prog (BitVec 64) :=
.seq body696_8 body696_22

def body696_24 : Prog (BitVec 64) :=
.seq body696_5 body696_23

def body696_25 : Prog (BitVec 64) :=
.seq body696_5 body696_8

def body696_26 : Prog (BitVec 64) :=
.seq body696_25 body696_11

def body696_27 : Prog (BitVec 64) :=
.seq body696_26 body696_14

def body696_28 : Prog (BitVec 64) :=
.seq body696_27 body696_17

def body696_29 : Prog (BitVec 64) :=
.seq body696_28 body696_18

def body696_30 : Prog (BitVec 64) :=
.seq body696_29 body696_3

def originalData696 : Decl (BitVec 64) :=
.function { name := "bls_fp_lt_raw", inline := false, exported := false, params := [("a",
    Flapjack.Shape.comb
      [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
        Flapjack.Shape.one]),
  ("b",
    Flapjack.Shape.comb
      [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
        Flapjack.Shape.one])], body := body696_24, returnShape := (Flapjack.Shape.one) }
def simplifiedData696 : Decl (BitVec 64) :=
.function { name := "bls_fp_lt_raw", inline := false, exported := false, params := [("a",
    Flapjack.Shape.comb
      [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
        Flapjack.Shape.one]),
  ("b",
    Flapjack.Shape.comb
      [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
        Flapjack.Shape.one])], body := body696_30, returnShape := (Flapjack.Shape.one) }
def original696 := Pancake.PanLang.declToHOL originalData696
def simplified696 := Pancake.PanLang.declToHOL simplifiedData696
end InitECandidate.Proofs.FrontendStages.Declarations
