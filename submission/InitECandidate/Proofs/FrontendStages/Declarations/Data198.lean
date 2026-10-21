import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify182
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body198_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body198_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body198_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 0#64)) body198_0 body198_1

def body198_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_fail" [Flapjack.Exp.const 10#64]

def body198_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "o")
        (Flapjack.Exp.var Flapjack.VarKind.local "fixed"),
      Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "len")
        (Flapjack.Exp.var Flapjack.VarKind.local "o")])) body198_3 body198_1

def body198_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_fail" [Flapjack.Exp.const 11#64]

def body198_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "o")
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "offs",
            Flapjack.Exp.panOp Flapjack.PanOp.mul
              [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]],
        Flapjack.Exp.const 8#64]))) body198_5 body198_1

def body198_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "i")) body198_6 body198_1

def body198_8 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body198_9 : Prog (BitVec 64) :=
.seq body198_7 body198_8

def body198_10 : Prog (BitVec 64) :=
.seq body198_4 body198_9

def body198_11 : Prog (BitVec 64) :=
.dec ("o") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "offs",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]])) body198_10

def body198_12 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body198_11

def body198_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_fail" [Flapjack.Exp.const 12#64]

def body198_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "offs"))
  (Flapjack.Exp.var Flapjack.VarKind.local "fixed")) body198_13 body198_1

def body198_15 : Prog (BitVec 64) :=
.seq body198_14 body198_0

def body198_16 : Prog (BitVec 64) :=
.seq body198_12 body198_15

def body198_17 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body198_16

def body198_18 : Prog (BitVec 64) :=
.seq body198_2 body198_17

def body198_19 : Prog (BitVec 64) :=
.seq body198_4 body198_7

def body198_20 : Prog (BitVec 64) :=
.seq body198_19 body198_8

def body198_21 : Prog (BitVec 64) :=
.dec ("o") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "offs",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]])) body198_20

def body198_22 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body198_21

def body198_23 : Prog (BitVec 64) :=
.seq body198_22 body198_14

def body198_24 : Prog (BitVec 64) :=
.seq body198_23 body198_0

def body198_25 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body198_24

def body198_26 : Prog (BitVec 64) :=
.seq body198_2 body198_25

def originalData198 : Decl (BitVec 64) :=
.function { name := "ssz_check_offsets", inline := false, exported := false, params := [("offs", Flapjack.Shape.one), ("n", Flapjack.Shape.one), ("fixed", Flapjack.Shape.one), ("len", Flapjack.Shape.one)], body := body198_18, returnShape := (Flapjack.Shape.one) }
def simplifiedData198 : Decl (BitVec 64) :=
.function { name := "ssz_check_offsets", inline := false, exported := false, params := [("offs", Flapjack.Shape.one), ("n", Flapjack.Shape.one), ("fixed", Flapjack.Shape.one), ("len", Flapjack.Shape.one)], body := body198_26, returnShape := (Flapjack.Shape.one) }
def original198 := Pancake.PanLang.declToHOL originalData198
def simplified198 := Pancake.PanLang.declToHOL simplifiedData198
end InitECandidate.Proofs.FrontendStages.Declarations
