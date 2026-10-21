import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify535
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body551_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 20#64]

def body551_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push"
  [Flapjack.Exp.rStruct
      [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]]

def body551_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body551_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body551_4 : Prog (BitVec 64) :=
.seq body551_2 body551_3

def body551_5 : Prog (BitVec 64) :=
.seq body551_1 body551_4

def body551_6 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body551_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "b")
        (Flapjack.Exp.var Flapjack.VarKind.local "current"),
      Flapjack.Exp.cmp Flapjack.Cmp.lower
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.const 256#64])
        (Flapjack.Exp.var Flapjack.VarKind.local "current"),
      Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "b")
        (Flapjack.Exp.const 18446744073709551615#64)])) body551_5 body551_6

def body551_8 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 50#64)

def body551_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "n")
  (Flapjack.Exp.var Flapjack.VarKind.local "offset")) body551_8 body551_6

def body551_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "track_ancestor_access" [Flapjack.Exp.var Flapjack.VarKind.local "offset"]

def body551_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push" [Flapjack.Exp.var Flapjack.VarKind.local "h"]

def body551_12 : Prog (BitVec 64) :=
.seq body551_11 body551_4

def body551_13 : Prog (BitVec 64) :=
.seq body551_10 body551_12

def body551_14 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "benv", Flapjack.Exp.const 16#64]),
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.sub
            [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "offset"],
          Flapjack.Exp.const 32#64]],
  Flapjack.Exp.const 32#64]) body551_13

def body551_15 : Prog (BitVec 64) :=
.seq body551_9 body551_14

def body551_16 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "benv", Flapjack.Exp.const 24#64])) body551_15

def body551_17 : Prog (BitVec 64) :=
.dec ("offset") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "current", Flapjack.Exp.var Flapjack.VarKind.local "b"]) body551_16

def body551_18 : Prog (BitVec 64) :=
.seq body551_7 body551_17

def body551_19 : Prog (BitVec 64) :=
.decCall ("b") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "bn"]) body551_18

def body551_20 : Prog (BitVec 64) :=
.dec ("current") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "benv", Flapjack.Exp.const 40#64])) body551_19

def body551_21 : Prog (BitVec 64) :=
.decCall ("benv") (Flapjack.Shape.one) ("block_env") ([]) body551_20

def body551_22 : Prog (BitVec 64) :=
.seq body551_0 body551_21

def body551_23 : Prog (BitVec 64) :=
.decCall ("bn") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body551_22

def body551_24 : Prog (BitVec 64) :=
.seq body551_1 body551_2

def body551_25 : Prog (BitVec 64) :=
.seq body551_24 body551_3

def body551_26 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "b")
        (Flapjack.Exp.var Flapjack.VarKind.local "current"),
      Flapjack.Exp.cmp Flapjack.Cmp.lower
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.const 256#64])
        (Flapjack.Exp.var Flapjack.VarKind.local "current"),
      Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "b")
        (Flapjack.Exp.const 18446744073709551615#64)])) body551_25 body551_6

def body551_27 : Prog (BitVec 64) :=
.seq body551_10 body551_11

def body551_28 : Prog (BitVec 64) :=
.seq body551_27 body551_2

def body551_29 : Prog (BitVec 64) :=
.seq body551_28 body551_3

def body551_30 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "benv", Flapjack.Exp.const 16#64]),
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.sub
            [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "offset"],
          Flapjack.Exp.const 32#64]],
  Flapjack.Exp.const 32#64]) body551_29

def body551_31 : Prog (BitVec 64) :=
.seq body551_9 body551_30

def body551_32 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "benv", Flapjack.Exp.const 24#64])) body551_31

def body551_33 : Prog (BitVec 64) :=
.dec ("offset") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "current", Flapjack.Exp.var Flapjack.VarKind.local "b"]) body551_32

def body551_34 : Prog (BitVec 64) :=
.seq body551_26 body551_33

def body551_35 : Prog (BitVec 64) :=
.decCall ("b") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "bn"]) body551_34

def body551_36 : Prog (BitVec 64) :=
.dec ("current") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "benv", Flapjack.Exp.const 40#64])) body551_35

def body551_37 : Prog (BitVec 64) :=
.decCall ("benv") (Flapjack.Shape.one) ("block_env") ([]) body551_36

def body551_38 : Prog (BitVec 64) :=
.seq body551_0 body551_37

def body551_39 : Prog (BitVec 64) :=
.decCall ("bn") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body551_38

def originalData551 : Decl (BitVec 64) :=
.function { name := "op_blockhash", inline := false, exported := false, params := [], body := body551_23, returnShape := (Flapjack.Shape.one) }
def simplifiedData551 : Decl (BitVec 64) :=
.function { name := "op_blockhash", inline := false, exported := false, params := [], body := body551_39, returnShape := (Flapjack.Shape.one) }
def original551 := Pancake.PanLang.declToHOL originalData551
def simplified551 := Pancake.PanLang.declToHOL simplifiedData551
end InitECandidate.Proofs.FrontendStages.Declarations
