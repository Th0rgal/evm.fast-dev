import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data551
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate535
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody551_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 20#64]

def globalBody551_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push"
  [Flapjack.Exp.rStruct
      [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]]

def globalBody551_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def globalBody551_3 : Prog (BitVec 64) :=
.seq globalBody551_1 globalBody551_2

def globalBody551_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody551_5 : Prog (BitVec 64) :=
.seq globalBody551_3 globalBody551_4

def globalBody551_6 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody551_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "b")
        (Flapjack.Exp.var Flapjack.VarKind.local "current"),
      Flapjack.Exp.cmp Flapjack.Cmp.lower
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.const 256#64])
        (Flapjack.Exp.var Flapjack.VarKind.local "current"),
      Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "b")
        (Flapjack.Exp.const 18446744073709551615#64)])) globalBody551_5 globalBody551_6

def globalBody551_8 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 50#64)

def globalBody551_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "n")
  (Flapjack.Exp.var Flapjack.VarKind.local "offset")) globalBody551_8 globalBody551_6

def globalBody551_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "track_ancestor_access" [Flapjack.Exp.var Flapjack.VarKind.local "offset"]

def globalBody551_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push" [Flapjack.Exp.var Flapjack.VarKind.local "h"]

def globalBody551_12 : Prog (BitVec 64) :=
.seq globalBody551_10 globalBody551_11

def globalBody551_13 : Prog (BitVec 64) :=
.seq globalBody551_12 globalBody551_2

def globalBody551_14 : Prog (BitVec 64) :=
.seq globalBody551_13 globalBody551_4

def globalBody551_15 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "benv", Flapjack.Exp.const 16#64]),
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.sub
            [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "offset"],
          Flapjack.Exp.const 32#64]],
  Flapjack.Exp.const 32#64]) globalBody551_14

def globalBody551_16 : Prog (BitVec 64) :=
.seq globalBody551_9 globalBody551_15

def globalBody551_17 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "benv", Flapjack.Exp.const 24#64])) globalBody551_16

def globalBody551_18 : Prog (BitVec 64) :=
.dec ("offset") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "current", Flapjack.Exp.var Flapjack.VarKind.local "b"]) globalBody551_17

def globalBody551_19 : Prog (BitVec 64) :=
.seq globalBody551_7 globalBody551_18

def globalBody551_20 : Prog (BitVec 64) :=
.decCall ("b") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "bn"]) globalBody551_19

def globalBody551_21 : Prog (BitVec 64) :=
.dec ("current") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "benv", Flapjack.Exp.const 40#64])) globalBody551_20

def globalBody551_22 : Prog (BitVec 64) :=
.decCall ("benv") (Flapjack.Shape.one) ("block_env") ([]) globalBody551_21

def globalBody551_23 : Prog (BitVec 64) :=
.seq globalBody551_0 globalBody551_22

def globalBody551_24 : Prog (BitVec 64) :=
.decCall ("bn") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody551_23

def globalData551 : Decl (BitVec 64) :=
.function { name := "op_blockhash", inline := false, exported := false, params := [], body := globalBody551_24, returnShape := (Flapjack.Shape.one) }
def globalOutput551 := Pancake.PanLang.declToHOL globalData551
end InitECandidate.Proofs.FrontendStages.Declarations
