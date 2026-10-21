import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data519
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate503
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody519_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 3#64]

def globalBody519_1 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 10#64)

def globalBody519_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody519_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 81#64) (Flapjack.Exp.var Flapjack.VarKind.local "imm")),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "imm") (Flapjack.Exp.const 128#64))]) globalBody519_1 globalBody519_2

def globalBody519_4 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "n"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 1#64])

def globalBody519_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "m"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 1#64])

def globalBody519_6 : Prog (BitVec 64) :=
.seq globalBody519_4 globalBody519_5

def globalBody519_7 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "n"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 1#64])

def globalBody519_8 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "m"
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.const 29#64, Flapjack.Exp.var Flapjack.VarKind.local "q"])

def globalBody519_9 : Prog (BitVec 64) :=
.seq globalBody519_7 globalBody519_8

def globalBody519_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "q")
  (Flapjack.Exp.var Flapjack.VarKind.local "r")) globalBody519_6 globalBody519_9

def globalBody519_11 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 2#64)

def globalBody519_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
        Flapjack.Exp.const 16#64]))
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "mx", Flapjack.Exp.const 1#64])) globalBody519_11 globalBody519_2

def globalBody519_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_swap_positions"
  [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "m"]

def globalBody519_14 : Prog (BitVec 64) :=
.seq globalBody519_12 globalBody519_13

def globalBody519_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 2#64]

def globalBody519_16 : Prog (BitVec 64) :=
.seq globalBody519_14 globalBody519_15

def globalBody519_17 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody519_18 : Prog (BitVec 64) :=
.seq globalBody519_16 globalBody519_17

def globalBody519_19 : Prog (BitVec 64) :=
.decCall ("mx") (Flapjack.Shape.one) ("max") ([Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "m"]) globalBody519_18

def globalBody519_20 : Prog (BitVec 64) :=
.seq globalBody519_10 globalBody519_19

def globalBody519_21 : Prog (BitVec 64) :=
.dec ("m") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody519_20

def globalBody519_22 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody519_21

def globalBody519_23 : Prog (BitVec 64) :=
.dec ("r") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 15#64]) globalBody519_22

def globalBody519_24 : Prog (BitVec 64) :=
.dec ("q") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 4#64)) globalBody519_23

def globalBody519_25 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.xor [Flapjack.Exp.var Flapjack.VarKind.local "imm", Flapjack.Exp.const 143#64]) globalBody519_24

def globalBody519_26 : Prog (BitVec 64) :=
.seq globalBody519_3 globalBody519_25

def globalBody519_27 : Prog (BitVec 64) :=
.decCall ("imm") (Flapjack.Shape.one) ("code_imm") ([]) globalBody519_26

def globalBody519_28 : Prog (BitVec 64) :=
.seq globalBody519_0 globalBody519_27

def globalData519 : Decl (BitVec 64) :=
.function { name := "op_exchange", inline := false, exported := false, params := [], body := globalBody519_28, returnShape := (Flapjack.Shape.one) }
def globalOutput519 := Pancake.PanLang.declToHOL globalData519
end InitECandidate.Proofs.FrontendStages.Declarations
