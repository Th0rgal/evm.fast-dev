import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data446
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate425
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody446_0 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 72#64])
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "sgl", Flapjack.Exp.var Flapjack.VarKind.local "amount"])

def globalBody446_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody446_2 : Prog (BitVec 64) :=
.seq globalBody446_0 globalBody446_1

def globalBody446_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody446_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "sgl")
  (Flapjack.Exp.var Flapjack.VarKind.local "amount")) globalBody446_2 globalBody446_3

def globalBody446_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 72#64])
  (Flapjack.Exp.const 0#64)

def globalBody446_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 64#64])
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "gl", Flapjack.Exp.var Flapjack.VarKind.local "rem"])

def globalBody446_7 : Prog (BitVec 64) :=
.seq globalBody446_5 globalBody446_6

def globalBody446_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 192#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.load Flapjack.Shape.one
              (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
            Flapjack.Exp.const 192#64]),
      Flapjack.Exp.var Flapjack.VarKind.local "rem"])

def globalBody446_9 : Prog (BitVec 64) :=
.seq globalBody446_7 globalBody446_8

def globalBody446_10 : Prog (BitVec 64) :=
.seq globalBody446_9 globalBody446_1

def globalBody446_11 : Prog (BitVec 64) :=
.dec ("rem") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "amount", Flapjack.Exp.var Flapjack.VarKind.local "sgl"]) globalBody446_10

def globalBody446_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "tot")
  (Flapjack.Exp.var Flapjack.VarKind.local "amount")) globalBody446_11 globalBody446_3

def globalBody446_13 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 4#64)

def globalBody446_14 : Prog (BitVec 64) :=
.seq globalBody446_12 globalBody446_13

def globalBody446_15 : Prog (BitVec 64) :=
.seq globalBody446_14 globalBody446_1

def globalBody446_16 : Prog (BitVec 64) :=
.decCall ("tot") (Flapjack.Shape.one) ("add_sat") ([Flapjack.Exp.var Flapjack.VarKind.local "sgl", Flapjack.Exp.var Flapjack.VarKind.local "gl"]) globalBody446_15

def globalBody446_17 : Prog (BitVec 64) :=
.seq globalBody446_4 globalBody446_16

def globalBody446_18 : Prog (BitVec 64) :=
.dec ("gl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 64#64])) globalBody446_17

def globalBody446_19 : Prog (BitVec 64) :=
.dec ("sgl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 72#64])) globalBody446_18

def globalData446 : Decl (BitVec 64) :=
.function { name := "charge_state_gas", inline := false, exported := false, params := [("amount", Flapjack.Shape.one)], body := globalBody446_19, returnShape := (Flapjack.Shape.one) }
def globalOutput446 := Pancake.PanLang.declToHOL globalData446
end InitECandidate.Proofs.FrontendStages.Declarations
