import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data492
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate476
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody492_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 3#64]

def globalBody492_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push"
  [Flapjack.Exp.rStruct
      [Flapjack.Exp.op Flapjack.BinOp.xor
          [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "x"),
            Flapjack.Exp.const 18446744073709551615#64],
        Flapjack.Exp.op Flapjack.BinOp.xor
          [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "x"),
            Flapjack.Exp.const 18446744073709551615#64],
        Flapjack.Exp.op Flapjack.BinOp.xor
          [Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "x"),
            Flapjack.Exp.const 18446744073709551615#64],
        Flapjack.Exp.op Flapjack.BinOp.xor
          [Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "x"),
            Flapjack.Exp.const 18446744073709551615#64]]]

def globalBody492_2 : Prog (BitVec 64) :=
.seq globalBody492_0 globalBody492_1

def globalBody492_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def globalBody492_4 : Prog (BitVec 64) :=
.seq globalBody492_2 globalBody492_3

def globalBody492_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody492_6 : Prog (BitVec 64) :=
.seq globalBody492_4 globalBody492_5

def globalBody492_7 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody492_6

def globalData492 : Decl (BitVec 64) :=
.function { name := "op_not", inline := false, exported := false, params := [], body := globalBody492_7, returnShape := (Flapjack.Shape.one) }
def globalOutput492 := Pancake.PanLang.declToHOL globalData492
end InitECandidate.Proofs.FrontendStages.Declarations
