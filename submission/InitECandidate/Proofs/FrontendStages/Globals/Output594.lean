import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data594
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate578
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody594_0 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "buf") (Flapjack.Exp.const 255#64)

def globalBody594_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 1#64],
    Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 20#64]

def globalBody594_2 : Prog (BitVec 64) :=
.seq globalBody594_0 globalBody594_1

def globalBody594_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 21#64],
    Flapjack.Exp.var Flapjack.VarKind.local "salt", Flapjack.Exp.const 32#64]

def globalBody594_4 : Prog (BitVec 64) :=
.seq globalBody594_2 globalBody594_3

def globalBody594_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.var Flapjack.VarKind.local "code", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 53#64]]

def globalBody594_6 : Prog (BitVec 64) :=
.seq globalBody594_4 globalBody594_5

def globalBody594_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 85#64, Flapjack.Exp.var Flapjack.VarKind.local "h"]

def globalBody594_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "out",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 12#64],
    Flapjack.Exp.const 20#64]

def globalBody594_9 : Prog (BitVec 64) :=
.seq globalBody594_7 globalBody594_8

def globalBody594_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody594_11 : Prog (BitVec 64) :=
.seq globalBody594_9 globalBody594_10

def globalBody594_12 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody594_13 : Prog (BitVec 64) :=
.seq globalBody594_11 globalBody594_12

def globalBody594_14 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) globalBody594_13

def globalBody594_15 : Prog (BitVec 64) :=
.seq globalBody594_6 globalBody594_14

def globalBody594_16 : Prog (BitVec 64) :=
.decCall ("buf") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) globalBody594_15

def globalBody594_17 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody594_16

def globalData594 : Decl (BitVec 64) :=
.function { name := "compute_create2_contract_address", inline := false, exported := false, params := [("addr", Flapjack.Shape.one), ("salt", Flapjack.Shape.one), ("code", Flapjack.Shape.one), ("n", Flapjack.Shape.one),
  ("out", Flapjack.Shape.one)], body := globalBody594_17, returnShape := (Flapjack.Shape.one) }
def globalOutput594 := Pancake.PanLang.declToHOL globalData594
end InitECandidate.Proofs.FrontendStages.Declarations
