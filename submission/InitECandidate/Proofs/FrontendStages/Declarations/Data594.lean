import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify578
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body594_0 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "buf") (Flapjack.Exp.const 255#64)

def body594_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 1#64],
    Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 20#64]

def body594_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 21#64],
    Flapjack.Exp.var Flapjack.VarKind.local "salt", Flapjack.Exp.const 32#64]

def body594_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.var Flapjack.VarKind.local "code", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 53#64]]

def body594_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 85#64, Flapjack.Exp.var Flapjack.VarKind.local "h"]

def body594_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "out",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 12#64],
    Flapjack.Exp.const 20#64]

def body594_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body594_7 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body594_8 : Prog (BitVec 64) :=
.seq body594_6 body594_7

def body594_9 : Prog (BitVec 64) :=
.seq body594_5 body594_8

def body594_10 : Prog (BitVec 64) :=
.seq body594_4 body594_9

def body594_11 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body594_10

def body594_12 : Prog (BitVec 64) :=
.seq body594_3 body594_11

def body594_13 : Prog (BitVec 64) :=
.seq body594_2 body594_12

def body594_14 : Prog (BitVec 64) :=
.seq body594_1 body594_13

def body594_15 : Prog (BitVec 64) :=
.seq body594_0 body594_14

def body594_16 : Prog (BitVec 64) :=
.decCall ("buf") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body594_15

def body594_17 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body594_16

def body594_18 : Prog (BitVec 64) :=
.seq body594_0 body594_1

def body594_19 : Prog (BitVec 64) :=
.seq body594_18 body594_2

def body594_20 : Prog (BitVec 64) :=
.seq body594_19 body594_3

def body594_21 : Prog (BitVec 64) :=
.seq body594_4 body594_5

def body594_22 : Prog (BitVec 64) :=
.seq body594_21 body594_6

def body594_23 : Prog (BitVec 64) :=
.seq body594_22 body594_7

def body594_24 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body594_23

def body594_25 : Prog (BitVec 64) :=
.seq body594_20 body594_24

def body594_26 : Prog (BitVec 64) :=
.decCall ("buf") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body594_25

def body594_27 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body594_26

def originalData594 : Decl (BitVec 64) :=
.function { name := "compute_create2_contract_address", inline := false, exported := false, params := [("addr", Flapjack.Shape.one), ("salt", Flapjack.Shape.one), ("code", Flapjack.Shape.one), ("n", Flapjack.Shape.one),
  ("out", Flapjack.Shape.one)], body := body594_17, returnShape := (Flapjack.Shape.one) }
def simplifiedData594 : Decl (BitVec 64) :=
.function { name := "compute_create2_contract_address", inline := false, exported := false, params := [("addr", Flapjack.Shape.one), ("salt", Flapjack.Shape.one), ("code", Flapjack.Shape.one), ("n", Flapjack.Shape.one),
  ("out", Flapjack.Shape.one)], body := body594_27, returnShape := (Flapjack.Shape.one) }
def original594 := Pancake.PanLang.declToHOL originalData594
def simplified594 := Pancake.PanLang.declToHOL simplifiedData594
end InitECandidate.Proofs.FrontendStages.Declarations
