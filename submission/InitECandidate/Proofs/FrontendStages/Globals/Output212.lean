import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data212
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate196
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody212_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_bytes_vector"
  [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 20#64, Flapjack.Exp.var Flapjack.VarKind.local "ch"]

def globalBody212_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_bytes_vector"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 20#64],
    Flapjack.Exp.const 48#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 32#64]]

def globalBody212_2 : Prog (BitVec 64) :=
.seq globalBody212_0 globalBody212_1

def globalBody212_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "merkleize"
  [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 2#64, Flapjack.Exp.const 2#64,
    Flapjack.Exp.var Flapjack.VarKind.local "out"]

def globalBody212_4 : Prog (BitVec 64) :=
.seq globalBody212_2 globalBody212_3

def globalBody212_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody212_6 : Prog (BitVec 64) :=
.seq globalBody212_4 globalBody212_5

def globalBody212_7 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody212_8 : Prog (BitVec 64) :=
.seq globalBody212_6 globalBody212_7

def globalBody212_9 : Prog (BitVec 64) :=
.decCall ("ch") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.const 32#64]]) globalBody212_8

def globalBody212_10 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody212_9

def globalData212 : Decl (BitVec 64) :=
.function { name := "htr_bexit", inline := false, exported := false, params := [("e", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := globalBody212_10, returnShape := (Flapjack.Shape.one) }
def globalOutput212 := Pancake.PanLang.declToHOL globalData212
end InitECandidate.Proofs.FrontendStages.Declarations
