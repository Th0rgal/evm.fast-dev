import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data804
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate788
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody804_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody804_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def globalBody804_2 : Prog (BitVec 64) :=
.seq globalBody804_0 globalBody804_1

def globalBody804_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody804_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 0#64)) globalBody804_2 globalBody804_3

def globalBody804_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "map_fp_to_g1"
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "tv"]

def globalBody804_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_encode"
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "out"]

def globalBody804_7 : Prog (BitVec 64) :=
.seq globalBody804_5 globalBody804_6

def globalBody804_8 : Prog (BitVec 64) :=
.seq globalBody804_7 globalBody804_0

def globalBody804_9 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody804_10 : Prog (BitVec 64) :=
.seq globalBody804_8 globalBody804_9

def globalBody804_11 : Prog (BitVec 64) :=
.dec ("tv") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "t")) globalBody804_10

def globalBody804_12 : Prog (BitVec 64) :=
.seq globalBody804_4 globalBody804_11

def globalBody804_13 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("bls_fp_decode64") ([Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.var Flapjack.VarKind.local "t"]) globalBody804_12

def globalBody804_14 : Prog (BitVec 64) :=
.decCall ("p") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) globalBody804_13

def globalBody804_15 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 48#64]) globalBody804_14

def globalBody804_16 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody804_15

def globalData804 : Decl (BitVec 64) :=
.function { name := "bls_map_fp_to_g1_exec", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := globalBody804_16, returnShape := (Flapjack.Shape.one) }
def globalOutput804 := Pancake.PanLang.declToHOL globalData804
end InitECandidate.Proofs.FrontendStages.Declarations
