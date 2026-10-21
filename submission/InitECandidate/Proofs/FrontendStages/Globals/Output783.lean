import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data783
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate767
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody783_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody783_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody783_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ip") (Flapjack.Exp.const 1#64)) globalBody783_0 globalBody783_1

def globalBody783_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "iq") (Flapjack.Exp.const 1#64)) globalBody783_0 globalBody783_1

def globalBody783_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_normalize"
  [Flapjack.Exp.var Flapjack.VarKind.local "pa", Flapjack.Exp.var Flapjack.VarKind.local "p"]

def globalBody783_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_normalize"
  [Flapjack.Exp.var Flapjack.VarKind.local "qa", Flapjack.Exp.var Flapjack.VarKind.local "q"]

def globalBody783_6 : Prog (BitVec 64) :=
.seq globalBody783_4 globalBody783_5

def globalBody783_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pair_miller_loop"
  [Flapjack.Exp.var Flapjack.VarKind.local "f", Flapjack.Exp.var Flapjack.VarKind.local "px",
    Flapjack.Exp.var Flapjack.VarKind.local "py", Flapjack.Exp.var Flapjack.VarKind.local "qa"]

def globalBody783_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "acc",
    Flapjack.Exp.var Flapjack.VarKind.local "f"]

def globalBody783_9 : Prog (BitVec 64) :=
.seq globalBody783_7 globalBody783_8

def globalBody783_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody783_11 : Prog (BitVec 64) :=
.seq globalBody783_9 globalBody783_10

def globalBody783_12 : Prog (BitVec 64) :=
.seq globalBody783_11 globalBody783_0

def globalBody783_13 : Prog (BitVec 64) :=
.dec ("py") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pa", Flapjack.Exp.const 48#64])) globalBody783_12

def globalBody783_14 : Prog (BitVec 64) :=
.dec ("px") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "pa")) globalBody783_13

def globalBody783_15 : Prog (BitVec 64) :=
.seq globalBody783_6 globalBody783_14

def globalBody783_16 : Prog (BitVec 64) :=
.decCall ("f") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 576#64]) globalBody783_15

def globalBody783_17 : Prog (BitVec 64) :=
.decCall ("qa") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 192#64]) globalBody783_16

def globalBody783_18 : Prog (BitVec 64) :=
.decCall ("pa") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) globalBody783_17

def globalBody783_19 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody783_18

def globalBody783_20 : Prog (BitVec 64) :=
.seq globalBody783_3 globalBody783_19

def globalBody783_21 : Prog (BitVec 64) :=
.decCall ("iq") (Flapjack.Shape.one) ("g2_is_inf") ([Flapjack.Exp.var Flapjack.VarKind.local "q"]) globalBody783_20

def globalBody783_22 : Prog (BitVec 64) :=
.seq globalBody783_2 globalBody783_21

def globalBody783_23 : Prog (BitVec 64) :=
.decCall ("ip") (Flapjack.Shape.one) ("g1_is_inf") ([Flapjack.Exp.var Flapjack.VarKind.local "p"]) globalBody783_22

def globalData783 : Decl (BitVec 64) :=
.function { name := "pair_accumulate", inline := false, exported := false, params := [("acc", Flapjack.Shape.one), ("p", Flapjack.Shape.one), ("q", Flapjack.Shape.one)], body := globalBody783_23, returnShape := (Flapjack.Shape.one) }
def globalOutput783 := Pancake.PanLang.declToHOL globalData783
end InitECandidate.Proofs.FrontendStages.Declarations
