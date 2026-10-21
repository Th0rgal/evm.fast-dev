import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data682
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate666
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody682_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bn254_init" []

def globalBody682_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_set_one"
  [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "out"]

def globalBody682_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody682_3 : Prog (BitVec 64) :=
.seq globalBody682_1 globalBody682_2

def globalBody682_4 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody682_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.var Flapjack.VarKind.local "qi", Flapjack.Exp.var Flapjack.VarKind.local "pi"])
  (Flapjack.Exp.const 1#64)) globalBody682_3 globalBody682_4

def globalBody682_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_twist"
  [Flapjack.Exp.var Flapjack.VarKind.local "Q", Flapjack.Exp.var Flapjack.VarKind.local "q2"]

def globalBody682_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_cast"
  [Flapjack.Exp.var Flapjack.VarKind.local "P", Flapjack.Exp.var Flapjack.VarKind.local "p1"]

def globalBody682_8 : Prog (BitVec 64) :=
.seq globalBody682_6 globalBody682_7

def globalBody682_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bn254_miller_raw"
  [Flapjack.Exp.var Flapjack.VarKind.local "fnum", Flapjack.Exp.var Flapjack.VarKind.local "fden",
    Flapjack.Exp.var Flapjack.VarKind.local "Q", Flapjack.Exp.var Flapjack.VarKind.local "P"]

def globalBody682_10 : Prog (BitVec 64) :=
.seq globalBody682_8 globalBody682_9

def globalBody682_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_inv"
  [Flapjack.Exp.var Flapjack.VarKind.local "fden", Flapjack.Exp.var Flapjack.VarKind.local "fden"]

def globalBody682_12 : Prog (BitVec 64) :=
.seq globalBody682_10 globalBody682_11

def globalBody682_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fnum", Flapjack.Exp.var Flapjack.VarKind.local "fnum",
    Flapjack.Exp.var Flapjack.VarKind.local "fden"]

def globalBody682_14 : Prog (BitVec 64) :=
.seq globalBody682_12 globalBody682_13

def globalBody682_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_pow_words"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "fnum",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
    Flapjack.Exp.const 44#64]

def globalBody682_16 : Prog (BitVec 64) :=
.seq globalBody682_14 globalBody682_15

def globalBody682_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody682_18 : Prog (BitVec 64) :=
.seq globalBody682_16 globalBody682_17

def globalBody682_19 : Prog (BitVec 64) :=
.seq globalBody682_18 globalBody682_2

def globalBody682_20 : Prog (BitVec 64) :=
.decCall ("fden") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 384#64]) globalBody682_19

def globalBody682_21 : Prog (BitVec 64) :=
.decCall ("fnum") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 384#64]) globalBody682_20

def globalBody682_22 : Prog (BitVec 64) :=
.decCall ("P") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 1152#64]) globalBody682_21

def globalBody682_23 : Prog (BitVec 64) :=
.decCall ("Q") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 1152#64]) globalBody682_22

def globalBody682_24 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody682_23

def globalBody682_25 : Prog (BitVec 64) :=
.seq globalBody682_5 globalBody682_24

def globalBody682_26 : Prog (BitVec 64) :=
.decCall ("pi") (Flapjack.Shape.one) ("ecp_is_inf") ([Flapjack.Exp.const 1#64, Flapjack.Exp.var Flapjack.VarKind.local "p1"]) globalBody682_25

def globalBody682_27 : Prog (BitVec 64) :=
.decCall ("qi") (Flapjack.Shape.one) ("ecp_is_inf") ([Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "q2"]) globalBody682_26

def globalBody682_28 : Prog (BitVec 64) :=
.seq globalBody682_0 globalBody682_27

def globalData682 : Decl (BitVec 64) :=
.function { name := "bn254_pairing", inline := false, exported := false, params := [("out", Flapjack.Shape.one), ("q2", Flapjack.Shape.one), ("p1", Flapjack.Shape.one)], body := globalBody682_28, returnShape := (Flapjack.Shape.one) }
def globalOutput682 := Pancake.PanLang.declToHOL globalData682
end InitECandidate.Proofs.FrontendStages.Declarations
