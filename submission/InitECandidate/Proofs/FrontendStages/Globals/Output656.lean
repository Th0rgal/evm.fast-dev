import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data656
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate638
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody656_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 11#64])

def globalBody656_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody656_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 11#64) (Flapjack.Exp.var Flapjack.VarKind.local "k")) globalBody656_0 globalBody656_1

def globalBody656_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "iend" (Flapjack.Exp.const 11#64)

def globalBody656_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 11#64) (Flapjack.Exp.var Flapjack.VarKind.local "iend")) globalBody656_3 globalBody656_1

def globalBody656_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "acc"), none)) "fq_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "p"]

def globalBody656_6 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody656_7 : Prog (BitVec 64) :=
.seq globalBody656_5 globalBody656_6

def globalBody656_8 : Prog (BitVec 64) :=
.decCall ("p") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("fq_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "ai", Flapjack.Exp.var Flapjack.VarKind.local "bj"]) globalBody656_7

def globalBody656_9 : Prog (BitVec 64) :=
.dec ("bj") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "b",
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.sub
            [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.var Flapjack.VarKind.local "i"],
          Flapjack.Exp.const 32#64]])) globalBody656_8

def globalBody656_10 : Prog (BitVec 64) :=
.dec ("ai") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "a",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 32#64]])) globalBody656_9

def globalBody656_11 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "iend")
  (Flapjack.Exp.var Flapjack.VarKind.local "i")) globalBody656_10

def globalBody656_12 : Prog (BitVec 64) :=
.seq globalBody656_4 globalBody656_11

def globalBody656_13 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "t",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 32#64]])
  (Flapjack.Exp.var Flapjack.VarKind.local "acc")

def globalBody656_14 : Prog (BitVec 64) :=
.seq globalBody656_12 globalBody656_13

def globalBody656_15 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "k"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 1#64])

def globalBody656_16 : Prog (BitVec 64) :=
.seq globalBody656_14 globalBody656_15

def globalBody656_17 : Prog (BitVec 64) :=
.dec ("iend") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "k") globalBody656_16

def globalBody656_18 : Prog (BitVec 64) :=
.seq globalBody656_2 globalBody656_17

def globalBody656_19 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody656_18

def globalBody656_20 : Prog (BitVec 64) :=
.dec ("acc") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) globalBody656_19

def globalBody656_21 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 23#64)) globalBody656_20

def globalBody656_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_reduce" [Flapjack.Exp.var Flapjack.VarKind.local "t"]

def globalBody656_23 : Prog (BitVec 64) :=
.seq globalBody656_21 globalBody656_22

def globalBody656_24 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 384#64]

def globalBody656_25 : Prog (BitVec 64) :=
.seq globalBody656_23 globalBody656_24

def globalBody656_26 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody656_27 : Prog (BitVec 64) :=
.seq globalBody656_25 globalBody656_26

def globalBody656_28 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody656_29 : Prog (BitVec 64) :=
.seq globalBody656_27 globalBody656_28

def globalBody656_30 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody656_29

def globalBody656_31 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 23#64, Flapjack.Exp.const 32#64]]) globalBody656_30

def globalBody656_32 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody656_31

def globalData656 : Decl (BitVec 64) :=
.function { name := "fq12_mul", inline := false, exported := false, params := [("d", Flapjack.Shape.one), ("a", Flapjack.Shape.one), ("b", Flapjack.Shape.one)], body := globalBody656_32, returnShape := (Flapjack.Shape.one) }
def globalOutput656 := Pancake.PanLang.declToHOL globalData656
end InitECandidate.Proofs.FrontendStages.Declarations
