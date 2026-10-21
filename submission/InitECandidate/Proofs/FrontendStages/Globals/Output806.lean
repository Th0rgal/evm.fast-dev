import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data806
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate790
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody806_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "sha256"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 96#64],
    Flapjack.Exp.const 48#64, Flapjack.Exp.var Flapjack.VarKind.local "h"]

def globalBody806_1 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "h") (Flapjack.Exp.const 1#64)

def globalBody806_2 : Prog (BitVec 64) :=
.seq globalBody806_0 globalBody806_1

def globalBody806_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody806_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def globalBody806_5 : Prog (BitVec 64) :=
.seq globalBody806_3 globalBody806_4

def globalBody806_6 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody806_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "heq") (Flapjack.Exp.const 0#64)) globalBody806_5 globalBody806_6

def globalBody806_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 0#64)) globalBody806_5 globalBody806_6

def globalBody806_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "ok"), none)) "kzg_load_g1"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 144#64],
    Flapjack.Exp.var Flapjack.VarKind.local "pr"]

def globalBody806_10 : Prog (BitVec 64) :=
.seq globalBody806_8 globalBody806_9

def globalBody806_11 : Prog (BitVec 64) :=
.seq globalBody806_10 globalBody806_8

def globalBody806_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "zlt") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ylt") (Flapjack.Exp.const 0#64)])) globalBody806_5 globalBody806_6

def globalBody806_13 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "v") (Flapjack.Exp.const 0#64)) globalBody806_4 globalBody806_6

def globalBody806_14 : Prog (BitVec 64) :=
.seq globalBody806_3 globalBody806_13

def globalBody806_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 64#64]

def globalBody806_16 : Prog (BitVec 64) :=
.seq globalBody806_14 globalBody806_15

def globalBody806_17 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 30#64])
  (Flapjack.Exp.const 16#64)

def globalBody806_18 : Prog (BitVec 64) :=
.seq globalBody806_16 globalBody806_17

def globalBody806_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "u256_to_be32"
  [Flapjack.Exp.var Flapjack.VarKind.local "r",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 32#64]]

def globalBody806_20 : Prog (BitVec 64) :=
.seq globalBody806_18 globalBody806_19

def globalBody806_21 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody806_22 : Prog (BitVec 64) :=
.seq globalBody806_20 globalBody806_21

def globalBody806_23 : Prog (BitVec 64) :=
.decCall ("v") (Flapjack.Shape.one) ("kzg_verify") ([Flapjack.Exp.var Flapjack.VarKind.local "c",
  Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 32#64],
  Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 64#64],
  Flapjack.Exp.var Flapjack.VarKind.local "pr"]) globalBody806_22

def globalBody806_24 : Prog (BitVec 64) :=
.seq globalBody806_12 globalBody806_23

def globalBody806_25 : Prog (BitVec 64) :=
.decCall ("ylt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "y", Flapjack.Exp.var Flapjack.VarKind.local "r"]) globalBody806_24

def globalBody806_26 : Prog (BitVec 64) :=
.decCall ("zlt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "z", Flapjack.Exp.var Flapjack.VarKind.local "r"]) globalBody806_25

def globalBody806_27 : Prog (BitVec 64) :=
.dec ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
      Flapjack.Exp.const 1344#64])) globalBody806_26

def globalBody806_28 : Prog (BitVec 64) :=
.decCall ("y") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 64#64],
  Flapjack.Exp.const 32#64]) globalBody806_27

def globalBody806_29 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 32#64],
  Flapjack.Exp.const 32#64]) globalBody806_28

def globalBody806_30 : Prog (BitVec 64) :=
.seq globalBody806_11 globalBody806_29

def globalBody806_31 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("kzg_load_g1") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 96#64],
  Flapjack.Exp.var Flapjack.VarKind.local "c"]) globalBody806_30

def globalBody806_32 : Prog (BitVec 64) :=
.seq globalBody806_7 globalBody806_31

def globalBody806_33 : Prog (BitVec 64) :=
.decCall ("heq") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 32#64]) globalBody806_32

def globalBody806_34 : Prog (BitVec 64) :=
.seq globalBody806_2 globalBody806_33

def globalBody806_35 : Prog (BitVec 64) :=
.decCall ("pr") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) globalBody806_34

def globalBody806_36 : Prog (BitVec 64) :=
.decCall ("c") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) globalBody806_35

def globalBody806_37 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) globalBody806_36

def globalBody806_38 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody806_37

def globalData806 : Decl (BitVec 64) :=
.function { name := "kzg_point_evaluation_exec", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := globalBody806_38, returnShape := (Flapjack.Shape.one) }
def globalOutput806 := Pancake.PanLang.declToHOL globalData806
end InitECandidate.Proofs.FrontendStages.Declarations
