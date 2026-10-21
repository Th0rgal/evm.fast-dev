import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data236
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate219
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody236_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 20#64)

def globalBody236_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody236_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 96#64]))
  (Flapjack.Exp.const 1#64)) globalBody236_0 globalBody236_1

def globalBody236_3 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 21#64)

def globalBody236_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 208#64]))
  (Flapjack.Exp.var Flapjack.VarKind.local "ebg")) globalBody236_3 globalBody236_1

def globalBody236_5 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 22#64)

def globalBody236_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 104#64]))
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 112#64]))) globalBody236_5 globalBody236_1

def globalBody236_7 : Prog (BitVec 64) :=
.seq globalBody236_4 globalBody236_6

def globalBody236_8 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 23#64)

def globalBody236_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) globalBody236_8 globalBody236_1

def globalBody236_10 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 24#64)

def globalBody236_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "parent", Flapjack.Exp.const 120#64]))
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 120#64]))) globalBody236_10 globalBody236_1

def globalBody236_12 : Prog (BitVec 64) :=
.seq globalBody236_9 globalBody236_11

def globalBody236_13 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 25#64)

def globalBody236_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 96#64]))
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "parent", Flapjack.Exp.const 96#64]),
      Flapjack.Exp.const 1#64])) globalBody236_13 globalBody236_1

def globalBody236_15 : Prog (BitVec 64) :=
.seq globalBody236_12 globalBody236_14

def globalBody236_16 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 26#64)

def globalBody236_17 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 32#64)
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 136#64]))) globalBody236_16 globalBody236_1

def globalBody236_18 : Prog (BitVec 64) :=
.seq globalBody236_15 globalBody236_17

def globalBody236_19 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 27#64)

def globalBody236_20 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "dz") (Flapjack.Exp.const 0#64)) globalBody236_19 globalBody236_1

def globalBody236_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "eq"), none)) "memeq"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 152#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 120#64]),
    Flapjack.Exp.const 8#64]

def globalBody236_22 : Prog (BitVec 64) :=
.seq globalBody236_20 globalBody236_21

def globalBody236_23 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 28#64)

def globalBody236_24 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) globalBody236_23 globalBody236_1

def globalBody236_25 : Prog (BitVec 64) :=
.seq globalBody236_22 globalBody236_24

def globalBody236_26 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "tmp") (Flapjack.Exp.const 192#64)

def globalBody236_27 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp", Flapjack.Exp.const 1#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tmp", Flapjack.Exp.const 32#64]]

def globalBody236_28 : Prog (BitVec 64) :=
.seq globalBody236_26 globalBody236_27

def globalBody236_29 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "eq"), none)) "memeq"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 16#64]),
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tmp", Flapjack.Exp.const 32#64],
    Flapjack.Exp.const 32#64]

def globalBody236_30 : Prog (BitVec 64) :=
.seq globalBody236_28 globalBody236_29

def globalBody236_31 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody236_32 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 29#64)

def globalBody236_33 : Prog (BitVec 64) :=
.seq globalBody236_31 globalBody236_32

def globalBody236_34 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) globalBody236_33 globalBody236_1

def globalBody236_35 : Prog (BitVec 64) :=
.seq globalBody236_30 globalBody236_34

def globalBody236_36 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "header_hash"
  [Flapjack.Exp.var Flapjack.VarKind.local "parent", Flapjack.Exp.var Flapjack.VarKind.local "tmp"]

def globalBody236_37 : Prog (BitVec 64) :=
.seq globalBody236_35 globalBody236_36

def globalBody236_38 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "eq"), none)) "memeq"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 8#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "tmp", Flapjack.Exp.const 32#64]

def globalBody236_39 : Prog (BitVec 64) :=
.seq globalBody236_37 globalBody236_38

def globalBody236_40 : Prog (BitVec 64) :=
.seq globalBody236_39 globalBody236_31

def globalBody236_41 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 30#64)

def globalBody236_42 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) globalBody236_41 globalBody236_1

def globalBody236_43 : Prog (BitVec 64) :=
.seq globalBody236_40 globalBody236_42

def globalBody236_44 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody236_45 : Prog (BitVec 64) :=
.seq globalBody236_43 globalBody236_44

def globalBody236_46 : Prog (BitVec 64) :=
.decCall ("tmp") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) globalBody236_45

def globalBody236_47 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody236_46

def globalBody236_48 : Prog (BitVec 64) :=
.seq globalBody236_25 globalBody236_47

def globalBody236_49 : Prog (BitVec 64) :=
.decCall ("dz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 64#64])]) globalBody236_48

def globalBody236_50 : Prog (BitVec 64) :=
.seq globalBody236_18 globalBody236_49

def globalBody236_51 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "expected",
  Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 160#64])]) globalBody236_50

def globalBody236_52 : Prog (BitVec 64) :=
.decCall ("expected") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("calculate_base_fee_per_gas") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 104#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "parent", Flapjack.Exp.const 104#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "parent", Flapjack.Exp.const 112#64]),
  Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "parent", Flapjack.Exp.const 160#64])]) globalBody236_51

def globalBody236_53 : Prog (BitVec 64) :=
.seq globalBody236_7 globalBody236_52

def globalBody236_54 : Prog (BitVec 64) :=
.decCall ("ebg") (Flapjack.Shape.one) ("calculate_excess_blob_gas") ([Flapjack.Exp.var Flapjack.VarKind.local "parent"]) globalBody236_53

def globalBody236_55 : Prog (BitVec 64) :=
.seq globalBody236_2 globalBody236_54

def globalData236 : Decl (BitVec 64) :=
.function { name := "validate_header", inline := false, exported := false, params := [("parent", Flapjack.Shape.one), ("h", Flapjack.Shape.one)], body := globalBody236_55, returnShape := (Flapjack.Shape.one) }
def globalOutput236 := Pancake.PanLang.declToHOL globalData236
end InitECandidate.Proofs.FrontendStages.Declarations
