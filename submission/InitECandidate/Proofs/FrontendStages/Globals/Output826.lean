import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data826
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate810
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody826_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "buffer_read"
  [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 0#64,
    Flapjack.Exp.const 96#64, Flapjack.Exp.var Flapjack.VarKind.local "hdr"]

def globalBody826_1 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 4#64)

def globalBody826_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody826_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 1024#64) (Flapjack.Exp.var Flapjack.VarKind.local "blen")) globalBody826_1 globalBody826_2

def globalBody826_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 1024#64) (Flapjack.Exp.var Flapjack.VarKind.local "elen")) globalBody826_1 globalBody826_2

def globalBody826_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 1024#64) (Flapjack.Exp.var Flapjack.VarKind.local "mlen")) globalBody826_1 globalBody826_2

def globalBody826_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "buffer_read"
  [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.var Flapjack.VarKind.local "exp_start", Flapjack.Exp.var Flapjack.VarKind.local "hlen",
    Flapjack.Exp.var Flapjack.VarKind.local "hdr"]

def globalBody826_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.var Flapjack.VarKind.local "cost"]

def globalBody826_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 120#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "empty")

def globalBody826_9 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 128#64])
  (Flapjack.Exp.const 0#64)

def globalBody826_10 : Prog (BitVec 64) :=
.seq globalBody826_8 globalBody826_9

def globalBody826_11 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody826_12 : Prog (BitVec 64) :=
.seq globalBody826_10 globalBody826_11

def globalBody826_13 : Prog (BitVec 64) :=
.decCall ("empty") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 8#64]) globalBody826_12

def globalBody826_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "blen") (Flapjack.Exp.const 0#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "mlen") (Flapjack.Exp.const 0#64))]) globalBody826_13 globalBody826_2

def globalBody826_15 : Prog (BitVec 64) :=
.seq globalBody826_7 globalBody826_14

def globalBody826_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "buffer_read"
  [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.const 96#64, Flapjack.Exp.var Flapjack.VarKind.local "blen",
    Flapjack.Exp.var Flapjack.VarKind.local "bp"]

def globalBody826_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "buffer_read"
  [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.var Flapjack.VarKind.local "exp_start", Flapjack.Exp.var Flapjack.VarKind.local "elen",
    Flapjack.Exp.var Flapjack.VarKind.local "ep"]

def globalBody826_18 : Prog (BitVec 64) :=
.seq globalBody826_16 globalBody826_17

def globalBody826_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "buffer_read"
  [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "exp_start", Flapjack.Exp.var Flapjack.VarKind.local "elen"],
    Flapjack.Exp.var Flapjack.VarKind.local "mlen", Flapjack.Exp.var Flapjack.VarKind.local "mp"]

def globalBody826_20 : Prog (BitVec 64) :=
.seq globalBody826_18 globalBody826_19

def globalBody826_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "modexp"
  [Flapjack.Exp.var Flapjack.VarKind.local "bp", Flapjack.Exp.var Flapjack.VarKind.local "blen",
    Flapjack.Exp.var Flapjack.VarKind.local "ep", Flapjack.Exp.var Flapjack.VarKind.local "elen",
    Flapjack.Exp.var Flapjack.VarKind.local "mp", Flapjack.Exp.var Flapjack.VarKind.local "mlen",
    Flapjack.Exp.var Flapjack.VarKind.local "out"]

def globalBody826_22 : Prog (BitVec 64) :=
.seq globalBody826_20 globalBody826_21

def globalBody826_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody826_24 : Prog (BitVec 64) :=
.seq globalBody826_22 globalBody826_23

def globalBody826_25 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 120#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "out")

def globalBody826_26 : Prog (BitVec 64) :=
.seq globalBody826_24 globalBody826_25

def globalBody826_27 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 128#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "mlen")

def globalBody826_28 : Prog (BitVec 64) :=
.seq globalBody826_26 globalBody826_27

def globalBody826_29 : Prog (BitVec 64) :=
.seq globalBody826_28 globalBody826_11

def globalBody826_30 : Prog (BitVec 64) :=
.decCall ("mp") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "mlen", Flapjack.Exp.const 8#64]]) globalBody826_29

def globalBody826_31 : Prog (BitVec 64) :=
.decCall ("ep") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "elen", Flapjack.Exp.const 8#64]]) globalBody826_30

def globalBody826_32 : Prog (BitVec 64) :=
.decCall ("bp") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "blen", Flapjack.Exp.const 8#64]]) globalBody826_31

def globalBody826_33 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody826_32

def globalBody826_34 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "mlen", Flapjack.Exp.const 8#64]]) globalBody826_33

def globalBody826_35 : Prog (BitVec 64) :=
.seq globalBody826_15 globalBody826_34

def globalBody826_36 : Prog (BitVec 64) :=
.decCall ("cost") (Flapjack.Shape.one) ("modexp_gas") ([Flapjack.Exp.var Flapjack.VarKind.local "blen", Flapjack.Exp.var Flapjack.VarKind.local "mlen",
  Flapjack.Exp.var Flapjack.VarKind.local "elen", Flapjack.Exp.var Flapjack.VarKind.local "head"]) globalBody826_35

def globalBody826_37 : Prog (BitVec 64) :=
.decCall ("head") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.var Flapjack.VarKind.local "hlen"]) globalBody826_36

def globalBody826_38 : Prog (BitVec 64) :=
.seq globalBody826_6 globalBody826_37

def globalBody826_39 : Prog (BitVec 64) :=
.decCall ("hlen") (Flapjack.Shape.one) ("min") ([Flapjack.Exp.const 32#64, Flapjack.Exp.var Flapjack.VarKind.local "elen"]) globalBody826_38

def globalBody826_40 : Prog (BitVec 64) :=
.dec ("exp_start") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.const 96#64, Flapjack.Exp.var Flapjack.VarKind.local "blen"]) globalBody826_39

def globalBody826_41 : Prog (BitVec 64) :=
.seq globalBody826_5 globalBody826_40

def globalBody826_42 : Prog (BitVec 64) :=
.decCall ("mlen") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "ml"]) globalBody826_41

def globalBody826_43 : Prog (BitVec 64) :=
.decCall ("ml") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 64#64],
  Flapjack.Exp.const 32#64]) globalBody826_42

def globalBody826_44 : Prog (BitVec 64) :=
.seq globalBody826_4 globalBody826_43

def globalBody826_45 : Prog (BitVec 64) :=
.decCall ("elen") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "el"]) globalBody826_44

def globalBody826_46 : Prog (BitVec 64) :=
.decCall ("el") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 32#64],
  Flapjack.Exp.const 32#64]) globalBody826_45

def globalBody826_47 : Prog (BitVec 64) :=
.seq globalBody826_3 globalBody826_46

def globalBody826_48 : Prog (BitVec 64) :=
.decCall ("blen") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "bl"]) globalBody826_47

def globalBody826_49 : Prog (BitVec 64) :=
.decCall ("bl") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.var Flapjack.VarKind.local "hdr", Flapjack.Exp.const 32#64]) globalBody826_48

def globalBody826_50 : Prog (BitVec 64) :=
.seq globalBody826_0 globalBody826_49

def globalBody826_51 : Prog (BitVec 64) :=
.dec ("hdr") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 272#64])) globalBody826_50

def globalBody826_52 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 96#64])) globalBody826_51

def globalBody826_53 : Prog (BitVec 64) :=
.dec ("data") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 88#64])) globalBody826_52

def globalBody826_54 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 112#64])) globalBody826_53

def globalData826 : Decl (BitVec 64) :=
.function { name := "pre_modexp", inline := false, exported := false, params := [], body := globalBody826_54, returnShape := (Flapjack.Shape.one) }
def globalOutput826 := Pancake.PanLang.declToHOL globalData826
end InitECandidate.Proofs.FrontendStages.Declarations
