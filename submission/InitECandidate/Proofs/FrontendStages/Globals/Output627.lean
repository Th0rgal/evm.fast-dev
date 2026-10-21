import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data627
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate604
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody627_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bn_from_be"
  [Flapjack.Exp.var Flapjack.VarKind.local "mp", Flapjack.Exp.var Flapjack.VarKind.local "mlen",
    Flapjack.Exp.var Flapjack.VarKind.local "md"]

def globalBody627_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "mlen"]

def globalBody627_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody627_3 : Prog (BitVec 64) :=
.seq globalBody627_1 globalBody627_2

def globalBody627_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody627_5 : Prog (BitVec 64) :=
.seq globalBody627_3 globalBody627_4

def globalBody627_6 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody627_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 0#64)) globalBody627_5 globalBody627_6

def globalBody627_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bn_from_be"
  [Flapjack.Exp.var Flapjack.VarKind.local "bp", Flapjack.Exp.var Flapjack.VarKind.local "blen",
    Flapjack.Exp.var Flapjack.VarKind.local "bd"]

def globalBody627_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bn_mod"
  [Flapjack.Exp.var Flapjack.VarKind.local "bd", Flapjack.Exp.var Flapjack.VarKind.local "nbd",
    Flapjack.Exp.var Flapjack.VarKind.local "md", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.var Flapjack.VarKind.local "base", Flapjack.Exp.var Flapjack.VarKind.local "q",
    Flapjack.Exp.var Flapjack.VarKind.local "un", Flapjack.Exp.var Flapjack.VarKind.local "vn"]

def globalBody627_10 : Prog (BitVec 64) :=
.seq globalBody627_8 globalBody627_9

def globalBody627_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "r",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 8#64]]

def globalBody627_12 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "r") (Flapjack.Exp.const 1#64)

def globalBody627_13 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 1#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal
        (Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "md"))
        (Flapjack.Exp.const 1#64))]) globalBody627_6 globalBody627_12

def globalBody627_14 : Prog (BitVec 64) :=
.seq globalBody627_11 globalBody627_13

def globalBody627_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "base",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 8#64]]

def globalBody627_16 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "t"
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 1#64])

def globalBody627_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bn_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.var Flapjack.VarKind.local "prod"]

def globalBody627_18 : Prog (BitVec 64) :=
.seq globalBody627_16 globalBody627_17

def globalBody627_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bn_mod"
  [Flapjack.Exp.var Flapjack.VarKind.local "prod",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "n"],
    Flapjack.Exp.var Flapjack.VarKind.local "md", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "q",
    Flapjack.Exp.var Flapjack.VarKind.local "un", Flapjack.Exp.var Flapjack.VarKind.local "vn"]

def globalBody627_20 : Prog (BitVec 64) :=
.seq globalBody627_18 globalBody627_19

def globalBody627_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bn_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.var Flapjack.VarKind.local "base", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.var Flapjack.VarKind.local "prod"]

def globalBody627_22 : Prog (BitVec 64) :=
.seq globalBody627_21 globalBody627_19

def globalBody627_23 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.shift Flapjack.Shift.lsr
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.sub
            [Flapjack.Exp.op Flapjack.BinOp.sub
                [Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "ep", Flapjack.Exp.var Flapjack.VarKind.local "elen"],
                  Flapjack.Exp.const 1#64],
              Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "t")
                (Flapjack.Exp.const 3#64)]))
        (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 7#64]),
      Flapjack.Exp.const 1#64])
  (Flapjack.Exp.const 1#64)) globalBody627_22 globalBody627_6

def globalBody627_24 : Prog (BitVec 64) :=
.seq globalBody627_20 globalBody627_23

def globalBody627_25 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "t")) globalBody627_24

def globalBody627_26 : Prog (BitVec 64) :=
.seq globalBody627_15 globalBody627_25

def globalBody627_27 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 0#64)) globalBody627_14 globalBody627_26

def globalBody627_28 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bn_to_be"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "mlen"]

def globalBody627_29 : Prog (BitVec 64) :=
.seq globalBody627_27 globalBody627_28

def globalBody627_30 : Prog (BitVec 64) :=
.seq globalBody627_29 globalBody627_2

def globalBody627_31 : Prog (BitVec 64) :=
.seq globalBody627_30 globalBody627_4

def globalBody627_32 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("be_top_bit") ([Flapjack.Exp.var Flapjack.VarKind.local "ep", Flapjack.Exp.var Flapjack.VarKind.local "elen"]) globalBody627_31

def globalBody627_33 : Prog (BitVec 64) :=
.seq globalBody627_10 globalBody627_32

def globalBody627_34 : Prog (BitVec 64) :=
.decCall ("vn") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 8#64]]) globalBody627_33

def globalBody627_35 : Prog (BitVec 64) :=
.decCall ("un") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "big", Flapjack.Exp.const 8#64],
      Flapjack.Exp.const 16#64]]) globalBody627_34

def globalBody627_36 : Prog (BitVec 64) :=
.decCall ("q") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "big", Flapjack.Exp.const 8#64],
      Flapjack.Exp.const 8#64]]) globalBody627_35

def globalBody627_37 : Prog (BitVec 64) :=
.decCall ("prod") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "n"],
      Flapjack.Exp.const 8#64]]) globalBody627_36

def globalBody627_38 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 8#64]]) globalBody627_37

def globalBody627_39 : Prog (BitVec 64) :=
.decCall ("base") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 8#64]]) globalBody627_38

def globalBody627_40 : Prog (BitVec 64) :=
.decCall ("bd") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "big", Flapjack.Exp.const 8#64],
      Flapjack.Exp.const 8#64]]) globalBody627_39

def globalBody627_41 : Prog (BitVec 64) :=
.decCall ("big") (Flapjack.Shape.one) ("max") ([Flapjack.Exp.var Flapjack.VarKind.local "nbd",
  Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "n"]]) globalBody627_40

def globalBody627_42 : Prog (BitVec 64) :=
.dec ("nbd") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "blen", Flapjack.Exp.const 3#64])
  (Flapjack.Exp.const 2#64)) globalBody627_41

def globalBody627_43 : Prog (BitVec 64) :=
.seq globalBody627_7 globalBody627_42

def globalBody627_44 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("digits_len") ([Flapjack.Exp.var Flapjack.VarKind.local "md", Flapjack.Exp.var Flapjack.VarKind.local "nmd"]) globalBody627_43

def globalBody627_45 : Prog (BitVec 64) :=
.seq globalBody627_0 globalBody627_44

def globalBody627_46 : Prog (BitVec 64) :=
.decCall ("md") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "nmd", Flapjack.Exp.const 8#64],
      Flapjack.Exp.const 8#64]]) globalBody627_45

def globalBody627_47 : Prog (BitVec 64) :=
.dec ("nmd") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "mlen", Flapjack.Exp.const 3#64])
  (Flapjack.Exp.const 2#64)) globalBody627_46

def globalBody627_48 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody627_47

def globalData627 : Decl (BitVec 64) :=
.function { name := "modexp", inline := false, exported := false, params := [("bp", Flapjack.Shape.one), ("blen", Flapjack.Shape.one), ("ep", Flapjack.Shape.one), ("elen", Flapjack.Shape.one),
  ("mp", Flapjack.Shape.one), ("mlen", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := globalBody627_48, returnShape := (Flapjack.Shape.one) }
def globalOutput627 := Pancake.PanLang.declToHOL globalData627
end InitECandidate.Proofs.FrontendStages.Declarations
