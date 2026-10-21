import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify611
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body627_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bn_from_be"
  [Flapjack.Exp.var Flapjack.VarKind.local "mp", Flapjack.Exp.var Flapjack.VarKind.local "mlen",
    Flapjack.Exp.var Flapjack.VarKind.local "md"]

def body627_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "mlen"]

def body627_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body627_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body627_4 : Prog (BitVec 64) :=
.seq body627_2 body627_3

def body627_5 : Prog (BitVec 64) :=
.seq body627_1 body627_4

def body627_6 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body627_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 0#64)) body627_5 body627_6

def body627_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bn_from_be"
  [Flapjack.Exp.var Flapjack.VarKind.local "bp", Flapjack.Exp.var Flapjack.VarKind.local "blen",
    Flapjack.Exp.var Flapjack.VarKind.local "bd"]

def body627_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bn_mod"
  [Flapjack.Exp.var Flapjack.VarKind.local "bd", Flapjack.Exp.var Flapjack.VarKind.local "nbd",
    Flapjack.Exp.var Flapjack.VarKind.local "md", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.var Flapjack.VarKind.local "base", Flapjack.Exp.var Flapjack.VarKind.local "q",
    Flapjack.Exp.var Flapjack.VarKind.local "un", Flapjack.Exp.var Flapjack.VarKind.local "vn"]

def body627_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "r",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 8#64]]

def body627_11 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "r") (Flapjack.Exp.const 1#64)

def body627_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 1#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal
        (Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "md"))
        (Flapjack.Exp.const 1#64))]) body627_6 body627_11

def body627_13 : Prog (BitVec 64) :=
.seq body627_10 body627_12

def body627_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "base",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 8#64]]

def body627_15 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "t"
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 1#64])

def body627_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bn_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.var Flapjack.VarKind.local "prod"]

def body627_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bn_mod"
  [Flapjack.Exp.var Flapjack.VarKind.local "prod",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "n"],
    Flapjack.Exp.var Flapjack.VarKind.local "md", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "q",
    Flapjack.Exp.var Flapjack.VarKind.local "un", Flapjack.Exp.var Flapjack.VarKind.local "vn"]

def body627_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bn_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.var Flapjack.VarKind.local "base", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.var Flapjack.VarKind.local "prod"]

def body627_19 : Prog (BitVec 64) :=
.seq body627_18 body627_17

def body627_20 : Prog (BitVec 64) :=
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
  (Flapjack.Exp.const 1#64)) body627_19 body627_6

def body627_21 : Prog (BitVec 64) :=
.seq body627_17 body627_20

def body627_22 : Prog (BitVec 64) :=
.seq body627_16 body627_21

def body627_23 : Prog (BitVec 64) :=
.seq body627_15 body627_22

def body627_24 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "t")) body627_23

def body627_25 : Prog (BitVec 64) :=
.seq body627_14 body627_24

def body627_26 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 0#64)) body627_13 body627_25

def body627_27 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bn_to_be"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "mlen"]

def body627_28 : Prog (BitVec 64) :=
.seq body627_27 body627_4

def body627_29 : Prog (BitVec 64) :=
.seq body627_26 body627_28

def body627_30 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("be_top_bit") ([Flapjack.Exp.var Flapjack.VarKind.local "ep", Flapjack.Exp.var Flapjack.VarKind.local "elen"]) body627_29

def body627_31 : Prog (BitVec 64) :=
.seq body627_9 body627_30

def body627_32 : Prog (BitVec 64) :=
.seq body627_8 body627_31

def body627_33 : Prog (BitVec 64) :=
.decCall ("vn") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 8#64]]) body627_32

def body627_34 : Prog (BitVec 64) :=
.decCall ("un") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "big", Flapjack.Exp.const 8#64],
      Flapjack.Exp.const 16#64]]) body627_33

def body627_35 : Prog (BitVec 64) :=
.decCall ("q") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "big", Flapjack.Exp.const 8#64],
      Flapjack.Exp.const 8#64]]) body627_34

def body627_36 : Prog (BitVec 64) :=
.decCall ("prod") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "n"],
      Flapjack.Exp.const 8#64]]) body627_35

def body627_37 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 8#64]]) body627_36

def body627_38 : Prog (BitVec 64) :=
.decCall ("base") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 8#64]]) body627_37

def body627_39 : Prog (BitVec 64) :=
.decCall ("bd") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "big", Flapjack.Exp.const 8#64],
      Flapjack.Exp.const 8#64]]) body627_38

def body627_40 : Prog (BitVec 64) :=
.decCall ("big") (Flapjack.Shape.one) ("max") ([Flapjack.Exp.var Flapjack.VarKind.local "nbd",
  Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "n"]]) body627_39

def body627_41 : Prog (BitVec 64) :=
.dec ("nbd") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "blen", Flapjack.Exp.const 3#64])
  (Flapjack.Exp.const 2#64)) body627_40

def body627_42 : Prog (BitVec 64) :=
.seq body627_7 body627_41

def body627_43 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("digits_len") ([Flapjack.Exp.var Flapjack.VarKind.local "md", Flapjack.Exp.var Flapjack.VarKind.local "nmd"]) body627_42

def body627_44 : Prog (BitVec 64) :=
.seq body627_0 body627_43

def body627_45 : Prog (BitVec 64) :=
.decCall ("md") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "nmd", Flapjack.Exp.const 8#64],
      Flapjack.Exp.const 8#64]]) body627_44

def body627_46 : Prog (BitVec 64) :=
.dec ("nmd") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "mlen", Flapjack.Exp.const 3#64])
  (Flapjack.Exp.const 2#64)) body627_45

def body627_47 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body627_46

def body627_48 : Prog (BitVec 64) :=
.seq body627_1 body627_2

def body627_49 : Prog (BitVec 64) :=
.seq body627_48 body627_3

def body627_50 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 0#64)) body627_49 body627_6

def body627_51 : Prog (BitVec 64) :=
.seq body627_8 body627_9

def body627_52 : Prog (BitVec 64) :=
.seq body627_15 body627_16

def body627_53 : Prog (BitVec 64) :=
.seq body627_52 body627_17

def body627_54 : Prog (BitVec 64) :=
.seq body627_53 body627_20

def body627_55 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "t")) body627_54

def body627_56 : Prog (BitVec 64) :=
.seq body627_14 body627_55

def body627_57 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 0#64)) body627_13 body627_56

def body627_58 : Prog (BitVec 64) :=
.seq body627_57 body627_27

def body627_59 : Prog (BitVec 64) :=
.seq body627_58 body627_2

def body627_60 : Prog (BitVec 64) :=
.seq body627_59 body627_3

def body627_61 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("be_top_bit") ([Flapjack.Exp.var Flapjack.VarKind.local "ep", Flapjack.Exp.var Flapjack.VarKind.local "elen"]) body627_60

def body627_62 : Prog (BitVec 64) :=
.seq body627_51 body627_61

def body627_63 : Prog (BitVec 64) :=
.decCall ("vn") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 8#64]]) body627_62

def body627_64 : Prog (BitVec 64) :=
.decCall ("un") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "big", Flapjack.Exp.const 8#64],
      Flapjack.Exp.const 16#64]]) body627_63

def body627_65 : Prog (BitVec 64) :=
.decCall ("q") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "big", Flapjack.Exp.const 8#64],
      Flapjack.Exp.const 8#64]]) body627_64

def body627_66 : Prog (BitVec 64) :=
.decCall ("prod") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "n"],
      Flapjack.Exp.const 8#64]]) body627_65

def body627_67 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 8#64]]) body627_66

def body627_68 : Prog (BitVec 64) :=
.decCall ("base") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 8#64]]) body627_67

def body627_69 : Prog (BitVec 64) :=
.decCall ("bd") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "big", Flapjack.Exp.const 8#64],
      Flapjack.Exp.const 8#64]]) body627_68

def body627_70 : Prog (BitVec 64) :=
.decCall ("big") (Flapjack.Shape.one) ("max") ([Flapjack.Exp.var Flapjack.VarKind.local "nbd",
  Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "n"]]) body627_69

def body627_71 : Prog (BitVec 64) :=
.dec ("nbd") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "blen", Flapjack.Exp.const 3#64])
  (Flapjack.Exp.const 2#64)) body627_70

def body627_72 : Prog (BitVec 64) :=
.seq body627_50 body627_71

def body627_73 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("digits_len") ([Flapjack.Exp.var Flapjack.VarKind.local "md", Flapjack.Exp.var Flapjack.VarKind.local "nmd"]) body627_72

def body627_74 : Prog (BitVec 64) :=
.seq body627_0 body627_73

def body627_75 : Prog (BitVec 64) :=
.decCall ("md") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "nmd", Flapjack.Exp.const 8#64],
      Flapjack.Exp.const 8#64]]) body627_74

def body627_76 : Prog (BitVec 64) :=
.dec ("nmd") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "mlen", Flapjack.Exp.const 3#64])
  (Flapjack.Exp.const 2#64)) body627_75

def body627_77 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body627_76

def originalData627 : Decl (BitVec 64) :=
.function { name := "modexp", inline := false, exported := false, params := [("bp", Flapjack.Shape.one), ("blen", Flapjack.Shape.one), ("ep", Flapjack.Shape.one), ("elen", Flapjack.Shape.one),
  ("mp", Flapjack.Shape.one), ("mlen", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body627_47, returnShape := (Flapjack.Shape.one) }
def simplifiedData627 : Decl (BitVec 64) :=
.function { name := "modexp", inline := false, exported := false, params := [("bp", Flapjack.Shape.one), ("blen", Flapjack.Shape.one), ("ep", Flapjack.Shape.one), ("elen", Flapjack.Shape.one),
  ("mp", Flapjack.Shape.one), ("mlen", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body627_77, returnShape := (Flapjack.Shape.one) }
def original627 := Pancake.PanLang.declToHOL originalData627
def simplified627 := Pancake.PanLang.declToHOL simplifiedData627
end InitECandidate.Proofs.FrontendStages.Declarations
