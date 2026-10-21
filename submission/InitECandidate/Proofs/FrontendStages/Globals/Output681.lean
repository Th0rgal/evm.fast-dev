import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data681
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate665
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody681_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "R", Flapjack.Exp.var Flapjack.VarKind.local "Q", Flapjack.Exp.const 1152#64]

def globalBody681_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "nQ", Flapjack.Exp.var Flapjack.VarKind.local "Q",
    Flapjack.Exp.const 1152#64]

def globalBody681_2 : Prog (BitVec 64) :=
.seq globalBody681_0 globalBody681_1

def globalBody681_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_neg"
  [Flapjack.Exp.const 12#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nQ", Flapjack.Exp.const 384#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "Q", Flapjack.Exp.const 384#64]]

def globalBody681_4 : Prog (BitVec 64) :=
.seq globalBody681_2 globalBody681_3

def globalBody681_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_set_one"
  [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "fnum"]

def globalBody681_6 : Prog (BitVec 64) :=
.seq globalBody681_4 globalBody681_5

def globalBody681_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_set_one"
  [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "fden"]

def globalBody681_8 : Prog (BitVec 64) :=
.seq globalBody681_6 globalBody681_7

def globalBody681_9 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody681_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_linefunc"
  [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "d",
    Flapjack.Exp.var Flapjack.VarKind.local "R", Flapjack.Exp.var Flapjack.VarKind.local "R",
    Flapjack.Exp.var Flapjack.VarKind.local "P"]

def globalBody681_11 : Prog (BitVec 64) :=
.seq globalBody681_9 globalBody681_10

def globalBody681_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "fnum", Flapjack.Exp.var Flapjack.VarKind.local "fnum"]

def globalBody681_13 : Prog (BitVec 64) :=
.seq globalBody681_11 globalBody681_12

def globalBody681_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fnum", Flapjack.Exp.var Flapjack.VarKind.local "fnum",
    Flapjack.Exp.var Flapjack.VarKind.local "n"]

def globalBody681_15 : Prog (BitVec 64) :=
.seq globalBody681_13 globalBody681_14

def globalBody681_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "fden", Flapjack.Exp.var Flapjack.VarKind.local "fden"]

def globalBody681_17 : Prog (BitVec 64) :=
.seq globalBody681_15 globalBody681_16

def globalBody681_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fden", Flapjack.Exp.var Flapjack.VarKind.local "fden",
    Flapjack.Exp.var Flapjack.VarKind.local "d"]

def globalBody681_19 : Prog (BitVec 64) :=
.seq globalBody681_17 globalBody681_18

def globalBody681_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_double"
  [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "R", Flapjack.Exp.var Flapjack.VarKind.local "R"]

def globalBody681_21 : Prog (BitVec 64) :=
.seq globalBody681_19 globalBody681_20

def globalBody681_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_linefunc"
  [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "d",
    Flapjack.Exp.var Flapjack.VarKind.local "R", Flapjack.Exp.var Flapjack.VarKind.local "Q",
    Flapjack.Exp.var Flapjack.VarKind.local "P"]

def globalBody681_23 : Prog (BitVec 64) :=
.seq globalBody681_22 globalBody681_14

def globalBody681_24 : Prog (BitVec 64) :=
.seq globalBody681_23 globalBody681_18

def globalBody681_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_add"
  [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "R", Flapjack.Exp.var Flapjack.VarKind.local "R",
    Flapjack.Exp.var Flapjack.VarKind.local "Q"]

def globalBody681_26 : Prog (BitVec 64) :=
.seq globalBody681_24 globalBody681_25

def globalBody681_27 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody681_28 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.const 11637723931993326632#64)
        (Flapjack.Exp.var Flapjack.VarKind.local "i"),
      Flapjack.Exp.const 1#64])
  (Flapjack.Exp.const 1#64)) globalBody681_26 globalBody681_27

def globalBody681_29 : Prog (BitVec 64) :=
.seq globalBody681_21 globalBody681_28

def globalBody681_30 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_linefunc"
  [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "d",
    Flapjack.Exp.var Flapjack.VarKind.local "R", Flapjack.Exp.var Flapjack.VarKind.local "nQ",
    Flapjack.Exp.var Flapjack.VarKind.local "P"]

def globalBody681_31 : Prog (BitVec 64) :=
.seq globalBody681_30 globalBody681_14

def globalBody681_32 : Prog (BitVec 64) :=
.seq globalBody681_31 globalBody681_18

def globalBody681_33 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_add"
  [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "R", Flapjack.Exp.var Flapjack.VarKind.local "R",
    Flapjack.Exp.var Flapjack.VarKind.local "nQ"]

def globalBody681_34 : Prog (BitVec 64) :=
.seq globalBody681_32 globalBody681_33

def globalBody681_35 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.const 290499802545784960#64)
        (Flapjack.Exp.var Flapjack.VarKind.local "i"),
      Flapjack.Exp.const 1#64])
  (Flapjack.Exp.const 1#64)) globalBody681_34 globalBody681_27

def globalBody681_36 : Prog (BitVec 64) :=
.seq globalBody681_29 globalBody681_35

def globalBody681_37 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64) (Flapjack.Exp.var Flapjack.VarKind.local "i")) globalBody681_36

def globalBody681_38 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_frob"
  [Flapjack.Exp.var Flapjack.VarKind.local "Q1", Flapjack.Exp.var Flapjack.VarKind.local "Q"]

def globalBody681_39 : Prog (BitVec 64) :=
.seq globalBody681_37 globalBody681_38

def globalBody681_40 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_frob"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "Q1", Flapjack.Exp.const 384#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "Q", Flapjack.Exp.const 384#64]]

def globalBody681_41 : Prog (BitVec 64) :=
.seq globalBody681_39 globalBody681_40

def globalBody681_42 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_frob"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "Q1",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.const 384#64]],
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "Q",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.const 384#64]]]

def globalBody681_43 : Prog (BitVec 64) :=
.seq globalBody681_41 globalBody681_42

def globalBody681_44 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_frob"
  [Flapjack.Exp.var Flapjack.VarKind.local "nQ2", Flapjack.Exp.var Flapjack.VarKind.local "Q1"]

def globalBody681_45 : Prog (BitVec 64) :=
.seq globalBody681_43 globalBody681_44

def globalBody681_46 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_frob"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nQ2", Flapjack.Exp.const 384#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "Q1", Flapjack.Exp.const 384#64]]

def globalBody681_47 : Prog (BitVec 64) :=
.seq globalBody681_45 globalBody681_46

def globalBody681_48 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_neg"
  [Flapjack.Exp.const 12#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nQ2", Flapjack.Exp.const 384#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nQ2", Flapjack.Exp.const 384#64]]

def globalBody681_49 : Prog (BitVec 64) :=
.seq globalBody681_47 globalBody681_48

def globalBody681_50 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_frob"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "nQ2",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.const 384#64]],
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "Q1",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.const 384#64]]]

def globalBody681_51 : Prog (BitVec 64) :=
.seq globalBody681_49 globalBody681_50

def globalBody681_52 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_linefunc"
  [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "d",
    Flapjack.Exp.var Flapjack.VarKind.local "R", Flapjack.Exp.var Flapjack.VarKind.local "Q1",
    Flapjack.Exp.var Flapjack.VarKind.local "P"]

def globalBody681_53 : Prog (BitVec 64) :=
.seq globalBody681_51 globalBody681_52

def globalBody681_54 : Prog (BitVec 64) :=
.seq globalBody681_53 globalBody681_14

def globalBody681_55 : Prog (BitVec 64) :=
.seq globalBody681_54 globalBody681_18

def globalBody681_56 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_add"
  [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "R", Flapjack.Exp.var Flapjack.VarKind.local "R",
    Flapjack.Exp.var Flapjack.VarKind.local "Q1"]

def globalBody681_57 : Prog (BitVec 64) :=
.seq globalBody681_55 globalBody681_56

def globalBody681_58 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_linefunc"
  [Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "d",
    Flapjack.Exp.var Flapjack.VarKind.local "R", Flapjack.Exp.var Flapjack.VarKind.local "nQ2",
    Flapjack.Exp.var Flapjack.VarKind.local "P"]

def globalBody681_59 : Prog (BitVec 64) :=
.seq globalBody681_57 globalBody681_58

def globalBody681_60 : Prog (BitVec 64) :=
.seq globalBody681_59 globalBody681_14

def globalBody681_61 : Prog (BitVec 64) :=
.seq globalBody681_60 globalBody681_18

def globalBody681_62 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody681_63 : Prog (BitVec 64) :=
.seq globalBody681_61 globalBody681_62

def globalBody681_64 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody681_65 : Prog (BitVec 64) :=
.seq globalBody681_63 globalBody681_64

def globalBody681_66 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 64#64) globalBody681_65

def globalBody681_67 : Prog (BitVec 64) :=
.seq globalBody681_8 globalBody681_66

def globalBody681_68 : Prog (BitVec 64) :=
.decCall ("d") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 384#64]) globalBody681_67

def globalBody681_69 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 384#64]) globalBody681_68

def globalBody681_70 : Prog (BitVec 64) :=
.decCall ("nQ2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 1152#64]) globalBody681_69

def globalBody681_71 : Prog (BitVec 64) :=
.decCall ("Q1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 1152#64]) globalBody681_70

def globalBody681_72 : Prog (BitVec 64) :=
.decCall ("nQ") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 1152#64]) globalBody681_71

def globalBody681_73 : Prog (BitVec 64) :=
.decCall ("R") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 1152#64]) globalBody681_72

def globalBody681_74 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody681_73

def globalData681 : Decl (BitVec 64) :=
.function { name := "bn254_miller_raw", inline := false, exported := false, params := [("fnum", Flapjack.Shape.one), ("fden", Flapjack.Shape.one), ("Q", Flapjack.Shape.one), ("P", Flapjack.Shape.one)], body := globalBody681_74, returnShape := (Flapjack.Shape.one) }
def globalOutput681 := Pancake.PanLang.declToHOL globalData681
end InitECandidate.Proofs.FrontendStages.Declarations
