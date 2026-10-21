import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data207
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate191
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody207_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "ch",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 0#64],
    Flapjack.Exp.const 32#64]

def globalBody207_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_bytes_vector"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 32#64],
    Flapjack.Exp.const 20#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 32#64]]

def globalBody207_2 : Prog (BitVec 64) :=
.seq globalBody207_0 globalBody207_1

def globalBody207_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 64#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 52#64],
    Flapjack.Exp.const 32#64]

def globalBody207_4 : Prog (BitVec 64) :=
.seq globalBody207_2 globalBody207_3

def globalBody207_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 96#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 84#64],
    Flapjack.Exp.const 32#64]

def globalBody207_6 : Prog (BitVec 64) :=
.seq globalBody207_4 globalBody207_5

def globalBody207_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_bytes_vector"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 116#64],
    Flapjack.Exp.const 256#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 128#64]]

def globalBody207_8 : Prog (BitVec 64) :=
.seq globalBody207_6 globalBody207_7

def globalBody207_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 160#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 372#64],
    Flapjack.Exp.const 32#64]

def globalBody207_10 : Prog (BitVec 64) :=
.seq globalBody207_8 globalBody207_9

def globalBody207_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_u64_at"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 404#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 192#64]]

def globalBody207_12 : Prog (BitVec 64) :=
.seq globalBody207_10 globalBody207_11

def globalBody207_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_u64_at"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 412#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 224#64]]

def globalBody207_14 : Prog (BitVec 64) :=
.seq globalBody207_12 globalBody207_13

def globalBody207_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_u64_at"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 420#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 256#64]]

def globalBody207_16 : Prog (BitVec 64) :=
.seq globalBody207_14 globalBody207_15

def globalBody207_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_u64_at"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 428#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 288#64]]

def globalBody207_18 : Prog (BitVec 64) :=
.seq globalBody207_16 globalBody207_17

def globalBody207_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_bytes_list"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 16#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 24#64]),
    Flapjack.Exp.const 1#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 320#64]]

def globalBody207_20 : Prog (BitVec 64) :=
.seq globalBody207_18 globalBody207_19

def globalBody207_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 352#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64],
    Flapjack.Exp.const 32#64]

def globalBody207_22 : Prog (BitVec 64) :=
.seq globalBody207_20 globalBody207_21

def globalBody207_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 384#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 472#64],
    Flapjack.Exp.const 32#64]

def globalBody207_24 : Prog (BitVec 64) :=
.seq globalBody207_22 globalBody207_23

def globalBody207_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_pbytes"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "txs",
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64]]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "txs",
          Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64],
          Flapjack.Exp.const 8#64]),
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "roots",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 32#64]]]

def globalBody207_26 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody207_27 : Prog (BitVec 64) :=
.seq globalBody207_25 globalBody207_26

def globalBody207_28 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "ntx")) globalBody207_27

def globalBody207_29 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_plist_chunks"
  [Flapjack.Exp.var Flapjack.VarKind.local "roots", Flapjack.Exp.var Flapjack.VarKind.local "ntx",
    Flapjack.Exp.var Flapjack.VarKind.local "ntx",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 416#64]]

def globalBody207_30 : Prog (BitVec 64) :=
.seq globalBody207_28 globalBody207_29

def globalBody207_31 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "m2"]

def globalBody207_32 : Prog (BitVec 64) :=
.seq globalBody207_30 globalBody207_31

def globalBody207_33 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "roots"), none)) "alloc"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "nwd", Flapjack.Exp.const 32#64],
        Flapjack.Exp.const 32#64]]

def globalBody207_34 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i" (Flapjack.Exp.const 0#64)

def globalBody207_35 : Prog (BitVec 64) :=
.seq globalBody207_33 globalBody207_34

def globalBody207_36 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_withdrawal"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "wd",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 44#64]],
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "roots",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 32#64]]]

def globalBody207_37 : Prog (BitVec 64) :=
.seq globalBody207_36 globalBody207_26

def globalBody207_38 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "nwd")) globalBody207_37

def globalBody207_39 : Prog (BitVec 64) :=
.seq globalBody207_35 globalBody207_38

def globalBody207_40 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_plist_chunks"
  [Flapjack.Exp.var Flapjack.VarKind.local "roots", Flapjack.Exp.var Flapjack.VarKind.local "nwd",
    Flapjack.Exp.var Flapjack.VarKind.local "nwd",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 448#64]]

def globalBody207_41 : Prog (BitVec 64) :=
.seq globalBody207_39 globalBody207_40

def globalBody207_42 : Prog (BitVec 64) :=
.seq globalBody207_41 globalBody207_31

def globalBody207_43 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_u64_at"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 512#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 480#64]]

def globalBody207_44 : Prog (BitVec 64) :=
.seq globalBody207_42 globalBody207_43

def globalBody207_45 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_u64_at"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 520#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 512#64]]

def globalBody207_46 : Prog (BitVec 64) :=
.seq globalBody207_44 globalBody207_45

def globalBody207_47 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_pbytes"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 64#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 72#64]),
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 544#64]]

def globalBody207_48 : Prog (BitVec 64) :=
.seq globalBody207_46 globalBody207_47

def globalBody207_49 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_u64_at"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 532#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 576#64]]

def globalBody207_50 : Prog (BitVec 64) :=
.seq globalBody207_48 globalBody207_49

def globalBody207_51 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_pcontainer"
  [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 19#64,
    Flapjack.Exp.var Flapjack.VarKind.local "out"]

def globalBody207_52 : Prog (BitVec 64) :=
.seq globalBody207_50 globalBody207_51

def globalBody207_53 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody207_54 : Prog (BitVec 64) :=
.seq globalBody207_52 globalBody207_53

def globalBody207_55 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody207_56 : Prog (BitVec 64) :=
.seq globalBody207_54 globalBody207_55

def globalBody207_57 : Prog (BitVec 64) :=
.dec ("nwd") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 56#64])) globalBody207_56

def globalBody207_58 : Prog (BitVec 64) :=
.dec ("wd") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 48#64])) globalBody207_57

def globalBody207_59 : Prog (BitVec 64) :=
.seq globalBody207_32 globalBody207_58

def globalBody207_60 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody207_59

def globalBody207_61 : Prog (BitVec 64) :=
.decCall ("roots") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "ntx", Flapjack.Exp.const 32#64],
      Flapjack.Exp.const 32#64]]) globalBody207_60

def globalBody207_62 : Prog (BitVec 64) :=
.decCall ("m2") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody207_61

def globalBody207_63 : Prog (BitVec 64) :=
.dec ("ntx") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 40#64])) globalBody207_62

def globalBody207_64 : Prog (BitVec 64) :=
.dec ("txs") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 32#64])) globalBody207_63

def globalBody207_65 : Prog (BitVec 64) :=
.seq globalBody207_24 globalBody207_64

def globalBody207_66 : Prog (BitVec 64) :=
.decCall ("ch") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 19#64, Flapjack.Exp.const 32#64]]) globalBody207_65

def globalBody207_67 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody207_66

def globalBody207_68 : Prog (BitVec 64) :=
.dec ("raw") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 0#64])) globalBody207_67

def globalData207 : Decl (BitVec 64) :=
.function { name := "htr_payload", inline := false, exported := false, params := [("pl", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := globalBody207_68, returnShape := (Flapjack.Shape.one) }
def globalOutput207 := Pancake.PanLang.declToHOL globalData207
end InitECandidate.Proofs.FrontendStages.Declarations
