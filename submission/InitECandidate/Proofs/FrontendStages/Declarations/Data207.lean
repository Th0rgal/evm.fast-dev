import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify191
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body207_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "ch",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 0#64],
    Flapjack.Exp.const 32#64]

def body207_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_bytes_vector"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 32#64],
    Flapjack.Exp.const 20#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 32#64]]

def body207_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 64#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 52#64],
    Flapjack.Exp.const 32#64]

def body207_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 96#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 84#64],
    Flapjack.Exp.const 32#64]

def body207_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_bytes_vector"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 116#64],
    Flapjack.Exp.const 256#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 128#64]]

def body207_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 160#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 372#64],
    Flapjack.Exp.const 32#64]

def body207_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_u64_at"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 404#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 192#64]]

def body207_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_u64_at"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 412#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 224#64]]

def body207_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_u64_at"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 420#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 256#64]]

def body207_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_u64_at"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 428#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 288#64]]

def body207_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_bytes_list"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 16#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 24#64]),
    Flapjack.Exp.const 1#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 320#64]]

def body207_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 352#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64],
    Flapjack.Exp.const 32#64]

def body207_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 384#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 472#64],
    Flapjack.Exp.const 32#64]

def body207_13 : Prog (BitVec 64) :=
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

def body207_14 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body207_15 : Prog (BitVec 64) :=
.seq body207_13 body207_14

def body207_16 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "ntx")) body207_15

def body207_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_plist_chunks"
  [Flapjack.Exp.var Flapjack.VarKind.local "roots", Flapjack.Exp.var Flapjack.VarKind.local "ntx",
    Flapjack.Exp.var Flapjack.VarKind.local "ntx",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 416#64]]

def body207_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "m2"]

def body207_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "roots"), none)) "alloc"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "nwd", Flapjack.Exp.const 32#64],
        Flapjack.Exp.const 32#64]]

def body207_20 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i" (Flapjack.Exp.const 0#64)

def body207_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_withdrawal"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "wd",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 44#64]],
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "roots",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 32#64]]]

def body207_22 : Prog (BitVec 64) :=
.seq body207_21 body207_14

def body207_23 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "nwd")) body207_22

def body207_24 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_plist_chunks"
  [Flapjack.Exp.var Flapjack.VarKind.local "roots", Flapjack.Exp.var Flapjack.VarKind.local "nwd",
    Flapjack.Exp.var Flapjack.VarKind.local "nwd",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 448#64]]

def body207_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_u64_at"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 512#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 480#64]]

def body207_26 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_u64_at"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 520#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 512#64]]

def body207_27 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_pbytes"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 64#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 72#64]),
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 544#64]]

def body207_28 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_u64_at"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 532#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 576#64]]

def body207_29 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_pcontainer"
  [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 19#64,
    Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body207_30 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body207_31 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body207_32 : Prog (BitVec 64) :=
.seq body207_30 body207_31

def body207_33 : Prog (BitVec 64) :=
.seq body207_29 body207_32

def body207_34 : Prog (BitVec 64) :=
.seq body207_28 body207_33

def body207_35 : Prog (BitVec 64) :=
.seq body207_27 body207_34

def body207_36 : Prog (BitVec 64) :=
.seq body207_26 body207_35

def body207_37 : Prog (BitVec 64) :=
.seq body207_25 body207_36

def body207_38 : Prog (BitVec 64) :=
.seq body207_18 body207_37

def body207_39 : Prog (BitVec 64) :=
.seq body207_24 body207_38

def body207_40 : Prog (BitVec 64) :=
.seq body207_23 body207_39

def body207_41 : Prog (BitVec 64) :=
.seq body207_20 body207_40

def body207_42 : Prog (BitVec 64) :=
.seq body207_19 body207_41

def body207_43 : Prog (BitVec 64) :=
.dec ("nwd") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 56#64])) body207_42

def body207_44 : Prog (BitVec 64) :=
.dec ("wd") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 48#64])) body207_43

def body207_45 : Prog (BitVec 64) :=
.seq body207_18 body207_44

def body207_46 : Prog (BitVec 64) :=
.seq body207_17 body207_45

def body207_47 : Prog (BitVec 64) :=
.seq body207_16 body207_46

def body207_48 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body207_47

def body207_49 : Prog (BitVec 64) :=
.decCall ("roots") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "ntx", Flapjack.Exp.const 32#64],
      Flapjack.Exp.const 32#64]]) body207_48

def body207_50 : Prog (BitVec 64) :=
.decCall ("m2") (Flapjack.Shape.one) ("heap_mark") ([]) body207_49

def body207_51 : Prog (BitVec 64) :=
.dec ("ntx") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 40#64])) body207_50

def body207_52 : Prog (BitVec 64) :=
.dec ("txs") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 32#64])) body207_51

def body207_53 : Prog (BitVec 64) :=
.seq body207_12 body207_52

def body207_54 : Prog (BitVec 64) :=
.seq body207_11 body207_53

def body207_55 : Prog (BitVec 64) :=
.seq body207_10 body207_54

def body207_56 : Prog (BitVec 64) :=
.seq body207_9 body207_55

def body207_57 : Prog (BitVec 64) :=
.seq body207_8 body207_56

def body207_58 : Prog (BitVec 64) :=
.seq body207_7 body207_57

def body207_59 : Prog (BitVec 64) :=
.seq body207_6 body207_58

def body207_60 : Prog (BitVec 64) :=
.seq body207_5 body207_59

def body207_61 : Prog (BitVec 64) :=
.seq body207_4 body207_60

def body207_62 : Prog (BitVec 64) :=
.seq body207_3 body207_61

def body207_63 : Prog (BitVec 64) :=
.seq body207_2 body207_62

def body207_64 : Prog (BitVec 64) :=
.seq body207_1 body207_63

def body207_65 : Prog (BitVec 64) :=
.seq body207_0 body207_64

def body207_66 : Prog (BitVec 64) :=
.decCall ("ch") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 19#64, Flapjack.Exp.const 32#64]]) body207_65

def body207_67 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body207_66

def body207_68 : Prog (BitVec 64) :=
.dec ("raw") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 0#64])) body207_67

def body207_69 : Prog (BitVec 64) :=
.seq body207_0 body207_1

def body207_70 : Prog (BitVec 64) :=
.seq body207_69 body207_2

def body207_71 : Prog (BitVec 64) :=
.seq body207_70 body207_3

def body207_72 : Prog (BitVec 64) :=
.seq body207_71 body207_4

def body207_73 : Prog (BitVec 64) :=
.seq body207_72 body207_5

def body207_74 : Prog (BitVec 64) :=
.seq body207_73 body207_6

def body207_75 : Prog (BitVec 64) :=
.seq body207_74 body207_7

def body207_76 : Prog (BitVec 64) :=
.seq body207_75 body207_8

def body207_77 : Prog (BitVec 64) :=
.seq body207_76 body207_9

def body207_78 : Prog (BitVec 64) :=
.seq body207_77 body207_10

def body207_79 : Prog (BitVec 64) :=
.seq body207_78 body207_11

def body207_80 : Prog (BitVec 64) :=
.seq body207_79 body207_12

def body207_81 : Prog (BitVec 64) :=
.seq body207_16 body207_17

def body207_82 : Prog (BitVec 64) :=
.seq body207_81 body207_18

def body207_83 : Prog (BitVec 64) :=
.seq body207_19 body207_20

def body207_84 : Prog (BitVec 64) :=
.seq body207_83 body207_23

def body207_85 : Prog (BitVec 64) :=
.seq body207_84 body207_24

def body207_86 : Prog (BitVec 64) :=
.seq body207_85 body207_18

def body207_87 : Prog (BitVec 64) :=
.seq body207_86 body207_25

def body207_88 : Prog (BitVec 64) :=
.seq body207_87 body207_26

def body207_89 : Prog (BitVec 64) :=
.seq body207_88 body207_27

def body207_90 : Prog (BitVec 64) :=
.seq body207_89 body207_28

def body207_91 : Prog (BitVec 64) :=
.seq body207_90 body207_29

def body207_92 : Prog (BitVec 64) :=
.seq body207_91 body207_30

def body207_93 : Prog (BitVec 64) :=
.seq body207_92 body207_31

def body207_94 : Prog (BitVec 64) :=
.dec ("nwd") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 56#64])) body207_93

def body207_95 : Prog (BitVec 64) :=
.dec ("wd") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 48#64])) body207_94

def body207_96 : Prog (BitVec 64) :=
.seq body207_82 body207_95

def body207_97 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body207_96

def body207_98 : Prog (BitVec 64) :=
.decCall ("roots") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "ntx", Flapjack.Exp.const 32#64],
      Flapjack.Exp.const 32#64]]) body207_97

def body207_99 : Prog (BitVec 64) :=
.decCall ("m2") (Flapjack.Shape.one) ("heap_mark") ([]) body207_98

def body207_100 : Prog (BitVec 64) :=
.dec ("ntx") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 40#64])) body207_99

def body207_101 : Prog (BitVec 64) :=
.dec ("txs") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 32#64])) body207_100

def body207_102 : Prog (BitVec 64) :=
.seq body207_80 body207_101

def body207_103 : Prog (BitVec 64) :=
.decCall ("ch") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 19#64, Flapjack.Exp.const 32#64]]) body207_102

def body207_104 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body207_103

def body207_105 : Prog (BitVec 64) :=
.dec ("raw") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 0#64])) body207_104

def originalData207 : Decl (BitVec 64) :=
.function { name := "htr_payload", inline := false, exported := false, params := [("pl", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body207_68, returnShape := (Flapjack.Shape.one) }
def simplifiedData207 : Decl (BitVec 64) :=
.function { name := "htr_payload", inline := false, exported := false, params := [("pl", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body207_105, returnShape := (Flapjack.Shape.one) }
def original207 := Pancake.PanLang.declToHOL originalData207
def simplified207 := Pancake.PanLang.declToHOL simplifiedData207
end InitECandidate.Proofs.FrontendStages.Declarations
