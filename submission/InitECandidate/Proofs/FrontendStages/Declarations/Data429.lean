import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify413
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body429_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "w"])

def body429_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "sort_elems"
  [Flapjack.Exp.var Flapjack.VarKind.local "lp", Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 40#64,
    Flapjack.Exp.const 0#64, Flapjack.Exp.var Flapjack.VarKind.local "tmp"]

def body429_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_put_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "sv"]

def body429_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "r"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "w"])

def body429_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "c",
    Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "e")]

def body429_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "c"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "c", Flapjack.Exp.var Flapjack.VarKind.local "w"])

def body429_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_put_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "c",
    Flapjack.Exp.load
      (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 8#64])]

def body429_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "cs", Flapjack.Exp.var Flapjack.VarKind.local "hl"],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cs", Flapjack.Exp.const 9#64],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "c",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cs", Flapjack.Exp.const 9#64]]]

def body429_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "rlp_encode_list_header"
  [Flapjack.Exp.var Flapjack.VarKind.local "cs",
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "c",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cs", Flapjack.Exp.const 9#64]]]

def body429_9 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "cs"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "cs", Flapjack.Exp.var Flapjack.VarKind.local "hl",
      Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "c",
          Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cs", Flapjack.Exp.const 9#64]]])

def body429_10 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "j"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 1#64])

def body429_11 : Prog (BitVec 64) :=
.seq body429_9 body429_10

def body429_12 : Prog (BitVec 64) :=
.seq body429_8 body429_11

def body429_13 : Prog (BitVec 64) :=
.seq body429_7 body429_12

def body429_14 : Prog (BitVec 64) :=
.decCall ("hl") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "c",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cs", Flapjack.Exp.const 9#64]]]) body429_13

def body429_15 : Prog (BitVec 64) :=
.seq body429_5 body429_14

def body429_16 : Prog (BitVec 64) :=
.seq body429_6 body429_15

def body429_17 : Prog (BitVec 64) :=
.seq body429_5 body429_16

def body429_18 : Prog (BitVec 64) :=
.seq body429_4 body429_17

def body429_19 : Prog (BitVec 64) :=
.dec ("c") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cs", Flapjack.Exp.const 9#64]) body429_18

def body429_20 : Prog (BitVec 64) :=
.dec ("e") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "lp",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 40#64]]) body429_19

def body429_21 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "j")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body429_20

def body429_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "hl2"],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 9#64],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "cs",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 9#64]]]

def body429_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "rlp_encode_list_header"
  [Flapjack.Exp.var Flapjack.VarKind.local "r",
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "cs",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 9#64]]]

def body429_24 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "r"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "hl2",
      Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "cs",
          Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 9#64]]])

def body429_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.var Flapjack.VarKind.local "hl3"],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "r",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]

def body429_26 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "rlp_encode_list_header"
  [Flapjack.Exp.var Flapjack.VarKind.local "q",
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "r",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]

def body429_27 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "q"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.var Flapjack.VarKind.local "hl3",
      Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "r",
          Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]])

def body429_28 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body429_29 : Prog (BitVec 64) :=
.seq body429_27 body429_28

def body429_30 : Prog (BitVec 64) :=
.seq body429_26 body429_29

def body429_31 : Prog (BitVec 64) :=
.seq body429_25 body429_30

def body429_32 : Prog (BitVec 64) :=
.decCall ("hl3") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "r",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]) body429_31

def body429_33 : Prog (BitVec 64) :=
.seq body429_24 body429_32

def body429_34 : Prog (BitVec 64) :=
.seq body429_23 body429_33

def body429_35 : Prog (BitVec 64) :=
.seq body429_22 body429_34

def body429_36 : Prog (BitVec 64) :=
.decCall ("hl2") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "cs",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 9#64]]]) body429_35

def body429_37 : Prog (BitVec 64) :=
.seq body429_21 body429_36

def body429_38 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body429_37

def body429_39 : Prog (BitVec 64) :=
.dec ("cs") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 9#64]) body429_38

def body429_40 : Prog (BitVec 64) :=
.seq body429_3 body429_39

def body429_41 : Prog (BitVec 64) :=
.seq body429_2 body429_40

def body429_42 : Prog (BitVec 64) :=
.decCall ("sv") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.var Flapjack.VarKind.local "slot", Flapjack.Exp.const 32#64]) body429_41

def body429_43 : Prog (BitVec 64) :=
.dec ("r") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]) body429_42

def body429_44 : Prog (BitVec 64) :=
.seq body429_1 body429_43

def body429_45 : Prog (BitVec 64) :=
.dec ("lp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 0#64])) body429_44

def body429_46 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 8#64])) body429_45

def body429_47 : Prog (BitVec 64) :=
.dec ("l") (Flapjack.Shape.one) (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "m")) body429_46

def body429_48 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.var Flapjack.VarKind.local "sc", Flapjack.Exp.var Flapjack.VarKind.local "slot"]) body429_47

def body429_49 : Prog (BitVec 64) :=
.dec ("slot") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "slots"),
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 32#64]]) body429_48

def body429_50 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "slots"))) body429_49

def body429_51 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "hl4"],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "q",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]

def body429_52 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "rlp_encode_list_header"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "q",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]

def body429_53 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "hl4",
      Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "q",
          Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]])

def body429_54 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i" (Flapjack.Exp.const 0#64)

def body429_55 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "rk"),
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "kept", Flapjack.Exp.const 32#64]])
  (Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "rk"),
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 32#64]]))

def body429_56 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "kept"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "kept", Flapjack.Exp.const 1#64])

def body429_57 : Prog (BitVec 64) :=
.seq body429_55 body429_56

def body429_58 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body429_59 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "hasw") (Flapjack.Exp.const 0#64)) body429_57 body429_58

def body429_60 : Prog (BitVec 64) :=
.seq body429_59 body429_28

def body429_61 : Prog (BitVec 64) :=
.decCall ("hasw") (Flapjack.Shape.one) ("htab_has") ([Flapjack.Exp.var Flapjack.VarKind.local "sc",
  Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "rk"),
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 32#64]]]) body429_60

def body429_62 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "rk"))) body429_61

def body429_63 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "sort_elems"
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "rk"), Flapjack.Exp.var Flapjack.VarKind.local "kept",
    Flapjack.Exp.const 32#64, Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "tmp"]

def body429_64 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "q"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64])

def body429_65 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_put_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.var Flapjack.VarKind.local "sv2"]

def body429_66 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "q"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.var Flapjack.VarKind.local "w"])

def body429_67 : Prog (BitVec 64) :=
.seq body429_66 body429_28

def body429_68 : Prog (BitVec 64) :=
.seq body429_65 body429_67

def body429_69 : Prog (BitVec 64) :=
.decCall ("sv2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "rk"),
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 32#64]],
  Flapjack.Exp.const 32#64]) body429_68

def body429_70 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "kept")) body429_69

def body429_71 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "hl5"],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "q",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]

def body429_72 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "hl5",
      Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "q",
          Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]])

def body429_73 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "sort_elems"
  [Flapjack.Exp.var Flapjack.VarKind.local "lp2", Flapjack.Exp.var Flapjack.VarKind.local "n2",
    Flapjack.Exp.const 40#64, Flapjack.Exp.const 0#64, Flapjack.Exp.var Flapjack.VarKind.local "tmp"]

def body429_74 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "c2",
    Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "e2")]

def body429_75 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "c2"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "c2", Flapjack.Exp.var Flapjack.VarKind.local "w"])

def body429_76 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_put_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "c2",
    Flapjack.Exp.load
      (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e2", Flapjack.Exp.const 8#64])]

def body429_77 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.var Flapjack.VarKind.local "hl6"],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "c2",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]

def body429_78 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "rlp_encode_list_header"
  [Flapjack.Exp.var Flapjack.VarKind.local "q",
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "c2",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]

def body429_79 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "q"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.var Flapjack.VarKind.local "hl6",
      Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "c2",
          Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]])

def body429_80 : Prog (BitVec 64) :=
.seq body429_79 body429_28

def body429_81 : Prog (BitVec 64) :=
.seq body429_78 body429_80

def body429_82 : Prog (BitVec 64) :=
.seq body429_77 body429_81

def body429_83 : Prog (BitVec 64) :=
.decCall ("hl6") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "c2",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]) body429_82

def body429_84 : Prog (BitVec 64) :=
.seq body429_75 body429_83

def body429_85 : Prog (BitVec 64) :=
.seq body429_76 body429_84

def body429_86 : Prog (BitVec 64) :=
.seq body429_75 body429_85

def body429_87 : Prog (BitVec 64) :=
.seq body429_74 body429_86

def body429_88 : Prog (BitVec 64) :=
.dec ("c2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]) body429_87

def body429_89 : Prog (BitVec 64) :=
.dec ("e2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "lp2",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 40#64]]) body429_88

def body429_90 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n2")) body429_89

def body429_91 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "hl7"],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "q",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]

def body429_92 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "hl7",
      Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "q",
          Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]])

def body429_93 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "sort_elems"
  [Flapjack.Exp.var Flapjack.VarKind.local "lp3", Flapjack.Exp.var Flapjack.VarKind.local "n3",
    Flapjack.Exp.const 16#64, Flapjack.Exp.const 0#64, Flapjack.Exp.var Flapjack.VarKind.local "tmp"]

def body429_94 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "c3",
    Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "e3")]

def body429_95 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "c3"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "c3", Flapjack.Exp.var Flapjack.VarKind.local "w"])

def body429_96 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "c3",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e3", Flapjack.Exp.const 8#64])]

def body429_97 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.var Flapjack.VarKind.local "hl8"],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "c3",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]

def body429_98 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "rlp_encode_list_header"
  [Flapjack.Exp.var Flapjack.VarKind.local "q",
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "c3",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]

def body429_99 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "q"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.var Flapjack.VarKind.local "hl8",
      Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "c3",
          Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]])

def body429_100 : Prog (BitVec 64) :=
.seq body429_99 body429_28

def body429_101 : Prog (BitVec 64) :=
.seq body429_98 body429_100

def body429_102 : Prog (BitVec 64) :=
.seq body429_97 body429_101

def body429_103 : Prog (BitVec 64) :=
.decCall ("hl8") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "c3",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]) body429_102

def body429_104 : Prog (BitVec 64) :=
.seq body429_95 body429_103

def body429_105 : Prog (BitVec 64) :=
.seq body429_96 body429_104

def body429_106 : Prog (BitVec 64) :=
.seq body429_95 body429_105

def body429_107 : Prog (BitVec 64) :=
.seq body429_94 body429_106

def body429_108 : Prog (BitVec 64) :=
.dec ("c3") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]) body429_107

def body429_109 : Prog (BitVec 64) :=
.dec ("e3") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "lp3",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64]]) body429_108

def body429_110 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n3")) body429_109

def body429_111 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "hl9"],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "q",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]

def body429_112 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "hl9",
      Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "q",
          Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]])

def body429_113 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "sort_elems"
  [Flapjack.Exp.var Flapjack.VarKind.local "lp4", Flapjack.Exp.var Flapjack.VarKind.local "n4",
    Flapjack.Exp.const 24#64, Flapjack.Exp.const 0#64, Flapjack.Exp.var Flapjack.VarKind.local "tmp"]

def body429_114 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "c4",
    Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "e4")]

def body429_115 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "c4"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "c4", Flapjack.Exp.var Flapjack.VarKind.local "w"])

def body429_116 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "c4",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e4", Flapjack.Exp.const 8#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e4", Flapjack.Exp.const 16#64])]

def body429_117 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.var Flapjack.VarKind.local "hl10"],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "c4",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]

def body429_118 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "rlp_encode_list_header"
  [Flapjack.Exp.var Flapjack.VarKind.local "q",
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "c4",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]

def body429_119 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "q"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.var Flapjack.VarKind.local "hl10",
      Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "c4",
          Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]])

def body429_120 : Prog (BitVec 64) :=
.seq body429_119 body429_28

def body429_121 : Prog (BitVec 64) :=
.seq body429_118 body429_120

def body429_122 : Prog (BitVec 64) :=
.seq body429_117 body429_121

def body429_123 : Prog (BitVec 64) :=
.decCall ("hl10") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "c4",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]) body429_122

def body429_124 : Prog (BitVec 64) :=
.seq body429_115 body429_123

def body429_125 : Prog (BitVec 64) :=
.seq body429_116 body429_124

def body429_126 : Prog (BitVec 64) :=
.seq body429_115 body429_125

def body429_127 : Prog (BitVec 64) :=
.seq body429_114 body429_126

def body429_128 : Prog (BitVec 64) :=
.dec ("c4") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]) body429_127

def body429_129 : Prog (BitVec 64) :=
.dec ("e4") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "lp4",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 24#64]]) body429_128

def body429_130 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n4")) body429_129

def body429_131 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "hl11"],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "q",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]

def body429_132 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "hl11",
      Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "q",
          Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]])

def body429_133 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body429_134 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.var Flapjack.VarKind.local "hl12"],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.const 9#64],
    Flapjack.Exp.var Flapjack.VarKind.local "payload"]

def body429_135 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "rlp_encode_list_header"
  [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.var Flapjack.VarKind.local "payload"]

def body429_136 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "hl12", Flapjack.Exp.var Flapjack.VarKind.local "payload"])

def body429_137 : Prog (BitVec 64) :=
.seq body429_135 body429_136

def body429_138 : Prog (BitVec 64) :=
.seq body429_134 body429_137

def body429_139 : Prog (BitVec 64) :=
.decCall ("hl12") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.var Flapjack.VarKind.local "payload"]) body429_138

def body429_140 : Prog (BitVec 64) :=
.dec ("payload") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.const 9#64]]) body429_139

def body429_141 : Prog (BitVec 64) :=
.seq body429_133 body429_140

def body429_142 : Prog (BitVec 64) :=
.seq body429_132 body429_141

def body429_143 : Prog (BitVec 64) :=
.seq body429_52 body429_142

def body429_144 : Prog (BitVec 64) :=
.seq body429_131 body429_143

def body429_145 : Prog (BitVec 64) :=
.decCall ("hl11") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "q",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]) body429_144

def body429_146 : Prog (BitVec 64) :=
.seq body429_130 body429_145

def body429_147 : Prog (BitVec 64) :=
.seq body429_54 body429_146

def body429_148 : Prog (BitVec 64) :=
.seq body429_64 body429_147

def body429_149 : Prog (BitVec 64) :=
.seq body429_113 body429_148

def body429_150 : Prog (BitVec 64) :=
.dec ("lp4") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l4", Flapjack.Exp.const 0#64])) body429_149

def body429_151 : Prog (BitVec 64) :=
.dec ("n4") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l4", Flapjack.Exp.const 8#64])) body429_150

def body429_152 : Prog (BitVec 64) :=
.dec ("l4") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 32#64])) body429_151

def body429_153 : Prog (BitVec 64) :=
.seq body429_112 body429_152

def body429_154 : Prog (BitVec 64) :=
.seq body429_52 body429_153

def body429_155 : Prog (BitVec 64) :=
.seq body429_111 body429_154

def body429_156 : Prog (BitVec 64) :=
.decCall ("hl9") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "q",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]) body429_155

def body429_157 : Prog (BitVec 64) :=
.seq body429_110 body429_156

def body429_158 : Prog (BitVec 64) :=
.seq body429_54 body429_157

def body429_159 : Prog (BitVec 64) :=
.seq body429_64 body429_158

def body429_160 : Prog (BitVec 64) :=
.seq body429_93 body429_159

def body429_161 : Prog (BitVec 64) :=
.dec ("lp3") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l3", Flapjack.Exp.const 0#64])) body429_160

def body429_162 : Prog (BitVec 64) :=
.dec ("n3") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l3", Flapjack.Exp.const 8#64])) body429_161

def body429_163 : Prog (BitVec 64) :=
.dec ("l3") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 24#64])) body429_162

def body429_164 : Prog (BitVec 64) :=
.seq body429_92 body429_163

def body429_165 : Prog (BitVec 64) :=
.seq body429_52 body429_164

def body429_166 : Prog (BitVec 64) :=
.seq body429_91 body429_165

def body429_167 : Prog (BitVec 64) :=
.decCall ("hl7") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "q",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]) body429_166

def body429_168 : Prog (BitVec 64) :=
.seq body429_90 body429_167

def body429_169 : Prog (BitVec 64) :=
.seq body429_54 body429_168

def body429_170 : Prog (BitVec 64) :=
.seq body429_64 body429_169

def body429_171 : Prog (BitVec 64) :=
.seq body429_73 body429_170

def body429_172 : Prog (BitVec 64) :=
.dec ("lp2") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l2", Flapjack.Exp.const 0#64])) body429_171

def body429_173 : Prog (BitVec 64) :=
.dec ("n2") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l2", Flapjack.Exp.const 8#64])) body429_172

def body429_174 : Prog (BitVec 64) :=
.dec ("l2") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 16#64])) body429_173

def body429_175 : Prog (BitVec 64) :=
.seq body429_72 body429_174

def body429_176 : Prog (BitVec 64) :=
.seq body429_52 body429_175

def body429_177 : Prog (BitVec 64) :=
.seq body429_71 body429_176

def body429_178 : Prog (BitVec 64) :=
.decCall ("hl5") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "q",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]) body429_177

def body429_179 : Prog (BitVec 64) :=
.seq body429_70 body429_178

def body429_180 : Prog (BitVec 64) :=
.seq body429_54 body429_179

def body429_181 : Prog (BitVec 64) :=
.seq body429_64 body429_180

def body429_182 : Prog (BitVec 64) :=
.seq body429_63 body429_181

def body429_183 : Prog (BitVec 64) :=
.seq body429_62 body429_182

def body429_184 : Prog (BitVec 64) :=
.seq body429_54 body429_183

def body429_185 : Prog (BitVec 64) :=
.dec ("kept") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body429_184

def body429_186 : Prog (BitVec 64) :=
.decCall ("rk") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_keys") ([Flapjack.Exp.var Flapjack.VarKind.local "sr"]) body429_185

def body429_187 : Prog (BitVec 64) :=
.dec ("sr") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 8#64])) body429_186

def body429_188 : Prog (BitVec 64) :=
.seq body429_53 body429_187

def body429_189 : Prog (BitVec 64) :=
.seq body429_52 body429_188

def body429_190 : Prog (BitVec 64) :=
.seq body429_51 body429_189

def body429_191 : Prog (BitVec 64) :=
.decCall ("hl4") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "q",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]) body429_190

def body429_192 : Prog (BitVec 64) :=
.seq body429_50 body429_191

def body429_193 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body429_192

def body429_194 : Prog (BitVec 64) :=
.dec ("q") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]) body429_193

def body429_195 : Prog (BitVec 64) :=
.decCall ("slots") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("sorted_keys32") ([Flapjack.Exp.var Flapjack.VarKind.local "sc", Flapjack.Exp.var Flapjack.VarKind.local "tmp"]) body429_194

def body429_196 : Prog (BitVec 64) :=
.dec ("sc") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 0#64])) body429_195

def body429_197 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body429_196

def body429_198 : Prog (BitVec 64) :=
.seq body429_0 body429_197

def body429_199 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("rlp_encode_bytes") ([Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 20#64]) body429_198

def body429_200 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.const 9#64]) body429_199

def body429_201 : Prog (BitVec 64) :=
.seq body429_2 body429_3

def body429_202 : Prog (BitVec 64) :=
.seq body429_4 body429_5

def body429_203 : Prog (BitVec 64) :=
.seq body429_202 body429_6

def body429_204 : Prog (BitVec 64) :=
.seq body429_203 body429_5

def body429_205 : Prog (BitVec 64) :=
.seq body429_7 body429_8

def body429_206 : Prog (BitVec 64) :=
.seq body429_205 body429_9

def body429_207 : Prog (BitVec 64) :=
.seq body429_206 body429_10

def body429_208 : Prog (BitVec 64) :=
.decCall ("hl") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "c",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cs", Flapjack.Exp.const 9#64]]]) body429_207

def body429_209 : Prog (BitVec 64) :=
.seq body429_204 body429_208

def body429_210 : Prog (BitVec 64) :=
.dec ("c") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cs", Flapjack.Exp.const 9#64]) body429_209

def body429_211 : Prog (BitVec 64) :=
.dec ("e") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "lp",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 40#64]]) body429_210

def body429_212 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "j")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body429_211

def body429_213 : Prog (BitVec 64) :=
.seq body429_22 body429_23

def body429_214 : Prog (BitVec 64) :=
.seq body429_213 body429_24

def body429_215 : Prog (BitVec 64) :=
.seq body429_25 body429_26

def body429_216 : Prog (BitVec 64) :=
.seq body429_215 body429_27

def body429_217 : Prog (BitVec 64) :=
.seq body429_216 body429_28

def body429_218 : Prog (BitVec 64) :=
.decCall ("hl3") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "r",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]) body429_217

def body429_219 : Prog (BitVec 64) :=
.seq body429_214 body429_218

def body429_220 : Prog (BitVec 64) :=
.decCall ("hl2") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "cs",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 9#64]]]) body429_219

def body429_221 : Prog (BitVec 64) :=
.seq body429_212 body429_220

def body429_222 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body429_221

def body429_223 : Prog (BitVec 64) :=
.dec ("cs") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 9#64]) body429_222

def body429_224 : Prog (BitVec 64) :=
.seq body429_201 body429_223

def body429_225 : Prog (BitVec 64) :=
.decCall ("sv") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.var Flapjack.VarKind.local "slot", Flapjack.Exp.const 32#64]) body429_224

def body429_226 : Prog (BitVec 64) :=
.dec ("r") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]) body429_225

def body429_227 : Prog (BitVec 64) :=
.seq body429_1 body429_226

def body429_228 : Prog (BitVec 64) :=
.dec ("lp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 0#64])) body429_227

def body429_229 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 8#64])) body429_228

def body429_230 : Prog (BitVec 64) :=
.dec ("l") (Flapjack.Shape.one) (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "m")) body429_229

def body429_231 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.var Flapjack.VarKind.local "sc", Flapjack.Exp.var Flapjack.VarKind.local "slot"]) body429_230

def body429_232 : Prog (BitVec 64) :=
.dec ("slot") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "slots"),
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 32#64]]) body429_231

def body429_233 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "slots"))) body429_232

def body429_234 : Prog (BitVec 64) :=
.seq body429_51 body429_52

def body429_235 : Prog (BitVec 64) :=
.seq body429_234 body429_53

def body429_236 : Prog (BitVec 64) :=
.seq body429_54 body429_62

def body429_237 : Prog (BitVec 64) :=
.seq body429_236 body429_63

def body429_238 : Prog (BitVec 64) :=
.seq body429_237 body429_64

def body429_239 : Prog (BitVec 64) :=
.seq body429_238 body429_54

def body429_240 : Prog (BitVec 64) :=
.seq body429_65 body429_66

def body429_241 : Prog (BitVec 64) :=
.seq body429_240 body429_28

def body429_242 : Prog (BitVec 64) :=
.decCall ("sv2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "rk"),
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 32#64]],
  Flapjack.Exp.const 32#64]) body429_241

def body429_243 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "kept")) body429_242

def body429_244 : Prog (BitVec 64) :=
.seq body429_239 body429_243

def body429_245 : Prog (BitVec 64) :=
.seq body429_71 body429_52

def body429_246 : Prog (BitVec 64) :=
.seq body429_245 body429_72

def body429_247 : Prog (BitVec 64) :=
.seq body429_73 body429_64

def body429_248 : Prog (BitVec 64) :=
.seq body429_247 body429_54

def body429_249 : Prog (BitVec 64) :=
.seq body429_74 body429_75

def body429_250 : Prog (BitVec 64) :=
.seq body429_249 body429_76

def body429_251 : Prog (BitVec 64) :=
.seq body429_250 body429_75

def body429_252 : Prog (BitVec 64) :=
.seq body429_77 body429_78

def body429_253 : Prog (BitVec 64) :=
.seq body429_252 body429_79

def body429_254 : Prog (BitVec 64) :=
.seq body429_253 body429_28

def body429_255 : Prog (BitVec 64) :=
.decCall ("hl6") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "c2",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]) body429_254

def body429_256 : Prog (BitVec 64) :=
.seq body429_251 body429_255

def body429_257 : Prog (BitVec 64) :=
.dec ("c2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]) body429_256

def body429_258 : Prog (BitVec 64) :=
.dec ("e2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "lp2",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 40#64]]) body429_257

def body429_259 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n2")) body429_258

def body429_260 : Prog (BitVec 64) :=
.seq body429_248 body429_259

def body429_261 : Prog (BitVec 64) :=
.seq body429_91 body429_52

def body429_262 : Prog (BitVec 64) :=
.seq body429_261 body429_92

def body429_263 : Prog (BitVec 64) :=
.seq body429_93 body429_64

def body429_264 : Prog (BitVec 64) :=
.seq body429_263 body429_54

def body429_265 : Prog (BitVec 64) :=
.seq body429_94 body429_95

def body429_266 : Prog (BitVec 64) :=
.seq body429_265 body429_96

def body429_267 : Prog (BitVec 64) :=
.seq body429_266 body429_95

def body429_268 : Prog (BitVec 64) :=
.seq body429_97 body429_98

def body429_269 : Prog (BitVec 64) :=
.seq body429_268 body429_99

def body429_270 : Prog (BitVec 64) :=
.seq body429_269 body429_28

def body429_271 : Prog (BitVec 64) :=
.decCall ("hl8") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "c3",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]) body429_270

def body429_272 : Prog (BitVec 64) :=
.seq body429_267 body429_271

def body429_273 : Prog (BitVec 64) :=
.dec ("c3") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]) body429_272

def body429_274 : Prog (BitVec 64) :=
.dec ("e3") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "lp3",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64]]) body429_273

def body429_275 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n3")) body429_274

def body429_276 : Prog (BitVec 64) :=
.seq body429_264 body429_275

def body429_277 : Prog (BitVec 64) :=
.seq body429_111 body429_52

def body429_278 : Prog (BitVec 64) :=
.seq body429_277 body429_112

def body429_279 : Prog (BitVec 64) :=
.seq body429_113 body429_64

def body429_280 : Prog (BitVec 64) :=
.seq body429_279 body429_54

def body429_281 : Prog (BitVec 64) :=
.seq body429_114 body429_115

def body429_282 : Prog (BitVec 64) :=
.seq body429_281 body429_116

def body429_283 : Prog (BitVec 64) :=
.seq body429_282 body429_115

def body429_284 : Prog (BitVec 64) :=
.seq body429_117 body429_118

def body429_285 : Prog (BitVec 64) :=
.seq body429_284 body429_119

def body429_286 : Prog (BitVec 64) :=
.seq body429_285 body429_28

def body429_287 : Prog (BitVec 64) :=
.decCall ("hl10") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "c4",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]) body429_286

def body429_288 : Prog (BitVec 64) :=
.seq body429_283 body429_287

def body429_289 : Prog (BitVec 64) :=
.dec ("c4") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]) body429_288

def body429_290 : Prog (BitVec 64) :=
.dec ("e4") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "lp4",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 24#64]]) body429_289

def body429_291 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n4")) body429_290

def body429_292 : Prog (BitVec 64) :=
.seq body429_280 body429_291

def body429_293 : Prog (BitVec 64) :=
.seq body429_131 body429_52

def body429_294 : Prog (BitVec 64) :=
.seq body429_293 body429_132

def body429_295 : Prog (BitVec 64) :=
.seq body429_294 body429_133

def body429_296 : Prog (BitVec 64) :=
.seq body429_134 body429_135

def body429_297 : Prog (BitVec 64) :=
.seq body429_296 body429_136

def body429_298 : Prog (BitVec 64) :=
.decCall ("hl12") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.var Flapjack.VarKind.local "payload"]) body429_297

def body429_299 : Prog (BitVec 64) :=
.dec ("payload") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.const 9#64]]) body429_298

def body429_300 : Prog (BitVec 64) :=
.seq body429_295 body429_299

def body429_301 : Prog (BitVec 64) :=
.decCall ("hl11") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "q",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]) body429_300

def body429_302 : Prog (BitVec 64) :=
.seq body429_292 body429_301

def body429_303 : Prog (BitVec 64) :=
.dec ("lp4") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l4", Flapjack.Exp.const 0#64])) body429_302

def body429_304 : Prog (BitVec 64) :=
.dec ("n4") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l4", Flapjack.Exp.const 8#64])) body429_303

def body429_305 : Prog (BitVec 64) :=
.dec ("l4") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 32#64])) body429_304

def body429_306 : Prog (BitVec 64) :=
.seq body429_278 body429_305

def body429_307 : Prog (BitVec 64) :=
.decCall ("hl9") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "q",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]) body429_306

def body429_308 : Prog (BitVec 64) :=
.seq body429_276 body429_307

def body429_309 : Prog (BitVec 64) :=
.dec ("lp3") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l3", Flapjack.Exp.const 0#64])) body429_308

def body429_310 : Prog (BitVec 64) :=
.dec ("n3") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l3", Flapjack.Exp.const 8#64])) body429_309

def body429_311 : Prog (BitVec 64) :=
.dec ("l3") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 24#64])) body429_310

def body429_312 : Prog (BitVec 64) :=
.seq body429_262 body429_311

def body429_313 : Prog (BitVec 64) :=
.decCall ("hl7") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "q",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]) body429_312

def body429_314 : Prog (BitVec 64) :=
.seq body429_260 body429_313

def body429_315 : Prog (BitVec 64) :=
.dec ("lp2") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l2", Flapjack.Exp.const 0#64])) body429_314

def body429_316 : Prog (BitVec 64) :=
.dec ("n2") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l2", Flapjack.Exp.const 8#64])) body429_315

def body429_317 : Prog (BitVec 64) :=
.dec ("l2") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 16#64])) body429_316

def body429_318 : Prog (BitVec 64) :=
.seq body429_246 body429_317

def body429_319 : Prog (BitVec 64) :=
.decCall ("hl5") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "q",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]) body429_318

def body429_320 : Prog (BitVec 64) :=
.seq body429_244 body429_319

def body429_321 : Prog (BitVec 64) :=
.dec ("kept") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body429_320

def body429_322 : Prog (BitVec 64) :=
.decCall ("rk") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_keys") ([Flapjack.Exp.var Flapjack.VarKind.local "sr"]) body429_321

def body429_323 : Prog (BitVec 64) :=
.dec ("sr") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 8#64])) body429_322

def body429_324 : Prog (BitVec 64) :=
.seq body429_235 body429_323

def body429_325 : Prog (BitVec 64) :=
.decCall ("hl4") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "q",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]) body429_324

def body429_326 : Prog (BitVec 64) :=
.seq body429_233 body429_325

def body429_327 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body429_326

def body429_328 : Prog (BitVec 64) :=
.dec ("q") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]) body429_327

def body429_329 : Prog (BitVec 64) :=
.decCall ("slots") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("sorted_keys32") ([Flapjack.Exp.var Flapjack.VarKind.local "sc", Flapjack.Exp.var Flapjack.VarKind.local "tmp"]) body429_328

def body429_330 : Prog (BitVec 64) :=
.dec ("sc") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 0#64])) body429_329

def body429_331 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body429_330

def body429_332 : Prog (BitVec 64) :=
.seq body429_0 body429_331

def body429_333 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("rlp_encode_bytes") ([Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 20#64]) body429_332

def body429_334 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.const 9#64]) body429_333

def originalData429 : Decl (BitVec 64) :=
.function { name := "bal_encode_account", inline := false, exported := false, params := [("dst", Flapjack.Shape.one), ("addr", Flapjack.Shape.one), ("ad", Flapjack.Shape.one), ("tmp", Flapjack.Shape.one)], body := body429_200, returnShape := (Flapjack.Shape.one) }
def simplifiedData429 : Decl (BitVec 64) :=
.function { name := "bal_encode_account", inline := false, exported := false, params := [("dst", Flapjack.Shape.one), ("addr", Flapjack.Shape.one), ("ad", Flapjack.Shape.one), ("tmp", Flapjack.Shape.one)], body := body429_334, returnShape := (Flapjack.Shape.one) }
def original429 := Pancake.PanLang.declToHOL originalData429
def simplified429 := Pancake.PanLang.declToHOL simplifiedData429
end InitECandidate.Proofs.FrontendStages.Declarations
