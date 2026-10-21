import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data429
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate413
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody429_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "w"])

def globalBody429_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "sort_elems"
  [Flapjack.Exp.var Flapjack.VarKind.local "lp", Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 40#64,
    Flapjack.Exp.const 0#64, Flapjack.Exp.var Flapjack.VarKind.local "tmp"]

def globalBody429_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_put_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "sv"]

def globalBody429_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "r"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "w"])

def globalBody429_4 : Prog (BitVec 64) :=
.seq globalBody429_2 globalBody429_3

def globalBody429_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "c",
    Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "e")]

def globalBody429_6 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "c"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "c", Flapjack.Exp.var Flapjack.VarKind.local "w"])

def globalBody429_7 : Prog (BitVec 64) :=
.seq globalBody429_5 globalBody429_6

def globalBody429_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_put_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "c",
    Flapjack.Exp.load
      (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 8#64])]

def globalBody429_9 : Prog (BitVec 64) :=
.seq globalBody429_7 globalBody429_8

def globalBody429_10 : Prog (BitVec 64) :=
.seq globalBody429_9 globalBody429_6

def globalBody429_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "cs", Flapjack.Exp.var Flapjack.VarKind.local "hl"],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cs", Flapjack.Exp.const 9#64],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "c",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cs", Flapjack.Exp.const 9#64]]]

def globalBody429_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "rlp_encode_list_header"
  [Flapjack.Exp.var Flapjack.VarKind.local "cs",
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "c",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cs", Flapjack.Exp.const 9#64]]]

def globalBody429_13 : Prog (BitVec 64) :=
.seq globalBody429_11 globalBody429_12

def globalBody429_14 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "cs"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "cs", Flapjack.Exp.var Flapjack.VarKind.local "hl",
      Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "c",
          Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cs", Flapjack.Exp.const 9#64]]])

def globalBody429_15 : Prog (BitVec 64) :=
.seq globalBody429_13 globalBody429_14

def globalBody429_16 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "j"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 1#64])

def globalBody429_17 : Prog (BitVec 64) :=
.seq globalBody429_15 globalBody429_16

def globalBody429_18 : Prog (BitVec 64) :=
.decCall ("hl") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "c",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cs", Flapjack.Exp.const 9#64]]]) globalBody429_17

def globalBody429_19 : Prog (BitVec 64) :=
.seq globalBody429_10 globalBody429_18

def globalBody429_20 : Prog (BitVec 64) :=
.dec ("c") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cs", Flapjack.Exp.const 9#64]) globalBody429_19

def globalBody429_21 : Prog (BitVec 64) :=
.dec ("e") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "lp",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 40#64]]) globalBody429_20

def globalBody429_22 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "j")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) globalBody429_21

def globalBody429_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "hl2"],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 9#64],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "cs",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 9#64]]]

def globalBody429_24 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "rlp_encode_list_header"
  [Flapjack.Exp.var Flapjack.VarKind.local "r",
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "cs",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 9#64]]]

def globalBody429_25 : Prog (BitVec 64) :=
.seq globalBody429_23 globalBody429_24

def globalBody429_26 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "r"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "hl2",
      Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "cs",
          Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 9#64]]])

def globalBody429_27 : Prog (BitVec 64) :=
.seq globalBody429_25 globalBody429_26

def globalBody429_28 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.var Flapjack.VarKind.local "hl3"],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "r",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]

def globalBody429_29 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "rlp_encode_list_header"
  [Flapjack.Exp.var Flapjack.VarKind.local "q",
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "r",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]

def globalBody429_30 : Prog (BitVec 64) :=
.seq globalBody429_28 globalBody429_29

def globalBody429_31 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "q"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.var Flapjack.VarKind.local "hl3",
      Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "r",
          Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]])

def globalBody429_32 : Prog (BitVec 64) :=
.seq globalBody429_30 globalBody429_31

def globalBody429_33 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody429_34 : Prog (BitVec 64) :=
.seq globalBody429_32 globalBody429_33

def globalBody429_35 : Prog (BitVec 64) :=
.decCall ("hl3") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "r",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]) globalBody429_34

def globalBody429_36 : Prog (BitVec 64) :=
.seq globalBody429_27 globalBody429_35

def globalBody429_37 : Prog (BitVec 64) :=
.decCall ("hl2") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "cs",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 9#64]]]) globalBody429_36

def globalBody429_38 : Prog (BitVec 64) :=
.seq globalBody429_22 globalBody429_37

def globalBody429_39 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody429_38

def globalBody429_40 : Prog (BitVec 64) :=
.dec ("cs") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 9#64]) globalBody429_39

def globalBody429_41 : Prog (BitVec 64) :=
.seq globalBody429_4 globalBody429_40

def globalBody429_42 : Prog (BitVec 64) :=
.decCall ("sv") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.var Flapjack.VarKind.local "slot", Flapjack.Exp.const 32#64]) globalBody429_41

def globalBody429_43 : Prog (BitVec 64) :=
.dec ("r") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]) globalBody429_42

def globalBody429_44 : Prog (BitVec 64) :=
.seq globalBody429_1 globalBody429_43

def globalBody429_45 : Prog (BitVec 64) :=
.dec ("lp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 0#64])) globalBody429_44

def globalBody429_46 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 8#64])) globalBody429_45

def globalBody429_47 : Prog (BitVec 64) :=
.dec ("l") (Flapjack.Shape.one) (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "m")) globalBody429_46

def globalBody429_48 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.var Flapjack.VarKind.local "sc", Flapjack.Exp.var Flapjack.VarKind.local "slot"]) globalBody429_47

def globalBody429_49 : Prog (BitVec 64) :=
.dec ("slot") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "slots"),
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 32#64]]) globalBody429_48

def globalBody429_50 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "slots"))) globalBody429_49

def globalBody429_51 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "hl4"],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "q",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]

def globalBody429_52 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "rlp_encode_list_header"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "q",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]

def globalBody429_53 : Prog (BitVec 64) :=
.seq globalBody429_51 globalBody429_52

def globalBody429_54 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "hl4",
      Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "q",
          Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]])

def globalBody429_55 : Prog (BitVec 64) :=
.seq globalBody429_53 globalBody429_54

def globalBody429_56 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i" (Flapjack.Exp.const 0#64)

def globalBody429_57 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "rk"),
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "kept", Flapjack.Exp.const 32#64]])
  (Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "rk"),
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 32#64]]))

def globalBody429_58 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "kept"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "kept", Flapjack.Exp.const 1#64])

def globalBody429_59 : Prog (BitVec 64) :=
.seq globalBody429_57 globalBody429_58

def globalBody429_60 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody429_61 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "hasw") (Flapjack.Exp.const 0#64)) globalBody429_59 globalBody429_60

def globalBody429_62 : Prog (BitVec 64) :=
.seq globalBody429_61 globalBody429_33

def globalBody429_63 : Prog (BitVec 64) :=
.decCall ("hasw") (Flapjack.Shape.one) ("htab_has") ([Flapjack.Exp.var Flapjack.VarKind.local "sc",
  Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "rk"),
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 32#64]]]) globalBody429_62

def globalBody429_64 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "rk"))) globalBody429_63

def globalBody429_65 : Prog (BitVec 64) :=
.seq globalBody429_56 globalBody429_64

def globalBody429_66 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "sort_elems"
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "rk"), Flapjack.Exp.var Flapjack.VarKind.local "kept",
    Flapjack.Exp.const 32#64, Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "tmp"]

def globalBody429_67 : Prog (BitVec 64) :=
.seq globalBody429_65 globalBody429_66

def globalBody429_68 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "q"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64])

def globalBody429_69 : Prog (BitVec 64) :=
.seq globalBody429_67 globalBody429_68

def globalBody429_70 : Prog (BitVec 64) :=
.seq globalBody429_69 globalBody429_56

def globalBody429_71 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_put_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.var Flapjack.VarKind.local "sv2"]

def globalBody429_72 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "q"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.var Flapjack.VarKind.local "w"])

def globalBody429_73 : Prog (BitVec 64) :=
.seq globalBody429_71 globalBody429_72

def globalBody429_74 : Prog (BitVec 64) :=
.seq globalBody429_73 globalBody429_33

def globalBody429_75 : Prog (BitVec 64) :=
.decCall ("sv2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "rk"),
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 32#64]],
  Flapjack.Exp.const 32#64]) globalBody429_74

def globalBody429_76 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "kept")) globalBody429_75

def globalBody429_77 : Prog (BitVec 64) :=
.seq globalBody429_70 globalBody429_76

def globalBody429_78 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "hl5"],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "q",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]

def globalBody429_79 : Prog (BitVec 64) :=
.seq globalBody429_78 globalBody429_52

def globalBody429_80 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "hl5",
      Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "q",
          Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]])

def globalBody429_81 : Prog (BitVec 64) :=
.seq globalBody429_79 globalBody429_80

def globalBody429_82 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "sort_elems"
  [Flapjack.Exp.var Flapjack.VarKind.local "lp2", Flapjack.Exp.var Flapjack.VarKind.local "n2",
    Flapjack.Exp.const 40#64, Flapjack.Exp.const 0#64, Flapjack.Exp.var Flapjack.VarKind.local "tmp"]

def globalBody429_83 : Prog (BitVec 64) :=
.seq globalBody429_82 globalBody429_68

def globalBody429_84 : Prog (BitVec 64) :=
.seq globalBody429_83 globalBody429_56

def globalBody429_85 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "c2",
    Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "e2")]

def globalBody429_86 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "c2"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "c2", Flapjack.Exp.var Flapjack.VarKind.local "w"])

def globalBody429_87 : Prog (BitVec 64) :=
.seq globalBody429_85 globalBody429_86

def globalBody429_88 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_put_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "c2",
    Flapjack.Exp.load
      (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e2", Flapjack.Exp.const 8#64])]

def globalBody429_89 : Prog (BitVec 64) :=
.seq globalBody429_87 globalBody429_88

def globalBody429_90 : Prog (BitVec 64) :=
.seq globalBody429_89 globalBody429_86

def globalBody429_91 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.var Flapjack.VarKind.local "hl6"],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "c2",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]

def globalBody429_92 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "rlp_encode_list_header"
  [Flapjack.Exp.var Flapjack.VarKind.local "q",
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "c2",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]

def globalBody429_93 : Prog (BitVec 64) :=
.seq globalBody429_91 globalBody429_92

def globalBody429_94 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "q"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.var Flapjack.VarKind.local "hl6",
      Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "c2",
          Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]])

def globalBody429_95 : Prog (BitVec 64) :=
.seq globalBody429_93 globalBody429_94

def globalBody429_96 : Prog (BitVec 64) :=
.seq globalBody429_95 globalBody429_33

def globalBody429_97 : Prog (BitVec 64) :=
.decCall ("hl6") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "c2",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]) globalBody429_96

def globalBody429_98 : Prog (BitVec 64) :=
.seq globalBody429_90 globalBody429_97

def globalBody429_99 : Prog (BitVec 64) :=
.dec ("c2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]) globalBody429_98

def globalBody429_100 : Prog (BitVec 64) :=
.dec ("e2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "lp2",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 40#64]]) globalBody429_99

def globalBody429_101 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n2")) globalBody429_100

def globalBody429_102 : Prog (BitVec 64) :=
.seq globalBody429_84 globalBody429_101

def globalBody429_103 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "hl7"],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "q",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]

def globalBody429_104 : Prog (BitVec 64) :=
.seq globalBody429_103 globalBody429_52

def globalBody429_105 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "hl7",
      Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "q",
          Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]])

def globalBody429_106 : Prog (BitVec 64) :=
.seq globalBody429_104 globalBody429_105

def globalBody429_107 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "sort_elems"
  [Flapjack.Exp.var Flapjack.VarKind.local "lp3", Flapjack.Exp.var Flapjack.VarKind.local "n3",
    Flapjack.Exp.const 16#64, Flapjack.Exp.const 0#64, Flapjack.Exp.var Flapjack.VarKind.local "tmp"]

def globalBody429_108 : Prog (BitVec 64) :=
.seq globalBody429_107 globalBody429_68

def globalBody429_109 : Prog (BitVec 64) :=
.seq globalBody429_108 globalBody429_56

def globalBody429_110 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "c3",
    Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "e3")]

def globalBody429_111 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "c3"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "c3", Flapjack.Exp.var Flapjack.VarKind.local "w"])

def globalBody429_112 : Prog (BitVec 64) :=
.seq globalBody429_110 globalBody429_111

def globalBody429_113 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "c3",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e3", Flapjack.Exp.const 8#64])]

def globalBody429_114 : Prog (BitVec 64) :=
.seq globalBody429_112 globalBody429_113

def globalBody429_115 : Prog (BitVec 64) :=
.seq globalBody429_114 globalBody429_111

def globalBody429_116 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.var Flapjack.VarKind.local "hl8"],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "c3",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]

def globalBody429_117 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "rlp_encode_list_header"
  [Flapjack.Exp.var Flapjack.VarKind.local "q",
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "c3",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]

def globalBody429_118 : Prog (BitVec 64) :=
.seq globalBody429_116 globalBody429_117

def globalBody429_119 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "q"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.var Flapjack.VarKind.local "hl8",
      Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "c3",
          Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]])

def globalBody429_120 : Prog (BitVec 64) :=
.seq globalBody429_118 globalBody429_119

def globalBody429_121 : Prog (BitVec 64) :=
.seq globalBody429_120 globalBody429_33

def globalBody429_122 : Prog (BitVec 64) :=
.decCall ("hl8") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "c3",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]) globalBody429_121

def globalBody429_123 : Prog (BitVec 64) :=
.seq globalBody429_115 globalBody429_122

def globalBody429_124 : Prog (BitVec 64) :=
.dec ("c3") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]) globalBody429_123

def globalBody429_125 : Prog (BitVec 64) :=
.dec ("e3") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "lp3",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64]]) globalBody429_124

def globalBody429_126 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n3")) globalBody429_125

def globalBody429_127 : Prog (BitVec 64) :=
.seq globalBody429_109 globalBody429_126

def globalBody429_128 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "hl9"],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "q",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]

def globalBody429_129 : Prog (BitVec 64) :=
.seq globalBody429_128 globalBody429_52

def globalBody429_130 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "hl9",
      Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "q",
          Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]])

def globalBody429_131 : Prog (BitVec 64) :=
.seq globalBody429_129 globalBody429_130

def globalBody429_132 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "sort_elems"
  [Flapjack.Exp.var Flapjack.VarKind.local "lp4", Flapjack.Exp.var Flapjack.VarKind.local "n4",
    Flapjack.Exp.const 24#64, Flapjack.Exp.const 0#64, Flapjack.Exp.var Flapjack.VarKind.local "tmp"]

def globalBody429_133 : Prog (BitVec 64) :=
.seq globalBody429_132 globalBody429_68

def globalBody429_134 : Prog (BitVec 64) :=
.seq globalBody429_133 globalBody429_56

def globalBody429_135 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "c4",
    Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "e4")]

def globalBody429_136 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "c4"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "c4", Flapjack.Exp.var Flapjack.VarKind.local "w"])

def globalBody429_137 : Prog (BitVec 64) :=
.seq globalBody429_135 globalBody429_136

def globalBody429_138 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "c4",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e4", Flapjack.Exp.const 8#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e4", Flapjack.Exp.const 16#64])]

def globalBody429_139 : Prog (BitVec 64) :=
.seq globalBody429_137 globalBody429_138

def globalBody429_140 : Prog (BitVec 64) :=
.seq globalBody429_139 globalBody429_136

def globalBody429_141 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.var Flapjack.VarKind.local "hl10"],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "c4",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]

def globalBody429_142 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "rlp_encode_list_header"
  [Flapjack.Exp.var Flapjack.VarKind.local "q",
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "c4",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]

def globalBody429_143 : Prog (BitVec 64) :=
.seq globalBody429_141 globalBody429_142

def globalBody429_144 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "q"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.var Flapjack.VarKind.local "hl10",
      Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "c4",
          Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]])

def globalBody429_145 : Prog (BitVec 64) :=
.seq globalBody429_143 globalBody429_144

def globalBody429_146 : Prog (BitVec 64) :=
.seq globalBody429_145 globalBody429_33

def globalBody429_147 : Prog (BitVec 64) :=
.decCall ("hl10") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "c4",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]]]) globalBody429_146

def globalBody429_148 : Prog (BitVec 64) :=
.seq globalBody429_140 globalBody429_147

def globalBody429_149 : Prog (BitVec 64) :=
.dec ("c4") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.const 9#64]) globalBody429_148

def globalBody429_150 : Prog (BitVec 64) :=
.dec ("e4") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "lp4",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 24#64]]) globalBody429_149

def globalBody429_151 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n4")) globalBody429_150

def globalBody429_152 : Prog (BitVec 64) :=
.seq globalBody429_134 globalBody429_151

def globalBody429_153 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "hl11"],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "q",
        Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]

def globalBody429_154 : Prog (BitVec 64) :=
.seq globalBody429_153 globalBody429_52

def globalBody429_155 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "hl11",
      Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "q",
          Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]])

def globalBody429_156 : Prog (BitVec 64) :=
.seq globalBody429_154 globalBody429_155

def globalBody429_157 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody429_158 : Prog (BitVec 64) :=
.seq globalBody429_156 globalBody429_157

def globalBody429_159 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.var Flapjack.VarKind.local "hl12"],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.const 9#64],
    Flapjack.Exp.var Flapjack.VarKind.local "payload"]

def globalBody429_160 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "rlp_encode_list_header"
  [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.var Flapjack.VarKind.local "payload"]

def globalBody429_161 : Prog (BitVec 64) :=
.seq globalBody429_159 globalBody429_160

def globalBody429_162 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "hl12", Flapjack.Exp.var Flapjack.VarKind.local "payload"])

def globalBody429_163 : Prog (BitVec 64) :=
.seq globalBody429_161 globalBody429_162

def globalBody429_164 : Prog (BitVec 64) :=
.decCall ("hl12") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.var Flapjack.VarKind.local "payload"]) globalBody429_163

def globalBody429_165 : Prog (BitVec 64) :=
.dec ("payload") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.const 9#64]]) globalBody429_164

def globalBody429_166 : Prog (BitVec 64) :=
.seq globalBody429_158 globalBody429_165

def globalBody429_167 : Prog (BitVec 64) :=
.decCall ("hl11") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "q",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]) globalBody429_166

def globalBody429_168 : Prog (BitVec 64) :=
.seq globalBody429_152 globalBody429_167

def globalBody429_169 : Prog (BitVec 64) :=
.dec ("lp4") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l4", Flapjack.Exp.const 0#64])) globalBody429_168

def globalBody429_170 : Prog (BitVec 64) :=
.dec ("n4") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l4", Flapjack.Exp.const 8#64])) globalBody429_169

def globalBody429_171 : Prog (BitVec 64) :=
.dec ("l4") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 32#64])) globalBody429_170

def globalBody429_172 : Prog (BitVec 64) :=
.seq globalBody429_131 globalBody429_171

def globalBody429_173 : Prog (BitVec 64) :=
.decCall ("hl9") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "q",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]) globalBody429_172

def globalBody429_174 : Prog (BitVec 64) :=
.seq globalBody429_127 globalBody429_173

def globalBody429_175 : Prog (BitVec 64) :=
.dec ("lp3") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l3", Flapjack.Exp.const 0#64])) globalBody429_174

def globalBody429_176 : Prog (BitVec 64) :=
.dec ("n3") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l3", Flapjack.Exp.const 8#64])) globalBody429_175

def globalBody429_177 : Prog (BitVec 64) :=
.dec ("l3") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 24#64])) globalBody429_176

def globalBody429_178 : Prog (BitVec 64) :=
.seq globalBody429_106 globalBody429_177

def globalBody429_179 : Prog (BitVec 64) :=
.decCall ("hl7") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "q",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]) globalBody429_178

def globalBody429_180 : Prog (BitVec 64) :=
.seq globalBody429_102 globalBody429_179

def globalBody429_181 : Prog (BitVec 64) :=
.dec ("lp2") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l2", Flapjack.Exp.const 0#64])) globalBody429_180

def globalBody429_182 : Prog (BitVec 64) :=
.dec ("n2") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l2", Flapjack.Exp.const 8#64])) globalBody429_181

def globalBody429_183 : Prog (BitVec 64) :=
.dec ("l2") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 16#64])) globalBody429_182

def globalBody429_184 : Prog (BitVec 64) :=
.seq globalBody429_81 globalBody429_183

def globalBody429_185 : Prog (BitVec 64) :=
.decCall ("hl5") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "q",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]) globalBody429_184

def globalBody429_186 : Prog (BitVec 64) :=
.seq globalBody429_77 globalBody429_185

def globalBody429_187 : Prog (BitVec 64) :=
.dec ("kept") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody429_186

def globalBody429_188 : Prog (BitVec 64) :=
.decCall ("rk") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_keys") ([Flapjack.Exp.var Flapjack.VarKind.local "sr"]) globalBody429_187

def globalBody429_189 : Prog (BitVec 64) :=
.dec ("sr") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 8#64])) globalBody429_188

def globalBody429_190 : Prog (BitVec 64) :=
.seq globalBody429_55 globalBody429_189

def globalBody429_191 : Prog (BitVec 64) :=
.decCall ("hl4") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "q",
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]]]) globalBody429_190

def globalBody429_192 : Prog (BitVec 64) :=
.seq globalBody429_50 globalBody429_191

def globalBody429_193 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody429_192

def globalBody429_194 : Prog (BitVec 64) :=
.dec ("q") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 9#64]) globalBody429_193

def globalBody429_195 : Prog (BitVec 64) :=
.decCall ("slots") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("sorted_keys32") ([Flapjack.Exp.var Flapjack.VarKind.local "sc", Flapjack.Exp.var Flapjack.VarKind.local "tmp"]) globalBody429_194

def globalBody429_196 : Prog (BitVec 64) :=
.dec ("sc") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 0#64])) globalBody429_195

def globalBody429_197 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody429_196

def globalBody429_198 : Prog (BitVec 64) :=
.seq globalBody429_0 globalBody429_197

def globalBody429_199 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("rlp_encode_bytes") ([Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 20#64]) globalBody429_198

def globalBody429_200 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.const 9#64]) globalBody429_199

def globalData429 : Decl (BitVec 64) :=
.function { name := "bal_encode_account", inline := false, exported := false, params := [("dst", Flapjack.Shape.one), ("addr", Flapjack.Shape.one), ("ad", Flapjack.Shape.one), ("tmp", Flapjack.Shape.one)], body := globalBody429_200, returnShape := (Flapjack.Shape.one) }
def globalOutput429 := Pancake.PanLang.declToHOL globalData429
end InitECandidate.Proofs.FrontendStages.Declarations
