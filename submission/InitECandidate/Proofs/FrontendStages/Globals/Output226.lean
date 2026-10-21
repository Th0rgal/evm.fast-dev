import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data226
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate208
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody226_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "w"])

def globalBody226_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 16#64]),
    Flapjack.Exp.const 32#64]

def globalBody226_2 : Prog (BitVec 64) :=
.seq globalBody226_0 globalBody226_1

def globalBody226_3 : Prog (BitVec 64) :=
.seq globalBody226_2 globalBody226_0

def globalBody226_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 24#64]),
    Flapjack.Exp.const 20#64]

def globalBody226_5 : Prog (BitVec 64) :=
.seq globalBody226_3 globalBody226_4

def globalBody226_6 : Prog (BitVec 64) :=
.seq globalBody226_5 globalBody226_0

def globalBody226_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 32#64]),
    Flapjack.Exp.const 32#64]

def globalBody226_8 : Prog (BitVec 64) :=
.seq globalBody226_6 globalBody226_7

def globalBody226_9 : Prog (BitVec 64) :=
.seq globalBody226_8 globalBody226_0

def globalBody226_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 40#64]),
    Flapjack.Exp.const 32#64]

def globalBody226_11 : Prog (BitVec 64) :=
.seq globalBody226_9 globalBody226_10

def globalBody226_12 : Prog (BitVec 64) :=
.seq globalBody226_11 globalBody226_0

def globalBody226_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 48#64]),
    Flapjack.Exp.const 32#64]

def globalBody226_14 : Prog (BitVec 64) :=
.seq globalBody226_12 globalBody226_13

def globalBody226_15 : Prog (BitVec 64) :=
.seq globalBody226_14 globalBody226_0

def globalBody226_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 56#64]),
    Flapjack.Exp.const 256#64]

def globalBody226_17 : Prog (BitVec 64) :=
.seq globalBody226_15 globalBody226_16

def globalBody226_18 : Prog (BitVec 64) :=
.seq globalBody226_17 globalBody226_0

def globalBody226_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_put_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load
      (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 64#64])]

def globalBody226_20 : Prog (BitVec 64) :=
.seq globalBody226_18 globalBody226_19

def globalBody226_21 : Prog (BitVec 64) :=
.seq globalBody226_20 globalBody226_0

def globalBody226_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 96#64])]

def globalBody226_23 : Prog (BitVec 64) :=
.seq globalBody226_21 globalBody226_22

def globalBody226_24 : Prog (BitVec 64) :=
.seq globalBody226_23 globalBody226_0

def globalBody226_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 104#64])]

def globalBody226_26 : Prog (BitVec 64) :=
.seq globalBody226_24 globalBody226_25

def globalBody226_27 : Prog (BitVec 64) :=
.seq globalBody226_26 globalBody226_0

def globalBody226_28 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 112#64])]

def globalBody226_29 : Prog (BitVec 64) :=
.seq globalBody226_27 globalBody226_28

def globalBody226_30 : Prog (BitVec 64) :=
.seq globalBody226_29 globalBody226_0

def globalBody226_31 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 120#64])]

def globalBody226_32 : Prog (BitVec 64) :=
.seq globalBody226_30 globalBody226_31

def globalBody226_33 : Prog (BitVec 64) :=
.seq globalBody226_32 globalBody226_0

def globalBody226_34 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 128#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 136#64])]

def globalBody226_35 : Prog (BitVec 64) :=
.seq globalBody226_33 globalBody226_34

def globalBody226_36 : Prog (BitVec 64) :=
.seq globalBody226_35 globalBody226_0

def globalBody226_37 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 144#64]),
    Flapjack.Exp.const 32#64]

def globalBody226_38 : Prog (BitVec 64) :=
.seq globalBody226_36 globalBody226_37

def globalBody226_39 : Prog (BitVec 64) :=
.seq globalBody226_38 globalBody226_0

def globalBody226_40 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 152#64]),
    Flapjack.Exp.const 8#64]

def globalBody226_41 : Prog (BitVec 64) :=
.seq globalBody226_39 globalBody226_40

def globalBody226_42 : Prog (BitVec 64) :=
.seq globalBody226_41 globalBody226_0

def globalBody226_43 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_put_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load
      (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 160#64])]

def globalBody226_44 : Prog (BitVec 64) :=
.seq globalBody226_42 globalBody226_43

def globalBody226_45 : Prog (BitVec 64) :=
.seq globalBody226_44 globalBody226_0

def globalBody226_46 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 192#64]),
    Flapjack.Exp.const 32#64]

def globalBody226_47 : Prog (BitVec 64) :=
.seq globalBody226_45 globalBody226_46

def globalBody226_48 : Prog (BitVec 64) :=
.seq globalBody226_47 globalBody226_0

def globalBody226_49 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 200#64])]

def globalBody226_50 : Prog (BitVec 64) :=
.seq globalBody226_48 globalBody226_49

def globalBody226_51 : Prog (BitVec 64) :=
.seq globalBody226_50 globalBody226_0

def globalBody226_52 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 208#64])]

def globalBody226_53 : Prog (BitVec 64) :=
.seq globalBody226_51 globalBody226_52

def globalBody226_54 : Prog (BitVec 64) :=
.seq globalBody226_53 globalBody226_0

def globalBody226_55 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 216#64]),
    Flapjack.Exp.const 32#64]

def globalBody226_56 : Prog (BitVec 64) :=
.seq globalBody226_54 globalBody226_55

def globalBody226_57 : Prog (BitVec 64) :=
.seq globalBody226_56 globalBody226_0

def globalBody226_58 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 224#64]),
    Flapjack.Exp.const 32#64]

def globalBody226_59 : Prog (BitVec 64) :=
.seq globalBody226_57 globalBody226_58

def globalBody226_60 : Prog (BitVec 64) :=
.seq globalBody226_59 globalBody226_0

def globalBody226_61 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 232#64]),
    Flapjack.Exp.const 32#64]

def globalBody226_62 : Prog (BitVec 64) :=
.seq globalBody226_61 globalBody226_0

def globalBody226_63 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 240#64])]

def globalBody226_64 : Prog (BitVec 64) :=
.seq globalBody226_62 globalBody226_63

def globalBody226_65 : Prog (BitVec 64) :=
.seq globalBody226_64 globalBody226_0

def globalBody226_66 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody226_67 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 0#64]))
  (Flapjack.Exp.const 0#64)) globalBody226_65 globalBody226_66

def globalBody226_68 : Prog (BitVec 64) :=
.seq globalBody226_60 globalBody226_67

def globalBody226_69 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "rlp_encode_list_header"
  [Flapjack.Exp.var Flapjack.VarKind.local "start", Flapjack.Exp.var Flapjack.VarKind.local "payload_len"]

def globalBody226_70 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.var Flapjack.VarKind.local "start",
      Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "payload_len", Flapjack.Exp.var Flapjack.VarKind.local "hl"]])

def globalBody226_71 : Prog (BitVec 64) :=
.seq globalBody226_69 globalBody226_70

def globalBody226_72 : Prog (BitVec 64) :=
.dec ("start") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 9#64],
    Flapjack.Exp.var Flapjack.VarKind.local "hl"]) globalBody226_71

def globalBody226_73 : Prog (BitVec 64) :=
.decCall ("hl") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.var Flapjack.VarKind.local "payload_len"]) globalBody226_72

def globalBody226_74 : Prog (BitVec 64) :=
.dec ("payload_len") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 9#64]]) globalBody226_73

def globalBody226_75 : Prog (BitVec 64) :=
.seq globalBody226_68 globalBody226_74

def globalBody226_76 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("rlp_encode_bytes") ([Flapjack.Exp.var Flapjack.VarKind.local "p",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 8#64]),
  Flapjack.Exp.const 32#64]) globalBody226_75

def globalBody226_77 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 9#64]) globalBody226_76

def globalBody226_78 : Prog (BitVec 64) :=
.decCall ("buf") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 1024#64]) globalBody226_77

def globalData226 : Decl (BitVec 64) :=
.function { name := "encode_header", inline := false, exported := false, params := [("h", Flapjack.Shape.one)], body := globalBody226_78, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def globalOutput226 := Pancake.PanLang.declToHOL globalData226
end InitECandidate.Proofs.FrontendStages.Declarations
