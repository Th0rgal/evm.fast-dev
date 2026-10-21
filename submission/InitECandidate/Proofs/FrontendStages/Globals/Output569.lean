import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data569
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate549
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody569_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody569_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody569_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "yp") (Flapjack.Exp.const 0#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "yp") (Flapjack.Exp.const 1#64))]) globalBody569_0 globalBody569_1

def globalBody569_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "rz") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "rge") (Flapjack.Exp.const 0#64)])) globalBody569_0 globalBody569_1

def globalBody569_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "sz") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "sgt") (Flapjack.Exp.const 0#64)])) globalBody569_0 globalBody569_1

def globalBody569_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "w"])

def globalBody569_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "auth", Flapjack.Exp.const 32#64]),
    Flapjack.Exp.const 20#64]

def globalBody569_7 : Prog (BitVec 64) :=
.seq globalBody569_5 globalBody569_6

def globalBody569_8 : Prog (BitVec 64) :=
.seq globalBody569_7 globalBody569_5

def globalBody569_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "auth", Flapjack.Exp.const 40#64])]

def globalBody569_10 : Prog (BitVec 64) :=
.seq globalBody569_8 globalBody569_9

def globalBody569_11 : Prog (BitVec 64) :=
.seq globalBody569_10 globalBody569_5

def globalBody569_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "rlp_encode_list_header"
  [Flapjack.Exp.var Flapjack.VarKind.local "start", Flapjack.Exp.var Flapjack.VarKind.local "payload"]

def globalBody569_13 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "start", Flapjack.Exp.const 1#64])
  (Flapjack.Exp.const 5#64)

def globalBody569_14 : Prog (BitVec 64) :=
.seq globalBody569_12 globalBody569_13

def globalBody569_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "start", Flapjack.Exp.const 1#64],
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "payload", Flapjack.Exp.var Flapjack.VarKind.local "hl",
        Flapjack.Exp.const 1#64],
    Flapjack.Exp.var Flapjack.VarKind.local "h"]

def globalBody569_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody569_17 : Prog (BitVec 64) :=
.seq globalBody569_16 globalBody569_0

def globalBody569_18 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 0#64)) globalBody569_17 globalBody569_1

def globalBody569_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.var Flapjack.VarKind.local "pt", Flapjack.Exp.const 64#64, Flapjack.Exp.var Flapjack.VarKind.local "h"]

def globalBody569_20 : Prog (BitVec 64) :=
.seq globalBody569_18 globalBody569_19

def globalBody569_21 : Prog (BitVec 64) :=
.seq globalBody569_20 globalBody569_16

def globalBody569_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "addr",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 12#64],
    Flapjack.Exp.const 20#64]

def globalBody569_23 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "addr")

def globalBody569_24 : Prog (BitVec 64) :=
.seq globalBody569_22 globalBody569_23

def globalBody569_25 : Prog (BitVec 64) :=
.decCall ("addr") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 24#64]) globalBody569_24

def globalBody569_26 : Prog (BitVec 64) :=
.seq globalBody569_21 globalBody569_25

def globalBody569_27 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("secp256k1_recover") ([Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.var Flapjack.VarKind.local "r",
  Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.var Flapjack.VarKind.local "yp",
  Flapjack.Exp.var Flapjack.VarKind.local "pt"]) globalBody569_26

def globalBody569_28 : Prog (BitVec 64) :=
.decCall ("pt") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) globalBody569_27

def globalBody569_29 : Prog (BitVec 64) :=
.seq globalBody569_15 globalBody569_28

def globalBody569_30 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) globalBody569_29

def globalBody569_31 : Prog (BitVec 64) :=
.seq globalBody569_14 globalBody569_30

def globalBody569_32 : Prog (BitVec 64) :=
.dec ("start") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 10#64],
    Flapjack.Exp.var Flapjack.VarKind.local "hl"]) globalBody569_31

def globalBody569_33 : Prog (BitVec 64) :=
.decCall ("hl") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.var Flapjack.VarKind.local "payload"]) globalBody569_32

def globalBody569_34 : Prog (BitVec 64) :=
.dec ("payload") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 10#64]]) globalBody569_33

def globalBody569_35 : Prog (BitVec 64) :=
.seq globalBody569_11 globalBody569_34

def globalBody569_36 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("rlp_put_u256") ([Flapjack.Exp.var Flapjack.VarKind.local "p",
  Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "auth", Flapjack.Exp.const 0#64])]) globalBody569_35

def globalBody569_37 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 10#64]) globalBody569_36

def globalBody569_38 : Prog (BitVec 64) :=
.decCall ("buf") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 128#64]) globalBody569_37

def globalBody569_39 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody569_38

def globalBody569_40 : Prog (BitVec 64) :=
.seq globalBody569_4 globalBody569_39

def globalBody569_41 : Prog (BitVec 64) :=
.decCall ("sgt") (Flapjack.Shape.one) ("u256_gt") ([Flapjack.Exp.var Flapjack.VarKind.local "s",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 16134479119472337056#64, Flapjack.Exp.const 6725966010171805725#64,
      Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 9223372036854775807#64]]) globalBody569_40

def globalBody569_42 : Prog (BitVec 64) :=
.decCall ("sz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "s"]) globalBody569_41

def globalBody569_43 : Prog (BitVec 64) :=
.seq globalBody569_3 globalBody569_42

def globalBody569_44 : Prog (BitVec 64) :=
.decCall ("rge") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "r",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 13822214165235122497#64, Flapjack.Exp.const 13451932020343611451#64,
      Flapjack.Exp.const 18446744073709551614#64, Flapjack.Exp.const 18446744073709551615#64]]) globalBody569_43

def globalBody569_45 : Prog (BitVec 64) :=
.decCall ("rz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "r"]) globalBody569_44

def globalBody569_46 : Prog (BitVec 64) :=
.dec ("s") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "auth", Flapjack.Exp.const 88#64])) globalBody569_45

def globalBody569_47 : Prog (BitVec 64) :=
.dec ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "auth", Flapjack.Exp.const 56#64])) globalBody569_46

def globalBody569_48 : Prog (BitVec 64) :=
.seq globalBody569_2 globalBody569_47

def globalBody569_49 : Prog (BitVec 64) :=
.dec ("yp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "auth", Flapjack.Exp.const 48#64])) globalBody569_48

def globalData569 : Decl (BitVec 64) :=
.function { name := "recover_authority", inline := false, exported := false, params := [("auth", Flapjack.Shape.one)], body := globalBody569_49, returnShape := (Flapjack.Shape.one) }
def globalOutput569 := Pancake.PanLang.declToHOL globalData569
end InitECandidate.Proofs.FrontendStages.Declarations
