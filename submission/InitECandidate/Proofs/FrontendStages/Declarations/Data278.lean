import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify262
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body278_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "cbuf"), none)) "alloc"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "nlen") (Flapjack.Exp.const 1#64),
        Flapjack.Exp.const 2#64]]

def body278_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "isl" (Flapjack.Exp.const 1#64)

def body278_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body278_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 1#64)) body278_1 body278_2

def body278_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "clen"), none)) "nibble_list_to_compact"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 32#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "nlen", Flapjack.Exp.var Flapjack.VarKind.local "isl",
    Flapjack.Exp.var Flapjack.VarKind.local "cbuf"]

def body278_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "payload" (Flapjack.Exp.var Flapjack.VarKind.local "el")

def body278_6 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "payload"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "payload", Flapjack.Exp.var Flapjack.VarKind.local "vl"])

def body278_7 : Prog (BitVec 64) :=
.decCall ("vl") (Flapjack.Shape.one) ("rlp_value_encoded_len") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 48#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 56#64])]) body278_6

def body278_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 1#64)) body278_7 body278_2

def body278_9 : Prog (BitVec 64) :=
.seq body278_5 body278_8

def body278_10 : Prog (BitVec 64) :=
.decCall ("el") (Flapjack.Shape.one) ("rlp_bytes_encoded_len") ([Flapjack.Exp.loadByte (Flapjack.Exp.var Flapjack.VarKind.local "cbuf"), Flapjack.Exp.var Flapjack.VarKind.local "clen"]) body278_9

def body278_11 : Prog (BitVec 64) :=
.seq body278_4 body278_10

def body278_12 : Prog (BitVec 64) :=
.seq body278_3 body278_11

def body278_13 : Prog (BitVec 64) :=
.dec ("isl") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body278_12

def body278_14 : Prog (BitVec 64) :=
.seq body278_0 body278_13

def body278_15 : Prog (BitVec 64) :=
.dec ("nlen") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 40#64])) body278_14

def body278_16 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 3#64)) body278_15 body278_2

def body278_17 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "fr", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "cbuf")

def body278_18 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "fr", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "clen")

def body278_19 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "fr", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "payload")

def body278_20 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body278_21 : Prog (BitVec 64) :=
.seq body278_19 body278_20

def body278_22 : Prog (BitVec 64) :=
.seq body278_18 body278_21

def body278_23 : Prog (BitVec 64) :=
.seq body278_17 body278_22

def body278_24 : Prog (BitVec 64) :=
.seq body278_16 body278_23

def body278_25 : Prog (BitVec 64) :=
.dec ("clen") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body278_24

def body278_26 : Prog (BitVec 64) :=
.dec ("cbuf") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body278_25

def body278_27 : Prog (BitVec 64) :=
.dec ("payload") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body278_26

def body278_28 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 0#64])) body278_27

def body278_29 : Prog (BitVec 64) :=
.seq body278_3 body278_4

def body278_30 : Prog (BitVec 64) :=
.seq body278_29 body278_10

def body278_31 : Prog (BitVec 64) :=
.dec ("isl") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body278_30

def body278_32 : Prog (BitVec 64) :=
.seq body278_0 body278_31

def body278_33 : Prog (BitVec 64) :=
.dec ("nlen") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 40#64])) body278_32

def body278_34 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 3#64)) body278_33 body278_2

def body278_35 : Prog (BitVec 64) :=
.seq body278_34 body278_17

def body278_36 : Prog (BitVec 64) :=
.seq body278_35 body278_18

def body278_37 : Prog (BitVec 64) :=
.seq body278_36 body278_19

def body278_38 : Prog (BitVec 64) :=
.seq body278_37 body278_20

def body278_39 : Prog (BitVec 64) :=
.dec ("clen") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body278_38

def body278_40 : Prog (BitVec 64) :=
.dec ("cbuf") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body278_39

def body278_41 : Prog (BitVec 64) :=
.dec ("payload") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body278_40

def body278_42 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 0#64])) body278_41

def originalData278 : Decl (BitVec 64) :=
.function { name := "_node_rlp_begin", inline := false, exported := false, params := [("fr", Flapjack.Shape.one), ("node", Flapjack.Shape.one)], body := body278_28, returnShape := (Flapjack.Shape.one) }
def simplifiedData278 : Decl (BitVec 64) :=
.function { name := "_node_rlp_begin", inline := false, exported := false, params := [("fr", Flapjack.Shape.one), ("node", Flapjack.Shape.one)], body := body278_42, returnShape := (Flapjack.Shape.one) }
def original278 := Pancake.PanLang.declToHOL originalData278
def simplified278 := Pancake.PanLang.declToHOL simplifiedData278
end InitECandidate.Proofs.FrontendStages.Declarations
