import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data278
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate262
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody278_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "cbuf"), none)) "alloc"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "nlen") (Flapjack.Exp.const 1#64),
        Flapjack.Exp.const 2#64]]

def globalBody278_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "isl" (Flapjack.Exp.const 1#64)

def globalBody278_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody278_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 1#64)) globalBody278_1 globalBody278_2

def globalBody278_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "clen"), none)) "nibble_list_to_compact"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 32#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "nlen", Flapjack.Exp.var Flapjack.VarKind.local "isl",
    Flapjack.Exp.var Flapjack.VarKind.local "cbuf"]

def globalBody278_5 : Prog (BitVec 64) :=
.seq globalBody278_3 globalBody278_4

def globalBody278_6 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "payload" (Flapjack.Exp.var Flapjack.VarKind.local "el")

def globalBody278_7 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "payload"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "payload", Flapjack.Exp.var Flapjack.VarKind.local "vl"])

def globalBody278_8 : Prog (BitVec 64) :=
.decCall ("vl") (Flapjack.Shape.one) ("rlp_value_encoded_len") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 48#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 56#64])]) globalBody278_7

def globalBody278_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 1#64)) globalBody278_8 globalBody278_2

def globalBody278_10 : Prog (BitVec 64) :=
.seq globalBody278_6 globalBody278_9

def globalBody278_11 : Prog (BitVec 64) :=
.decCall ("el") (Flapjack.Shape.one) ("rlp_bytes_encoded_len") ([Flapjack.Exp.loadByte (Flapjack.Exp.var Flapjack.VarKind.local "cbuf"), Flapjack.Exp.var Flapjack.VarKind.local "clen"]) globalBody278_10

def globalBody278_12 : Prog (BitVec 64) :=
.seq globalBody278_5 globalBody278_11

def globalBody278_13 : Prog (BitVec 64) :=
.dec ("isl") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody278_12

def globalBody278_14 : Prog (BitVec 64) :=
.seq globalBody278_0 globalBody278_13

def globalBody278_15 : Prog (BitVec 64) :=
.dec ("nlen") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 40#64])) globalBody278_14

def globalBody278_16 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 3#64)) globalBody278_15 globalBody278_2

def globalBody278_17 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "fr", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "cbuf")

def globalBody278_18 : Prog (BitVec 64) :=
.seq globalBody278_16 globalBody278_17

def globalBody278_19 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "fr", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "clen")

def globalBody278_20 : Prog (BitVec 64) :=
.seq globalBody278_18 globalBody278_19

def globalBody278_21 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "fr", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "payload")

def globalBody278_22 : Prog (BitVec 64) :=
.seq globalBody278_20 globalBody278_21

def globalBody278_23 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody278_24 : Prog (BitVec 64) :=
.seq globalBody278_22 globalBody278_23

def globalBody278_25 : Prog (BitVec 64) :=
.dec ("clen") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody278_24

def globalBody278_26 : Prog (BitVec 64) :=
.dec ("cbuf") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody278_25

def globalBody278_27 : Prog (BitVec 64) :=
.dec ("payload") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody278_26

def globalBody278_28 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 0#64])) globalBody278_27

def globalData278 : Decl (BitVec 64) :=
.function { name := "_node_rlp_begin", inline := false, exported := false, params := [("fr", Flapjack.Shape.one), ("node", Flapjack.Shape.one)], body := globalBody278_28, returnShape := (Flapjack.Shape.one) }
def globalOutput278 := Pancake.PanLang.declToHOL globalData278
end InitECandidate.Proofs.FrontendStages.Declarations
