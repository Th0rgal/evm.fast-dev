import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data302
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate285
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody302_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 20#64)

def globalBody302_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody302_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "it"))
  (Flapjack.Exp.const 1#64)) globalBody302_0 globalBody302_1

def globalBody302_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "ent"))
  (Flapjack.Exp.const 6#64)) globalBody302_0 globalBody302_1

def globalBody302_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "cid")

def globalBody302_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "addr")

def globalBody302_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "w")

def globalBody302_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "tx_scalar_word"
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "ent"), Flapjack.Exp.const 3#64,
    Flapjack.Exp.const 1#64, Flapjack.Exp.const 12#64]

def globalBody302_8 : Prog (BitVec 64) :=
.seq globalBody302_6 globalBody302_7

def globalBody302_9 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "w")

def globalBody302_10 : Prog (BitVec 64) :=
.seq globalBody302_8 globalBody302_9

def globalBody302_11 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "r")

def globalBody302_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 88#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "s")

def globalBody302_13 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody302_14 : Prog (BitVec 64) :=
.seq globalBody302_12 globalBody302_13

def globalBody302_15 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("tx_scalar_u256") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "ent"), Flapjack.Exp.const 5#64,
  Flapjack.Exp.const 32#64]) globalBody302_14

def globalBody302_16 : Prog (BitVec 64) :=
.seq globalBody302_11 globalBody302_15

def globalBody302_17 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("tx_scalar_u256") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "ent"), Flapjack.Exp.const 4#64,
  Flapjack.Exp.const 32#64]) globalBody302_16

def globalBody302_18 : Prog (BitVec 64) :=
.seq globalBody302_10 globalBody302_17

def globalBody302_19 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("tx_scalar_word") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "ent"), Flapjack.Exp.const 2#64,
  Flapjack.Exp.const 8#64, Flapjack.Exp.const 12#64]) globalBody302_18

def globalBody302_20 : Prog (BitVec 64) :=
.seq globalBody302_5 globalBody302_19

def globalBody302_21 : Prog (BitVec 64) :=
.decCall ("addr") (Flapjack.Shape.one) ("tx_fixed_bytes") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "ent"), Flapjack.Exp.const 1#64,
  Flapjack.Exp.const 20#64]) globalBody302_20

def globalBody302_22 : Prog (BitVec 64) :=
.seq globalBody302_4 globalBody302_21

def globalBody302_23 : Prog (BitVec 64) :=
.decCall ("cid") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("tx_scalar_u256") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "ent"), Flapjack.Exp.const 0#64,
  Flapjack.Exp.const 32#64]) globalBody302_22

def globalBody302_24 : Prog (BitVec 64) :=
.dec ("a") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "recs",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 120#64]]) globalBody302_23

def globalBody302_25 : Prog (BitVec 64) :=
.seq globalBody302_3 globalBody302_24

def globalBody302_26 : Prog (BitVec 64) :=
.decCall ("ent") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("rlp_list_to_slices") ([Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "it"),
  Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "it")]) globalBody302_25

def globalBody302_27 : Prog (BitVec 64) :=
.seq globalBody302_2 globalBody302_26

def globalBody302_28 : Prog (BitVec 64) :=
.decCall ("it") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("rlp_item") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "lst"),
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64]]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "lst"),
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64],
        Flapjack.Exp.const 8#64])]) globalBody302_27

def globalBody302_29 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "lst"))) globalBody302_28

def globalBody302_30 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.var Flapjack.VarKind.local "recs",
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "lst")])

def globalBody302_31 : Prog (BitVec 64) :=
.seq globalBody302_29 globalBody302_30

def globalBody302_32 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody302_31

def globalBody302_33 : Prog (BitVec 64) :=
.decCall ("recs") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "lst"), Flapjack.Exp.const 120#64]]) globalBody302_32

def globalBody302_34 : Prog (BitVec 64) :=
.decCall ("lst") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("rlp_list_to_slices") ([Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "len"]) globalBody302_33

def globalData302 : Decl (BitVec 64) :=
.function { name := "decode_authorizations", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("len", Flapjack.Shape.one)], body := globalBody302_34, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def globalOutput302 := Pancake.PanLang.declToHOL globalData302
end InitECandidate.Proofs.FrontendStages.Declarations
