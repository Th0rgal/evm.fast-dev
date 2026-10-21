import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data300
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate283
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody300_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 19#64)

def globalBody300_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody300_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "it"))
  (Flapjack.Exp.const 1#64)) globalBody300_0 globalBody300_1

def globalBody300_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "ent"))
  (Flapjack.Exp.const 2#64)) globalBody300_0 globalBody300_1

def globalBody300_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "keys",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 32#64]],
    Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 32#64]

def globalBody300_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "j"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 1#64])

def globalBody300_6 : Prog (BitVec 64) :=
.seq globalBody300_4 globalBody300_5

def globalBody300_7 : Prog (BitVec 64) :=
.decCall ("k") (Flapjack.Shape.one) ("tx_fixed_bytes") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "slots"), Flapjack.Exp.var Flapjack.VarKind.local "j",
  Flapjack.Exp.const 32#64]) globalBody300_6

def globalBody300_8 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "j")
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "slots"))) globalBody300_7

def globalBody300_9 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "addr")

def globalBody300_10 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "keys")

def globalBody300_11 : Prog (BitVec 64) :=
.seq globalBody300_9 globalBody300_10

def globalBody300_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "slots"))

def globalBody300_13 : Prog (BitVec 64) :=
.seq globalBody300_11 globalBody300_12

def globalBody300_14 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody300_15 : Prog (BitVec 64) :=
.seq globalBody300_13 globalBody300_14

def globalBody300_16 : Prog (BitVec 64) :=
.dec ("rec") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "recs",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 24#64]]) globalBody300_15

def globalBody300_17 : Prog (BitVec 64) :=
.seq globalBody300_8 globalBody300_16

def globalBody300_18 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody300_17

def globalBody300_19 : Prog (BitVec 64) :=
.decCall ("keys") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "slots"), Flapjack.Exp.const 32#64]]) globalBody300_18

def globalBody300_20 : Prog (BitVec 64) :=
.decCall ("slots") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("rlp_list_to_slices") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "sl"),
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "sl")]) globalBody300_19

def globalBody300_21 : Prog (BitVec 64) :=
.decCall ("sl") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("tx_list_item") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "ent"), Flapjack.Exp.const 1#64]) globalBody300_20

def globalBody300_22 : Prog (BitVec 64) :=
.decCall ("addr") (Flapjack.Shape.one) ("tx_fixed_bytes") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "ent"), Flapjack.Exp.const 0#64,
  Flapjack.Exp.const 20#64]) globalBody300_21

def globalBody300_23 : Prog (BitVec 64) :=
.seq globalBody300_3 globalBody300_22

def globalBody300_24 : Prog (BitVec 64) :=
.decCall ("ent") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("rlp_list_to_slices") ([Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "it"),
  Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "it")]) globalBody300_23

def globalBody300_25 : Prog (BitVec 64) :=
.seq globalBody300_2 globalBody300_24

def globalBody300_26 : Prog (BitVec 64) :=
.decCall ("it") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("rlp_item") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "lst"),
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64]]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "lst"),
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64],
        Flapjack.Exp.const 8#64])]) globalBody300_25

def globalBody300_27 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "lst"))) globalBody300_26

def globalBody300_28 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.var Flapjack.VarKind.local "recs",
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "lst")])

def globalBody300_29 : Prog (BitVec 64) :=
.seq globalBody300_27 globalBody300_28

def globalBody300_30 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody300_29

def globalBody300_31 : Prog (BitVec 64) :=
.decCall ("recs") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "lst"), Flapjack.Exp.const 24#64]]) globalBody300_30

def globalBody300_32 : Prog (BitVec 64) :=
.decCall ("lst") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("rlp_list_to_slices") ([Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "len"]) globalBody300_31

def globalData300 : Decl (BitVec 64) :=
.function { name := "decode_access_list", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("len", Flapjack.Shape.one)], body := globalBody300_32, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def globalOutput300 := Pancake.PanLang.declToHOL globalData300
end InitECandidate.Proofs.FrontendStages.Declarations
