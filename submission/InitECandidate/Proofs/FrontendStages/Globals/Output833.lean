import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data833
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate817
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody833_0 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "p") (Flapjack.Exp.const 1#64)

def globalBody833_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "w" (Flapjack.Exp.const 1#64)

def globalBody833_2 : Prog (BitVec 64) :=
.seq globalBody833_0 globalBody833_1

def globalBody833_3 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "p") (Flapjack.Exp.const 128#64)

def globalBody833_4 : Prog (BitVec 64) :=
.seq globalBody833_3 globalBody833_1

def globalBody833_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "succeeded") (Flapjack.Exp.const 0#64)) globalBody833_2 globalBody833_4

def globalBody833_6 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "w"])

def globalBody833_7 : Prog (BitVec 64) :=
.seq globalBody833_5 globalBody833_6

def globalBody833_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "cumulative_gas"]

def globalBody833_9 : Prog (BitVec 64) :=
.seq globalBody833_7 globalBody833_8

def globalBody833_10 : Prog (BitVec 64) :=
.seq globalBody833_9 globalBody833_6

def globalBody833_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "logs_bloom"
  [Flapjack.Exp.var Flapjack.VarKind.local "logs", Flapjack.Exp.var Flapjack.VarKind.local "bloom"]

def globalBody833_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "bloom",
    Flapjack.Exp.const 256#64]

def globalBody833_13 : Prog (BitVec 64) :=
.seq globalBody833_11 globalBody833_12

def globalBody833_14 : Prog (BitVec 64) :=
.seq globalBody833_13 globalBody833_6

def globalBody833_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "encode_logs"
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "logs"]

def globalBody833_16 : Prog (BitVec 64) :=
.seq globalBody833_14 globalBody833_15

def globalBody833_17 : Prog (BitVec 64) :=
.seq globalBody833_16 globalBody833_6

def globalBody833_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_finish_list"
  [Flapjack.Exp.var Flapjack.VarKind.local "start", Flapjack.Exp.var Flapjack.VarKind.local "p"]

def globalBody833_19 : Prog (BitVec 64) :=
.seq globalBody833_17 globalBody833_18

def globalBody833_20 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "start", Flapjack.Exp.const 1#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "tx_type")

def globalBody833_21 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "start", Flapjack.Exp.const 1#64],
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.const 1#64]])

def globalBody833_22 : Prog (BitVec 64) :=
.seq globalBody833_20 globalBody833_21

def globalBody833_23 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody833_24 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "tx_type") (Flapjack.Exp.const 0#64)) globalBody833_22 globalBody833_23

def globalBody833_25 : Prog (BitVec 64) :=
.seq globalBody833_19 globalBody833_24

def globalBody833_26 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct [Flapjack.Exp.var Flapjack.VarKind.local "start", Flapjack.Exp.var Flapjack.VarKind.local "w"])

def globalBody833_27 : Prog (BitVec 64) :=
.seq globalBody833_25 globalBody833_26

def globalBody833_28 : Prog (BitVec 64) :=
.decCall ("bloom") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 256#64]) globalBody833_27

def globalBody833_29 : Prog (BitVec 64) :=
.seq globalBody833_10 globalBody833_28

def globalBody833_30 : Prog (BitVec 64) :=
.dec ("w") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody833_29

def globalBody833_31 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "start", Flapjack.Exp.const 9#64]) globalBody833_30

def globalBody833_32 : Prog (BitVec 64) :=
.dec ("start") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 1#64]) globalBody833_31

def globalBody833_33 : Prog (BitVec 64) :=
.decCall ("buf") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "bound", Flapjack.Exp.const 400#64]]) globalBody833_32

def globalBody833_34 : Prog (BitVec 64) :=
.decCall ("bound") (Flapjack.Shape.one) ("logs_encoded_bound") ([Flapjack.Exp.var Flapjack.VarKind.local "logs"]) globalBody833_33

def globalData833 : Decl (BitVec 64) :=
.function { name := "encode_receipt", inline := false, exported := false, params := [("tx_type", Flapjack.Shape.one), ("succeeded", Flapjack.Shape.one), ("cumulative_gas", Flapjack.Shape.one),
  ("logs", Flapjack.Shape.one)], body := globalBody833_34, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def globalOutput833 := Pancake.PanLang.declToHOL globalData833
end InitECandidate.Proofs.FrontendStages.Declarations
