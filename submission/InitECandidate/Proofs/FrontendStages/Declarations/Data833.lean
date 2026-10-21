import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify817
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body833_0 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "p") (Flapjack.Exp.const 1#64)

def body833_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "w" (Flapjack.Exp.const 1#64)

def body833_2 : Prog (BitVec 64) :=
.seq body833_0 body833_1

def body833_3 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "p") (Flapjack.Exp.const 128#64)

def body833_4 : Prog (BitVec 64) :=
.seq body833_3 body833_1

def body833_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "succeeded") (Flapjack.Exp.const 0#64)) body833_2 body833_4

def body833_6 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "w"])

def body833_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "cumulative_gas"]

def body833_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "logs_bloom"
  [Flapjack.Exp.var Flapjack.VarKind.local "logs", Flapjack.Exp.var Flapjack.VarKind.local "bloom"]

def body833_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "bloom",
    Flapjack.Exp.const 256#64]

def body833_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "encode_logs"
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "logs"]

def body833_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_finish_list"
  [Flapjack.Exp.var Flapjack.VarKind.local "start", Flapjack.Exp.var Flapjack.VarKind.local "p"]

def body833_12 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "start", Flapjack.Exp.const 1#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "tx_type")

def body833_13 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "start", Flapjack.Exp.const 1#64],
      Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.const 1#64]])

def body833_14 : Prog (BitVec 64) :=
.seq body833_12 body833_13

def body833_15 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body833_16 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "tx_type") (Flapjack.Exp.const 0#64)) body833_14 body833_15

def body833_17 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct [Flapjack.Exp.var Flapjack.VarKind.local "start", Flapjack.Exp.var Flapjack.VarKind.local "w"])

def body833_18 : Prog (BitVec 64) :=
.seq body833_16 body833_17

def body833_19 : Prog (BitVec 64) :=
.seq body833_11 body833_18

def body833_20 : Prog (BitVec 64) :=
.seq body833_6 body833_19

def body833_21 : Prog (BitVec 64) :=
.seq body833_10 body833_20

def body833_22 : Prog (BitVec 64) :=
.seq body833_6 body833_21

def body833_23 : Prog (BitVec 64) :=
.seq body833_9 body833_22

def body833_24 : Prog (BitVec 64) :=
.seq body833_8 body833_23

def body833_25 : Prog (BitVec 64) :=
.decCall ("bloom") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 256#64]) body833_24

def body833_26 : Prog (BitVec 64) :=
.seq body833_6 body833_25

def body833_27 : Prog (BitVec 64) :=
.seq body833_7 body833_26

def body833_28 : Prog (BitVec 64) :=
.seq body833_6 body833_27

def body833_29 : Prog (BitVec 64) :=
.seq body833_5 body833_28

def body833_30 : Prog (BitVec 64) :=
.dec ("w") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body833_29

def body833_31 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "start", Flapjack.Exp.const 9#64]) body833_30

def body833_32 : Prog (BitVec 64) :=
.dec ("start") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 1#64]) body833_31

def body833_33 : Prog (BitVec 64) :=
.decCall ("buf") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "bound", Flapjack.Exp.const 400#64]]) body833_32

def body833_34 : Prog (BitVec 64) :=
.decCall ("bound") (Flapjack.Shape.one) ("logs_encoded_bound") ([Flapjack.Exp.var Flapjack.VarKind.local "logs"]) body833_33

def body833_35 : Prog (BitVec 64) :=
.seq body833_5 body833_6

def body833_36 : Prog (BitVec 64) :=
.seq body833_35 body833_7

def body833_37 : Prog (BitVec 64) :=
.seq body833_36 body833_6

def body833_38 : Prog (BitVec 64) :=
.seq body833_8 body833_9

def body833_39 : Prog (BitVec 64) :=
.seq body833_38 body833_6

def body833_40 : Prog (BitVec 64) :=
.seq body833_39 body833_10

def body833_41 : Prog (BitVec 64) :=
.seq body833_40 body833_6

def body833_42 : Prog (BitVec 64) :=
.seq body833_41 body833_11

def body833_43 : Prog (BitVec 64) :=
.seq body833_42 body833_16

def body833_44 : Prog (BitVec 64) :=
.seq body833_43 body833_17

def body833_45 : Prog (BitVec 64) :=
.decCall ("bloom") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 256#64]) body833_44

def body833_46 : Prog (BitVec 64) :=
.seq body833_37 body833_45

def body833_47 : Prog (BitVec 64) :=
.dec ("w") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body833_46

def body833_48 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "start", Flapjack.Exp.const 9#64]) body833_47

def body833_49 : Prog (BitVec 64) :=
.dec ("start") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 1#64]) body833_48

def body833_50 : Prog (BitVec 64) :=
.decCall ("buf") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "bound", Flapjack.Exp.const 400#64]]) body833_49

def body833_51 : Prog (BitVec 64) :=
.decCall ("bound") (Flapjack.Shape.one) ("logs_encoded_bound") ([Flapjack.Exp.var Flapjack.VarKind.local "logs"]) body833_50

def originalData833 : Decl (BitVec 64) :=
.function { name := "encode_receipt", inline := false, exported := false, params := [("tx_type", Flapjack.Shape.one), ("succeeded", Flapjack.Shape.one), ("cumulative_gas", Flapjack.Shape.one),
  ("logs", Flapjack.Shape.one)], body := body833_34, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData833 : Decl (BitVec 64) :=
.function { name := "encode_receipt", inline := false, exported := false, params := [("tx_type", Flapjack.Shape.one), ("succeeded", Flapjack.Shape.one), ("cumulative_gas", Flapjack.Shape.one),
  ("logs", Flapjack.Shape.one)], body := body833_51, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def original833 := Pancake.PanLang.declToHOL originalData833
def simplified833 := Pancake.PanLang.declToHOL simplifiedData833
end InitECandidate.Proofs.FrontendStages.Declarations
