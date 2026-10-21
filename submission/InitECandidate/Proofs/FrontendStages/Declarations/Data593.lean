import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify577
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body593_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "w"])

def body593_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "nonce"]

def body593_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "rlp_encode_list_header"
  [Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 9#64],
        Flapjack.Exp.var Flapjack.VarKind.local "hl"],
    Flapjack.Exp.var Flapjack.VarKind.local "payload"]

def body593_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 9#64],
        Flapjack.Exp.var Flapjack.VarKind.local "hl"],
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "payload", Flapjack.Exp.var Flapjack.VarKind.local "hl"],
    Flapjack.Exp.var Flapjack.VarKind.local "h"]

def body593_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "out",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 12#64],
    Flapjack.Exp.const 20#64]

def body593_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body593_6 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body593_7 : Prog (BitVec 64) :=
.seq body593_5 body593_6

def body593_8 : Prog (BitVec 64) :=
.seq body593_4 body593_7

def body593_9 : Prog (BitVec 64) :=
.seq body593_3 body593_8

def body593_10 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body593_9

def body593_11 : Prog (BitVec 64) :=
.seq body593_2 body593_10

def body593_12 : Prog (BitVec 64) :=
.decCall ("hl") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.var Flapjack.VarKind.local "payload"]) body593_11

def body593_13 : Prog (BitVec 64) :=
.dec ("payload") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 9#64]]) body593_12

def body593_14 : Prog (BitVec 64) :=
.seq body593_0 body593_13

def body593_15 : Prog (BitVec 64) :=
.seq body593_1 body593_14

def body593_16 : Prog (BitVec 64) :=
.seq body593_0 body593_15

def body593_17 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("rlp_encode_bytes") ([Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 20#64]) body593_16

def body593_18 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 9#64]) body593_17

def body593_19 : Prog (BitVec 64) :=
.decCall ("buf") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) body593_18

def body593_20 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body593_19

def body593_21 : Prog (BitVec 64) :=
.seq body593_0 body593_1

def body593_22 : Prog (BitVec 64) :=
.seq body593_21 body593_0

def body593_23 : Prog (BitVec 64) :=
.seq body593_3 body593_4

def body593_24 : Prog (BitVec 64) :=
.seq body593_23 body593_5

def body593_25 : Prog (BitVec 64) :=
.seq body593_24 body593_6

def body593_26 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body593_25

def body593_27 : Prog (BitVec 64) :=
.seq body593_2 body593_26

def body593_28 : Prog (BitVec 64) :=
.decCall ("hl") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.var Flapjack.VarKind.local "payload"]) body593_27

def body593_29 : Prog (BitVec 64) :=
.dec ("payload") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 9#64]]) body593_28

def body593_30 : Prog (BitVec 64) :=
.seq body593_22 body593_29

def body593_31 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("rlp_encode_bytes") ([Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 20#64]) body593_30

def body593_32 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 9#64]) body593_31

def body593_33 : Prog (BitVec 64) :=
.decCall ("buf") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) body593_32

def body593_34 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body593_33

def originalData593 : Decl (BitVec 64) :=
.function { name := "compute_contract_address", inline := false, exported := false, params := [("addr", Flapjack.Shape.one), ("nonce", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body593_20, returnShape := (Flapjack.Shape.one) }
def simplifiedData593 : Decl (BitVec 64) :=
.function { name := "compute_contract_address", inline := false, exported := false, params := [("addr", Flapjack.Shape.one), ("nonce", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body593_34, returnShape := (Flapjack.Shape.one) }
def original593 := Pancake.PanLang.declToHOL originalData593
def simplified593 := Pancake.PanLang.declToHOL simplifiedData593
end InitECandidate.Proofs.FrontendStages.Declarations
