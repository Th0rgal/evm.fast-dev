import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify303
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body319_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_list_header"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.const 21#64, Flapjack.Exp.var Flapjack.VarKind.local "ih",
        Flapjack.Exp.var Flapjack.VarKind.local "inner"]]

def body319_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "w"])

def body319_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 0#64]),
    Flapjack.Exp.const 20#64]

def body319_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_list_header"
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "inner"]

def body319_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "keys",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 32#64]],
    Flapjack.Exp.const 32#64]

def body319_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "j"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 1#64])

def body319_6 : Prog (BitVec 64) :=
.seq body319_1 body319_5

def body319_7 : Prog (BitVec 64) :=
.seq body319_4 body319_6

def body319_8 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "j")
  (Flapjack.Exp.var Flapjack.VarKind.local "ns")) body319_7

def body319_9 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body319_10 : Prog (BitVec 64) :=
.seq body319_8 body319_9

def body319_11 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body319_10

def body319_12 : Prog (BitVec 64) :=
.dec ("keys") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 8#64])) body319_11

def body319_13 : Prog (BitVec 64) :=
.seq body319_1 body319_12

def body319_14 : Prog (BitVec 64) :=
.seq body319_3 body319_13

def body319_15 : Prog (BitVec 64) :=
.seq body319_1 body319_14

def body319_16 : Prog (BitVec 64) :=
.seq body319_2 body319_15

def body319_17 : Prog (BitVec 64) :=
.seq body319_1 body319_16

def body319_18 : Prog (BitVec 64) :=
.seq body319_0 body319_17

def body319_19 : Prog (BitVec 64) :=
.decCall ("ih") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.var Flapjack.VarKind.local "inner"]) body319_18

def body319_20 : Prog (BitVec 64) :=
.dec ("inner") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 33#64, Flapjack.Exp.var Flapjack.VarKind.local "ns"]) body319_19

def body319_21 : Prog (BitVec 64) :=
.dec ("ns") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 16#64])) body319_20

def body319_22 : Prog (BitVec 64) :=
.dec ("rec") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "recs",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 24#64]]) body319_21

def body319_23 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body319_22

def body319_24 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "dst"])

def body319_25 : Prog (BitVec 64) :=
.seq body319_23 body319_24

def body319_26 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body319_25

def body319_27 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.var Flapjack.VarKind.local "w"]) body319_26

def body319_28 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("rlp_encode_list_header") ([Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.var Flapjack.VarKind.local "pl"]) body319_27

def body319_29 : Prog (BitVec 64) :=
.decCall ("pl") (Flapjack.Shape.one) ("access_list_payload_len") ([Flapjack.Exp.var Flapjack.VarKind.local "recs", Flapjack.Exp.var Flapjack.VarKind.local "n"]) body319_28

def body319_30 : Prog (BitVec 64) :=
.seq body319_0 body319_1

def body319_31 : Prog (BitVec 64) :=
.seq body319_30 body319_2

def body319_32 : Prog (BitVec 64) :=
.seq body319_31 body319_1

def body319_33 : Prog (BitVec 64) :=
.seq body319_32 body319_3

def body319_34 : Prog (BitVec 64) :=
.seq body319_33 body319_1

def body319_35 : Prog (BitVec 64) :=
.seq body319_4 body319_1

def body319_36 : Prog (BitVec 64) :=
.seq body319_35 body319_5

def body319_37 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "j")
  (Flapjack.Exp.var Flapjack.VarKind.local "ns")) body319_36

def body319_38 : Prog (BitVec 64) :=
.seq body319_37 body319_9

def body319_39 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body319_38

def body319_40 : Prog (BitVec 64) :=
.dec ("keys") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 8#64])) body319_39

def body319_41 : Prog (BitVec 64) :=
.seq body319_34 body319_40

def body319_42 : Prog (BitVec 64) :=
.decCall ("ih") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.var Flapjack.VarKind.local "inner"]) body319_41

def body319_43 : Prog (BitVec 64) :=
.dec ("inner") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 33#64, Flapjack.Exp.var Flapjack.VarKind.local "ns"]) body319_42

def body319_44 : Prog (BitVec 64) :=
.dec ("ns") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 16#64])) body319_43

def body319_45 : Prog (BitVec 64) :=
.dec ("rec") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "recs",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 24#64]]) body319_44

def body319_46 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body319_45

def body319_47 : Prog (BitVec 64) :=
.seq body319_46 body319_24

def body319_48 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body319_47

def body319_49 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.var Flapjack.VarKind.local "w"]) body319_48

def body319_50 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("rlp_encode_list_header") ([Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.var Flapjack.VarKind.local "pl"]) body319_49

def body319_51 : Prog (BitVec 64) :=
.decCall ("pl") (Flapjack.Shape.one) ("access_list_payload_len") ([Flapjack.Exp.var Flapjack.VarKind.local "recs", Flapjack.Exp.var Flapjack.VarKind.local "n"]) body319_50

def originalData319 : Decl (BitVec 64) :=
.function { name := "tx_put_access_list", inline := false, exported := false, params := [("dst", Flapjack.Shape.one), ("recs", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body319_29, returnShape := (Flapjack.Shape.one) }
def simplifiedData319 : Decl (BitVec 64) :=
.function { name := "tx_put_access_list", inline := false, exported := false, params := [("dst", Flapjack.Shape.one), ("recs", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body319_51, returnShape := (Flapjack.Shape.one) }
def original319 := Pancake.PanLang.declToHOL originalData319
def simplified319 := Pancake.PanLang.declToHOL simplifiedData319
end InitECandidate.Proofs.FrontendStages.Declarations
