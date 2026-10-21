import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify247
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body263_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 2#64]

def body263_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body263_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 0#64)) body263_0 body263_1

def body263_3 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 1#64,
      Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 48#64]),
      Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 56#64])])

def body263_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) body263_3 body263_1

def body263_5 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 32#64]),
  Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "nibs", Flapjack.Exp.var Flapjack.VarKind.local "pos"],
  Flapjack.Exp.var Flapjack.VarKind.local "rl"]) body263_4

def body263_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "rl")
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "nlen", Flapjack.Exp.var Flapjack.VarKind.local "pos"])) body263_5 body263_1

def body263_7 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rStruct [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64])

def body263_8 : Prog (BitVec 64) :=
.seq body263_6 body263_7

def body263_9 : Prog (BitVec 64) :=
.dec ("rl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 40#64])) body263_8

def body263_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 1#64)) body263_9 body263_1

def body263_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "nlen", Flapjack.Exp.var Flapjack.VarKind.local "pos"])
  (Flapjack.Exp.var Flapjack.VarKind.local "sl")) body263_7 body263_1

def body263_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq2") (Flapjack.Exp.const 0#64)) body263_7 body263_1

def body263_13 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pos"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "pos", Flapjack.Exp.var Flapjack.VarKind.local "sl"])

def body263_14 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "node"
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 48#64]))

def body263_15 : Prog (BitVec 64) :=
.seq body263_13 body263_14

def body263_16 : Prog (BitVec 64) :=
.seq body263_12 body263_15

def body263_17 : Prog (BitVec 64) :=
.decCall ("eq2") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 32#64]),
  Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "nibs", Flapjack.Exp.var Flapjack.VarKind.local "pos"],
  Flapjack.Exp.var Flapjack.VarKind.local "sl"]) body263_16

def body263_18 : Prog (BitVec 64) :=
.seq body263_11 body263_17

def body263_19 : Prog (BitVec 64) :=
.dec ("sl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 40#64])) body263_18

def body263_20 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "vl") (Flapjack.Exp.const 0#64)) body263_7 body263_1

def body263_21 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 1#64,
      Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 160#64]),
      Flapjack.Exp.var Flapjack.VarKind.local "vl"])

def body263_22 : Prog (BitVec 64) :=
.seq body263_20 body263_21

def body263_23 : Prog (BitVec 64) :=
.dec ("vl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 168#64])) body263_22

def body263_24 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "pos")
  (Flapjack.Exp.var Flapjack.VarKind.local "nlen")) body263_23 body263_1

def body263_25 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "node"
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 32#64,
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.loadByte
              (Flapjack.Exp.op Flapjack.BinOp.add
                [Flapjack.Exp.var Flapjack.VarKind.local "nibs", Flapjack.Exp.var Flapjack.VarKind.local "pos"]),
            Flapjack.Exp.const 8#64]]))

def body263_26 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pos"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pos", Flapjack.Exp.const 1#64])

def body263_27 : Prog (BitVec 64) :=
.seq body263_25 body263_26

def body263_28 : Prog (BitVec 64) :=
.seq body263_24 body263_27

def body263_29 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 2#64)) body263_19 body263_28

def body263_30 : Prog (BitVec 64) :=
.seq body263_10 body263_29

def body263_31 : Prog (BitVec 64) :=
.seq body263_2 body263_30

def body263_32 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 0#64])) body263_31

def body263_33 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "node") (Flapjack.Exp.const 0#64)) body263_32

def body263_34 : Prog (BitVec 64) :=
.seq body263_33 body263_7

def body263_35 : Prog (BitVec 64) :=
.dec ("pos") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body263_34

def body263_36 : Prog (BitVec 64) :=
.seq body263_2 body263_10

def body263_37 : Prog (BitVec 64) :=
.seq body263_12 body263_13

def body263_38 : Prog (BitVec 64) :=
.seq body263_37 body263_14

def body263_39 : Prog (BitVec 64) :=
.decCall ("eq2") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 32#64]),
  Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "nibs", Flapjack.Exp.var Flapjack.VarKind.local "pos"],
  Flapjack.Exp.var Flapjack.VarKind.local "sl"]) body263_38

def body263_40 : Prog (BitVec 64) :=
.seq body263_11 body263_39

def body263_41 : Prog (BitVec 64) :=
.dec ("sl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 40#64])) body263_40

def body263_42 : Prog (BitVec 64) :=
.seq body263_24 body263_25

def body263_43 : Prog (BitVec 64) :=
.seq body263_42 body263_26

def body263_44 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 2#64)) body263_41 body263_43

def body263_45 : Prog (BitVec 64) :=
.seq body263_36 body263_44

def body263_46 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 0#64])) body263_45

def body263_47 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "node") (Flapjack.Exp.const 0#64)) body263_46

def body263_48 : Prog (BitVec 64) :=
.seq body263_47 body263_7

def body263_49 : Prog (BitVec 64) :=
.dec ("pos") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body263_48

def originalData263 : Decl (BitVec 64) :=
.function { name := "trie_walk", inline := false, exported := false, params := [("node", Flapjack.Shape.one), ("nibs", Flapjack.Shape.one), ("nlen", Flapjack.Shape.one)], body := body263_35, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData263 : Decl (BitVec 64) :=
.function { name := "trie_walk", inline := false, exported := false, params := [("node", Flapjack.Shape.one), ("nibs", Flapjack.Shape.one), ("nlen", Flapjack.Shape.one)], body := body263_49, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def original263 := Pancake.PanLang.declToHOL originalData263
def simplified263 := Pancake.PanLang.declToHOL simplifiedData263
end InitECandidate.Proofs.FrontendStages.Declarations
