import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify270
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body286_0 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "dst") (Flapjack.Exp.const 128#64)

def body286_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body286_2 : Prog (BitVec 64) :=
.seq body286_0 body286_1

def body286_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body286_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "child") (Flapjack.Exp.const 0#64)) body286_2 body286_3

def body286_5 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "dst") (Flapjack.Exp.const 160#64)

def body286_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.const 1#64],
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 24#64]),
    Flapjack.Exp.const 32#64]

def body286_7 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 33#64)

def body286_8 : Prog (BitVec 64) :=
.seq body286_6 body286_7

def body286_9 : Prog (BitVec 64) :=
.seq body286_5 body286_8

def body286_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 0#64]))
  (Flapjack.Exp.const 0#64)) body286_9 body286_3

def body286_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 13#64]

def body286_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 8#64]))
  (Flapjack.Exp.const 0#64)) body286_11 body286_3

def body286_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.var Flapjack.VarKind.local "rp",
    Flapjack.Exp.var Flapjack.VarKind.local "rl"]

def body286_14 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "rl")

def body286_15 : Prog (BitVec 64) :=
.seq body286_13 body286_14

def body286_16 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "rl") (Flapjack.Exp.const 32#64)) body286_15 body286_3

def body286_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.const 1#64],
    Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 32#64]

def body286_18 : Prog (BitVec 64) :=
.seq body286_17 body286_7

def body286_19 : Prog (BitVec 64) :=
.seq body286_5 body286_18

def body286_20 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("node_hash_cached") ([Flapjack.Exp.var Flapjack.VarKind.local "child"]) body286_19

def body286_21 : Prog (BitVec 64) :=
.seq body286_16 body286_20

def body286_22 : Prog (BitVec 64) :=
.dec ("rl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 16#64])) body286_21

def body286_23 : Prog (BitVec 64) :=
.dec ("rp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 8#64])) body286_22

def body286_24 : Prog (BitVec 64) :=
.seq body286_12 body286_23

def body286_25 : Prog (BitVec 64) :=
.seq body286_10 body286_24

def body286_26 : Prog (BitVec 64) :=
.seq body286_4 body286_25

def body286_27 : Prog (BitVec 64) :=
.seq body286_5 body286_6

def body286_28 : Prog (BitVec 64) :=
.seq body286_27 body286_7

def body286_29 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 0#64]))
  (Flapjack.Exp.const 0#64)) body286_28 body286_3

def body286_30 : Prog (BitVec 64) :=
.seq body286_4 body286_29

def body286_31 : Prog (BitVec 64) :=
.seq body286_30 body286_12

def body286_32 : Prog (BitVec 64) :=
.seq body286_5 body286_17

def body286_33 : Prog (BitVec 64) :=
.seq body286_32 body286_7

def body286_34 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("node_hash_cached") ([Flapjack.Exp.var Flapjack.VarKind.local "child"]) body286_33

def body286_35 : Prog (BitVec 64) :=
.seq body286_16 body286_34

def body286_36 : Prog (BitVec 64) :=
.dec ("rl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 16#64])) body286_35

def body286_37 : Prog (BitVec 64) :=
.dec ("rp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 8#64])) body286_36

def body286_38 : Prog (BitVec 64) :=
.seq body286_31 body286_37

def originalData286 : Decl (BitVec 64) :=
.function { name := "node_write_ref", inline := false, exported := false, params := [("child", Flapjack.Shape.one), ("dst", Flapjack.Shape.one)], body := body286_26, returnShape := (Flapjack.Shape.one) }
def simplifiedData286 : Decl (BitVec 64) :=
.function { name := "node_write_ref", inline := false, exported := false, params := [("child", Flapjack.Shape.one), ("dst", Flapjack.Shape.one)], body := body286_38, returnShape := (Flapjack.Shape.one) }
def original286 := Pancake.PanLang.declToHOL originalData286
def simplified286 := Pancake.PanLang.declToHOL simplifiedData286
end InitECandidate.Proofs.FrontendStages.Declarations
