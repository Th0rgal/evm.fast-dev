import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify338
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body354_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body354_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body354_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "old"))
  (Flapjack.Exp.const 0#64)) body354_0 body354_1

def body354_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "trap_with" [Flapjack.Exp.const 5#64]

def body354_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.global "journal_n")
  (Flapjack.Exp.var Flapjack.VarKind.global "journal_cap")) body354_3 body354_1

def body354_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "kc", Flapjack.Exp.var Flapjack.VarKind.local "key",
    Flapjack.Exp.var Flapjack.VarKind.local "klen"]

def body354_6 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "r") (Flapjack.Exp.var Flapjack.VarKind.local "t")

def body354_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "kc")

def body354_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.const 1#64)

def body354_9 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "old"))

def body354_10 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.global "journal_n"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "journal_n", Flapjack.Exp.const 1#64])

def body354_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_del"
  [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.var Flapjack.VarKind.local "key"]

def body354_12 : Prog (BitVec 64) :=
.seq body354_11 body354_0

def body354_13 : Prog (BitVec 64) :=
.seq body354_10 body354_12

def body354_14 : Prog (BitVec 64) :=
.seq body354_9 body354_13

def body354_15 : Prog (BitVec 64) :=
.seq body354_8 body354_14

def body354_16 : Prog (BitVec 64) :=
.seq body354_7 body354_15

def body354_17 : Prog (BitVec 64) :=
.seq body354_6 body354_16

def body354_18 : Prog (BitVec 64) :=
.dec ("r") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.global "journal",
    Flapjack.Exp.panOp Flapjack.PanOp.mul
      [Flapjack.Exp.var Flapjack.VarKind.global "journal_n", Flapjack.Exp.const 32#64]]) body354_17

def body354_19 : Prog (BitVec 64) :=
.seq body354_5 body354_18

def body354_20 : Prog (BitVec 64) :=
.decCall ("kc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "klen"]) body354_19

def body354_21 : Prog (BitVec 64) :=
.dec ("klen") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 0#64])) body354_20

def body354_22 : Prog (BitVec 64) :=
.seq body354_4 body354_21

def body354_23 : Prog (BitVec 64) :=
.seq body354_2 body354_22

def body354_24 : Prog (BitVec 64) :=
.decCall ("old") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.var Flapjack.VarKind.local "key"]) body354_23

def body354_25 : Prog (BitVec 64) :=
.seq body354_2 body354_4

def body354_26 : Prog (BitVec 64) :=
.seq body354_6 body354_7

def body354_27 : Prog (BitVec 64) :=
.seq body354_26 body354_8

def body354_28 : Prog (BitVec 64) :=
.seq body354_27 body354_9

def body354_29 : Prog (BitVec 64) :=
.seq body354_28 body354_10

def body354_30 : Prog (BitVec 64) :=
.seq body354_29 body354_11

def body354_31 : Prog (BitVec 64) :=
.seq body354_30 body354_0

def body354_32 : Prog (BitVec 64) :=
.dec ("r") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.global "journal",
    Flapjack.Exp.panOp Flapjack.PanOp.mul
      [Flapjack.Exp.var Flapjack.VarKind.global "journal_n", Flapjack.Exp.const 32#64]]) body354_31

def body354_33 : Prog (BitVec 64) :=
.seq body354_5 body354_32

def body354_34 : Prog (BitVec 64) :=
.decCall ("kc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "klen"]) body354_33

def body354_35 : Prog (BitVec 64) :=
.dec ("klen") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 0#64])) body354_34

def body354_36 : Prog (BitVec 64) :=
.seq body354_25 body354_35

def body354_37 : Prog (BitVec 64) :=
.decCall ("old") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.var Flapjack.VarKind.local "key"]) body354_36

def originalData354 : Decl (BitVec 64) :=
.function { name := "jdel", inline := false, exported := false, params := [("t", Flapjack.Shape.one), ("key", Flapjack.Shape.one)], body := body354_24, returnShape := (Flapjack.Shape.one) }
def simplifiedData354 : Decl (BitVec 64) :=
.function { name := "jdel", inline := false, exported := false, params := [("t", Flapjack.Shape.one), ("key", Flapjack.Shape.one)], body := body354_37, returnShape := (Flapjack.Shape.one) }
def original354 := Pancake.PanLang.declToHOL originalData354
def simplified354 := Pancake.PanLang.declToHOL simplifiedData354
end InitECandidate.Proofs.FrontendStages.Declarations
