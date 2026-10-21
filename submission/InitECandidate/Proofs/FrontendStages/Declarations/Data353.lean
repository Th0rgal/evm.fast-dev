import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify337
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body353_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "trap_with" [Flapjack.Exp.const 4#64]

def body353_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body353_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.global "journal_n")
  (Flapjack.Exp.var Flapjack.VarKind.global "journal_cap")) body353_0 body353_1

def body353_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "kc", Flapjack.Exp.var Flapjack.VarKind.local "key",
    Flapjack.Exp.var Flapjack.VarKind.local "klen"]

def body353_4 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "r") (Flapjack.Exp.var Flapjack.VarKind.local "t")

def body353_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "kc")

def body353_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "old"))

def body353_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "old"))

def body353_8 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.global "journal_n"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "journal_n", Flapjack.Exp.const 1#64])

def body353_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.var Flapjack.VarKind.local "key",
    Flapjack.Exp.var Flapjack.VarKind.local "value"]

def body353_10 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body353_11 : Prog (BitVec 64) :=
.seq body353_9 body353_10

def body353_12 : Prog (BitVec 64) :=
.seq body353_8 body353_11

def body353_13 : Prog (BitVec 64) :=
.seq body353_7 body353_12

def body353_14 : Prog (BitVec 64) :=
.seq body353_6 body353_13

def body353_15 : Prog (BitVec 64) :=
.seq body353_5 body353_14

def body353_16 : Prog (BitVec 64) :=
.seq body353_4 body353_15

def body353_17 : Prog (BitVec 64) :=
.dec ("r") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.global "journal",
    Flapjack.Exp.panOp Flapjack.PanOp.mul
      [Flapjack.Exp.var Flapjack.VarKind.global "journal_n", Flapjack.Exp.const 32#64]]) body353_16

def body353_18 : Prog (BitVec 64) :=
.seq body353_3 body353_17

def body353_19 : Prog (BitVec 64) :=
.decCall ("kc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "klen"]) body353_18

def body353_20 : Prog (BitVec 64) :=
.dec ("klen") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 0#64])) body353_19

def body353_21 : Prog (BitVec 64) :=
.seq body353_2 body353_20

def body353_22 : Prog (BitVec 64) :=
.decCall ("old") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.var Flapjack.VarKind.local "key"]) body353_21

def body353_23 : Prog (BitVec 64) :=
.seq body353_4 body353_5

def body353_24 : Prog (BitVec 64) :=
.seq body353_23 body353_6

def body353_25 : Prog (BitVec 64) :=
.seq body353_24 body353_7

def body353_26 : Prog (BitVec 64) :=
.seq body353_25 body353_8

def body353_27 : Prog (BitVec 64) :=
.seq body353_26 body353_9

def body353_28 : Prog (BitVec 64) :=
.seq body353_27 body353_10

def body353_29 : Prog (BitVec 64) :=
.dec ("r") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.global "journal",
    Flapjack.Exp.panOp Flapjack.PanOp.mul
      [Flapjack.Exp.var Flapjack.VarKind.global "journal_n", Flapjack.Exp.const 32#64]]) body353_28

def body353_30 : Prog (BitVec 64) :=
.seq body353_3 body353_29

def body353_31 : Prog (BitVec 64) :=
.decCall ("kc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "klen"]) body353_30

def body353_32 : Prog (BitVec 64) :=
.dec ("klen") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 0#64])) body353_31

def body353_33 : Prog (BitVec 64) :=
.seq body353_2 body353_32

def body353_34 : Prog (BitVec 64) :=
.decCall ("old") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.var Flapjack.VarKind.local "key"]) body353_33

def originalData353 : Decl (BitVec 64) :=
.function { name := "jset", inline := false, exported := false, params := [("t", Flapjack.Shape.one), ("key", Flapjack.Shape.one), ("value", Flapjack.Shape.one)], body := body353_22, returnShape := (Flapjack.Shape.one) }
def simplifiedData353 : Decl (BitVec 64) :=
.function { name := "jset", inline := false, exported := false, params := [("t", Flapjack.Shape.one), ("key", Flapjack.Shape.one), ("value", Flapjack.Shape.one)], body := body353_34, returnShape := (Flapjack.Shape.one) }
def original353 := Pancake.PanLang.declToHOL originalData353
def simplified353 := Pancake.PanLang.declToHOL simplifiedData353
end InitECandidate.Proofs.FrontendStages.Declarations
