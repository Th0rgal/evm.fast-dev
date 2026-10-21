import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify357
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body373_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rStruct [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64])

def body373_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body373_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) body373_0 body373_1

def body373_3 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "w")),
      Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "w"), Flapjack.Exp.const 8#64])])

def body373_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "w"))
  (Flapjack.Exp.const 0#64)) body373_3 body373_1

def body373_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "htab_get"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bs", Flapjack.Exp.const 48#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "code_hash"]

def body373_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ts", Flapjack.Exp.const 40#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 1#64]

def body373_7 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "c")

def body373_8 : Prog (BitVec 64) :=
.decCall ("c") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("ws_get_code") ([Flapjack.Exp.var Flapjack.VarKind.local "code_hash"]) body373_7

def body373_9 : Prog (BitVec 64) :=
.seq body373_6 body373_8

def body373_10 : Prog (BitVec 64) :=
.decCall ("k") (Flapjack.Shape.one) ("sk_make") ([Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.var Flapjack.VarKind.local "code_hash"]) body373_9

def body373_11 : Prog (BitVec 64) :=
.seq body373_4 body373_10

def body373_12 : Prog (BitVec 64) :=
.seq body373_5 body373_11

def body373_13 : Prog (BitVec 64) :=
.seq body373_4 body373_12

def body373_14 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ts", Flapjack.Exp.const 48#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "code_hash"]) body373_13

def body373_15 : Prog (BitVec 64) :=
.seq body373_2 body373_14

def body373_16 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.var Flapjack.VarKind.local "code_hash", Flapjack.Exp.var Flapjack.VarKind.global "empty_code_hash",
  Flapjack.Exp.const 32#64]) body373_15

def body373_17 : Prog (BitVec 64) :=
.seq body373_4 body373_5

def body373_18 : Prog (BitVec 64) :=
.seq body373_17 body373_4

def body373_19 : Prog (BitVec 64) :=
.seq body373_18 body373_10

def body373_20 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ts", Flapjack.Exp.const 48#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "code_hash"]) body373_19

def body373_21 : Prog (BitVec 64) :=
.seq body373_2 body373_20

def body373_22 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.var Flapjack.VarKind.local "code_hash", Flapjack.Exp.var Flapjack.VarKind.global "empty_code_hash",
  Flapjack.Exp.const 32#64]) body373_21

def originalData373 : Decl (BitVec 64) :=
.function { name := "get_code", inline := false, exported := false, params := [("code_hash", Flapjack.Shape.one), ("addr", Flapjack.Shape.one)], body := body373_16, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData373 : Decl (BitVec 64) :=
.function { name := "get_code", inline := false, exported := false, params := [("code_hash", Flapjack.Shape.one), ("addr", Flapjack.Shape.one)], body := body373_22, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def original373 := Pancake.PanLang.declToHOL originalData373
def simplified373 := Pancake.PanLang.declToHOL simplifiedData373
end InitECandidate.Proofs.FrontendStages.Declarations
