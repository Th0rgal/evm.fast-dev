import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify554
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body570_0 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 0#64, Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 0#64])

def body570_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body570_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "v") (Flapjack.Exp.const 0#64)) body570_0 body570_1

def body570_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "da",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "code"), Flapjack.Exp.const 3#64],
    Flapjack.Exp.const 20#64]

def body570_4 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 1#64, Flapjack.Exp.var Flapjack.VarKind.local "da", Flapjack.Exp.const 100#64])

def body570_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "warm") (Flapjack.Exp.const 0#64)) body570_4 body570_1

def body570_6 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 1#64, Flapjack.Exp.var Flapjack.VarKind.local "da", Flapjack.Exp.const 3000#64])

def body570_7 : Prog (BitVec 64) :=
.seq body570_5 body570_6

def body570_8 : Prog (BitVec 64) :=
.decCall ("warm") (Flapjack.Shape.one) ("is_warm_address") ([Flapjack.Exp.var Flapjack.VarKind.local "da"]) body570_7

def body570_9 : Prog (BitVec 64) :=
.seq body570_3 body570_8

def body570_10 : Prog (BitVec 64) :=
.decCall ("da") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 24#64]) body570_9

def body570_11 : Prog (BitVec 64) :=
.seq body570_2 body570_10

def body570_12 : Prog (BitVec 64) :=
.decCall ("v") (Flapjack.Shape.one) ("is_valid_delegation") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "code"),
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "code")]) body570_11

def body570_13 : Prog (BitVec 64) :=
.decCall ("code") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("ext_code_of") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body570_12

def originalData570 : Decl (BitVec 64) :=
.function { name := "calculate_delegation_cost", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body570_13, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData570 : Decl (BitVec 64) :=
.function { name := "calculate_delegation_cost", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body570_13, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def original570 := Pancake.PanLang.declToHOL originalData570
def simplified570 := Pancake.PanLang.declToHOL simplifiedData570
end InitECandidate.Proofs.FrontendStages.Declarations
