import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify427
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body443_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body443_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body443_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 23#64)) body443_0 body443_1

def body443_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body443_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.loadByte (Flapjack.Exp.var Flapjack.VarKind.local "code"))
        (Flapjack.Exp.const 239#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "code", Flapjack.Exp.const 1#64]))
        (Flapjack.Exp.const 1#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "code", Flapjack.Exp.const 2#64]))
        (Flapjack.Exp.const 0#64))]) body443_3 body443_1

def body443_5 : Prog (BitVec 64) :=
.seq body443_4 body443_0

def body443_6 : Prog (BitVec 64) :=
.seq body443_2 body443_5

def body443_7 : Prog (BitVec 64) :=
.seq body443_2 body443_4

def body443_8 : Prog (BitVec 64) :=
.seq body443_7 body443_0

def originalData443 : Decl (BitVec 64) :=
.function { name := "is_valid_delegation", inline := false, exported := false, params := [("code", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body443_6, returnShape := (Flapjack.Shape.one) }
def simplifiedData443 : Decl (BitVec 64) :=
.function { name := "is_valid_delegation", inline := false, exported := false, params := [("code", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body443_8, returnShape := (Flapjack.Shape.one) }
def original443 := Pancake.PanLang.declToHOL originalData443
def simplified443 := Pancake.PanLang.declToHOL simplifiedData443
end InitECandidate.Proofs.FrontendStages.Declarations
