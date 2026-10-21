import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify848
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body864_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "ovf" (Flapjack.Exp.const 1#64)

def body864_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body864_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "p"),
      Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "p"),
      Flapjack.Exp.rField 6 (Flapjack.Exp.var Flapjack.VarKind.local "p"),
      Flapjack.Exp.rField 7 (Flapjack.Exp.var Flapjack.VarKind.local "p")])
  (Flapjack.Exp.const 0#64)) body864_0 body864_1

def body864_3 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.var Flapjack.VarKind.local "ovf", Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "p"),
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "p"),
      Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "p"),
      Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "p")])

def body864_4 : Prog (BitVec 64) :=
.seq body864_2 body864_3

def body864_5 : Prog (BitVec 64) :=
.dec ("ovf") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body864_4

def body864_6 : Prog (BitVec 64) :=
.decCall ("p") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_mul_full") ([Flapjack.Exp.rStruct
    [Flapjack.Exp.var Flapjack.VarKind.local "gas", Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64,
      Flapjack.Exp.const 0#64],
  Flapjack.Exp.var Flapjack.VarKind.local "price"]) body864_5

def originalData864 : Decl (BitVec 64) :=
.function { name := "fee_mul", inline := false, exported := false, params := [("gas", Flapjack.Shape.one),
  ("price", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body864_6, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData864 : Decl (BitVec 64) :=
.function { name := "fee_mul", inline := false, exported := false, params := [("gas", Flapjack.Shape.one),
  ("price", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body864_6, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def original864 := Pancake.PanLang.declToHOL originalData864
def simplified864 := Pancake.PanLang.declToHOL simplifiedData864
end InitECandidate.Proofs.FrontendStages.Declarations
