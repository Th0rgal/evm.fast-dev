import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify445
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body461_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body461_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body461_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "dest"),
      Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "dest"),
      Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "dest")])
  (Flapjack.Exp.const 0#64)) body461_0 body461_1

def body461_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "d")
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 56#64]))) body461_0 body461_1

def body461_4 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.shift Flapjack.Shift.lsr
        (Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "bm",
              Flapjack.Exp.panOp Flapjack.PanOp.mul
                [Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "d")
                    (Flapjack.Exp.const 6#64),
                  Flapjack.Exp.const 8#64]]))
        (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.const 63#64]),
      Flapjack.Exp.const 1#64])

def body461_5 : Prog (BitVec 64) :=
.dec ("bm") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 80#64])) body461_4

def body461_6 : Prog (BitVec 64) :=
.seq body461_3 body461_5

def body461_7 : Prog (BitVec 64) :=
.dec ("d") (Flapjack.Shape.one) (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "dest")) body461_6

def body461_8 : Prog (BitVec 64) :=
.seq body461_2 body461_7

def originalData461 : Decl (BitVec 64) :=
.function { name := "is_valid_jumpdest", inline := false, exported := false, params := [("dest", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body461_8, returnShape := (Flapjack.Shape.one) }
def simplifiedData461 : Decl (BitVec 64) :=
.function { name := "is_valid_jumpdest", inline := false, exported := false, params := [("dest", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body461_8, returnShape := (Flapjack.Shape.one) }
def original461 := Pancake.PanLang.declToHOL originalData461
def simplified461 := Pancake.PanLang.declToHOL simplifiedData461
end InitECandidate.Proofs.FrontendStages.Declarations
