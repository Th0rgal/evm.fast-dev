import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify398
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body414_0 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64],
      Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "new_nonce")

def body414_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body414_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "p",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64],
        Flapjack.Exp.const 8#64]))
  (Flapjack.Exp.var Flapjack.VarKind.local "new_nonce")) body414_0 body414_1

def body414_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body414_4 : Prog (BitVec 64) :=
.seq body414_2 body414_3

def body414_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "p",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64]]))
  (Flapjack.Exp.var Flapjack.VarKind.local "idx")) body414_4 body414_1

def body414_6 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body414_7 : Prog (BitVec 64) :=
.seq body414_5 body414_6

def body414_8 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body414_7

def body414_9 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "e") (Flapjack.Exp.var Flapjack.VarKind.local "idx")

def body414_10 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "new_nonce")

def body414_11 : Prog (BitVec 64) :=
.seq body414_10 body414_3

def body414_12 : Prog (BitVec 64) :=
.seq body414_9 body414_11

def body414_13 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.one) ("lst_push") ([Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 16#64]) body414_12

def body414_14 : Prog (BitVec 64) :=
.seq body414_8 body414_13

def body414_15 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body414_14

def body414_16 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 0#64])) body414_15

def body414_17 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 8#64])) body414_16

def body414_18 : Prog (BitVec 64) :=
.dec ("l") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 24#64])) body414_17

def body414_19 : Prog (BitVec 64) :=
.decCall ("ad") (Flapjack.Shape.one) ("bal_ensure_account") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body414_18

def body414_20 : Prog (BitVec 64) :=
.seq body414_9 body414_10

def body414_21 : Prog (BitVec 64) :=
.seq body414_20 body414_3

def body414_22 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.one) ("lst_push") ([Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 16#64]) body414_21

def body414_23 : Prog (BitVec 64) :=
.seq body414_8 body414_22

def body414_24 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body414_23

def body414_25 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 0#64])) body414_24

def body414_26 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 8#64])) body414_25

def body414_27 : Prog (BitVec 64) :=
.dec ("l") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ad", Flapjack.Exp.const 24#64])) body414_26

def body414_28 : Prog (BitVec 64) :=
.decCall ("ad") (Flapjack.Shape.one) ("bal_ensure_account") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body414_27

def originalData414 : Decl (BitVec 64) :=
.function { name := "add_nonce_change", inline := false, exported := false, params := [("addr", Flapjack.Shape.one), ("idx", Flapjack.Shape.one), ("new_nonce", Flapjack.Shape.one)], body := body414_19, returnShape := (Flapjack.Shape.one) }
def simplifiedData414 : Decl (BitVec 64) :=
.function { name := "add_nonce_change", inline := false, exported := false, params := [("addr", Flapjack.Shape.one), ("idx", Flapjack.Shape.one), ("new_nonce", Flapjack.Shape.one)], body := body414_28, returnShape := (Flapjack.Shape.one) }
def original414 := Pancake.PanLang.declToHOL originalData414
def simplified414 := Pancake.PanLang.declToHOL simplifiedData414
end InitECandidate.Proofs.FrontendStages.Declarations
