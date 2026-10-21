import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify682
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body698_0 : Prog (BitVec 64) :=
Flapjack.Prog.primitive "r0" Flapjack.PrimOp.addCarry
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.op Flapjack.BinOp.xor
      [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "b"),
        Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.const 0#64, Flapjack.Exp.const 1#64]],
    Flapjack.Exp.const 1#64]

def body698_1 : Prog (BitVec 64) :=
Flapjack.Prog.primitive "r1" Flapjack.PrimOp.addCarry
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.op Flapjack.BinOp.xor
      [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "b"),
        Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.const 0#64, Flapjack.Exp.const 1#64]],
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "r0")]

def body698_2 : Prog (BitVec 64) :=
Flapjack.Prog.primitive "r2" Flapjack.PrimOp.addCarry
  [Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.op Flapjack.BinOp.xor
      [Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "b"),
        Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.const 0#64, Flapjack.Exp.const 1#64]],
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "r1")]

def body698_3 : Prog (BitVec 64) :=
Flapjack.Prog.primitive "r3" Flapjack.PrimOp.addCarry
  [Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.op Flapjack.BinOp.xor
      [Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "b"),
        Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.const 0#64, Flapjack.Exp.const 1#64]],
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "r2")]

def body698_4 : Prog (BitVec 64) :=
Flapjack.Prog.primitive "r4" Flapjack.PrimOp.addCarry
  [Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.op Flapjack.BinOp.xor
      [Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "b"),
        Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.const 0#64, Flapjack.Exp.const 1#64]],
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "r3")]

def body698_5 : Prog (BitVec 64) :=
Flapjack.Prog.primitive "r5" Flapjack.PrimOp.addCarry
  [Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "a"),
    Flapjack.Exp.op Flapjack.BinOp.xor
      [Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "b"),
        Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.const 0#64, Flapjack.Exp.const 1#64]],
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "r4")]

def body698_6 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "r0"),
      Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "r1"),
      Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "r2"),
      Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "r3"),
      Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "r4"),
      Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "r5"),
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "r5")])

def body698_7 : Prog (BitVec 64) :=
.seq body698_5 body698_6

def body698_8 : Prog (BitVec 64) :=
.dec ("r5") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body698_7

def body698_9 : Prog (BitVec 64) :=
.seq body698_4 body698_8

def body698_10 : Prog (BitVec 64) :=
.dec ("r4") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body698_9

def body698_11 : Prog (BitVec 64) :=
.seq body698_3 body698_10

def body698_12 : Prog (BitVec 64) :=
.dec ("r3") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body698_11

def body698_13 : Prog (BitVec 64) :=
.seq body698_2 body698_12

def body698_14 : Prog (BitVec 64) :=
.dec ("r2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body698_13

def body698_15 : Prog (BitVec 64) :=
.seq body698_1 body698_14

def body698_16 : Prog (BitVec 64) :=
.dec ("r1") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body698_15

def body698_17 : Prog (BitVec 64) :=
.seq body698_0 body698_16

def body698_18 : Prog (BitVec 64) :=
.dec ("r0") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body698_17

def originalData698 : Decl (BitVec 64) :=
.function { name := "bls_fp_sub_raw", inline := false, exported := false, params := [("a",
    Flapjack.Shape.comb
      [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
        Flapjack.Shape.one]),
  ("b",
    Flapjack.Shape.comb
      [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
        Flapjack.Shape.one])], body := body698_18, returnShape := (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData698 : Decl (BitVec 64) :=
.function { name := "bls_fp_sub_raw", inline := false, exported := false, params := [("a",
    Flapjack.Shape.comb
      [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
        Flapjack.Shape.one]),
  ("b",
    Flapjack.Shape.comb
      [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
        Flapjack.Shape.one])], body := body698_18, returnShape := (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one, Flapjack.Shape.one]) }
def original698 := Pancake.PanLang.declToHOL originalData698
def simplified698 := Pancake.PanLang.declToHOL simplifiedData698
end InitECandidate.Proofs.FrontendStages.Declarations
