import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify441
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body457_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body457_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body457_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "expand_by") (Flapjack.Exp.const 0#64)) body457_0 body457_1

def body457_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "ncap"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nlen", Flapjack.Exp.const 1024#64])

def body457_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "ncap")
  (Flapjack.Exp.var Flapjack.VarKind.local "nlen")) body457_3 body457_1

def body457_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "frame_mem_alloc"
  [Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "ncap", Flapjack.Exp.var Flapjack.VarKind.local "cap"]]

def body457_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 24#64]),
        Flapjack.Exp.var Flapjack.VarKind.local "cap"],
    Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "ncap", Flapjack.Exp.var Flapjack.VarKind.local "cap"]]

def body457_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "ncap")

def body457_8 : Prog (BitVec 64) :=
.seq body457_6 body457_7

def body457_9 : Prog (BitVec 64) :=
.seq body457_5 body457_8

def body457_10 : Prog (BitVec 64) :=
.seq body457_4 body457_9

def body457_11 : Prog (BitVec 64) :=
.dec ("ncap") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "cap", Flapjack.Exp.const 2#64]) body457_10

def body457_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "cap")
  (Flapjack.Exp.var Flapjack.VarKind.local "nlen")) body457_11 body457_1

def body457_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 24#64]),
        Flapjack.Exp.var Flapjack.VarKind.local "len"],
    Flapjack.Exp.var Flapjack.VarKind.local "expand_by"]

def body457_14 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "nlen")

def body457_15 : Prog (BitVec 64) :=
.seq body457_14 body457_0

def body457_16 : Prog (BitVec 64) :=
.seq body457_13 body457_15

def body457_17 : Prog (BitVec 64) :=
.seq body457_12 body457_16

def body457_18 : Prog (BitVec 64) :=
.dec ("nlen") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "len", Flapjack.Exp.var Flapjack.VarKind.local "expand_by"]) body457_17

def body457_19 : Prog (BitVec 64) :=
.dec ("cap") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 40#64])) body457_18

def body457_20 : Prog (BitVec 64) :=
.dec ("len") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 32#64])) body457_19

def body457_21 : Prog (BitVec 64) :=
.seq body457_2 body457_20

def body457_22 : Prog (BitVec 64) :=
.seq body457_4 body457_5

def body457_23 : Prog (BitVec 64) :=
.seq body457_22 body457_6

def body457_24 : Prog (BitVec 64) :=
.seq body457_23 body457_7

def body457_25 : Prog (BitVec 64) :=
.dec ("ncap") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "cap", Flapjack.Exp.const 2#64]) body457_24

def body457_26 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "cap")
  (Flapjack.Exp.var Flapjack.VarKind.local "nlen")) body457_25 body457_1

def body457_27 : Prog (BitVec 64) :=
.seq body457_26 body457_13

def body457_28 : Prog (BitVec 64) :=
.seq body457_27 body457_14

def body457_29 : Prog (BitVec 64) :=
.seq body457_28 body457_0

def body457_30 : Prog (BitVec 64) :=
.dec ("nlen") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "len", Flapjack.Exp.var Flapjack.VarKind.local "expand_by"]) body457_29

def body457_31 : Prog (BitVec 64) :=
.dec ("cap") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 40#64])) body457_30

def body457_32 : Prog (BitVec 64) :=
.dec ("len") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 32#64])) body457_31

def body457_33 : Prog (BitVec 64) :=
.seq body457_2 body457_32

def originalData457 : Decl (BitVec 64) :=
.function { name := "extend_memory", inline := false, exported := false, params := [("expand_by", Flapjack.Shape.one)], body := body457_21, returnShape := (Flapjack.Shape.one) }
def simplifiedData457 : Decl (BitVec 64) :=
.function { name := "extend_memory", inline := false, exported := false, params := [("expand_by", Flapjack.Shape.one)], body := body457_33, returnShape := (Flapjack.Shape.one) }
def original457 := Pancake.PanLang.declToHOL originalData457
def simplified457 := Pancake.PanLang.declToHOL simplifiedData457
end InitECandidate.Proofs.FrontendStages.Declarations
