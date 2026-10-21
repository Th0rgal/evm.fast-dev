import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify444
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body460_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "bm",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.shift Flapjack.Shift.lsr
              (Flapjack.Exp.op Flapjack.BinOp.add
                [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 63#64])
              (Flapjack.Exp.const 6#64),
            Flapjack.Exp.const 8#64],
        Flapjack.Exp.const 8#64]]

def body460_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "bm",
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "pc") (Flapjack.Exp.const 6#64),
          Flapjack.Exp.const 8#64]])
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "bm",
            Flapjack.Exp.panOp Flapjack.PanOp.mul
              [Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "pc")
                  (Flapjack.Exp.const 6#64),
                Flapjack.Exp.const 8#64]]),
      Flapjack.Exp.shift Flapjack.Shift.lsl (Flapjack.Exp.const 1#64)
        (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "pc", Flapjack.Exp.const 63#64])])

def body460_2 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "adv"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "op", Flapjack.Exp.const 96#64],
      Flapjack.Exp.const 2#64])

def body460_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "adv" (Flapjack.Exp.const 2#64)

def body460_4 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "adv" (Flapjack.Exp.const 1#64)

def body460_5 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body460_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "nx")
        (Flapjack.Exp.const 91#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.const 127#64)
        (Flapjack.Exp.var Flapjack.VarKind.local "nx"))]) body460_4 body460_5

def body460_7 : Prog (BitVec 64) :=
.dec ("nx") (Flapjack.Shape.one) (Flapjack.Exp.loadByte
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "code", Flapjack.Exp.var Flapjack.VarKind.local "pc",
      Flapjack.Exp.const 1#64])) body460_6

def body460_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pc", Flapjack.Exp.const 1#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body460_7 body460_5

def body460_9 : Prog (BitVec 64) :=
.seq body460_3 body460_8

def body460_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 230#64),
      Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 231#64)])) body460_9 body460_5

def body460_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "nx2")
        (Flapjack.Exp.const 82#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.const 127#64)
        (Flapjack.Exp.var Flapjack.VarKind.local "nx2"))]) body460_4 body460_5

def body460_12 : Prog (BitVec 64) :=
.dec ("nx2") (Flapjack.Shape.one) (Flapjack.Exp.loadByte
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "code", Flapjack.Exp.var Flapjack.VarKind.local "pc",
      Flapjack.Exp.const 1#64])) body460_11

def body460_13 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pc", Flapjack.Exp.const 1#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body460_12 body460_5

def body460_14 : Prog (BitVec 64) :=
.seq body460_3 body460_13

def body460_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 232#64)) body460_14 body460_5

def body460_16 : Prog (BitVec 64) :=
.seq body460_10 body460_15

def body460_17 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "op")
        (Flapjack.Exp.const 96#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.const 127#64)
        (Flapjack.Exp.var Flapjack.VarKind.local "op"))]) body460_2 body460_16

def body460_18 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 91#64)) body460_1 body460_17

def body460_19 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pc"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "pc", Flapjack.Exp.var Flapjack.VarKind.local "adv"])

def body460_20 : Prog (BitVec 64) :=
.seq body460_18 body460_19

def body460_21 : Prog (BitVec 64) :=
.dec ("adv") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) body460_20

def body460_22 : Prog (BitVec 64) :=
.dec ("op") (Flapjack.Shape.one) (Flapjack.Exp.loadByte
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "code", Flapjack.Exp.var Flapjack.VarKind.local "pc"])) body460_21

def body460_23 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "pc")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body460_22

def body460_24 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "bm")

def body460_25 : Prog (BitVec 64) :=
.seq body460_23 body460_24

def body460_26 : Prog (BitVec 64) :=
.dec ("pc") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body460_25

def body460_27 : Prog (BitVec 64) :=
.seq body460_0 body460_26

def body460_28 : Prog (BitVec 64) :=
.decCall ("bm") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.shift Flapjack.Shift.lsr
            (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 63#64])
            (Flapjack.Exp.const 6#64),
          Flapjack.Exp.const 8#64],
      Flapjack.Exp.const 8#64]]) body460_27

def originalData460 : Decl (BitVec 64) :=
.function { name := "compute_jumpdests", inline := false, exported := false, params := [("code", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body460_28, returnShape := (Flapjack.Shape.one) }
def simplifiedData460 : Decl (BitVec 64) :=
.function { name := "compute_jumpdests", inline := false, exported := false, params := [("code", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body460_28, returnShape := (Flapjack.Shape.one) }
def original460 := Pancake.PanLang.declToHOL originalData460
def simplified460 := Pancake.PanLang.declToHOL simplifiedData460
end InitECandidate.Proofs.FrontendStages.Declarations
