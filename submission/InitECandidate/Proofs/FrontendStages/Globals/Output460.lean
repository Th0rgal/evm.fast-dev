import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data460
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate444
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody460_0 : Prog (BitVec 64) :=
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

def globalBody460_1 : Prog (BitVec 64) :=
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

def globalBody460_2 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "adv"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "op", Flapjack.Exp.const 96#64],
      Flapjack.Exp.const 2#64])

def globalBody460_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "adv" (Flapjack.Exp.const 2#64)

def globalBody460_4 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "adv" (Flapjack.Exp.const 1#64)

def globalBody460_5 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody460_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "nx")
        (Flapjack.Exp.const 91#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.const 127#64)
        (Flapjack.Exp.var Flapjack.VarKind.local "nx"))]) globalBody460_4 globalBody460_5

def globalBody460_7 : Prog (BitVec 64) :=
.dec ("nx") (Flapjack.Shape.one) (Flapjack.Exp.loadByte
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "code", Flapjack.Exp.var Flapjack.VarKind.local "pc",
      Flapjack.Exp.const 1#64])) globalBody460_6

def globalBody460_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pc", Flapjack.Exp.const 1#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) globalBody460_7 globalBody460_5

def globalBody460_9 : Prog (BitVec 64) :=
.seq globalBody460_3 globalBody460_8

def globalBody460_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 230#64),
      Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 231#64)])) globalBody460_9 globalBody460_5

def globalBody460_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "nx2")
        (Flapjack.Exp.const 82#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.const 127#64)
        (Flapjack.Exp.var Flapjack.VarKind.local "nx2"))]) globalBody460_4 globalBody460_5

def globalBody460_12 : Prog (BitVec 64) :=
.dec ("nx2") (Flapjack.Shape.one) (Flapjack.Exp.loadByte
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "code", Flapjack.Exp.var Flapjack.VarKind.local "pc",
      Flapjack.Exp.const 1#64])) globalBody460_11

def globalBody460_13 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pc", Flapjack.Exp.const 1#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) globalBody460_12 globalBody460_5

def globalBody460_14 : Prog (BitVec 64) :=
.seq globalBody460_3 globalBody460_13

def globalBody460_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 232#64)) globalBody460_14 globalBody460_5

def globalBody460_16 : Prog (BitVec 64) :=
.seq globalBody460_10 globalBody460_15

def globalBody460_17 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "op")
        (Flapjack.Exp.const 96#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.const 127#64)
        (Flapjack.Exp.var Flapjack.VarKind.local "op"))]) globalBody460_2 globalBody460_16

def globalBody460_18 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "op") (Flapjack.Exp.const 91#64)) globalBody460_1 globalBody460_17

def globalBody460_19 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "pc"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "pc", Flapjack.Exp.var Flapjack.VarKind.local "adv"])

def globalBody460_20 : Prog (BitVec 64) :=
.seq globalBody460_18 globalBody460_19

def globalBody460_21 : Prog (BitVec 64) :=
.dec ("adv") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) globalBody460_20

def globalBody460_22 : Prog (BitVec 64) :=
.dec ("op") (Flapjack.Shape.one) (Flapjack.Exp.loadByte
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "code", Flapjack.Exp.var Flapjack.VarKind.local "pc"])) globalBody460_21

def globalBody460_23 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "pc")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) globalBody460_22

def globalBody460_24 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "bm")

def globalBody460_25 : Prog (BitVec 64) :=
.seq globalBody460_23 globalBody460_24

def globalBody460_26 : Prog (BitVec 64) :=
.dec ("pc") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody460_25

def globalBody460_27 : Prog (BitVec 64) :=
.seq globalBody460_0 globalBody460_26

def globalBody460_28 : Prog (BitVec 64) :=
.decCall ("bm") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.shift Flapjack.Shift.lsr
            (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 63#64])
            (Flapjack.Exp.const 6#64),
          Flapjack.Exp.const 8#64],
      Flapjack.Exp.const 8#64]]) globalBody460_27

def globalData460 : Decl (BitVec 64) :=
.function { name := "compute_jumpdests", inline := false, exported := false, params := [("code", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := globalBody460_28, returnShape := (Flapjack.Shape.one) }
def globalOutput460 := Pancake.PanLang.declToHOL globalData460
end InitECandidate.Proofs.FrontendStages.Declarations
