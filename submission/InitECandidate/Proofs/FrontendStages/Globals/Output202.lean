import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data202
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate186
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody202_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_fail" [Flapjack.Exp.const 60#64]

def globalBody202_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody202_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "len") (Flapjack.Exp.const 20#64)) globalBody202_0 globalBody202_1

def globalBody202_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 112#64]),
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]])
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.loadByte
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "p",
            Flapjack.Exp.panOp Flapjack.PanOp.mul
              [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 4#64]]),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "p",
              Flapjack.Exp.panOp Flapjack.PanOp.mul
                [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 4#64],
              Flapjack.Exp.const 1#64]))
        (Flapjack.Exp.const 8#64),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "p",
              Flapjack.Exp.panOp Flapjack.PanOp.mul
                [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 4#64],
              Flapjack.Exp.const 2#64]))
        (Flapjack.Exp.const 16#64),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "p",
              Flapjack.Exp.panOp Flapjack.PanOp.mul
                [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 4#64],
              Flapjack.Exp.const 3#64]))
        (Flapjack.Exp.const 24#64)])

def globalBody202_4 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody202_5 : Prog (BitVec 64) :=
.seq globalBody202_3 globalBody202_4

def globalBody202_6 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 5#64)) globalBody202_5

def globalBody202_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_check_offsets"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 112#64]),
    Flapjack.Exp.const 5#64, Flapjack.Exp.const 20#64, Flapjack.Exp.var Flapjack.VarKind.local "len"]

def globalBody202_8 : Prog (BitVec 64) :=
.seq globalBody202_6 globalBody202_7

def globalBody202_9 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "o0"])

def globalBody202_10 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "n0")

def globalBody202_11 : Prog (BitVec 64) :=
.seq globalBody202_9 globalBody202_10

def globalBody202_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "o1"])

def globalBody202_13 : Prog (BitVec 64) :=
.seq globalBody202_11 globalBody202_12

def globalBody202_14 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "n1")

def globalBody202_15 : Prog (BitVec 64) :=
.seq globalBody202_13 globalBody202_14

def globalBody202_16 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "o2"])

def globalBody202_17 : Prog (BitVec 64) :=
.seq globalBody202_15 globalBody202_16

def globalBody202_18 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "n2")

def globalBody202_19 : Prog (BitVec 64) :=
.seq globalBody202_17 globalBody202_18

def globalBody202_20 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "o3"])

def globalBody202_21 : Prog (BitVec 64) :=
.seq globalBody202_19 globalBody202_20

def globalBody202_22 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "n3")

def globalBody202_23 : Prog (BitVec 64) :=
.seq globalBody202_21 globalBody202_22

def globalBody202_24 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "o4"])

def globalBody202_25 : Prog (BitVec 64) :=
.seq globalBody202_23 globalBody202_24

def globalBody202_26 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 72#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "n4")

def globalBody202_27 : Prog (BitVec 64) :=
.seq globalBody202_25 globalBody202_26

def globalBody202_28 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "rq")

def globalBody202_29 : Prog (BitVec 64) :=
.seq globalBody202_27 globalBody202_28

def globalBody202_30 : Prog (BitVec 64) :=
.decCall ("n4") (Flapjack.Shape.one) ("ssz_fixed_list_count") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "len", Flapjack.Exp.var Flapjack.VarKind.local "o4"],
  Flapjack.Exp.const 68#64, Flapjack.Exp.const 9223372036854775807#64]) globalBody202_29

def globalBody202_31 : Prog (BitVec 64) :=
.decCall ("n3") (Flapjack.Shape.one) ("ssz_fixed_list_count") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "o4", Flapjack.Exp.var Flapjack.VarKind.local "o3"],
  Flapjack.Exp.const 184#64, Flapjack.Exp.const 9223372036854775807#64]) globalBody202_30

def globalBody202_32 : Prog (BitVec 64) :=
.decCall ("n2") (Flapjack.Shape.one) ("ssz_fixed_list_count") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "o3", Flapjack.Exp.var Flapjack.VarKind.local "o2"],
  Flapjack.Exp.const 116#64, Flapjack.Exp.const 9223372036854775807#64]) globalBody202_31

def globalBody202_33 : Prog (BitVec 64) :=
.decCall ("n1") (Flapjack.Shape.one) ("ssz_fixed_list_count") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "o2", Flapjack.Exp.var Flapjack.VarKind.local "o1"],
  Flapjack.Exp.const 76#64, Flapjack.Exp.const 9223372036854775807#64]) globalBody202_32

def globalBody202_34 : Prog (BitVec 64) :=
.decCall ("n0") (Flapjack.Shape.one) ("ssz_fixed_list_count") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "o1", Flapjack.Exp.var Flapjack.VarKind.local "o0"],
  Flapjack.Exp.const 192#64, Flapjack.Exp.const 9223372036854775807#64]) globalBody202_33

def globalBody202_35 : Prog (BitVec 64) :=
.dec ("o4") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 112#64]),
      Flapjack.Exp.const 32#64])) globalBody202_34

def globalBody202_36 : Prog (BitVec 64) :=
.dec ("o3") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 112#64]),
      Flapjack.Exp.const 24#64])) globalBody202_35

def globalBody202_37 : Prog (BitVec 64) :=
.dec ("o2") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 112#64]),
      Flapjack.Exp.const 16#64])) globalBody202_36

def globalBody202_38 : Prog (BitVec 64) :=
.dec ("o1") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 112#64]),
      Flapjack.Exp.const 8#64])) globalBody202_37

def globalBody202_39 : Prog (BitVec 64) :=
.dec ("o0") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 112#64]))) globalBody202_38

def globalBody202_40 : Prog (BitVec 64) :=
.decCall ("rq") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 80#64]) globalBody202_39

def globalBody202_41 : Prog (BitVec 64) :=
.seq globalBody202_8 globalBody202_40

def globalBody202_42 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody202_41

def globalBody202_43 : Prog (BitVec 64) :=
.seq globalBody202_2 globalBody202_42

def globalData202 : Decl (BitVec 64) :=
.function { name := "decode_requests", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("len", Flapjack.Shape.one)], body := globalBody202_43, returnShape := (Flapjack.Shape.one) }
def globalOutput202 := Pancake.PanLang.declToHOL globalData202
end InitECandidate.Proofs.FrontendStages.Declarations
