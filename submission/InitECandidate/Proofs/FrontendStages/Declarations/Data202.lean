import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify186
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body202_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_fail" [Flapjack.Exp.const 60#64]

def body202_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body202_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "len") (Flapjack.Exp.const 20#64)) body202_0 body202_1

def body202_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs",
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

def body202_4 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body202_5 : Prog (BitVec 64) :=
.seq body202_3 body202_4

def body202_6 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 5#64)) body202_5

def body202_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_check_offsets"
  [Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs", Flapjack.Exp.const 5#64, Flapjack.Exp.const 20#64,
    Flapjack.Exp.var Flapjack.VarKind.local "len"]

def body202_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "o0"])

def body202_9 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "n0")

def body202_10 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "o1"])

def body202_11 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "n1")

def body202_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "o2"])

def body202_13 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "n2")

def body202_14 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "o3"])

def body202_15 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "n3")

def body202_16 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "o4"])

def body202_17 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 72#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "n4")

def body202_18 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "rq")

def body202_19 : Prog (BitVec 64) :=
.seq body202_17 body202_18

def body202_20 : Prog (BitVec 64) :=
.seq body202_16 body202_19

def body202_21 : Prog (BitVec 64) :=
.seq body202_15 body202_20

def body202_22 : Prog (BitVec 64) :=
.seq body202_14 body202_21

def body202_23 : Prog (BitVec 64) :=
.seq body202_13 body202_22

def body202_24 : Prog (BitVec 64) :=
.seq body202_12 body202_23

def body202_25 : Prog (BitVec 64) :=
.seq body202_11 body202_24

def body202_26 : Prog (BitVec 64) :=
.seq body202_10 body202_25

def body202_27 : Prog (BitVec 64) :=
.seq body202_9 body202_26

def body202_28 : Prog (BitVec 64) :=
.seq body202_8 body202_27

def body202_29 : Prog (BitVec 64) :=
.decCall ("n4") (Flapjack.Shape.one) ("ssz_fixed_list_count") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "len", Flapjack.Exp.var Flapjack.VarKind.local "o4"],
  Flapjack.Exp.const 68#64, Flapjack.Exp.const 9223372036854775807#64]) body202_28

def body202_30 : Prog (BitVec 64) :=
.decCall ("n3") (Flapjack.Shape.one) ("ssz_fixed_list_count") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "o4", Flapjack.Exp.var Flapjack.VarKind.local "o3"],
  Flapjack.Exp.const 184#64, Flapjack.Exp.const 9223372036854775807#64]) body202_29

def body202_31 : Prog (BitVec 64) :=
.decCall ("n2") (Flapjack.Shape.one) ("ssz_fixed_list_count") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "o3", Flapjack.Exp.var Flapjack.VarKind.local "o2"],
  Flapjack.Exp.const 116#64, Flapjack.Exp.const 9223372036854775807#64]) body202_30

def body202_32 : Prog (BitVec 64) :=
.decCall ("n1") (Flapjack.Shape.one) ("ssz_fixed_list_count") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "o2", Flapjack.Exp.var Flapjack.VarKind.local "o1"],
  Flapjack.Exp.const 76#64, Flapjack.Exp.const 9223372036854775807#64]) body202_31

def body202_33 : Prog (BitVec 64) :=
.decCall ("n0") (Flapjack.Shape.one) ("ssz_fixed_list_count") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "o1", Flapjack.Exp.var Flapjack.VarKind.local "o0"],
  Flapjack.Exp.const 192#64, Flapjack.Exp.const 9223372036854775807#64]) body202_32

def body202_34 : Prog (BitVec 64) :=
.dec ("o4") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs", Flapjack.Exp.const 32#64])) body202_33

def body202_35 : Prog (BitVec 64) :=
.dec ("o3") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs", Flapjack.Exp.const 24#64])) body202_34

def body202_36 : Prog (BitVec 64) :=
.dec ("o2") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs", Flapjack.Exp.const 16#64])) body202_35

def body202_37 : Prog (BitVec 64) :=
.dec ("o1") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs", Flapjack.Exp.const 8#64])) body202_36

def body202_38 : Prog (BitVec 64) :=
.dec ("o0") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs")) body202_37

def body202_39 : Prog (BitVec 64) :=
.decCall ("rq") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 80#64]) body202_38

def body202_40 : Prog (BitVec 64) :=
.seq body202_7 body202_39

def body202_41 : Prog (BitVec 64) :=
.seq body202_6 body202_40

def body202_42 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body202_41

def body202_43 : Prog (BitVec 64) :=
.seq body202_2 body202_42

def body202_44 : Prog (BitVec 64) :=
.seq body202_6 body202_7

def body202_45 : Prog (BitVec 64) :=
.seq body202_8 body202_9

def body202_46 : Prog (BitVec 64) :=
.seq body202_45 body202_10

def body202_47 : Prog (BitVec 64) :=
.seq body202_46 body202_11

def body202_48 : Prog (BitVec 64) :=
.seq body202_47 body202_12

def body202_49 : Prog (BitVec 64) :=
.seq body202_48 body202_13

def body202_50 : Prog (BitVec 64) :=
.seq body202_49 body202_14

def body202_51 : Prog (BitVec 64) :=
.seq body202_50 body202_15

def body202_52 : Prog (BitVec 64) :=
.seq body202_51 body202_16

def body202_53 : Prog (BitVec 64) :=
.seq body202_52 body202_17

def body202_54 : Prog (BitVec 64) :=
.seq body202_53 body202_18

def body202_55 : Prog (BitVec 64) :=
.decCall ("n4") (Flapjack.Shape.one) ("ssz_fixed_list_count") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "len", Flapjack.Exp.var Flapjack.VarKind.local "o4"],
  Flapjack.Exp.const 68#64, Flapjack.Exp.const 9223372036854775807#64]) body202_54

def body202_56 : Prog (BitVec 64) :=
.decCall ("n3") (Flapjack.Shape.one) ("ssz_fixed_list_count") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "o4", Flapjack.Exp.var Flapjack.VarKind.local "o3"],
  Flapjack.Exp.const 184#64, Flapjack.Exp.const 9223372036854775807#64]) body202_55

def body202_57 : Prog (BitVec 64) :=
.decCall ("n2") (Flapjack.Shape.one) ("ssz_fixed_list_count") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "o3", Flapjack.Exp.var Flapjack.VarKind.local "o2"],
  Flapjack.Exp.const 116#64, Flapjack.Exp.const 9223372036854775807#64]) body202_56

def body202_58 : Prog (BitVec 64) :=
.decCall ("n1") (Flapjack.Shape.one) ("ssz_fixed_list_count") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "o2", Flapjack.Exp.var Flapjack.VarKind.local "o1"],
  Flapjack.Exp.const 76#64, Flapjack.Exp.const 9223372036854775807#64]) body202_57

def body202_59 : Prog (BitVec 64) :=
.decCall ("n0") (Flapjack.Shape.one) ("ssz_fixed_list_count") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "o1", Flapjack.Exp.var Flapjack.VarKind.local "o0"],
  Flapjack.Exp.const 192#64, Flapjack.Exp.const 9223372036854775807#64]) body202_58

def body202_60 : Prog (BitVec 64) :=
.dec ("o4") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs", Flapjack.Exp.const 32#64])) body202_59

def body202_61 : Prog (BitVec 64) :=
.dec ("o3") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs", Flapjack.Exp.const 24#64])) body202_60

def body202_62 : Prog (BitVec 64) :=
.dec ("o2") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs", Flapjack.Exp.const 16#64])) body202_61

def body202_63 : Prog (BitVec 64) :=
.dec ("o1") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs", Flapjack.Exp.const 8#64])) body202_62

def body202_64 : Prog (BitVec 64) :=
.dec ("o0") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs")) body202_63

def body202_65 : Prog (BitVec 64) :=
.decCall ("rq") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 80#64]) body202_64

def body202_66 : Prog (BitVec 64) :=
.seq body202_44 body202_65

def body202_67 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body202_66

def body202_68 : Prog (BitVec 64) :=
.seq body202_2 body202_67

def originalData202 : Decl (BitVec 64) :=
.function { name := "decode_requests", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("len", Flapjack.Shape.one)], body := body202_43, returnShape := (Flapjack.Shape.one) }
def simplifiedData202 : Decl (BitVec 64) :=
.function { name := "decode_requests", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("len", Flapjack.Shape.one)], body := body202_68, returnShape := (Flapjack.Shape.one) }
def original202 := Pancake.PanLang.declToHOL originalData202
def simplified202 := Pancake.PanLang.declToHOL simplifiedData202
end InitECandidate.Proofs.FrontendStages.Declarations
