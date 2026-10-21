import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data618
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate595
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody618_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody618_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody618_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 352#64]))
  (Flapjack.Exp.const 0#64)) globalBody618_0 globalBody618_1

def globalBody618_3 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 352#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "")

def globalBody618_4 : Prog (BitVec 64) :=
.decCall ("") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 80#64]) globalBody618_3

def globalBody618_5 : Prog (BitVec 64) :=
.seq globalBody618_2 globalBody618_4

def globalBody618_6 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 360#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "")

def globalBody618_7 : Prog (BitVec 64) :=
.decCall ("") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) globalBody618_6

def globalBody618_8 : Prog (BitVec 64) :=
.seq globalBody618_5 globalBody618_7

def globalBody618_9 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 368#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "")

def globalBody618_10 : Prog (BitVec 64) :=
.decCall ("") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 128#64]) globalBody618_9

def globalBody618_11 : Prog (BitVec 64) :=
.seq globalBody618_8 globalBody618_10

def globalBody618_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 352#64]),
      Flapjack.Exp.const 0#64])
  (Flapjack.Exp.const 18364758544493064720#64)

def globalBody618_13 : Prog (BitVec 64) :=
.seq globalBody618_11 globalBody618_12

def globalBody618_14 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 352#64]),
      Flapjack.Exp.const 8#64])
  (Flapjack.Exp.const 3853709921291437230#64)

def globalBody618_15 : Prog (BitVec 64) :=
.seq globalBody618_13 globalBody618_14

def globalBody618_16 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 352#64]),
      Flapjack.Exp.const 16#64])
  (Flapjack.Exp.const 5266788149650328715#64)

def globalBody618_17 : Prog (BitVec 64) :=
.seq globalBody618_15 globalBody618_16

def globalBody618_18 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 352#64]),
      Flapjack.Exp.const 24#64])
  (Flapjack.Exp.const 10305543691612001175#64)

def globalBody618_19 : Prog (BitVec 64) :=
.seq globalBody618_17 globalBody618_18

def globalBody618_20 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 352#64]),
      Flapjack.Exp.const 32#64])
  (Flapjack.Exp.const 15242093322790139145#64)

def globalBody618_21 : Prog (BitVec 64) :=
.seq globalBody618_19 globalBody618_20

def globalBody618_22 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 352#64]),
      Flapjack.Exp.const 40#64])
  (Flapjack.Exp.const 10515720223929181890#64)

def globalBody618_23 : Prog (BitVec 64) :=
.seq globalBody618_21 globalBody618_22

def globalBody618_24 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 352#64]),
      Flapjack.Exp.const 48#64])
  (Flapjack.Exp.const 13270197634454188380#64)

def globalBody618_25 : Prog (BitVec 64) :=
.seq globalBody618_23 globalBody618_24

def globalBody618_26 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 352#64]),
      Flapjack.Exp.const 56#64])
  (Flapjack.Exp.const 11702690517083809725#64)

def globalBody618_27 : Prog (BitVec 64) :=
.seq globalBody618_25 globalBody618_26

def globalBody618_28 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 352#64]),
      Flapjack.Exp.const 64#64])
  (Flapjack.Exp.const 6503616966983130870#64)

def globalBody618_29 : Prog (BitVec 64) :=
.seq globalBody618_27 globalBody618_28

def globalBody618_30 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 352#64]),
      Flapjack.Exp.const 72#64])
  (Flapjack.Exp.const 991893350865389610#64)

def globalBody618_31 : Prog (BitVec 64) :=
.seq globalBody618_29 globalBody618_30

def globalBody618_32 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 360#64]),
      Flapjack.Exp.const 0#64])
  (Flapjack.Exp.const 7640891576956012808#64)

def globalBody618_33 : Prog (BitVec 64) :=
.seq globalBody618_31 globalBody618_32

def globalBody618_34 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 360#64]),
      Flapjack.Exp.const 8#64])
  (Flapjack.Exp.const 13503953896175478587#64)

def globalBody618_35 : Prog (BitVec 64) :=
.seq globalBody618_33 globalBody618_34

def globalBody618_36 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 360#64]),
      Flapjack.Exp.const 16#64])
  (Flapjack.Exp.const 4354685564936845355#64)

def globalBody618_37 : Prog (BitVec 64) :=
.seq globalBody618_35 globalBody618_36

def globalBody618_38 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 360#64]),
      Flapjack.Exp.const 24#64])
  (Flapjack.Exp.const 11912009170470909681#64)

def globalBody618_39 : Prog (BitVec 64) :=
.seq globalBody618_37 globalBody618_38

def globalBody618_40 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 360#64]),
      Flapjack.Exp.const 32#64])
  (Flapjack.Exp.const 5840696475078001361#64)

def globalBody618_41 : Prog (BitVec 64) :=
.seq globalBody618_39 globalBody618_40

def globalBody618_42 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 360#64]),
      Flapjack.Exp.const 40#64])
  (Flapjack.Exp.const 11170449401992604703#64)

def globalBody618_43 : Prog (BitVec 64) :=
.seq globalBody618_41 globalBody618_42

def globalBody618_44 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 360#64]),
      Flapjack.Exp.const 48#64])
  (Flapjack.Exp.const 2270897969802886507#64)

def globalBody618_45 : Prog (BitVec 64) :=
.seq globalBody618_43 globalBody618_44

def globalBody618_46 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 360#64]),
      Flapjack.Exp.const 56#64])
  (Flapjack.Exp.const 6620516959819538809#64)

def globalBody618_47 : Prog (BitVec 64) :=
.seq globalBody618_45 globalBody618_46

def globalBody618_48 : Prog (BitVec 64) :=
.seq globalBody618_47 globalBody618_0

def globalData618 : Decl (BitVec 64) :=
.function { name := "blake2_init", inline := false, exported := false, params := [], body := globalBody618_48, returnShape := (Flapjack.Shape.one) }
def globalOutput618 := Pancake.PanLang.declToHOL globalData618
end InitECandidate.Proofs.FrontendStages.Declarations
