import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify602
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body618_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body618_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body618_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma") (Flapjack.Exp.const 0#64)) body618_0 body618_1

def body618_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "b2_sigma"), none)) "alloc" [Flapjack.Exp.const 80#64]

def body618_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "b2_iv"), none)) "alloc" [Flapjack.Exp.const 64#64]

def body618_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "b2_v"), none)) "alloc" [Flapjack.Exp.const 128#64]

def body618_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.const 18364758544493064720#64)

def body618_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.const 3853709921291437230#64)

def body618_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.const 5266788149650328715#64)

def body618_9 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.const 10305543691612001175#64)

def body618_10 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.const 15242093322790139145#64)

def body618_11 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.const 10515720223929181890#64)

def body618_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.const 13270197634454188380#64)

def body618_13 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.const 11702690517083809725#64)

def body618_14 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.const 6503616966983130870#64)

def body618_15 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma", Flapjack.Exp.const 72#64])
  (Flapjack.Exp.const 991893350865389610#64)

def body618_16 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "b2_iv", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.const 7640891576956012808#64)

def body618_17 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "b2_iv", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.const 13503953896175478587#64)

def body618_18 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "b2_iv", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.const 4354685564936845355#64)

def body618_19 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "b2_iv", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.const 11912009170470909681#64)

def body618_20 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "b2_iv", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.const 5840696475078001361#64)

def body618_21 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "b2_iv", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.const 11170449401992604703#64)

def body618_22 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "b2_iv", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.const 2270897969802886507#64)

def body618_23 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "b2_iv", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.const 6620516959819538809#64)

def body618_24 : Prog (BitVec 64) :=
.seq body618_23 body618_0

def body618_25 : Prog (BitVec 64) :=
.seq body618_22 body618_24

def body618_26 : Prog (BitVec 64) :=
.seq body618_21 body618_25

def body618_27 : Prog (BitVec 64) :=
.seq body618_20 body618_26

def body618_28 : Prog (BitVec 64) :=
.seq body618_19 body618_27

def body618_29 : Prog (BitVec 64) :=
.seq body618_18 body618_28

def body618_30 : Prog (BitVec 64) :=
.seq body618_17 body618_29

def body618_31 : Prog (BitVec 64) :=
.seq body618_16 body618_30

def body618_32 : Prog (BitVec 64) :=
.seq body618_15 body618_31

def body618_33 : Prog (BitVec 64) :=
.seq body618_14 body618_32

def body618_34 : Prog (BitVec 64) :=
.seq body618_13 body618_33

def body618_35 : Prog (BitVec 64) :=
.seq body618_12 body618_34

def body618_36 : Prog (BitVec 64) :=
.seq body618_11 body618_35

def body618_37 : Prog (BitVec 64) :=
.seq body618_10 body618_36

def body618_38 : Prog (BitVec 64) :=
.seq body618_9 body618_37

def body618_39 : Prog (BitVec 64) :=
.seq body618_8 body618_38

def body618_40 : Prog (BitVec 64) :=
.seq body618_7 body618_39

def body618_41 : Prog (BitVec 64) :=
.seq body618_6 body618_40

def body618_42 : Prog (BitVec 64) :=
.seq body618_5 body618_41

def body618_43 : Prog (BitVec 64) :=
.seq body618_4 body618_42

def body618_44 : Prog (BitVec 64) :=
.seq body618_3 body618_43

def body618_45 : Prog (BitVec 64) :=
.seq body618_2 body618_44

def body618_46 : Prog (BitVec 64) :=
.seq body618_2 body618_3

def body618_47 : Prog (BitVec 64) :=
.seq body618_46 body618_4

def body618_48 : Prog (BitVec 64) :=
.seq body618_47 body618_5

def body618_49 : Prog (BitVec 64) :=
.seq body618_48 body618_6

def body618_50 : Prog (BitVec 64) :=
.seq body618_49 body618_7

def body618_51 : Prog (BitVec 64) :=
.seq body618_50 body618_8

def body618_52 : Prog (BitVec 64) :=
.seq body618_51 body618_9

def body618_53 : Prog (BitVec 64) :=
.seq body618_52 body618_10

def body618_54 : Prog (BitVec 64) :=
.seq body618_53 body618_11

def body618_55 : Prog (BitVec 64) :=
.seq body618_54 body618_12

def body618_56 : Prog (BitVec 64) :=
.seq body618_55 body618_13

def body618_57 : Prog (BitVec 64) :=
.seq body618_56 body618_14

def body618_58 : Prog (BitVec 64) :=
.seq body618_57 body618_15

def body618_59 : Prog (BitVec 64) :=
.seq body618_58 body618_16

def body618_60 : Prog (BitVec 64) :=
.seq body618_59 body618_17

def body618_61 : Prog (BitVec 64) :=
.seq body618_60 body618_18

def body618_62 : Prog (BitVec 64) :=
.seq body618_61 body618_19

def body618_63 : Prog (BitVec 64) :=
.seq body618_62 body618_20

def body618_64 : Prog (BitVec 64) :=
.seq body618_63 body618_21

def body618_65 : Prog (BitVec 64) :=
.seq body618_64 body618_22

def body618_66 : Prog (BitVec 64) :=
.seq body618_65 body618_23

def body618_67 : Prog (BitVec 64) :=
.seq body618_66 body618_0

def originalData618 : Decl (BitVec 64) :=
.function { name := "blake2_init", inline := false, exported := false, params := [], body := body618_45, returnShape := (Flapjack.Shape.one) }
def simplifiedData618 : Decl (BitVec 64) :=
.function { name := "blake2_init", inline := false, exported := false, params := [], body := body618_67, returnShape := (Flapjack.Shape.one) }
def original618 := Pancake.PanLang.declToHOL originalData618
def simplified618 := Pancake.PanLang.declToHOL simplifiedData618
end InitECandidate.Proofs.FrontendStages.Declarations
