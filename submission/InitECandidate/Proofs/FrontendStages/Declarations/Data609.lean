import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify593
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body609_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body609_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body609_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.global "rmd_tab") (Flapjack.Exp.const 0#64)) body609_0 body609_1

def body609_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "rmd_tab"), none)) "alloc" [Flapjack.Exp.const 160#64]

def body609_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "rmd_x"), none)) "alloc" [Flapjack.Exp.const 128#64]

def body609_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "rmd_h"), none)) "alloc" [Flapjack.Exp.const 40#64]

def body609_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "rmd_pad"), none)) "alloc" [Flapjack.Exp.const 128#64]

def body609_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "rmd_tab", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.const 18364758544493064720#64)

def body609_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "rmd_tab", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.const 10079716825146989895#64)

def body609_9 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "rmd_tab", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.const 14248650839231647395#64)

def body609_10 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "rmd_tab", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.const 2764919063900629905#64)

def body609_11 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "rmd_tab", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.const 16099105460569216260#64)

def body609_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "rmd_tab", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.const 14096706008221550565#64)

def body609_13 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "rmd_tab", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.const 2419779895833949110#64)

def body609_14 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "rmd_tab", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.const 15279073663851639135#64)

def body609_15 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "rmd_tab", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.const 16895767220870911080#64)

def body609_16 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "rmd_tab", Flapjack.Exp.const 72#64])
  (Flapjack.Exp.const 13344426445381913340#64)

def body609_17 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "rmd_tab", Flapjack.Exp.const 80#64])
  (Flapjack.Exp.const 9905384649541406699#64)

def body609_18 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "rmd_tab", Flapjack.Exp.const 88#64])
  (Flapjack.Exp.const 14806603881112131687#64)

def body609_19 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "rmd_tab", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.const 6324581712619534043#64)

def body609_20 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "rmd_tab", Flapjack.Exp.const 104#64])
  (Flapjack.Exp.const 14224731476766686923#64)

def body609_21 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "rmd_tab", Flapjack.Exp.const 112#64])
  (Flapjack.Exp.const 7317203453406000633#64)

def body609_22 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "rmd_tab", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.const 7849414023404435864#64)

def body609_23 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "rmd_tab", Flapjack.Exp.const 128#64])
  (Flapjack.Exp.const 13688264971095146457#64)

def body609_24 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "rmd_tab", Flapjack.Exp.const 136#64])
  (Flapjack.Exp.const 6331469388073975673#64)

def body609_25 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "rmd_tab", Flapjack.Exp.const 144#64])
  (Flapjack.Exp.const 10330303817214507103#64)

def body609_26 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "rmd_tab", Flapjack.Exp.const 152#64])
  (Flapjack.Exp.const 13537634492463488088#64)

def body609_27 : Prog (BitVec 64) :=
.seq body609_26 body609_0

def body609_28 : Prog (BitVec 64) :=
.seq body609_25 body609_27

def body609_29 : Prog (BitVec 64) :=
.seq body609_24 body609_28

def body609_30 : Prog (BitVec 64) :=
.seq body609_23 body609_29

def body609_31 : Prog (BitVec 64) :=
.seq body609_22 body609_30

def body609_32 : Prog (BitVec 64) :=
.seq body609_21 body609_31

def body609_33 : Prog (BitVec 64) :=
.seq body609_20 body609_32

def body609_34 : Prog (BitVec 64) :=
.seq body609_19 body609_33

def body609_35 : Prog (BitVec 64) :=
.seq body609_18 body609_34

def body609_36 : Prog (BitVec 64) :=
.seq body609_17 body609_35

def body609_37 : Prog (BitVec 64) :=
.seq body609_16 body609_36

def body609_38 : Prog (BitVec 64) :=
.seq body609_15 body609_37

def body609_39 : Prog (BitVec 64) :=
.seq body609_14 body609_38

def body609_40 : Prog (BitVec 64) :=
.seq body609_13 body609_39

def body609_41 : Prog (BitVec 64) :=
.seq body609_12 body609_40

def body609_42 : Prog (BitVec 64) :=
.seq body609_11 body609_41

def body609_43 : Prog (BitVec 64) :=
.seq body609_10 body609_42

def body609_44 : Prog (BitVec 64) :=
.seq body609_9 body609_43

def body609_45 : Prog (BitVec 64) :=
.seq body609_8 body609_44

def body609_46 : Prog (BitVec 64) :=
.seq body609_7 body609_45

def body609_47 : Prog (BitVec 64) :=
.seq body609_6 body609_46

def body609_48 : Prog (BitVec 64) :=
.seq body609_5 body609_47

def body609_49 : Prog (BitVec 64) :=
.seq body609_4 body609_48

def body609_50 : Prog (BitVec 64) :=
.seq body609_3 body609_49

def body609_51 : Prog (BitVec 64) :=
.seq body609_2 body609_50

def body609_52 : Prog (BitVec 64) :=
.seq body609_2 body609_3

def body609_53 : Prog (BitVec 64) :=
.seq body609_52 body609_4

def body609_54 : Prog (BitVec 64) :=
.seq body609_53 body609_5

def body609_55 : Prog (BitVec 64) :=
.seq body609_54 body609_6

def body609_56 : Prog (BitVec 64) :=
.seq body609_55 body609_7

def body609_57 : Prog (BitVec 64) :=
.seq body609_56 body609_8

def body609_58 : Prog (BitVec 64) :=
.seq body609_57 body609_9

def body609_59 : Prog (BitVec 64) :=
.seq body609_58 body609_10

def body609_60 : Prog (BitVec 64) :=
.seq body609_59 body609_11

def body609_61 : Prog (BitVec 64) :=
.seq body609_60 body609_12

def body609_62 : Prog (BitVec 64) :=
.seq body609_61 body609_13

def body609_63 : Prog (BitVec 64) :=
.seq body609_62 body609_14

def body609_64 : Prog (BitVec 64) :=
.seq body609_63 body609_15

def body609_65 : Prog (BitVec 64) :=
.seq body609_64 body609_16

def body609_66 : Prog (BitVec 64) :=
.seq body609_65 body609_17

def body609_67 : Prog (BitVec 64) :=
.seq body609_66 body609_18

def body609_68 : Prog (BitVec 64) :=
.seq body609_67 body609_19

def body609_69 : Prog (BitVec 64) :=
.seq body609_68 body609_20

def body609_70 : Prog (BitVec 64) :=
.seq body609_69 body609_21

def body609_71 : Prog (BitVec 64) :=
.seq body609_70 body609_22

def body609_72 : Prog (BitVec 64) :=
.seq body609_71 body609_23

def body609_73 : Prog (BitVec 64) :=
.seq body609_72 body609_24

def body609_74 : Prog (BitVec 64) :=
.seq body609_73 body609_25

def body609_75 : Prog (BitVec 64) :=
.seq body609_74 body609_26

def body609_76 : Prog (BitVec 64) :=
.seq body609_75 body609_0

def originalData609 : Decl (BitVec 64) :=
.function { name := "ripemd160_init", inline := false, exported := false, params := [], body := body609_51, returnShape := (Flapjack.Shape.one) }
def simplifiedData609 : Decl (BitVec 64) :=
.function { name := "ripemd160_init", inline := false, exported := false, params := [], body := body609_76, returnShape := (Flapjack.Shape.one) }
def original609 := Pancake.PanLang.declToHOL originalData609
def simplified609 := Pancake.PanLang.declToHOL simplifiedData609
end InitECandidate.Proofs.FrontendStages.Declarations
