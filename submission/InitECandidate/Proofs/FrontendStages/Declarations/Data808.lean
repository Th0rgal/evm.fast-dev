import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify792
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body808_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body808_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body808_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.global "bls_discount")
  (Flapjack.Exp.const 0#64)) body808_0 body808_1

def body808_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bls_lib_init" []

def body808_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "bls_discount"), none)) "alloc"
  [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 256#64, Flapjack.Exp.const 8#64]]

def body808_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.const 1000#64)

def body808_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.const 949#64)

def body808_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.const 848#64)

def body808_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.const 797#64)

def body808_9 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.const 764#64)

def body808_10 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.const 750#64)

def body808_11 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.const 738#64)

def body808_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.const 728#64)

def body808_13 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.const 719#64)

def body808_14 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 72#64])
  (Flapjack.Exp.const 712#64)

def body808_15 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 80#64])
  (Flapjack.Exp.const 705#64)

def body808_16 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 88#64])
  (Flapjack.Exp.const 698#64)

def body808_17 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.const 692#64)

def body808_18 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 104#64])
  (Flapjack.Exp.const 687#64)

def body808_19 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 112#64])
  (Flapjack.Exp.const 682#64)

def body808_20 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.const 677#64)

def body808_21 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 128#64])
  (Flapjack.Exp.const 673#64)

def body808_22 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 136#64])
  (Flapjack.Exp.const 669#64)

def body808_23 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 144#64])
  (Flapjack.Exp.const 665#64)

def body808_24 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 152#64])
  (Flapjack.Exp.const 661#64)

def body808_25 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 160#64])
  (Flapjack.Exp.const 658#64)

def body808_26 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 168#64])
  (Flapjack.Exp.const 654#64)

def body808_27 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 176#64])
  (Flapjack.Exp.const 651#64)

def body808_28 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 184#64])
  (Flapjack.Exp.const 648#64)

def body808_29 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 192#64])
  (Flapjack.Exp.const 645#64)

def body808_30 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 200#64])
  (Flapjack.Exp.const 642#64)

def body808_31 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 208#64])
  (Flapjack.Exp.const 640#64)

def body808_32 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 216#64])
  (Flapjack.Exp.const 637#64)

def body808_33 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 224#64])
  (Flapjack.Exp.const 635#64)

def body808_34 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 232#64])
  (Flapjack.Exp.const 632#64)

def body808_35 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 240#64])
  (Flapjack.Exp.const 630#64)

def body808_36 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 248#64])
  (Flapjack.Exp.const 627#64)

def body808_37 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 256#64])
  (Flapjack.Exp.const 625#64)

def body808_38 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 264#64])
  (Flapjack.Exp.const 623#64)

def body808_39 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 272#64])
  (Flapjack.Exp.const 621#64)

def body808_40 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 280#64])
  (Flapjack.Exp.const 619#64)

def body808_41 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 288#64])
  (Flapjack.Exp.const 617#64)

def body808_42 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 296#64])
  (Flapjack.Exp.const 615#64)

def body808_43 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 304#64])
  (Flapjack.Exp.const 613#64)

def body808_44 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 312#64])
  (Flapjack.Exp.const 611#64)

def body808_45 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 320#64])
  (Flapjack.Exp.const 609#64)

def body808_46 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 328#64])
  (Flapjack.Exp.const 608#64)

def body808_47 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 336#64])
  (Flapjack.Exp.const 606#64)

def body808_48 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 344#64])
  (Flapjack.Exp.const 604#64)

def body808_49 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 352#64])
  (Flapjack.Exp.const 603#64)

def body808_50 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 360#64])
  (Flapjack.Exp.const 601#64)

def body808_51 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 368#64])
  (Flapjack.Exp.const 599#64)

def body808_52 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 376#64])
  (Flapjack.Exp.const 598#64)

def body808_53 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 384#64])
  (Flapjack.Exp.const 596#64)

def body808_54 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 392#64])
  (Flapjack.Exp.const 595#64)

def body808_55 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 400#64])
  (Flapjack.Exp.const 593#64)

def body808_56 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 408#64])
  (Flapjack.Exp.const 592#64)

def body808_57 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 416#64])
  (Flapjack.Exp.const 591#64)

def body808_58 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 424#64])
  (Flapjack.Exp.const 589#64)

def body808_59 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 432#64])
  (Flapjack.Exp.const 588#64)

def body808_60 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 440#64])
  (Flapjack.Exp.const 586#64)

def body808_61 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 448#64])
  (Flapjack.Exp.const 585#64)

def body808_62 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 456#64])
  (Flapjack.Exp.const 584#64)

def body808_63 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 464#64])
  (Flapjack.Exp.const 582#64)

def body808_64 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 472#64])
  (Flapjack.Exp.const 581#64)

def body808_65 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 480#64])
  (Flapjack.Exp.const 580#64)

def body808_66 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 488#64])
  (Flapjack.Exp.const 579#64)

def body808_67 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 496#64])
  (Flapjack.Exp.const 577#64)

def body808_68 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 504#64])
  (Flapjack.Exp.const 576#64)

def body808_69 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 512#64])
  (Flapjack.Exp.const 575#64)

def body808_70 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 520#64])
  (Flapjack.Exp.const 574#64)

def body808_71 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 528#64])
  (Flapjack.Exp.const 573#64)

def body808_72 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 536#64])
  (Flapjack.Exp.const 572#64)

def body808_73 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 544#64])
  (Flapjack.Exp.const 570#64)

def body808_74 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 552#64])
  (Flapjack.Exp.const 569#64)

def body808_75 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 560#64])
  (Flapjack.Exp.const 568#64)

def body808_76 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 568#64])
  (Flapjack.Exp.const 567#64)

def body808_77 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 576#64])
  (Flapjack.Exp.const 566#64)

def body808_78 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 584#64])
  (Flapjack.Exp.const 565#64)

def body808_79 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 592#64])
  (Flapjack.Exp.const 564#64)

def body808_80 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 600#64])
  (Flapjack.Exp.const 563#64)

def body808_81 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 608#64])
  (Flapjack.Exp.const 562#64)

def body808_82 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 616#64])
  (Flapjack.Exp.const 561#64)

def body808_83 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 624#64])
  (Flapjack.Exp.const 560#64)

def body808_84 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 632#64])
  (Flapjack.Exp.const 559#64)

def body808_85 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 640#64])
  (Flapjack.Exp.const 558#64)

def body808_86 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 648#64])
  (Flapjack.Exp.const 557#64)

def body808_87 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 656#64])
  (Flapjack.Exp.const 556#64)

def body808_88 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 664#64])
  (Flapjack.Exp.const 555#64)

def body808_89 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 672#64])
  (Flapjack.Exp.const 554#64)

def body808_90 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 680#64])
  (Flapjack.Exp.const 553#64)

def body808_91 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 688#64])
  (Flapjack.Exp.const 552#64)

def body808_92 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 696#64])
  (Flapjack.Exp.const 551#64)

def body808_93 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 704#64])
  (Flapjack.Exp.const 550#64)

def body808_94 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 712#64])
  (Flapjack.Exp.const 549#64)

def body808_95 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 720#64])
  (Flapjack.Exp.const 548#64)

def body808_96 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 728#64])
  (Flapjack.Exp.const 547#64)

def body808_97 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 736#64])
  (Flapjack.Exp.const 547#64)

def body808_98 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 744#64])
  (Flapjack.Exp.const 546#64)

def body808_99 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 752#64])
  (Flapjack.Exp.const 545#64)

def body808_100 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 760#64])
  (Flapjack.Exp.const 544#64)

def body808_101 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 768#64])
  (Flapjack.Exp.const 543#64)

def body808_102 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 776#64])
  (Flapjack.Exp.const 542#64)

def body808_103 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 784#64])
  (Flapjack.Exp.const 541#64)

def body808_104 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 792#64])
  (Flapjack.Exp.const 540#64)

def body808_105 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 800#64])
  (Flapjack.Exp.const 540#64)

def body808_106 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 808#64])
  (Flapjack.Exp.const 539#64)

def body808_107 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 816#64])
  (Flapjack.Exp.const 538#64)

def body808_108 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 824#64])
  (Flapjack.Exp.const 537#64)

def body808_109 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 832#64])
  (Flapjack.Exp.const 536#64)

def body808_110 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 840#64])
  (Flapjack.Exp.const 536#64)

def body808_111 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 848#64])
  (Flapjack.Exp.const 535#64)

def body808_112 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 856#64])
  (Flapjack.Exp.const 534#64)

def body808_113 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 864#64])
  (Flapjack.Exp.const 533#64)

def body808_114 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 872#64])
  (Flapjack.Exp.const 532#64)

def body808_115 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 880#64])
  (Flapjack.Exp.const 532#64)

def body808_116 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 888#64])
  (Flapjack.Exp.const 531#64)

def body808_117 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 896#64])
  (Flapjack.Exp.const 530#64)

def body808_118 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 904#64])
  (Flapjack.Exp.const 529#64)

def body808_119 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 912#64])
  (Flapjack.Exp.const 528#64)

def body808_120 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 920#64])
  (Flapjack.Exp.const 528#64)

def body808_121 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 928#64])
  (Flapjack.Exp.const 527#64)

def body808_122 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 936#64])
  (Flapjack.Exp.const 526#64)

def body808_123 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 944#64])
  (Flapjack.Exp.const 525#64)

def body808_124 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 952#64])
  (Flapjack.Exp.const 525#64)

def body808_125 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 960#64])
  (Flapjack.Exp.const 524#64)

def body808_126 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 968#64])
  (Flapjack.Exp.const 523#64)

def body808_127 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 976#64])
  (Flapjack.Exp.const 522#64)

def body808_128 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 984#64])
  (Flapjack.Exp.const 522#64)

def body808_129 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 992#64])
  (Flapjack.Exp.const 521#64)

def body808_130 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1000#64])
  (Flapjack.Exp.const 520#64)

def body808_131 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1008#64])
  (Flapjack.Exp.const 520#64)

def body808_132 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1016#64])
  (Flapjack.Exp.const 519#64)

def body808_133 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1024#64])
  (Flapjack.Exp.const 1000#64)

def body808_134 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1032#64])
  (Flapjack.Exp.const 1000#64)

def body808_135 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1040#64])
  (Flapjack.Exp.const 923#64)

def body808_136 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1048#64])
  (Flapjack.Exp.const 884#64)

def body808_137 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1056#64])
  (Flapjack.Exp.const 855#64)

def body808_138 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1064#64])
  (Flapjack.Exp.const 832#64)

def body808_139 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1072#64])
  (Flapjack.Exp.const 812#64)

def body808_140 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1080#64])
  (Flapjack.Exp.const 796#64)

def body808_141 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1088#64])
  (Flapjack.Exp.const 782#64)

def body808_142 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1096#64])
  (Flapjack.Exp.const 770#64)

def body808_143 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1104#64])
  (Flapjack.Exp.const 759#64)

def body808_144 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1112#64])
  (Flapjack.Exp.const 749#64)

def body808_145 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1120#64])
  (Flapjack.Exp.const 740#64)

def body808_146 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1128#64])
  (Flapjack.Exp.const 732#64)

def body808_147 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1136#64])
  (Flapjack.Exp.const 724#64)

def body808_148 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1144#64])
  (Flapjack.Exp.const 717#64)

def body808_149 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1152#64])
  (Flapjack.Exp.const 711#64)

def body808_150 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1160#64])
  (Flapjack.Exp.const 704#64)

def body808_151 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1168#64])
  (Flapjack.Exp.const 699#64)

def body808_152 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1176#64])
  (Flapjack.Exp.const 693#64)

def body808_153 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1184#64])
  (Flapjack.Exp.const 688#64)

def body808_154 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1192#64])
  (Flapjack.Exp.const 683#64)

def body808_155 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1200#64])
  (Flapjack.Exp.const 679#64)

def body808_156 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1208#64])
  (Flapjack.Exp.const 674#64)

def body808_157 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1216#64])
  (Flapjack.Exp.const 670#64)

def body808_158 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1224#64])
  (Flapjack.Exp.const 666#64)

def body808_159 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1232#64])
  (Flapjack.Exp.const 663#64)

def body808_160 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1240#64])
  (Flapjack.Exp.const 659#64)

def body808_161 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1248#64])
  (Flapjack.Exp.const 655#64)

def body808_162 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1256#64])
  (Flapjack.Exp.const 652#64)

def body808_163 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1264#64])
  (Flapjack.Exp.const 649#64)

def body808_164 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1272#64])
  (Flapjack.Exp.const 646#64)

def body808_165 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1280#64])
  (Flapjack.Exp.const 643#64)

def body808_166 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1288#64])
  (Flapjack.Exp.const 640#64)

def body808_167 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1296#64])
  (Flapjack.Exp.const 637#64)

def body808_168 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1304#64])
  (Flapjack.Exp.const 634#64)

def body808_169 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1312#64])
  (Flapjack.Exp.const 632#64)

def body808_170 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1320#64])
  (Flapjack.Exp.const 629#64)

def body808_171 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1328#64])
  (Flapjack.Exp.const 627#64)

def body808_172 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1336#64])
  (Flapjack.Exp.const 624#64)

def body808_173 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1344#64])
  (Flapjack.Exp.const 622#64)

def body808_174 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1352#64])
  (Flapjack.Exp.const 620#64)

def body808_175 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1360#64])
  (Flapjack.Exp.const 618#64)

def body808_176 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1368#64])
  (Flapjack.Exp.const 615#64)

def body808_177 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1376#64])
  (Flapjack.Exp.const 613#64)

def body808_178 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1384#64])
  (Flapjack.Exp.const 611#64)

def body808_179 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1392#64])
  (Flapjack.Exp.const 609#64)

def body808_180 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1400#64])
  (Flapjack.Exp.const 607#64)

def body808_181 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1408#64])
  (Flapjack.Exp.const 606#64)

def body808_182 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1416#64])
  (Flapjack.Exp.const 604#64)

def body808_183 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1424#64])
  (Flapjack.Exp.const 602#64)

def body808_184 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1432#64])
  (Flapjack.Exp.const 600#64)

def body808_185 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1440#64])
  (Flapjack.Exp.const 598#64)

def body808_186 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1448#64])
  (Flapjack.Exp.const 597#64)

def body808_187 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1456#64])
  (Flapjack.Exp.const 595#64)

def body808_188 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1464#64])
  (Flapjack.Exp.const 593#64)

def body808_189 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1472#64])
  (Flapjack.Exp.const 592#64)

def body808_190 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1480#64])
  (Flapjack.Exp.const 590#64)

def body808_191 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1488#64])
  (Flapjack.Exp.const 589#64)

def body808_192 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1496#64])
  (Flapjack.Exp.const 587#64)

def body808_193 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1504#64])
  (Flapjack.Exp.const 586#64)

def body808_194 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1512#64])
  (Flapjack.Exp.const 584#64)

def body808_195 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1520#64])
  (Flapjack.Exp.const 583#64)

def body808_196 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1528#64])
  (Flapjack.Exp.const 582#64)

def body808_197 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1536#64])
  (Flapjack.Exp.const 580#64)

def body808_198 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1544#64])
  (Flapjack.Exp.const 579#64)

def body808_199 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1552#64])
  (Flapjack.Exp.const 578#64)

def body808_200 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1560#64])
  (Flapjack.Exp.const 576#64)

def body808_201 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1568#64])
  (Flapjack.Exp.const 575#64)

def body808_202 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1576#64])
  (Flapjack.Exp.const 574#64)

def body808_203 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1584#64])
  (Flapjack.Exp.const 573#64)

def body808_204 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1592#64])
  (Flapjack.Exp.const 571#64)

def body808_205 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1600#64])
  (Flapjack.Exp.const 570#64)

def body808_206 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1608#64])
  (Flapjack.Exp.const 569#64)

def body808_207 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1616#64])
  (Flapjack.Exp.const 568#64)

def body808_208 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1624#64])
  (Flapjack.Exp.const 567#64)

def body808_209 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1632#64])
  (Flapjack.Exp.const 566#64)

def body808_210 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1640#64])
  (Flapjack.Exp.const 565#64)

def body808_211 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1648#64])
  (Flapjack.Exp.const 563#64)

def body808_212 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1656#64])
  (Flapjack.Exp.const 562#64)

def body808_213 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1664#64])
  (Flapjack.Exp.const 561#64)

def body808_214 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1672#64])
  (Flapjack.Exp.const 560#64)

def body808_215 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1680#64])
  (Flapjack.Exp.const 559#64)

def body808_216 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1688#64])
  (Flapjack.Exp.const 558#64)

def body808_217 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1696#64])
  (Flapjack.Exp.const 557#64)

def body808_218 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1704#64])
  (Flapjack.Exp.const 556#64)

def body808_219 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1712#64])
  (Flapjack.Exp.const 555#64)

def body808_220 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1720#64])
  (Flapjack.Exp.const 554#64)

def body808_221 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1728#64])
  (Flapjack.Exp.const 553#64)

def body808_222 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1736#64])
  (Flapjack.Exp.const 552#64)

def body808_223 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1744#64])
  (Flapjack.Exp.const 552#64)

def body808_224 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1752#64])
  (Flapjack.Exp.const 551#64)

def body808_225 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1760#64])
  (Flapjack.Exp.const 550#64)

def body808_226 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1768#64])
  (Flapjack.Exp.const 549#64)

def body808_227 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1776#64])
  (Flapjack.Exp.const 548#64)

def body808_228 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1784#64])
  (Flapjack.Exp.const 547#64)

def body808_229 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1792#64])
  (Flapjack.Exp.const 546#64)

def body808_230 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1800#64])
  (Flapjack.Exp.const 545#64)

def body808_231 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1808#64])
  (Flapjack.Exp.const 545#64)

def body808_232 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1816#64])
  (Flapjack.Exp.const 544#64)

def body808_233 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1824#64])
  (Flapjack.Exp.const 543#64)

def body808_234 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1832#64])
  (Flapjack.Exp.const 542#64)

def body808_235 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1840#64])
  (Flapjack.Exp.const 541#64)

def body808_236 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1848#64])
  (Flapjack.Exp.const 541#64)

def body808_237 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1856#64])
  (Flapjack.Exp.const 540#64)

def body808_238 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1864#64])
  (Flapjack.Exp.const 539#64)

def body808_239 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1872#64])
  (Flapjack.Exp.const 538#64)

def body808_240 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1880#64])
  (Flapjack.Exp.const 537#64)

def body808_241 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1888#64])
  (Flapjack.Exp.const 537#64)

def body808_242 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1896#64])
  (Flapjack.Exp.const 536#64)

def body808_243 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1904#64])
  (Flapjack.Exp.const 535#64)

def body808_244 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1912#64])
  (Flapjack.Exp.const 535#64)

def body808_245 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1920#64])
  (Flapjack.Exp.const 534#64)

def body808_246 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1928#64])
  (Flapjack.Exp.const 533#64)

def body808_247 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1936#64])
  (Flapjack.Exp.const 532#64)

def body808_248 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1944#64])
  (Flapjack.Exp.const 532#64)

def body808_249 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1952#64])
  (Flapjack.Exp.const 531#64)

def body808_250 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1960#64])
  (Flapjack.Exp.const 530#64)

def body808_251 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1968#64])
  (Flapjack.Exp.const 530#64)

def body808_252 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1976#64])
  (Flapjack.Exp.const 529#64)

def body808_253 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1984#64])
  (Flapjack.Exp.const 528#64)

def body808_254 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 1992#64])
  (Flapjack.Exp.const 528#64)

def body808_255 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 2000#64])
  (Flapjack.Exp.const 527#64)

def body808_256 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 2008#64])
  (Flapjack.Exp.const 526#64)

def body808_257 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 2016#64])
  (Flapjack.Exp.const 526#64)

def body808_258 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 2024#64])
  (Flapjack.Exp.const 525#64)

def body808_259 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 2032#64])
  (Flapjack.Exp.const 524#64)

def body808_260 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "bls_discount", Flapjack.Exp.const 2040#64])
  (Flapjack.Exp.const 524#64)

def body808_261 : Prog (BitVec 64) :=
.seq body808_260 body808_0

def body808_262 : Prog (BitVec 64) :=
.seq body808_259 body808_261

def body808_263 : Prog (BitVec 64) :=
.seq body808_258 body808_262

def body808_264 : Prog (BitVec 64) :=
.seq body808_257 body808_263

def body808_265 : Prog (BitVec 64) :=
.seq body808_256 body808_264

def body808_266 : Prog (BitVec 64) :=
.seq body808_255 body808_265

def body808_267 : Prog (BitVec 64) :=
.seq body808_254 body808_266

def body808_268 : Prog (BitVec 64) :=
.seq body808_253 body808_267

def body808_269 : Prog (BitVec 64) :=
.seq body808_252 body808_268

def body808_270 : Prog (BitVec 64) :=
.seq body808_251 body808_269

def body808_271 : Prog (BitVec 64) :=
.seq body808_250 body808_270

def body808_272 : Prog (BitVec 64) :=
.seq body808_249 body808_271

def body808_273 : Prog (BitVec 64) :=
.seq body808_248 body808_272

def body808_274 : Prog (BitVec 64) :=
.seq body808_247 body808_273

def body808_275 : Prog (BitVec 64) :=
.seq body808_246 body808_274

def body808_276 : Prog (BitVec 64) :=
.seq body808_245 body808_275

def body808_277 : Prog (BitVec 64) :=
.seq body808_244 body808_276

def body808_278 : Prog (BitVec 64) :=
.seq body808_243 body808_277

def body808_279 : Prog (BitVec 64) :=
.seq body808_242 body808_278

def body808_280 : Prog (BitVec 64) :=
.seq body808_241 body808_279

def body808_281 : Prog (BitVec 64) :=
.seq body808_240 body808_280

def body808_282 : Prog (BitVec 64) :=
.seq body808_239 body808_281

def body808_283 : Prog (BitVec 64) :=
.seq body808_238 body808_282

def body808_284 : Prog (BitVec 64) :=
.seq body808_237 body808_283

def body808_285 : Prog (BitVec 64) :=
.seq body808_236 body808_284

def body808_286 : Prog (BitVec 64) :=
.seq body808_235 body808_285

def body808_287 : Prog (BitVec 64) :=
.seq body808_234 body808_286

def body808_288 : Prog (BitVec 64) :=
.seq body808_233 body808_287

def body808_289 : Prog (BitVec 64) :=
.seq body808_232 body808_288

def body808_290 : Prog (BitVec 64) :=
.seq body808_231 body808_289

def body808_291 : Prog (BitVec 64) :=
.seq body808_230 body808_290

def body808_292 : Prog (BitVec 64) :=
.seq body808_229 body808_291

def body808_293 : Prog (BitVec 64) :=
.seq body808_228 body808_292

def body808_294 : Prog (BitVec 64) :=
.seq body808_227 body808_293

def body808_295 : Prog (BitVec 64) :=
.seq body808_226 body808_294

def body808_296 : Prog (BitVec 64) :=
.seq body808_225 body808_295

def body808_297 : Prog (BitVec 64) :=
.seq body808_224 body808_296

def body808_298 : Prog (BitVec 64) :=
.seq body808_223 body808_297

def body808_299 : Prog (BitVec 64) :=
.seq body808_222 body808_298

def body808_300 : Prog (BitVec 64) :=
.seq body808_221 body808_299

def body808_301 : Prog (BitVec 64) :=
.seq body808_220 body808_300

def body808_302 : Prog (BitVec 64) :=
.seq body808_219 body808_301

def body808_303 : Prog (BitVec 64) :=
.seq body808_218 body808_302

def body808_304 : Prog (BitVec 64) :=
.seq body808_217 body808_303

def body808_305 : Prog (BitVec 64) :=
.seq body808_216 body808_304

def body808_306 : Prog (BitVec 64) :=
.seq body808_215 body808_305

def body808_307 : Prog (BitVec 64) :=
.seq body808_214 body808_306

def body808_308 : Prog (BitVec 64) :=
.seq body808_213 body808_307

def body808_309 : Prog (BitVec 64) :=
.seq body808_212 body808_308

def body808_310 : Prog (BitVec 64) :=
.seq body808_211 body808_309

def body808_311 : Prog (BitVec 64) :=
.seq body808_210 body808_310

def body808_312 : Prog (BitVec 64) :=
.seq body808_209 body808_311

def body808_313 : Prog (BitVec 64) :=
.seq body808_208 body808_312

def body808_314 : Prog (BitVec 64) :=
.seq body808_207 body808_313

def body808_315 : Prog (BitVec 64) :=
.seq body808_206 body808_314

def body808_316 : Prog (BitVec 64) :=
.seq body808_205 body808_315

def body808_317 : Prog (BitVec 64) :=
.seq body808_204 body808_316

def body808_318 : Prog (BitVec 64) :=
.seq body808_203 body808_317

def body808_319 : Prog (BitVec 64) :=
.seq body808_202 body808_318

def body808_320 : Prog (BitVec 64) :=
.seq body808_201 body808_319

def body808_321 : Prog (BitVec 64) :=
.seq body808_200 body808_320

def body808_322 : Prog (BitVec 64) :=
.seq body808_199 body808_321

def body808_323 : Prog (BitVec 64) :=
.seq body808_198 body808_322

def body808_324 : Prog (BitVec 64) :=
.seq body808_197 body808_323

def body808_325 : Prog (BitVec 64) :=
.seq body808_196 body808_324

def body808_326 : Prog (BitVec 64) :=
.seq body808_195 body808_325

def body808_327 : Prog (BitVec 64) :=
.seq body808_194 body808_326

def body808_328 : Prog (BitVec 64) :=
.seq body808_193 body808_327

def body808_329 : Prog (BitVec 64) :=
.seq body808_192 body808_328

def body808_330 : Prog (BitVec 64) :=
.seq body808_191 body808_329

def body808_331 : Prog (BitVec 64) :=
.seq body808_190 body808_330

def body808_332 : Prog (BitVec 64) :=
.seq body808_189 body808_331

def body808_333 : Prog (BitVec 64) :=
.seq body808_188 body808_332

def body808_334 : Prog (BitVec 64) :=
.seq body808_187 body808_333

def body808_335 : Prog (BitVec 64) :=
.seq body808_186 body808_334

def body808_336 : Prog (BitVec 64) :=
.seq body808_185 body808_335

def body808_337 : Prog (BitVec 64) :=
.seq body808_184 body808_336

def body808_338 : Prog (BitVec 64) :=
.seq body808_183 body808_337

def body808_339 : Prog (BitVec 64) :=
.seq body808_182 body808_338

def body808_340 : Prog (BitVec 64) :=
.seq body808_181 body808_339

def body808_341 : Prog (BitVec 64) :=
.seq body808_180 body808_340

def body808_342 : Prog (BitVec 64) :=
.seq body808_179 body808_341

def body808_343 : Prog (BitVec 64) :=
.seq body808_178 body808_342

def body808_344 : Prog (BitVec 64) :=
.seq body808_177 body808_343

def body808_345 : Prog (BitVec 64) :=
.seq body808_176 body808_344

def body808_346 : Prog (BitVec 64) :=
.seq body808_175 body808_345

def body808_347 : Prog (BitVec 64) :=
.seq body808_174 body808_346

def body808_348 : Prog (BitVec 64) :=
.seq body808_173 body808_347

def body808_349 : Prog (BitVec 64) :=
.seq body808_172 body808_348

def body808_350 : Prog (BitVec 64) :=
.seq body808_171 body808_349

def body808_351 : Prog (BitVec 64) :=
.seq body808_170 body808_350

def body808_352 : Prog (BitVec 64) :=
.seq body808_169 body808_351

def body808_353 : Prog (BitVec 64) :=
.seq body808_168 body808_352

def body808_354 : Prog (BitVec 64) :=
.seq body808_167 body808_353

def body808_355 : Prog (BitVec 64) :=
.seq body808_166 body808_354

def body808_356 : Prog (BitVec 64) :=
.seq body808_165 body808_355

def body808_357 : Prog (BitVec 64) :=
.seq body808_164 body808_356

def body808_358 : Prog (BitVec 64) :=
.seq body808_163 body808_357

def body808_359 : Prog (BitVec 64) :=
.seq body808_162 body808_358

def body808_360 : Prog (BitVec 64) :=
.seq body808_161 body808_359

def body808_361 : Prog (BitVec 64) :=
.seq body808_160 body808_360

def body808_362 : Prog (BitVec 64) :=
.seq body808_159 body808_361

def body808_363 : Prog (BitVec 64) :=
.seq body808_158 body808_362

def body808_364 : Prog (BitVec 64) :=
.seq body808_157 body808_363

def body808_365 : Prog (BitVec 64) :=
.seq body808_156 body808_364

def body808_366 : Prog (BitVec 64) :=
.seq body808_155 body808_365

def body808_367 : Prog (BitVec 64) :=
.seq body808_154 body808_366

def body808_368 : Prog (BitVec 64) :=
.seq body808_153 body808_367

def body808_369 : Prog (BitVec 64) :=
.seq body808_152 body808_368

def body808_370 : Prog (BitVec 64) :=
.seq body808_151 body808_369

def body808_371 : Prog (BitVec 64) :=
.seq body808_150 body808_370

def body808_372 : Prog (BitVec 64) :=
.seq body808_149 body808_371

def body808_373 : Prog (BitVec 64) :=
.seq body808_148 body808_372

def body808_374 : Prog (BitVec 64) :=
.seq body808_147 body808_373

def body808_375 : Prog (BitVec 64) :=
.seq body808_146 body808_374

def body808_376 : Prog (BitVec 64) :=
.seq body808_145 body808_375

def body808_377 : Prog (BitVec 64) :=
.seq body808_144 body808_376

def body808_378 : Prog (BitVec 64) :=
.seq body808_143 body808_377

def body808_379 : Prog (BitVec 64) :=
.seq body808_142 body808_378

def body808_380 : Prog (BitVec 64) :=
.seq body808_141 body808_379

def body808_381 : Prog (BitVec 64) :=
.seq body808_140 body808_380

def body808_382 : Prog (BitVec 64) :=
.seq body808_139 body808_381

def body808_383 : Prog (BitVec 64) :=
.seq body808_138 body808_382

def body808_384 : Prog (BitVec 64) :=
.seq body808_137 body808_383

def body808_385 : Prog (BitVec 64) :=
.seq body808_136 body808_384

def body808_386 : Prog (BitVec 64) :=
.seq body808_135 body808_385

def body808_387 : Prog (BitVec 64) :=
.seq body808_134 body808_386

def body808_388 : Prog (BitVec 64) :=
.seq body808_133 body808_387

def body808_389 : Prog (BitVec 64) :=
.seq body808_132 body808_388

def body808_390 : Prog (BitVec 64) :=
.seq body808_131 body808_389

def body808_391 : Prog (BitVec 64) :=
.seq body808_130 body808_390

def body808_392 : Prog (BitVec 64) :=
.seq body808_129 body808_391

def body808_393 : Prog (BitVec 64) :=
.seq body808_128 body808_392

def body808_394 : Prog (BitVec 64) :=
.seq body808_127 body808_393

def body808_395 : Prog (BitVec 64) :=
.seq body808_126 body808_394

def body808_396 : Prog (BitVec 64) :=
.seq body808_125 body808_395

def body808_397 : Prog (BitVec 64) :=
.seq body808_124 body808_396

def body808_398 : Prog (BitVec 64) :=
.seq body808_123 body808_397

def body808_399 : Prog (BitVec 64) :=
.seq body808_122 body808_398

def body808_400 : Prog (BitVec 64) :=
.seq body808_121 body808_399

def body808_401 : Prog (BitVec 64) :=
.seq body808_120 body808_400

def body808_402 : Prog (BitVec 64) :=
.seq body808_119 body808_401

def body808_403 : Prog (BitVec 64) :=
.seq body808_118 body808_402

def body808_404 : Prog (BitVec 64) :=
.seq body808_117 body808_403

def body808_405 : Prog (BitVec 64) :=
.seq body808_116 body808_404

def body808_406 : Prog (BitVec 64) :=
.seq body808_115 body808_405

def body808_407 : Prog (BitVec 64) :=
.seq body808_114 body808_406

def body808_408 : Prog (BitVec 64) :=
.seq body808_113 body808_407

def body808_409 : Prog (BitVec 64) :=
.seq body808_112 body808_408

def body808_410 : Prog (BitVec 64) :=
.seq body808_111 body808_409

def body808_411 : Prog (BitVec 64) :=
.seq body808_110 body808_410

def body808_412 : Prog (BitVec 64) :=
.seq body808_109 body808_411

def body808_413 : Prog (BitVec 64) :=
.seq body808_108 body808_412

def body808_414 : Prog (BitVec 64) :=
.seq body808_107 body808_413

def body808_415 : Prog (BitVec 64) :=
.seq body808_106 body808_414

def body808_416 : Prog (BitVec 64) :=
.seq body808_105 body808_415

def body808_417 : Prog (BitVec 64) :=
.seq body808_104 body808_416

def body808_418 : Prog (BitVec 64) :=
.seq body808_103 body808_417

def body808_419 : Prog (BitVec 64) :=
.seq body808_102 body808_418

def body808_420 : Prog (BitVec 64) :=
.seq body808_101 body808_419

def body808_421 : Prog (BitVec 64) :=
.seq body808_100 body808_420

def body808_422 : Prog (BitVec 64) :=
.seq body808_99 body808_421

def body808_423 : Prog (BitVec 64) :=
.seq body808_98 body808_422

def body808_424 : Prog (BitVec 64) :=
.seq body808_97 body808_423

def body808_425 : Prog (BitVec 64) :=
.seq body808_96 body808_424

def body808_426 : Prog (BitVec 64) :=
.seq body808_95 body808_425

def body808_427 : Prog (BitVec 64) :=
.seq body808_94 body808_426

def body808_428 : Prog (BitVec 64) :=
.seq body808_93 body808_427

def body808_429 : Prog (BitVec 64) :=
.seq body808_92 body808_428

def body808_430 : Prog (BitVec 64) :=
.seq body808_91 body808_429

def body808_431 : Prog (BitVec 64) :=
.seq body808_90 body808_430

def body808_432 : Prog (BitVec 64) :=
.seq body808_89 body808_431

def body808_433 : Prog (BitVec 64) :=
.seq body808_88 body808_432

def body808_434 : Prog (BitVec 64) :=
.seq body808_87 body808_433

def body808_435 : Prog (BitVec 64) :=
.seq body808_86 body808_434

def body808_436 : Prog (BitVec 64) :=
.seq body808_85 body808_435

def body808_437 : Prog (BitVec 64) :=
.seq body808_84 body808_436

def body808_438 : Prog (BitVec 64) :=
.seq body808_83 body808_437

def body808_439 : Prog (BitVec 64) :=
.seq body808_82 body808_438

def body808_440 : Prog (BitVec 64) :=
.seq body808_81 body808_439

def body808_441 : Prog (BitVec 64) :=
.seq body808_80 body808_440

def body808_442 : Prog (BitVec 64) :=
.seq body808_79 body808_441

def body808_443 : Prog (BitVec 64) :=
.seq body808_78 body808_442

def body808_444 : Prog (BitVec 64) :=
.seq body808_77 body808_443

def body808_445 : Prog (BitVec 64) :=
.seq body808_76 body808_444

def body808_446 : Prog (BitVec 64) :=
.seq body808_75 body808_445

def body808_447 : Prog (BitVec 64) :=
.seq body808_74 body808_446

def body808_448 : Prog (BitVec 64) :=
.seq body808_73 body808_447

def body808_449 : Prog (BitVec 64) :=
.seq body808_72 body808_448

def body808_450 : Prog (BitVec 64) :=
.seq body808_71 body808_449

def body808_451 : Prog (BitVec 64) :=
.seq body808_70 body808_450

def body808_452 : Prog (BitVec 64) :=
.seq body808_69 body808_451

def body808_453 : Prog (BitVec 64) :=
.seq body808_68 body808_452

def body808_454 : Prog (BitVec 64) :=
.seq body808_67 body808_453

def body808_455 : Prog (BitVec 64) :=
.seq body808_66 body808_454

def body808_456 : Prog (BitVec 64) :=
.seq body808_65 body808_455

def body808_457 : Prog (BitVec 64) :=
.seq body808_64 body808_456

def body808_458 : Prog (BitVec 64) :=
.seq body808_63 body808_457

def body808_459 : Prog (BitVec 64) :=
.seq body808_62 body808_458

def body808_460 : Prog (BitVec 64) :=
.seq body808_61 body808_459

def body808_461 : Prog (BitVec 64) :=
.seq body808_60 body808_460

def body808_462 : Prog (BitVec 64) :=
.seq body808_59 body808_461

def body808_463 : Prog (BitVec 64) :=
.seq body808_58 body808_462

def body808_464 : Prog (BitVec 64) :=
.seq body808_57 body808_463

def body808_465 : Prog (BitVec 64) :=
.seq body808_56 body808_464

def body808_466 : Prog (BitVec 64) :=
.seq body808_55 body808_465

def body808_467 : Prog (BitVec 64) :=
.seq body808_54 body808_466

def body808_468 : Prog (BitVec 64) :=
.seq body808_53 body808_467

def body808_469 : Prog (BitVec 64) :=
.seq body808_52 body808_468

def body808_470 : Prog (BitVec 64) :=
.seq body808_51 body808_469

def body808_471 : Prog (BitVec 64) :=
.seq body808_50 body808_470

def body808_472 : Prog (BitVec 64) :=
.seq body808_49 body808_471

def body808_473 : Prog (BitVec 64) :=
.seq body808_48 body808_472

def body808_474 : Prog (BitVec 64) :=
.seq body808_47 body808_473

def body808_475 : Prog (BitVec 64) :=
.seq body808_46 body808_474

def body808_476 : Prog (BitVec 64) :=
.seq body808_45 body808_475

def body808_477 : Prog (BitVec 64) :=
.seq body808_44 body808_476

def body808_478 : Prog (BitVec 64) :=
.seq body808_43 body808_477

def body808_479 : Prog (BitVec 64) :=
.seq body808_42 body808_478

def body808_480 : Prog (BitVec 64) :=
.seq body808_41 body808_479

def body808_481 : Prog (BitVec 64) :=
.seq body808_40 body808_480

def body808_482 : Prog (BitVec 64) :=
.seq body808_39 body808_481

def body808_483 : Prog (BitVec 64) :=
.seq body808_38 body808_482

def body808_484 : Prog (BitVec 64) :=
.seq body808_37 body808_483

def body808_485 : Prog (BitVec 64) :=
.seq body808_36 body808_484

def body808_486 : Prog (BitVec 64) :=
.seq body808_35 body808_485

def body808_487 : Prog (BitVec 64) :=
.seq body808_34 body808_486

def body808_488 : Prog (BitVec 64) :=
.seq body808_33 body808_487

def body808_489 : Prog (BitVec 64) :=
.seq body808_32 body808_488

def body808_490 : Prog (BitVec 64) :=
.seq body808_31 body808_489

def body808_491 : Prog (BitVec 64) :=
.seq body808_30 body808_490

def body808_492 : Prog (BitVec 64) :=
.seq body808_29 body808_491

def body808_493 : Prog (BitVec 64) :=
.seq body808_28 body808_492

def body808_494 : Prog (BitVec 64) :=
.seq body808_27 body808_493

def body808_495 : Prog (BitVec 64) :=
.seq body808_26 body808_494

def body808_496 : Prog (BitVec 64) :=
.seq body808_25 body808_495

def body808_497 : Prog (BitVec 64) :=
.seq body808_24 body808_496

def body808_498 : Prog (BitVec 64) :=
.seq body808_23 body808_497

def body808_499 : Prog (BitVec 64) :=
.seq body808_22 body808_498

def body808_500 : Prog (BitVec 64) :=
.seq body808_21 body808_499

def body808_501 : Prog (BitVec 64) :=
.seq body808_20 body808_500

def body808_502 : Prog (BitVec 64) :=
.seq body808_19 body808_501

def body808_503 : Prog (BitVec 64) :=
.seq body808_18 body808_502

def body808_504 : Prog (BitVec 64) :=
.seq body808_17 body808_503

def body808_505 : Prog (BitVec 64) :=
.seq body808_16 body808_504

def body808_506 : Prog (BitVec 64) :=
.seq body808_15 body808_505

def body808_507 : Prog (BitVec 64) :=
.seq body808_14 body808_506

def body808_508 : Prog (BitVec 64) :=
.seq body808_13 body808_507

def body808_509 : Prog (BitVec 64) :=
.seq body808_12 body808_508

def body808_510 : Prog (BitVec 64) :=
.seq body808_11 body808_509

def body808_511 : Prog (BitVec 64) :=
.seq body808_10 body808_510

def body808_512 : Prog (BitVec 64) :=
.seq body808_9 body808_511

def body808_513 : Prog (BitVec 64) :=
.seq body808_8 body808_512

def body808_514 : Prog (BitVec 64) :=
.seq body808_7 body808_513

def body808_515 : Prog (BitVec 64) :=
.seq body808_6 body808_514

def body808_516 : Prog (BitVec 64) :=
.seq body808_5 body808_515

def body808_517 : Prog (BitVec 64) :=
.seq body808_4 body808_516

def body808_518 : Prog (BitVec 64) :=
.seq body808_3 body808_517

def body808_519 : Prog (BitVec 64) :=
.seq body808_2 body808_518

def body808_520 : Prog (BitVec 64) :=
.seq body808_2 body808_3

def body808_521 : Prog (BitVec 64) :=
.seq body808_520 body808_4

def body808_522 : Prog (BitVec 64) :=
.seq body808_521 body808_5

def body808_523 : Prog (BitVec 64) :=
.seq body808_522 body808_6

def body808_524 : Prog (BitVec 64) :=
.seq body808_523 body808_7

def body808_525 : Prog (BitVec 64) :=
.seq body808_524 body808_8

def body808_526 : Prog (BitVec 64) :=
.seq body808_525 body808_9

def body808_527 : Prog (BitVec 64) :=
.seq body808_526 body808_10

def body808_528 : Prog (BitVec 64) :=
.seq body808_527 body808_11

def body808_529 : Prog (BitVec 64) :=
.seq body808_528 body808_12

def body808_530 : Prog (BitVec 64) :=
.seq body808_529 body808_13

def body808_531 : Prog (BitVec 64) :=
.seq body808_530 body808_14

def body808_532 : Prog (BitVec 64) :=
.seq body808_531 body808_15

def body808_533 : Prog (BitVec 64) :=
.seq body808_532 body808_16

def body808_534 : Prog (BitVec 64) :=
.seq body808_533 body808_17

def body808_535 : Prog (BitVec 64) :=
.seq body808_534 body808_18

def body808_536 : Prog (BitVec 64) :=
.seq body808_535 body808_19

def body808_537 : Prog (BitVec 64) :=
.seq body808_536 body808_20

def body808_538 : Prog (BitVec 64) :=
.seq body808_537 body808_21

def body808_539 : Prog (BitVec 64) :=
.seq body808_538 body808_22

def body808_540 : Prog (BitVec 64) :=
.seq body808_539 body808_23

def body808_541 : Prog (BitVec 64) :=
.seq body808_540 body808_24

def body808_542 : Prog (BitVec 64) :=
.seq body808_541 body808_25

def body808_543 : Prog (BitVec 64) :=
.seq body808_542 body808_26

def body808_544 : Prog (BitVec 64) :=
.seq body808_543 body808_27

def body808_545 : Prog (BitVec 64) :=
.seq body808_544 body808_28

def body808_546 : Prog (BitVec 64) :=
.seq body808_545 body808_29

def body808_547 : Prog (BitVec 64) :=
.seq body808_546 body808_30

def body808_548 : Prog (BitVec 64) :=
.seq body808_547 body808_31

def body808_549 : Prog (BitVec 64) :=
.seq body808_548 body808_32

def body808_550 : Prog (BitVec 64) :=
.seq body808_549 body808_33

def body808_551 : Prog (BitVec 64) :=
.seq body808_550 body808_34

def body808_552 : Prog (BitVec 64) :=
.seq body808_551 body808_35

def body808_553 : Prog (BitVec 64) :=
.seq body808_552 body808_36

def body808_554 : Prog (BitVec 64) :=
.seq body808_553 body808_37

def body808_555 : Prog (BitVec 64) :=
.seq body808_554 body808_38

def body808_556 : Prog (BitVec 64) :=
.seq body808_555 body808_39

def body808_557 : Prog (BitVec 64) :=
.seq body808_556 body808_40

def body808_558 : Prog (BitVec 64) :=
.seq body808_557 body808_41

def body808_559 : Prog (BitVec 64) :=
.seq body808_558 body808_42

def body808_560 : Prog (BitVec 64) :=
.seq body808_559 body808_43

def body808_561 : Prog (BitVec 64) :=
.seq body808_560 body808_44

def body808_562 : Prog (BitVec 64) :=
.seq body808_561 body808_45

def body808_563 : Prog (BitVec 64) :=
.seq body808_562 body808_46

def body808_564 : Prog (BitVec 64) :=
.seq body808_563 body808_47

def body808_565 : Prog (BitVec 64) :=
.seq body808_564 body808_48

def body808_566 : Prog (BitVec 64) :=
.seq body808_565 body808_49

def body808_567 : Prog (BitVec 64) :=
.seq body808_566 body808_50

def body808_568 : Prog (BitVec 64) :=
.seq body808_567 body808_51

def body808_569 : Prog (BitVec 64) :=
.seq body808_568 body808_52

def body808_570 : Prog (BitVec 64) :=
.seq body808_569 body808_53

def body808_571 : Prog (BitVec 64) :=
.seq body808_570 body808_54

def body808_572 : Prog (BitVec 64) :=
.seq body808_571 body808_55

def body808_573 : Prog (BitVec 64) :=
.seq body808_572 body808_56

def body808_574 : Prog (BitVec 64) :=
.seq body808_573 body808_57

def body808_575 : Prog (BitVec 64) :=
.seq body808_574 body808_58

def body808_576 : Prog (BitVec 64) :=
.seq body808_575 body808_59

def body808_577 : Prog (BitVec 64) :=
.seq body808_576 body808_60

def body808_578 : Prog (BitVec 64) :=
.seq body808_577 body808_61

def body808_579 : Prog (BitVec 64) :=
.seq body808_578 body808_62

def body808_580 : Prog (BitVec 64) :=
.seq body808_579 body808_63

def body808_581 : Prog (BitVec 64) :=
.seq body808_580 body808_64

def body808_582 : Prog (BitVec 64) :=
.seq body808_581 body808_65

def body808_583 : Prog (BitVec 64) :=
.seq body808_582 body808_66

def body808_584 : Prog (BitVec 64) :=
.seq body808_583 body808_67

def body808_585 : Prog (BitVec 64) :=
.seq body808_584 body808_68

def body808_586 : Prog (BitVec 64) :=
.seq body808_585 body808_69

def body808_587 : Prog (BitVec 64) :=
.seq body808_586 body808_70

def body808_588 : Prog (BitVec 64) :=
.seq body808_587 body808_71

def body808_589 : Prog (BitVec 64) :=
.seq body808_588 body808_72

def body808_590 : Prog (BitVec 64) :=
.seq body808_589 body808_73

def body808_591 : Prog (BitVec 64) :=
.seq body808_590 body808_74

def body808_592 : Prog (BitVec 64) :=
.seq body808_591 body808_75

def body808_593 : Prog (BitVec 64) :=
.seq body808_592 body808_76

def body808_594 : Prog (BitVec 64) :=
.seq body808_593 body808_77

def body808_595 : Prog (BitVec 64) :=
.seq body808_594 body808_78

def body808_596 : Prog (BitVec 64) :=
.seq body808_595 body808_79

def body808_597 : Prog (BitVec 64) :=
.seq body808_596 body808_80

def body808_598 : Prog (BitVec 64) :=
.seq body808_597 body808_81

def body808_599 : Prog (BitVec 64) :=
.seq body808_598 body808_82

def body808_600 : Prog (BitVec 64) :=
.seq body808_599 body808_83

def body808_601 : Prog (BitVec 64) :=
.seq body808_600 body808_84

def body808_602 : Prog (BitVec 64) :=
.seq body808_601 body808_85

def body808_603 : Prog (BitVec 64) :=
.seq body808_602 body808_86

def body808_604 : Prog (BitVec 64) :=
.seq body808_603 body808_87

def body808_605 : Prog (BitVec 64) :=
.seq body808_604 body808_88

def body808_606 : Prog (BitVec 64) :=
.seq body808_605 body808_89

def body808_607 : Prog (BitVec 64) :=
.seq body808_606 body808_90

def body808_608 : Prog (BitVec 64) :=
.seq body808_607 body808_91

def body808_609 : Prog (BitVec 64) :=
.seq body808_608 body808_92

def body808_610 : Prog (BitVec 64) :=
.seq body808_609 body808_93

def body808_611 : Prog (BitVec 64) :=
.seq body808_610 body808_94

def body808_612 : Prog (BitVec 64) :=
.seq body808_611 body808_95

def body808_613 : Prog (BitVec 64) :=
.seq body808_612 body808_96

def body808_614 : Prog (BitVec 64) :=
.seq body808_613 body808_97

def body808_615 : Prog (BitVec 64) :=
.seq body808_614 body808_98

def body808_616 : Prog (BitVec 64) :=
.seq body808_615 body808_99

def body808_617 : Prog (BitVec 64) :=
.seq body808_616 body808_100

def body808_618 : Prog (BitVec 64) :=
.seq body808_617 body808_101

def body808_619 : Prog (BitVec 64) :=
.seq body808_618 body808_102

def body808_620 : Prog (BitVec 64) :=
.seq body808_619 body808_103

def body808_621 : Prog (BitVec 64) :=
.seq body808_620 body808_104

def body808_622 : Prog (BitVec 64) :=
.seq body808_621 body808_105

def body808_623 : Prog (BitVec 64) :=
.seq body808_622 body808_106

def body808_624 : Prog (BitVec 64) :=
.seq body808_623 body808_107

def body808_625 : Prog (BitVec 64) :=
.seq body808_624 body808_108

def body808_626 : Prog (BitVec 64) :=
.seq body808_625 body808_109

def body808_627 : Prog (BitVec 64) :=
.seq body808_626 body808_110

def body808_628 : Prog (BitVec 64) :=
.seq body808_627 body808_111

def body808_629 : Prog (BitVec 64) :=
.seq body808_628 body808_112

def body808_630 : Prog (BitVec 64) :=
.seq body808_629 body808_113

def body808_631 : Prog (BitVec 64) :=
.seq body808_630 body808_114

def body808_632 : Prog (BitVec 64) :=
.seq body808_631 body808_115

def body808_633 : Prog (BitVec 64) :=
.seq body808_632 body808_116

def body808_634 : Prog (BitVec 64) :=
.seq body808_633 body808_117

def body808_635 : Prog (BitVec 64) :=
.seq body808_634 body808_118

def body808_636 : Prog (BitVec 64) :=
.seq body808_635 body808_119

def body808_637 : Prog (BitVec 64) :=
.seq body808_636 body808_120

def body808_638 : Prog (BitVec 64) :=
.seq body808_637 body808_121

def body808_639 : Prog (BitVec 64) :=
.seq body808_638 body808_122

def body808_640 : Prog (BitVec 64) :=
.seq body808_639 body808_123

def body808_641 : Prog (BitVec 64) :=
.seq body808_640 body808_124

def body808_642 : Prog (BitVec 64) :=
.seq body808_641 body808_125

def body808_643 : Prog (BitVec 64) :=
.seq body808_642 body808_126

def body808_644 : Prog (BitVec 64) :=
.seq body808_643 body808_127

def body808_645 : Prog (BitVec 64) :=
.seq body808_644 body808_128

def body808_646 : Prog (BitVec 64) :=
.seq body808_645 body808_129

def body808_647 : Prog (BitVec 64) :=
.seq body808_646 body808_130

def body808_648 : Prog (BitVec 64) :=
.seq body808_647 body808_131

def body808_649 : Prog (BitVec 64) :=
.seq body808_648 body808_132

def body808_650 : Prog (BitVec 64) :=
.seq body808_649 body808_133

def body808_651 : Prog (BitVec 64) :=
.seq body808_650 body808_134

def body808_652 : Prog (BitVec 64) :=
.seq body808_651 body808_135

def body808_653 : Prog (BitVec 64) :=
.seq body808_652 body808_136

def body808_654 : Prog (BitVec 64) :=
.seq body808_653 body808_137

def body808_655 : Prog (BitVec 64) :=
.seq body808_654 body808_138

def body808_656 : Prog (BitVec 64) :=
.seq body808_655 body808_139

def body808_657 : Prog (BitVec 64) :=
.seq body808_656 body808_140

def body808_658 : Prog (BitVec 64) :=
.seq body808_657 body808_141

def body808_659 : Prog (BitVec 64) :=
.seq body808_658 body808_142

def body808_660 : Prog (BitVec 64) :=
.seq body808_659 body808_143

def body808_661 : Prog (BitVec 64) :=
.seq body808_660 body808_144

def body808_662 : Prog (BitVec 64) :=
.seq body808_661 body808_145

def body808_663 : Prog (BitVec 64) :=
.seq body808_662 body808_146

def body808_664 : Prog (BitVec 64) :=
.seq body808_663 body808_147

def body808_665 : Prog (BitVec 64) :=
.seq body808_664 body808_148

def body808_666 : Prog (BitVec 64) :=
.seq body808_665 body808_149

def body808_667 : Prog (BitVec 64) :=
.seq body808_666 body808_150

def body808_668 : Prog (BitVec 64) :=
.seq body808_667 body808_151

def body808_669 : Prog (BitVec 64) :=
.seq body808_668 body808_152

def body808_670 : Prog (BitVec 64) :=
.seq body808_669 body808_153

def body808_671 : Prog (BitVec 64) :=
.seq body808_670 body808_154

def body808_672 : Prog (BitVec 64) :=
.seq body808_671 body808_155

def body808_673 : Prog (BitVec 64) :=
.seq body808_672 body808_156

def body808_674 : Prog (BitVec 64) :=
.seq body808_673 body808_157

def body808_675 : Prog (BitVec 64) :=
.seq body808_674 body808_158

def body808_676 : Prog (BitVec 64) :=
.seq body808_675 body808_159

def body808_677 : Prog (BitVec 64) :=
.seq body808_676 body808_160

def body808_678 : Prog (BitVec 64) :=
.seq body808_677 body808_161

def body808_679 : Prog (BitVec 64) :=
.seq body808_678 body808_162

def body808_680 : Prog (BitVec 64) :=
.seq body808_679 body808_163

def body808_681 : Prog (BitVec 64) :=
.seq body808_680 body808_164

def body808_682 : Prog (BitVec 64) :=
.seq body808_681 body808_165

def body808_683 : Prog (BitVec 64) :=
.seq body808_682 body808_166

def body808_684 : Prog (BitVec 64) :=
.seq body808_683 body808_167

def body808_685 : Prog (BitVec 64) :=
.seq body808_684 body808_168

def body808_686 : Prog (BitVec 64) :=
.seq body808_685 body808_169

def body808_687 : Prog (BitVec 64) :=
.seq body808_686 body808_170

def body808_688 : Prog (BitVec 64) :=
.seq body808_687 body808_171

def body808_689 : Prog (BitVec 64) :=
.seq body808_688 body808_172

def body808_690 : Prog (BitVec 64) :=
.seq body808_689 body808_173

def body808_691 : Prog (BitVec 64) :=
.seq body808_690 body808_174

def body808_692 : Prog (BitVec 64) :=
.seq body808_691 body808_175

def body808_693 : Prog (BitVec 64) :=
.seq body808_692 body808_176

def body808_694 : Prog (BitVec 64) :=
.seq body808_693 body808_177

def body808_695 : Prog (BitVec 64) :=
.seq body808_694 body808_178

def body808_696 : Prog (BitVec 64) :=
.seq body808_695 body808_179

def body808_697 : Prog (BitVec 64) :=
.seq body808_696 body808_180

def body808_698 : Prog (BitVec 64) :=
.seq body808_697 body808_181

def body808_699 : Prog (BitVec 64) :=
.seq body808_698 body808_182

def body808_700 : Prog (BitVec 64) :=
.seq body808_699 body808_183

def body808_701 : Prog (BitVec 64) :=
.seq body808_700 body808_184

def body808_702 : Prog (BitVec 64) :=
.seq body808_701 body808_185

def body808_703 : Prog (BitVec 64) :=
.seq body808_702 body808_186

def body808_704 : Prog (BitVec 64) :=
.seq body808_703 body808_187

def body808_705 : Prog (BitVec 64) :=
.seq body808_704 body808_188

def body808_706 : Prog (BitVec 64) :=
.seq body808_705 body808_189

def body808_707 : Prog (BitVec 64) :=
.seq body808_706 body808_190

def body808_708 : Prog (BitVec 64) :=
.seq body808_707 body808_191

def body808_709 : Prog (BitVec 64) :=
.seq body808_708 body808_192

def body808_710 : Prog (BitVec 64) :=
.seq body808_709 body808_193

def body808_711 : Prog (BitVec 64) :=
.seq body808_710 body808_194

def body808_712 : Prog (BitVec 64) :=
.seq body808_711 body808_195

def body808_713 : Prog (BitVec 64) :=
.seq body808_712 body808_196

def body808_714 : Prog (BitVec 64) :=
.seq body808_713 body808_197

def body808_715 : Prog (BitVec 64) :=
.seq body808_714 body808_198

def body808_716 : Prog (BitVec 64) :=
.seq body808_715 body808_199

def body808_717 : Prog (BitVec 64) :=
.seq body808_716 body808_200

def body808_718 : Prog (BitVec 64) :=
.seq body808_717 body808_201

def body808_719 : Prog (BitVec 64) :=
.seq body808_718 body808_202

def body808_720 : Prog (BitVec 64) :=
.seq body808_719 body808_203

def body808_721 : Prog (BitVec 64) :=
.seq body808_720 body808_204

def body808_722 : Prog (BitVec 64) :=
.seq body808_721 body808_205

def body808_723 : Prog (BitVec 64) :=
.seq body808_722 body808_206

def body808_724 : Prog (BitVec 64) :=
.seq body808_723 body808_207

def body808_725 : Prog (BitVec 64) :=
.seq body808_724 body808_208

def body808_726 : Prog (BitVec 64) :=
.seq body808_725 body808_209

def body808_727 : Prog (BitVec 64) :=
.seq body808_726 body808_210

def body808_728 : Prog (BitVec 64) :=
.seq body808_727 body808_211

def body808_729 : Prog (BitVec 64) :=
.seq body808_728 body808_212

def body808_730 : Prog (BitVec 64) :=
.seq body808_729 body808_213

def body808_731 : Prog (BitVec 64) :=
.seq body808_730 body808_214

def body808_732 : Prog (BitVec 64) :=
.seq body808_731 body808_215

def body808_733 : Prog (BitVec 64) :=
.seq body808_732 body808_216

def body808_734 : Prog (BitVec 64) :=
.seq body808_733 body808_217

def body808_735 : Prog (BitVec 64) :=
.seq body808_734 body808_218

def body808_736 : Prog (BitVec 64) :=
.seq body808_735 body808_219

def body808_737 : Prog (BitVec 64) :=
.seq body808_736 body808_220

def body808_738 : Prog (BitVec 64) :=
.seq body808_737 body808_221

def body808_739 : Prog (BitVec 64) :=
.seq body808_738 body808_222

def body808_740 : Prog (BitVec 64) :=
.seq body808_739 body808_223

def body808_741 : Prog (BitVec 64) :=
.seq body808_740 body808_224

def body808_742 : Prog (BitVec 64) :=
.seq body808_741 body808_225

def body808_743 : Prog (BitVec 64) :=
.seq body808_742 body808_226

def body808_744 : Prog (BitVec 64) :=
.seq body808_743 body808_227

def body808_745 : Prog (BitVec 64) :=
.seq body808_744 body808_228

def body808_746 : Prog (BitVec 64) :=
.seq body808_745 body808_229

def body808_747 : Prog (BitVec 64) :=
.seq body808_746 body808_230

def body808_748 : Prog (BitVec 64) :=
.seq body808_747 body808_231

def body808_749 : Prog (BitVec 64) :=
.seq body808_748 body808_232

def body808_750 : Prog (BitVec 64) :=
.seq body808_749 body808_233

def body808_751 : Prog (BitVec 64) :=
.seq body808_750 body808_234

def body808_752 : Prog (BitVec 64) :=
.seq body808_751 body808_235

def body808_753 : Prog (BitVec 64) :=
.seq body808_752 body808_236

def body808_754 : Prog (BitVec 64) :=
.seq body808_753 body808_237

def body808_755 : Prog (BitVec 64) :=
.seq body808_754 body808_238

def body808_756 : Prog (BitVec 64) :=
.seq body808_755 body808_239

def body808_757 : Prog (BitVec 64) :=
.seq body808_756 body808_240

def body808_758 : Prog (BitVec 64) :=
.seq body808_757 body808_241

def body808_759 : Prog (BitVec 64) :=
.seq body808_758 body808_242

def body808_760 : Prog (BitVec 64) :=
.seq body808_759 body808_243

def body808_761 : Prog (BitVec 64) :=
.seq body808_760 body808_244

def body808_762 : Prog (BitVec 64) :=
.seq body808_761 body808_245

def body808_763 : Prog (BitVec 64) :=
.seq body808_762 body808_246

def body808_764 : Prog (BitVec 64) :=
.seq body808_763 body808_247

def body808_765 : Prog (BitVec 64) :=
.seq body808_764 body808_248

def body808_766 : Prog (BitVec 64) :=
.seq body808_765 body808_249

def body808_767 : Prog (BitVec 64) :=
.seq body808_766 body808_250

def body808_768 : Prog (BitVec 64) :=
.seq body808_767 body808_251

def body808_769 : Prog (BitVec 64) :=
.seq body808_768 body808_252

def body808_770 : Prog (BitVec 64) :=
.seq body808_769 body808_253

def body808_771 : Prog (BitVec 64) :=
.seq body808_770 body808_254

def body808_772 : Prog (BitVec 64) :=
.seq body808_771 body808_255

def body808_773 : Prog (BitVec 64) :=
.seq body808_772 body808_256

def body808_774 : Prog (BitVec 64) :=
.seq body808_773 body808_257

def body808_775 : Prog (BitVec 64) :=
.seq body808_774 body808_258

def body808_776 : Prog (BitVec 64) :=
.seq body808_775 body808_259

def body808_777 : Prog (BitVec 64) :=
.seq body808_776 body808_260

def body808_778 : Prog (BitVec 64) :=
.seq body808_777 body808_0

def originalData808 : Decl (BitVec 64) :=
.function { name := "bls_precompiles_init", inline := false, exported := false, params := [], body := body808_519, returnShape := (Flapjack.Shape.one) }
def simplifiedData808 : Decl (BitVec 64) :=
.function { name := "bls_precompiles_init", inline := false, exported := false, params := [], body := body808_778, returnShape := (Flapjack.Shape.one) }
def original808 := Pancake.PanLang.declToHOL originalData808
def simplified808 := Pancake.PanLang.declToHOL simplifiedData808
end InitECandidate.Proofs.FrontendStages.Declarations
