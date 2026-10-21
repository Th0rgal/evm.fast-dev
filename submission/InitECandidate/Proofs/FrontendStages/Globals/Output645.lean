import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data645
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate627
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody645_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody645_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody645_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 376#64]))
  (Flapjack.Exp.const 0#64)) globalBody645_0 globalBody645_1

def globalBody645_3 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 376#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "")

def globalBody645_4 : Prog (BitVec 64) :=
.decCall ("") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 6#64, Flapjack.Exp.const 64#64]]) globalBody645_3

def globalBody645_5 : Prog (BitVec 64) :=
.seq globalBody645_2 globalBody645_4

def globalBody645_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 376#64]))
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 15230403791020821917#64, Flapjack.Exp.const 754611498739239741#64,
      Flapjack.Exp.const 7381016538464732716#64, Flapjack.Exp.const 1011752739694698287#64])

def globalBody645_7 : Prog (BitVec 64) :=
.seq globalBody645_5 globalBody645_6

def globalBody645_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 376#64]),
      Flapjack.Exp.const 32#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64])

def globalBody645_9 : Prog (BitVec 64) :=
.seq globalBody645_7 globalBody645_8

def globalBody645_10 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 376#64]),
      Flapjack.Exp.const 64#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 12653890742059813127#64, Flapjack.Exp.const 14585784200204367754#64,
      Flapjack.Exp.const 1278438861261381767#64, Flapjack.Exp.const 212598772761311868#64])

def globalBody645_11 : Prog (BitVec 64) :=
.seq globalBody645_9 globalBody645_10

def globalBody645_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 376#64]),
      Flapjack.Exp.const 96#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 11683091849979440498#64, Flapjack.Exp.const 14992204589386555739#64,
      Flapjack.Exp.const 15866167890766973222#64, Flapjack.Exp.const 1200023580730561873#64])

def globalBody645_13 : Prog (BitVec 64) :=
.seq globalBody645_11 globalBody645_12

def globalBody645_14 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 376#64]),
      Flapjack.Exp.const 128#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 13075984984163199792#64, Flapjack.Exp.const 3782902503040509012#64,
      Flapjack.Exp.const 8791150885551868305#64, Flapjack.Exp.const 1825854335138010348#64])

def globalBody645_15 : Prog (BitVec 64) :=
.seq globalBody645_13 globalBody645_14

def globalBody645_16 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 376#64]),
      Flapjack.Exp.const 160#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 7963664994991228759#64, Flapjack.Exp.const 12257807996192067905#64,
      Flapjack.Exp.const 13179524609921305146#64, Flapjack.Exp.const 2767831111890561987#64])

def globalBody645_17 : Prog (BitVec 64) :=
.seq globalBody645_15 globalBody645_16

def globalBody645_18 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 376#64]),
      Flapjack.Exp.const 192#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 16482010305593259561#64, Flapjack.Exp.const 13488546290961988299#64,
      Flapjack.Exp.const 3578621962720924518#64, Flapjack.Exp.const 2681173117283399901#64])

def globalBody645_19 : Prog (BitVec 64) :=
.seq globalBody645_17 globalBody645_18

def globalBody645_20 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 376#64]),
      Flapjack.Exp.const 224#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 11661927080404088775#64, Flapjack.Exp.const 553939530661941723#64,
      Flapjack.Exp.const 7860678177968807019#64, Flapjack.Exp.const 3208568454732775116#64])

def globalBody645_21 : Prog (BitVec 64) :=
.seq globalBody645_19 globalBody645_20

def globalBody645_22 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 376#64]),
      Flapjack.Exp.const 256#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 8314163329781907090#64, Flapjack.Exp.const 11942187022798819835#64,
      Flapjack.Exp.const 11282677263046157209#64, Flapjack.Exp.const 1576150870752482284#64])

def globalBody645_23 : Prog (BitVec 64) :=
.seq globalBody645_21 globalBody645_22

def globalBody645_24 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 376#64]),
      Flapjack.Exp.const 288#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 6763840483288992073#64, Flapjack.Exp.const 7118829427391486816#64,
      Flapjack.Exp.const 4016233444936635065#64, Flapjack.Exp.const 2630958277570195709#64])

def globalBody645_25 : Prog (BitVec 64) :=
.seq globalBody645_23 globalBody645_24

def globalBody645_26 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 376#64]),
      Flapjack.Exp.const 320#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 14515217250696892391#64, Flapjack.Exp.const 16303087968080972555#64,
      Flapjack.Exp.const 3656613296917993960#64, Flapjack.Exp.const 1345095164996126785#64])

def globalBody645_27 : Prog (BitVec 64) :=
.seq globalBody645_25 globalBody645_26

def globalBody645_28 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 376#64]),
      Flapjack.Exp.const 352#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 957117326806663081#64, Flapjack.Exp.const 367382125163301975#64,
      Flapjack.Exp.const 15253872307375509749#64, Flapjack.Exp.const 3396254757538665050#64])

def globalBody645_29 : Prog (BitVec 64) :=
.seq globalBody645_27 globalBody645_28

def globalBody645_30 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "")

def globalBody645_31 : Prog (BitVec 64) :=
.decCall ("") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 44#64, Flapjack.Exp.const 8#64]]) globalBody645_30

def globalBody645_32 : Prog (BitVec 64) :=
.seq globalBody645_29 globalBody645_31

def globalBody645_33 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]))
  (Flapjack.Exp.const 9698021743855595808#64)

def globalBody645_34 : Prog (BitVec 64) :=
.seq globalBody645_32 globalBody645_33

def globalBody645_35 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 8#64])
  (Flapjack.Exp.const 4658111487712502692#64)

def globalBody645_36 : Prog (BitVec 64) :=
.seq globalBody645_34 globalBody645_35

def globalBody645_37 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 16#64])
  (Flapjack.Exp.const 9475478476403788475#64)

def globalBody645_38 : Prog (BitVec 64) :=
.seq globalBody645_36 globalBody645_37

def globalBody645_39 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 24#64])
  (Flapjack.Exp.const 3895898136474990872#64)

def globalBody645_40 : Prog (BitVec 64) :=
.seq globalBody645_38 globalBody645_39

def globalBody645_41 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 32#64])
  (Flapjack.Exp.const 13897688294677189338#64)

def globalBody645_42 : Prog (BitVec 64) :=
.seq globalBody645_40 globalBody645_41

def globalBody645_43 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 40#64])
  (Flapjack.Exp.const 13692288569157338976#64)

def globalBody645_44 : Prog (BitVec 64) :=
.seq globalBody645_42 globalBody645_43

def globalBody645_45 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 48#64])
  (Flapjack.Exp.const 15521367811043670911#64)

def globalBody645_46 : Prog (BitVec 64) :=
.seq globalBody645_44 globalBody645_45

def globalBody645_47 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 56#64])
  (Flapjack.Exp.const 13992850401411864641#64)

def globalBody645_48 : Prog (BitVec 64) :=
.seq globalBody645_46 globalBody645_47

def globalBody645_49 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 64#64])
  (Flapjack.Exp.const 6609620042336070051#64)

def globalBody645_50 : Prog (BitVec 64) :=
.seq globalBody645_48 globalBody645_49

def globalBody645_51 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 72#64])
  (Flapjack.Exp.const 9167096575297741460#64)

def globalBody645_52 : Prog (BitVec 64) :=
.seq globalBody645_50 globalBody645_51

def globalBody645_53 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 80#64])
  (Flapjack.Exp.const 3006977925533509404#64)

def globalBody645_54 : Prog (BitVec 64) :=
.seq globalBody645_52 globalBody645_53

def globalBody645_55 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 88#64])
  (Flapjack.Exp.const 13799376210358020352#64)

def globalBody645_56 : Prog (BitVec 64) :=
.seq globalBody645_54 globalBody645_55

def globalBody645_57 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 96#64])
  (Flapjack.Exp.const 7213564696215919148#64)

def globalBody645_58 : Prog (BitVec 64) :=
.seq globalBody645_56 globalBody645_57

def globalBody645_59 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 104#64])
  (Flapjack.Exp.const 12108970941387295838#64)

def globalBody645_60 : Prog (BitVec 64) :=
.seq globalBody645_58 globalBody645_59

def globalBody645_61 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 112#64])
  (Flapjack.Exp.const 14800348210198864764#64)

def globalBody645_62 : Prog (BitVec 64) :=
.seq globalBody645_60 globalBody645_61

def globalBody645_63 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 120#64])
  (Flapjack.Exp.const 5333217130945090002#64)

def globalBody645_64 : Prog (BitVec 64) :=
.seq globalBody645_62 globalBody645_63

def globalBody645_65 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 128#64])
  (Flapjack.Exp.const 17191330154042290397#64)

def globalBody645_66 : Prog (BitVec 64) :=
.seq globalBody645_64 globalBody645_65

def globalBody645_67 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 136#64])
  (Flapjack.Exp.const 7728981312468502308#64)

def globalBody645_68 : Prog (BitVec 64) :=
.seq globalBody645_66 globalBody645_67

def globalBody645_69 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 144#64])
  (Flapjack.Exp.const 13479501571575199621#64)

def globalBody645_70 : Prog (BitVec 64) :=
.seq globalBody645_68 globalBody645_69

def globalBody645_71 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 152#64])
  (Flapjack.Exp.const 4632319730382815766#64)

def globalBody645_72 : Prog (BitVec 64) :=
.seq globalBody645_70 globalBody645_71

def globalBody645_73 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 160#64])
  (Flapjack.Exp.const 6183408236485651195#64)

def globalBody645_74 : Prog (BitVec 64) :=
.seq globalBody645_72 globalBody645_73

def globalBody645_75 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 168#64])
  (Flapjack.Exp.const 2344383644319854215#64)

def globalBody645_76 : Prog (BitVec 64) :=
.seq globalBody645_74 globalBody645_75

def globalBody645_77 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 176#64])
  (Flapjack.Exp.const 9541507823907846048#64)

def globalBody645_78 : Prog (BitVec 64) :=
.seq globalBody645_76 globalBody645_77

def globalBody645_79 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 184#64])
  (Flapjack.Exp.const 5234407941292577173#64)

def globalBody645_80 : Prog (BitVec 64) :=
.seq globalBody645_78 globalBody645_79

def globalBody645_81 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 192#64])
  (Flapjack.Exp.const 16529975799043132950#64)

def globalBody645_82 : Prog (BitVec 64) :=
.seq globalBody645_80 globalBody645_81

def globalBody645_83 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 200#64])
  (Flapjack.Exp.const 12351756573642376427#64)

def globalBody645_84 : Prog (BitVec 64) :=
.seq globalBody645_82 globalBody645_83

def globalBody645_85 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 208#64])
  (Flapjack.Exp.const 9426269327694809050#64)

def globalBody645_86 : Prog (BitVec 64) :=
.seq globalBody645_84 globalBody645_85

def globalBody645_87 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 216#64])
  (Flapjack.Exp.const 7379223421642392714#64)

def globalBody645_88 : Prog (BitVec 64) :=
.seq globalBody645_86 globalBody645_87

def globalBody645_89 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 224#64])
  (Flapjack.Exp.const 5792417538046516732#64)

def globalBody645_90 : Prog (BitVec 64) :=
.seq globalBody645_88 globalBody645_89

def globalBody645_91 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 232#64])
  (Flapjack.Exp.const 9162926010144764881#64)

def globalBody645_92 : Prog (BitVec 64) :=
.seq globalBody645_90 globalBody645_91

def globalBody645_93 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 240#64])
  (Flapjack.Exp.const 8644015420738790472#64)

def globalBody645_94 : Prog (BitVec 64) :=
.seq globalBody645_92 globalBody645_93

def globalBody645_95 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 248#64])
  (Flapjack.Exp.const 18370314904686314414#64)

def globalBody645_96 : Prog (BitVec 64) :=
.seq globalBody645_94 globalBody645_95

def globalBody645_97 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 256#64])
  (Flapjack.Exp.const 17975984934167627464#64)

def globalBody645_98 : Prog (BitVec 64) :=
.seq globalBody645_96 globalBody645_97

def globalBody645_99 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 264#64])
  (Flapjack.Exp.const 8719923968173632426#64)

def globalBody645_100 : Prog (BitVec 64) :=
.seq globalBody645_98 globalBody645_99

def globalBody645_101 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 272#64])
  (Flapjack.Exp.const 6379321585415610019#64)

def globalBody645_102 : Prog (BitVec 64) :=
.seq globalBody645_100 globalBody645_101

def globalBody645_103 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 280#64])
  (Flapjack.Exp.const 1402842025008175984#64)

def globalBody645_104 : Prog (BitVec 64) :=
.seq globalBody645_102 globalBody645_103

def globalBody645_105 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 288#64])
  (Flapjack.Exp.const 888598832447275954#64)

def globalBody645_106 : Prog (BitVec 64) :=
.seq globalBody645_104 globalBody645_105

def globalBody645_107 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 296#64])
  (Flapjack.Exp.const 4522688638863333623#64)

def globalBody645_108 : Prog (BitVec 64) :=
.seq globalBody645_106 globalBody645_107

def globalBody645_109 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 304#64])
  (Flapjack.Exp.const 15776483769708984925#64)

def globalBody645_110 : Prog (BitVec 64) :=
.seq globalBody645_108 globalBody645_109

def globalBody645_111 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 312#64])
  (Flapjack.Exp.const 16276864970431725248#64)

def globalBody645_112 : Prog (BitVec 64) :=
.seq globalBody645_110 globalBody645_111

def globalBody645_113 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 320#64])
  (Flapjack.Exp.const 7646110518075161570#64)

def globalBody645_114 : Prog (BitVec 64) :=
.seq globalBody645_112 globalBody645_113

def globalBody645_115 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 328#64])
  (Flapjack.Exp.const 9524343276244152831#64)

def globalBody645_116 : Prog (BitVec 64) :=
.seq globalBody645_114 globalBody645_115

def globalBody645_117 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 336#64])
  (Flapjack.Exp.const 2377296829910687932#64)

def globalBody645_118 : Prog (BitVec 64) :=
.seq globalBody645_116 globalBody645_117

def globalBody645_119 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 384#64]),
      Flapjack.Exp.const 344#64])
  (Flapjack.Exp.const 203128949104#64)

def globalBody645_120 : Prog (BitVec 64) :=
.seq globalBody645_118 globalBody645_119

def globalBody645_121 : Prog (BitVec 64) :=
.seq globalBody645_120 globalBody645_0

def globalData645 : Decl (BitVec 64) :=
.function { name := "bn254_init", inline := false, exported := false, params := [], body := globalBody645_121, returnShape := (Flapjack.Shape.one) }
def globalOutput645 := Pancake.PanLang.declToHOL globalData645
end InitECandidate.Proofs.FrontendStages.Declarations
