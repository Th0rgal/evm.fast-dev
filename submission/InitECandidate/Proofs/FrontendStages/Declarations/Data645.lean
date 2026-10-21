import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify629
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body645_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body645_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body645_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.global "bn_gamma") (Flapjack.Exp.const 0#64)) body645_0 body645_1

def body645_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "bn_gamma"), none)) "alloc"
  [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 6#64, Flapjack.Exp.const 64#64]]

def body645_4 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.global "bn_gamma")
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 15230403791020821917#64, Flapjack.Exp.const 754611498739239741#64,
      Flapjack.Exp.const 7381016538464732716#64, Flapjack.Exp.const 1011752739694698287#64])

def body645_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_gamma", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64])

def body645_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_gamma", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 12653890742059813127#64, Flapjack.Exp.const 14585784200204367754#64,
      Flapjack.Exp.const 1278438861261381767#64, Flapjack.Exp.const 212598772761311868#64])

def body645_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_gamma", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 11683091849979440498#64, Flapjack.Exp.const 14992204589386555739#64,
      Flapjack.Exp.const 15866167890766973222#64, Flapjack.Exp.const 1200023580730561873#64])

def body645_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_gamma", Flapjack.Exp.const 128#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 13075984984163199792#64, Flapjack.Exp.const 3782902503040509012#64,
      Flapjack.Exp.const 8791150885551868305#64, Flapjack.Exp.const 1825854335138010348#64])

def body645_9 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_gamma", Flapjack.Exp.const 160#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 7963664994991228759#64, Flapjack.Exp.const 12257807996192067905#64,
      Flapjack.Exp.const 13179524609921305146#64, Flapjack.Exp.const 2767831111890561987#64])

def body645_10 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_gamma", Flapjack.Exp.const 192#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 16482010305593259561#64, Flapjack.Exp.const 13488546290961988299#64,
      Flapjack.Exp.const 3578621962720924518#64, Flapjack.Exp.const 2681173117283399901#64])

def body645_11 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_gamma", Flapjack.Exp.const 224#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 11661927080404088775#64, Flapjack.Exp.const 553939530661941723#64,
      Flapjack.Exp.const 7860678177968807019#64, Flapjack.Exp.const 3208568454732775116#64])

def body645_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_gamma", Flapjack.Exp.const 256#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 8314163329781907090#64, Flapjack.Exp.const 11942187022798819835#64,
      Flapjack.Exp.const 11282677263046157209#64, Flapjack.Exp.const 1576150870752482284#64])

def body645_13 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_gamma", Flapjack.Exp.const 288#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 6763840483288992073#64, Flapjack.Exp.const 7118829427391486816#64,
      Flapjack.Exp.const 4016233444936635065#64, Flapjack.Exp.const 2630958277570195709#64])

def body645_14 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_gamma", Flapjack.Exp.const 320#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 14515217250696892391#64, Flapjack.Exp.const 16303087968080972555#64,
      Flapjack.Exp.const 3656613296917993960#64, Flapjack.Exp.const 1345095164996126785#64])

def body645_15 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_gamma", Flapjack.Exp.const 352#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 957117326806663081#64, Flapjack.Exp.const 367382125163301975#64,
      Flapjack.Exp.const 15253872307375509749#64, Flapjack.Exp.const 3396254757538665050#64])

def body645_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "bn_expw"), none)) "alloc"
  [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 44#64, Flapjack.Exp.const 8#64]]

def body645_17 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.global "bn_expw") (Flapjack.Exp.const 9698021743855595808#64)

def body645_18 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.const 4658111487712502692#64)

def body645_19 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.const 9475478476403788475#64)

def body645_20 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.const 3895898136474990872#64)

def body645_21 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.const 13897688294677189338#64)

def body645_22 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.const 13692288569157338976#64)

def body645_23 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.const 15521367811043670911#64)

def body645_24 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.const 13992850401411864641#64)

def body645_25 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.const 6609620042336070051#64)

def body645_26 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 72#64])
  (Flapjack.Exp.const 9167096575297741460#64)

def body645_27 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 80#64])
  (Flapjack.Exp.const 3006977925533509404#64)

def body645_28 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 88#64])
  (Flapjack.Exp.const 13799376210358020352#64)

def body645_29 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.const 7213564696215919148#64)

def body645_30 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 104#64])
  (Flapjack.Exp.const 12108970941387295838#64)

def body645_31 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 112#64])
  (Flapjack.Exp.const 14800348210198864764#64)

def body645_32 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.const 5333217130945090002#64)

def body645_33 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 128#64])
  (Flapjack.Exp.const 17191330154042290397#64)

def body645_34 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 136#64])
  (Flapjack.Exp.const 7728981312468502308#64)

def body645_35 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 144#64])
  (Flapjack.Exp.const 13479501571575199621#64)

def body645_36 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 152#64])
  (Flapjack.Exp.const 4632319730382815766#64)

def body645_37 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 160#64])
  (Flapjack.Exp.const 6183408236485651195#64)

def body645_38 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 168#64])
  (Flapjack.Exp.const 2344383644319854215#64)

def body645_39 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 176#64])
  (Flapjack.Exp.const 9541507823907846048#64)

def body645_40 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 184#64])
  (Flapjack.Exp.const 5234407941292577173#64)

def body645_41 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 192#64])
  (Flapjack.Exp.const 16529975799043132950#64)

def body645_42 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 200#64])
  (Flapjack.Exp.const 12351756573642376427#64)

def body645_43 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 208#64])
  (Flapjack.Exp.const 9426269327694809050#64)

def body645_44 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 216#64])
  (Flapjack.Exp.const 7379223421642392714#64)

def body645_45 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 224#64])
  (Flapjack.Exp.const 5792417538046516732#64)

def body645_46 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 232#64])
  (Flapjack.Exp.const 9162926010144764881#64)

def body645_47 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 240#64])
  (Flapjack.Exp.const 8644015420738790472#64)

def body645_48 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 248#64])
  (Flapjack.Exp.const 18370314904686314414#64)

def body645_49 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 256#64])
  (Flapjack.Exp.const 17975984934167627464#64)

def body645_50 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 264#64])
  (Flapjack.Exp.const 8719923968173632426#64)

def body645_51 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 272#64])
  (Flapjack.Exp.const 6379321585415610019#64)

def body645_52 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 280#64])
  (Flapjack.Exp.const 1402842025008175984#64)

def body645_53 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 288#64])
  (Flapjack.Exp.const 888598832447275954#64)

def body645_54 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 296#64])
  (Flapjack.Exp.const 4522688638863333623#64)

def body645_55 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 304#64])
  (Flapjack.Exp.const 15776483769708984925#64)

def body645_56 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 312#64])
  (Flapjack.Exp.const 16276864970431725248#64)

def body645_57 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 320#64])
  (Flapjack.Exp.const 7646110518075161570#64)

def body645_58 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 328#64])
  (Flapjack.Exp.const 9524343276244152831#64)

def body645_59 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 336#64])
  (Flapjack.Exp.const 2377296829910687932#64)

def body645_60 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bn_expw", Flapjack.Exp.const 344#64])
  (Flapjack.Exp.const 203128949104#64)

def body645_61 : Prog (BitVec 64) :=
.seq body645_60 body645_0

def body645_62 : Prog (BitVec 64) :=
.seq body645_59 body645_61

def body645_63 : Prog (BitVec 64) :=
.seq body645_58 body645_62

def body645_64 : Prog (BitVec 64) :=
.seq body645_57 body645_63

def body645_65 : Prog (BitVec 64) :=
.seq body645_56 body645_64

def body645_66 : Prog (BitVec 64) :=
.seq body645_55 body645_65

def body645_67 : Prog (BitVec 64) :=
.seq body645_54 body645_66

def body645_68 : Prog (BitVec 64) :=
.seq body645_53 body645_67

def body645_69 : Prog (BitVec 64) :=
.seq body645_52 body645_68

def body645_70 : Prog (BitVec 64) :=
.seq body645_51 body645_69

def body645_71 : Prog (BitVec 64) :=
.seq body645_50 body645_70

def body645_72 : Prog (BitVec 64) :=
.seq body645_49 body645_71

def body645_73 : Prog (BitVec 64) :=
.seq body645_48 body645_72

def body645_74 : Prog (BitVec 64) :=
.seq body645_47 body645_73

def body645_75 : Prog (BitVec 64) :=
.seq body645_46 body645_74

def body645_76 : Prog (BitVec 64) :=
.seq body645_45 body645_75

def body645_77 : Prog (BitVec 64) :=
.seq body645_44 body645_76

def body645_78 : Prog (BitVec 64) :=
.seq body645_43 body645_77

def body645_79 : Prog (BitVec 64) :=
.seq body645_42 body645_78

def body645_80 : Prog (BitVec 64) :=
.seq body645_41 body645_79

def body645_81 : Prog (BitVec 64) :=
.seq body645_40 body645_80

def body645_82 : Prog (BitVec 64) :=
.seq body645_39 body645_81

def body645_83 : Prog (BitVec 64) :=
.seq body645_38 body645_82

def body645_84 : Prog (BitVec 64) :=
.seq body645_37 body645_83

def body645_85 : Prog (BitVec 64) :=
.seq body645_36 body645_84

def body645_86 : Prog (BitVec 64) :=
.seq body645_35 body645_85

def body645_87 : Prog (BitVec 64) :=
.seq body645_34 body645_86

def body645_88 : Prog (BitVec 64) :=
.seq body645_33 body645_87

def body645_89 : Prog (BitVec 64) :=
.seq body645_32 body645_88

def body645_90 : Prog (BitVec 64) :=
.seq body645_31 body645_89

def body645_91 : Prog (BitVec 64) :=
.seq body645_30 body645_90

def body645_92 : Prog (BitVec 64) :=
.seq body645_29 body645_91

def body645_93 : Prog (BitVec 64) :=
.seq body645_28 body645_92

def body645_94 : Prog (BitVec 64) :=
.seq body645_27 body645_93

def body645_95 : Prog (BitVec 64) :=
.seq body645_26 body645_94

def body645_96 : Prog (BitVec 64) :=
.seq body645_25 body645_95

def body645_97 : Prog (BitVec 64) :=
.seq body645_24 body645_96

def body645_98 : Prog (BitVec 64) :=
.seq body645_23 body645_97

def body645_99 : Prog (BitVec 64) :=
.seq body645_22 body645_98

def body645_100 : Prog (BitVec 64) :=
.seq body645_21 body645_99

def body645_101 : Prog (BitVec 64) :=
.seq body645_20 body645_100

def body645_102 : Prog (BitVec 64) :=
.seq body645_19 body645_101

def body645_103 : Prog (BitVec 64) :=
.seq body645_18 body645_102

def body645_104 : Prog (BitVec 64) :=
.seq body645_17 body645_103

def body645_105 : Prog (BitVec 64) :=
.seq body645_16 body645_104

def body645_106 : Prog (BitVec 64) :=
.seq body645_15 body645_105

def body645_107 : Prog (BitVec 64) :=
.seq body645_14 body645_106

def body645_108 : Prog (BitVec 64) :=
.seq body645_13 body645_107

def body645_109 : Prog (BitVec 64) :=
.seq body645_12 body645_108

def body645_110 : Prog (BitVec 64) :=
.seq body645_11 body645_109

def body645_111 : Prog (BitVec 64) :=
.seq body645_10 body645_110

def body645_112 : Prog (BitVec 64) :=
.seq body645_9 body645_111

def body645_113 : Prog (BitVec 64) :=
.seq body645_8 body645_112

def body645_114 : Prog (BitVec 64) :=
.seq body645_7 body645_113

def body645_115 : Prog (BitVec 64) :=
.seq body645_6 body645_114

def body645_116 : Prog (BitVec 64) :=
.seq body645_5 body645_115

def body645_117 : Prog (BitVec 64) :=
.seq body645_4 body645_116

def body645_118 : Prog (BitVec 64) :=
.seq body645_3 body645_117

def body645_119 : Prog (BitVec 64) :=
.seq body645_2 body645_118

def body645_120 : Prog (BitVec 64) :=
.seq body645_2 body645_3

def body645_121 : Prog (BitVec 64) :=
.seq body645_120 body645_4

def body645_122 : Prog (BitVec 64) :=
.seq body645_121 body645_5

def body645_123 : Prog (BitVec 64) :=
.seq body645_122 body645_6

def body645_124 : Prog (BitVec 64) :=
.seq body645_123 body645_7

def body645_125 : Prog (BitVec 64) :=
.seq body645_124 body645_8

def body645_126 : Prog (BitVec 64) :=
.seq body645_125 body645_9

def body645_127 : Prog (BitVec 64) :=
.seq body645_126 body645_10

def body645_128 : Prog (BitVec 64) :=
.seq body645_127 body645_11

def body645_129 : Prog (BitVec 64) :=
.seq body645_128 body645_12

def body645_130 : Prog (BitVec 64) :=
.seq body645_129 body645_13

def body645_131 : Prog (BitVec 64) :=
.seq body645_130 body645_14

def body645_132 : Prog (BitVec 64) :=
.seq body645_131 body645_15

def body645_133 : Prog (BitVec 64) :=
.seq body645_132 body645_16

def body645_134 : Prog (BitVec 64) :=
.seq body645_133 body645_17

def body645_135 : Prog (BitVec 64) :=
.seq body645_134 body645_18

def body645_136 : Prog (BitVec 64) :=
.seq body645_135 body645_19

def body645_137 : Prog (BitVec 64) :=
.seq body645_136 body645_20

def body645_138 : Prog (BitVec 64) :=
.seq body645_137 body645_21

def body645_139 : Prog (BitVec 64) :=
.seq body645_138 body645_22

def body645_140 : Prog (BitVec 64) :=
.seq body645_139 body645_23

def body645_141 : Prog (BitVec 64) :=
.seq body645_140 body645_24

def body645_142 : Prog (BitVec 64) :=
.seq body645_141 body645_25

def body645_143 : Prog (BitVec 64) :=
.seq body645_142 body645_26

def body645_144 : Prog (BitVec 64) :=
.seq body645_143 body645_27

def body645_145 : Prog (BitVec 64) :=
.seq body645_144 body645_28

def body645_146 : Prog (BitVec 64) :=
.seq body645_145 body645_29

def body645_147 : Prog (BitVec 64) :=
.seq body645_146 body645_30

def body645_148 : Prog (BitVec 64) :=
.seq body645_147 body645_31

def body645_149 : Prog (BitVec 64) :=
.seq body645_148 body645_32

def body645_150 : Prog (BitVec 64) :=
.seq body645_149 body645_33

def body645_151 : Prog (BitVec 64) :=
.seq body645_150 body645_34

def body645_152 : Prog (BitVec 64) :=
.seq body645_151 body645_35

def body645_153 : Prog (BitVec 64) :=
.seq body645_152 body645_36

def body645_154 : Prog (BitVec 64) :=
.seq body645_153 body645_37

def body645_155 : Prog (BitVec 64) :=
.seq body645_154 body645_38

def body645_156 : Prog (BitVec 64) :=
.seq body645_155 body645_39

def body645_157 : Prog (BitVec 64) :=
.seq body645_156 body645_40

def body645_158 : Prog (BitVec 64) :=
.seq body645_157 body645_41

def body645_159 : Prog (BitVec 64) :=
.seq body645_158 body645_42

def body645_160 : Prog (BitVec 64) :=
.seq body645_159 body645_43

def body645_161 : Prog (BitVec 64) :=
.seq body645_160 body645_44

def body645_162 : Prog (BitVec 64) :=
.seq body645_161 body645_45

def body645_163 : Prog (BitVec 64) :=
.seq body645_162 body645_46

def body645_164 : Prog (BitVec 64) :=
.seq body645_163 body645_47

def body645_165 : Prog (BitVec 64) :=
.seq body645_164 body645_48

def body645_166 : Prog (BitVec 64) :=
.seq body645_165 body645_49

def body645_167 : Prog (BitVec 64) :=
.seq body645_166 body645_50

def body645_168 : Prog (BitVec 64) :=
.seq body645_167 body645_51

def body645_169 : Prog (BitVec 64) :=
.seq body645_168 body645_52

def body645_170 : Prog (BitVec 64) :=
.seq body645_169 body645_53

def body645_171 : Prog (BitVec 64) :=
.seq body645_170 body645_54

def body645_172 : Prog (BitVec 64) :=
.seq body645_171 body645_55

def body645_173 : Prog (BitVec 64) :=
.seq body645_172 body645_56

def body645_174 : Prog (BitVec 64) :=
.seq body645_173 body645_57

def body645_175 : Prog (BitVec 64) :=
.seq body645_174 body645_58

def body645_176 : Prog (BitVec 64) :=
.seq body645_175 body645_59

def body645_177 : Prog (BitVec 64) :=
.seq body645_176 body645_60

def body645_178 : Prog (BitVec 64) :=
.seq body645_177 body645_0

def originalData645 : Decl (BitVec 64) :=
.function { name := "bn254_init", inline := false, exported := false, params := [], body := body645_119, returnShape := (Flapjack.Shape.one) }
def simplifiedData645 : Decl (BitVec 64) :=
.function { name := "bn254_init", inline := false, exported := false, params := [], body := body645_178, returnShape := (Flapjack.Shape.one) }
def original645 := Pancake.PanLang.declToHOL originalData645
def simplified645 := Pancake.PanLang.declToHOL simplifiedData645
end InitECandidate.Proofs.FrontendStages.Declarations
