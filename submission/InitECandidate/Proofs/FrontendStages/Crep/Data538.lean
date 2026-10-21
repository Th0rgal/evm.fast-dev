import InitECandidate.Proofs.FrontendStages.Crep.Translate522
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody538_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 1)

def crepBody538_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody538_2 : CrepProg (BitVec 64) :=
.seq crepBody538_0 crepBody538_1

def crepBody538_3 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 7#64) crepBody538_2

def crepBody538_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 8#64

def crepBody538_5 : CrepProg (BitVec 64) :=
.seq crepBody538_3 crepBody538_4

def crepBody538_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 1024#64)
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 128#64]))) crepBody538_5 crepBody538_1

def crepBody538_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "frame_open" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64]

def crepBody538_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "state_snapshot" []

def crepBody538_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6 (Flapjack.CrepExp.loadGlob 0#5)

def crepBody538_10 : CrepProg (BitVec 64) :=
.seq crepBody538_9 crepBody538_1

def crepBody538_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "scratch_release"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 208#64])]

def crepBody538_12 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody538_11

def crepBody538_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "frame_mem_release"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 224#64])]

def crepBody538_14 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody538_13

def crepBody538_15 : CrepProg (BitVec 64) :=
.seq crepBody538_12 crepBody538_14

def crepBody538_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.var 8)

def crepBody538_17 : CrepProg (BitVec 64) :=
.seq crepBody538_16 crepBody538_1

def crepBody538_18 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 1) crepBody538_17

def crepBody538_19 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]) crepBody538_18

def crepBody538_20 : CrepProg (BitVec 64) :=
.seq crepBody538_15 crepBody538_19

def crepBody538_21 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 2) crepBody538_17

def crepBody538_22 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 288#64]) crepBody538_21

def crepBody538_23 : CrepProg (BitVec 64) :=
.seq crepBody538_20 crepBody538_22

def crepBody538_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 7)

def crepBody538_25 : CrepProg (BitVec 64) :=
.seq crepBody538_24 crepBody538_1

def crepBody538_26 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 6) crepBody538_25

def crepBody538_27 : CrepProg (BitVec 64) :=
.seq crepBody538_26 crepBody538_4

def crepBody538_28 : CrepProg (BitVec 64) :=
.seq crepBody538_23 crepBody538_27

def crepBody538_29 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 1#64)) crepBody538_28 crepBody538_1

def crepBody538_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "state_restore" [Flapjack.CrepExp.var 4]

def crepBody538_31 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody538_30

def crepBody538_32 : CrepProg (BitVec 64) :=
.seq crepBody538_29 crepBody538_31

def crepBody538_33 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 5) crepBody538_17

def crepBody538_34 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64]) crepBody538_33

def crepBody538_35 : CrepProg (BitVec 64) :=
.seq crepBody538_32 crepBody538_34

def crepBody538_36 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody538_17

def crepBody538_37 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 200#64]) crepBody538_36

def crepBody538_38 : CrepProg (BitVec 64) :=
.seq crepBody538_35 crepBody538_37

def crepBody538_39 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "refill_frame_state_gas" []

def crepBody538_40 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody538_39

def crepBody538_41 : CrepProg (BitVec 64) :=
.seq crepBody538_38 crepBody538_40

def crepBody538_42 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "frame_halt" [Flapjack.CrepExp.var 6]

def crepBody538_43 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody538_42

def crepBody538_44 : CrepProg (BitVec 64) :=
.seq crepBody538_41 crepBody538_43

def crepBody538_45 : CrepProg (BitVec 64) :=
.seq crepBody538_44 crepBody538_19

def crepBody538_46 : CrepProg (BitVec 64) :=
.seq crepBody538_45 crepBody538_22

def crepBody538_47 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 3]

def crepBody538_48 : CrepProg (BitVec 64) :=
.seq crepBody538_46 crepBody538_47

def crepBody538_49 : CrepProg (BitVec 64) :=
.seq crepBody538_10 crepBody538_48

def crepBody538_50 : CrepProg (BitVec 64) :=
.call (some (([7]), some ((8#64), crepBody538_49))) ("depth0_prepare") ([])

def crepBody538_51 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody538_50

def crepBody538_52 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody538_51

def crepBody538_53 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64])) crepBody538_52

def crepBody538_54 : CrepProg (BitVec 64) :=
.seq crepBody538_8 crepBody538_53

def crepBody538_55 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody538_54

def crepBody538_56 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 128#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody538_55 crepBody538_1

def crepBody538_57 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 6)

def crepBody538_58 : CrepProg (BitVec 64) :=
.seq crepBody538_57 crepBody538_1

def crepBody538_59 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 4) crepBody538_58

def crepBody538_60 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 288#64]),
    Flapjack.CrepExp.const 24#64]) crepBody538_59

def crepBody538_61 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "frame_start" []

def crepBody538_62 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody538_61

def crepBody538_63 : CrepProg (BitVec 64) :=
.seq crepBody538_60 crepBody538_62

def crepBody538_64 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "run_frames" []

def crepBody538_65 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody538_64

def crepBody538_66 : CrepProg (BitVec 64) :=
.seq crepBody538_63 crepBody538_65

def crepBody538_67 : CrepProg (BitVec 64) :=
.seq crepBody538_66 crepBody538_47

def crepBody538_68 : CrepProg (BitVec 64) :=
.seq crepBody538_8 crepBody538_67

def crepBody538_69 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody538_68

def crepBody538_70 : CrepProg (BitVec 64) :=
.seq crepBody538_56 crepBody538_69

def crepBody538_71 : CrepProg (BitVec 64) :=
.seq crepBody538_7 crepBody538_70

def crepBody538_72 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody538_71

def crepBody538_73 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 288#64])) crepBody538_72

def crepBody538_74 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64])) crepBody538_73

def crepBody538_75 : CrepProg (BitVec 64) :=
.seq crepBody538_6 crepBody538_74

def data538 : CrepProg (BitVec 64) := crepBody538_75
def output538 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 114#8, 111#8, 99#8, 101#8, 115#8, 115#8, 95#8, 109#8, 101#8, 115#8, 115#8, 97#8, 103#8, 101#8], [0], crepProgToHOL data538)
end InitECandidate.Proofs.FrontendStages.Crep
