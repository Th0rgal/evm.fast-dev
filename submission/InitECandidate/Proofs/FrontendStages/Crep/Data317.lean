import InitECandidate.Proofs.FrontendStages.Crep.Translate301
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody317_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2, 3, 4], none)) "calculate_intrinsic_cost"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody317_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 6)

def crepBody317_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody317_3 : CrepProg (BitVec 64) :=
.seq crepBody317_1 crepBody317_2

def crepBody317_4 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 66#64) crepBody317_3

def crepBody317_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 6#64

def crepBody317_6 : CrepProg (BitVec 64) :=
.seq crepBody317_4 crepBody317_5

def crepBody317_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 4294967295#64) (Flapjack.CrepExp.var 5)) crepBody317_6 crepBody317_2

def crepBody317_8 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 60#64) crepBody317_3

def crepBody317_9 : CrepProg (BitVec 64) :=
.seq crepBody317_8 crepBody317_5

def crepBody317_10 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 5)
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3])) crepBody317_9 crepBody317_2

def crepBody317_11 : CrepProg (BitVec 64) :=
.seq crepBody317_7 crepBody317_10

def crepBody317_12 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 61#64) crepBody317_3

def crepBody317_13 : CrepProg (BitVec 64) :=
.seq crepBody317_12 crepBody317_5

def crepBody317_14 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 4)) crepBody317_13 crepBody317_2

def crepBody317_15 : CrepProg (BitVec 64) :=
.seq crepBody317_11 crepBody317_14

def crepBody317_16 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 62#64) crepBody317_3

def crepBody317_17 : CrepProg (BitVec 64) :=
.seq crepBody317_16 crepBody317_5

def crepBody317_18 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 131072#64)
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 200#64]))) crepBody317_17 crepBody317_2

def crepBody317_19 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 152#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody317_18 crepBody317_2

def crepBody317_20 : CrepProg (BitVec 64) :=
.seq crepBody317_15 crepBody317_19

def crepBody317_21 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 63#64) crepBody317_3

def crepBody317_22 : CrepProg (BitVec 64) :=
.seq crepBody317_21 crepBody317_5

def crepBody317_23 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 16777216#64) (Flapjack.CrepExp.var 2)) crepBody317_22 crepBody317_2

def crepBody317_24 : CrepProg (BitVec 64) :=
.seq crepBody317_20 crepBody317_23

def crepBody317_25 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 64#64) crepBody317_3

def crepBody317_26 : CrepProg (BitVec 64) :=
.seq crepBody317_25 crepBody317_5

def crepBody317_27 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 16777216#64) (Flapjack.CrepExp.var 4)) crepBody317_26 crepBody317_2

def crepBody317_28 : CrepProg (BitVec 64) :=
.seq crepBody317_24 crepBody317_27

def crepBody317_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "u256_fits_word"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9]

def crepBody317_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 11)

def crepBody317_31 : CrepProg (BitVec 64) :=
.seq crepBody317_30 crepBody317_2

def crepBody317_32 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 65#64) crepBody317_31

def crepBody317_33 : CrepProg (BitVec 64) :=
.seq crepBody317_32 crepBody317_5

def crepBody317_34 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 0#64)) crepBody317_33 crepBody317_2

def crepBody317_35 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 6)
  (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 1#64])) crepBody317_33 crepBody317_2

def crepBody317_36 : CrepProg (BitVec 64) :=
.seq crepBody317_34 crepBody317_35

def crepBody317_37 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody317_38 : CrepProg (BitVec 64) :=
.seq crepBody317_36 crepBody317_37

def crepBody317_39 : CrepProg (BitVec 64) :=
.seq crepBody317_29 crepBody317_38

def crepBody317_40 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody317_39

def crepBody317_41 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 16#64],
      Flapjack.CrepExp.const 24#64])) crepBody317_40

def crepBody317_42 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 16#64],
      Flapjack.CrepExp.const 16#64])) crepBody317_41

def crepBody317_43 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 16#64],
      Flapjack.CrepExp.const 8#64])) crepBody317_42

def crepBody317_44 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 16#64])) crepBody317_43

def crepBody317_45 : CrepProg (BitVec 64) :=
.seq crepBody317_28 crepBody317_44

def crepBody317_46 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 144#64])) crepBody317_45

def crepBody317_47 : CrepProg (BitVec 64) :=
.seq crepBody317_0 crepBody317_46

def crepBody317_48 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody317_47

def crepBody317_49 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody317_48

def crepBody317_50 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody317_49

def data317 : CrepProg (BitVec 64) := crepBody317_50
def output317 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [118#8, 97#8, 108#8, 105#8, 100#8, 97#8, 116#8, 101#8, 95#8, 116#8, 114#8, 97#8, 110#8, 115#8, 97#8, 99#8, 116#8,
    105#8, 111#8, 110#8], [0, 1], crepProgToHOL data317)
end InitECandidate.Proofs.FrontendStages.Crep
