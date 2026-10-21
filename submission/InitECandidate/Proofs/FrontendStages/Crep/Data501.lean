import InitECandidate.Proofs.FrontendStages.Crep.Translate485
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody501_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3, 4], none)) "stack_pop" []

def crepBody501_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6, 7, 8], none)) "stack_pop" []

def crepBody501_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9, 10, 11, 12], none)) "stack_pop" []

def crepBody501_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "sat_word"
  [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12]

def crepBody501_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "words_of" [Flapjack.CrepExp.var 13]

def crepBody501_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15, 16], none)) "extend_memory_cost1"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12]

def crepBody501_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "add_sat"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.const 3#64,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 3#64, Flapjack.CrepExp.var 14]],
    Flapjack.CrepExp.var 15]

def crepBody501_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "charge_gas" [Flapjack.CrepExp.var 17]

def crepBody501_8 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody501_7

def crepBody501_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "sat_word"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody501_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "add_sat" [Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 13]

def crepBody501_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 20)

def crepBody501_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody501_13 : CrepProg (BitVec 64) :=
.seq crepBody501_11 crepBody501_12

def crepBody501_14 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 9#64) crepBody501_13

def crepBody501_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 8#64

def crepBody501_16 : CrepProg (BitVec 64) :=
.seq crepBody501_14 crepBody501_15

def crepBody501_17 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
        Flapjack.CrepExp.const 152#64]))
  (Flapjack.CrepExp.var 19)) crepBody501_16 crepBody501_12

def crepBody501_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "extend_memory" [Flapjack.CrepExp.var 16]

def crepBody501_19 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody501_18

def crepBody501_20 : CrepProg (BitVec 64) :=
.seq crepBody501_17 crepBody501_19

def crepBody501_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "sat_word"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody501_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.load
                (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
              Flapjack.CrepExp.const 24#64]),
        Flapjack.CrepExp.var 20],
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.load
                (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
              Flapjack.CrepExp.const 144#64]),
        Flapjack.CrepExp.var 18],
    Flapjack.CrepExp.var 13]

def crepBody501_23 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody501_22

def crepBody501_24 : CrepProg (BitVec 64) :=
.seq crepBody501_21 crepBody501_23

def crepBody501_25 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody501_24

def crepBody501_26 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.const 0#64)) crepBody501_25 crepBody501_12

def crepBody501_27 : CrepProg (BitVec 64) :=
.seq crepBody501_20 crepBody501_26

def crepBody501_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody501_29 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody501_28

def crepBody501_30 : CrepProg (BitVec 64) :=
.seq crepBody501_27 crepBody501_29

def crepBody501_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody501_32 : CrepProg (BitVec 64) :=
.seq crepBody501_30 crepBody501_31

def crepBody501_33 : CrepProg (BitVec 64) :=
.seq crepBody501_10 crepBody501_32

def crepBody501_34 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody501_33

def crepBody501_35 : CrepProg (BitVec 64) :=
.seq crepBody501_9 crepBody501_34

def crepBody501_36 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody501_35

def crepBody501_37 : CrepProg (BitVec 64) :=
.seq crepBody501_8 crepBody501_36

def crepBody501_38 : CrepProg (BitVec 64) :=
.seq crepBody501_6 crepBody501_37

def crepBody501_39 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody501_38

def crepBody501_40 : CrepProg (BitVec 64) :=
.seq crepBody501_5 crepBody501_39

def crepBody501_41 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody501_40

def crepBody501_42 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody501_41

def crepBody501_43 : CrepProg (BitVec 64) :=
.seq crepBody501_4 crepBody501_42

def crepBody501_44 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody501_43

def crepBody501_45 : CrepProg (BitVec 64) :=
.seq crepBody501_3 crepBody501_44

def crepBody501_46 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody501_45

def crepBody501_47 : CrepProg (BitVec 64) :=
.seq crepBody501_2 crepBody501_46

def crepBody501_48 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody501_47

def crepBody501_49 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody501_48

def crepBody501_50 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody501_49

def crepBody501_51 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody501_50

def crepBody501_52 : CrepProg (BitVec 64) :=
.seq crepBody501_1 crepBody501_51

def crepBody501_53 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody501_52

def crepBody501_54 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody501_53

def crepBody501_55 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody501_54

def crepBody501_56 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody501_55

def crepBody501_57 : CrepProg (BitVec 64) :=
.seq crepBody501_0 crepBody501_56

def crepBody501_58 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody501_57

def crepBody501_59 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody501_58

def crepBody501_60 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody501_59

def crepBody501_61 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody501_60

def data501 : CrepProg (BitVec 64) := crepBody501_61
def output501 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [111#8, 112#8, 95#8, 114#8, 101#8, 116#8, 117#8, 114#8, 110#8, 100#8, 97#8, 116#8, 97#8, 99#8, 111#8, 112#8, 121#8], [], crepProgToHOL data501)
end InitECandidate.Proofs.FrontendStages.Crep
