import InitECandidate.Proofs.FrontendStages.Crep.Translate450
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody466_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3, 4], none)) "stack_pop" []

def crepBody466_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6, 7, 8], none)) "stack_pop" []

def crepBody466_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9, 10, 11, 12], none)) "stack_pop" []

def crepBody466_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "sat_word"
  [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12]

def crepBody466_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "words_of" [Flapjack.CrepExp.var 13]

def crepBody466_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15, 16], none)) "extend_memory_cost2"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8,
    Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12,
    Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12]

def crepBody466_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "add_sat"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.const 3#64,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 3#64, Flapjack.CrepExp.var 14]],
    Flapjack.CrepExp.var 15]

def crepBody466_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "charge_gas" [Flapjack.CrepExp.var 17]

def crepBody466_8 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody466_7

def crepBody466_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "extend_memory" [Flapjack.CrepExp.var 16]

def crepBody466_10 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody466_9

def crepBody466_11 : CrepProg (BitVec 64) :=
.seq crepBody466_8 crepBody466_10

def crepBody466_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "sat_word"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody466_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "sat_word"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody466_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "heap_mark" []

def crepBody466_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "alloc" [Flapjack.CrepExp.var 13]

def crepBody466_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "memcpy"
  [Flapjack.CrepExp.var 21,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.load
                (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
              Flapjack.CrepExp.const 24#64]),
        Flapjack.CrepExp.var 19],
    Flapjack.CrepExp.var 13]

def crepBody466_17 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody466_16

def crepBody466_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.load
                (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
              Flapjack.CrepExp.const 24#64]),
        Flapjack.CrepExp.var 18],
    Flapjack.CrepExp.var 21, Flapjack.CrepExp.var 13]

def crepBody466_19 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody466_18

def crepBody466_20 : CrepProg (BitVec 64) :=
.seq crepBody466_17 crepBody466_19

def crepBody466_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "heap_release" [Flapjack.CrepExp.var 20]

def crepBody466_22 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody466_21

def crepBody466_23 : CrepProg (BitVec 64) :=
.seq crepBody466_20 crepBody466_22

def crepBody466_24 : CrepProg (BitVec 64) :=
.seq crepBody466_15 crepBody466_23

def crepBody466_25 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody466_24

def crepBody466_26 : CrepProg (BitVec 64) :=
.seq crepBody466_14 crepBody466_25

def crepBody466_27 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody466_26

def crepBody466_28 : CrepProg (BitVec 64) :=
.seq crepBody466_13 crepBody466_27

def crepBody466_29 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody466_28

def crepBody466_30 : CrepProg (BitVec 64) :=
.seq crepBody466_12 crepBody466_29

def crepBody466_31 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody466_30

def crepBody466_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody466_33 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.const 0#64)) crepBody466_31 crepBody466_32

def crepBody466_34 : CrepProg (BitVec 64) :=
.seq crepBody466_11 crepBody466_33

def crepBody466_35 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody466_36 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody466_35

def crepBody466_37 : CrepProg (BitVec 64) :=
.seq crepBody466_34 crepBody466_36

def crepBody466_38 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody466_39 : CrepProg (BitVec 64) :=
.seq crepBody466_37 crepBody466_38

def crepBody466_40 : CrepProg (BitVec 64) :=
.seq crepBody466_6 crepBody466_39

def crepBody466_41 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody466_40

def crepBody466_42 : CrepProg (BitVec 64) :=
.seq crepBody466_5 crepBody466_41

def crepBody466_43 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody466_42

def crepBody466_44 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody466_43

def crepBody466_45 : CrepProg (BitVec 64) :=
.seq crepBody466_4 crepBody466_44

def crepBody466_46 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody466_45

def crepBody466_47 : CrepProg (BitVec 64) :=
.seq crepBody466_3 crepBody466_46

def crepBody466_48 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody466_47

def crepBody466_49 : CrepProg (BitVec 64) :=
.seq crepBody466_2 crepBody466_48

def crepBody466_50 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody466_49

def crepBody466_51 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody466_50

def crepBody466_52 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody466_51

def crepBody466_53 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody466_52

def crepBody466_54 : CrepProg (BitVec 64) :=
.seq crepBody466_1 crepBody466_53

def crepBody466_55 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody466_54

def crepBody466_56 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody466_55

def crepBody466_57 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody466_56

def crepBody466_58 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody466_57

def crepBody466_59 : CrepProg (BitVec 64) :=
.seq crepBody466_0 crepBody466_58

def crepBody466_60 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody466_59

def crepBody466_61 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody466_60

def crepBody466_62 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody466_61

def crepBody466_63 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody466_62

def data466 : CrepProg (BitVec 64) := crepBody466_63
def output466 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 109#8, 99#8, 111#8, 112#8, 121#8], [], crepProgToHOL data466)
end InitECandidate.Proofs.FrontendStages.Crep
