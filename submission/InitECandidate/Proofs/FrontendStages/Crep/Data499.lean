import InitECandidate.Proofs.FrontendStages.Crep.Translate483
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody499_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3, 4], none)) "stack_pop" []

def crepBody499_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "to_address_masked"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody499_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6, 7, 8, 9], none)) "stack_pop" []

def crepBody499_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10, 11, 12, 13], none)) "stack_pop" []

def crepBody499_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14, 15, 16, 17], none)) "stack_pop" []

def crepBody499_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "sat_word"
  [Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17]

def crepBody499_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "words_of" [Flapjack.CrepExp.var 18]

def crepBody499_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20, 21], none)) "extend_memory_cost1"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9,
    Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17]

def crepBody499_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "access_gas_cost" [Flapjack.CrepExp.var 5]

def crepBody499_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23], none)) "add_sat"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 22, Flapjack.CrepExp.const 100#64,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 3#64, Flapjack.CrepExp.var 19]],
    Flapjack.CrepExp.var 20]

def crepBody499_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([24], none)) "charge_gas" [Flapjack.CrepExp.var 23]

def crepBody499_11 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody499_10

def crepBody499_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([24], none)) "warm_after_charge" [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 22]

def crepBody499_13 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody499_12

def crepBody499_14 : CrepProg (BitVec 64) :=
.seq crepBody499_11 crepBody499_13

def crepBody499_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([24], none)) "extend_memory" [Flapjack.CrepExp.var 21]

def crepBody499_16 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody499_15

def crepBody499_17 : CrepProg (BitVec 64) :=
.seq crepBody499_14 crepBody499_16

def crepBody499_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([24, 25], none)) "ext_code_of" [Flapjack.CrepExp.var 5]

def crepBody499_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([26], none)) "sat_word"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9]

def crepBody499_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "sat_word"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13]

def crepBody499_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([28], none)) "buffer_read"
  [Flapjack.CrepExp.var 24, Flapjack.CrepExp.var 25, Flapjack.CrepExp.var 27, Flapjack.CrepExp.var 18,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.load
                (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
              Flapjack.CrepExp.const 24#64]),
        Flapjack.CrepExp.var 26]]

def crepBody499_22 : CrepProg (BitVec 64) :=
.dec 28 (Flapjack.CrepExp.const 0#64) crepBody499_21

def crepBody499_23 : CrepProg (BitVec 64) :=
.seq crepBody499_20 crepBody499_22

def crepBody499_24 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody499_23

def crepBody499_25 : CrepProg (BitVec 64) :=
.seq crepBody499_19 crepBody499_24

def crepBody499_26 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.const 0#64) crepBody499_25

def crepBody499_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody499_28 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 18) (Flapjack.CrepExp.const 0#64)) crepBody499_26 crepBody499_27

def crepBody499_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([26], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody499_30 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.const 0#64) crepBody499_29

def crepBody499_31 : CrepProg (BitVec 64) :=
.seq crepBody499_28 crepBody499_30

def crepBody499_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody499_33 : CrepProg (BitVec 64) :=
.seq crepBody499_31 crepBody499_32

def crepBody499_34 : CrepProg (BitVec 64) :=
.seq crepBody499_18 crepBody499_33

def crepBody499_35 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.const 0#64) crepBody499_34

def crepBody499_36 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody499_35

def crepBody499_37 : CrepProg (BitVec 64) :=
.seq crepBody499_17 crepBody499_36

def crepBody499_38 : CrepProg (BitVec 64) :=
.seq crepBody499_9 crepBody499_37

def crepBody499_39 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody499_38

def crepBody499_40 : CrepProg (BitVec 64) :=
.seq crepBody499_8 crepBody499_39

def crepBody499_41 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody499_40

def crepBody499_42 : CrepProg (BitVec 64) :=
.seq crepBody499_7 crepBody499_41

def crepBody499_43 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody499_42

def crepBody499_44 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody499_43

def crepBody499_45 : CrepProg (BitVec 64) :=
.seq crepBody499_6 crepBody499_44

def crepBody499_46 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody499_45

def crepBody499_47 : CrepProg (BitVec 64) :=
.seq crepBody499_5 crepBody499_46

def crepBody499_48 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody499_47

def crepBody499_49 : CrepProg (BitVec 64) :=
.seq crepBody499_4 crepBody499_48

def crepBody499_50 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody499_49

def crepBody499_51 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody499_50

def crepBody499_52 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody499_51

def crepBody499_53 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody499_52

def crepBody499_54 : CrepProg (BitVec 64) :=
.seq crepBody499_3 crepBody499_53

def crepBody499_55 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody499_54

def crepBody499_56 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody499_55

def crepBody499_57 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody499_56

def crepBody499_58 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody499_57

def crepBody499_59 : CrepProg (BitVec 64) :=
.seq crepBody499_2 crepBody499_58

def crepBody499_60 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody499_59

def crepBody499_61 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody499_60

def crepBody499_62 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody499_61

def crepBody499_63 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody499_62

def crepBody499_64 : CrepProg (BitVec 64) :=
.seq crepBody499_1 crepBody499_63

def crepBody499_65 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody499_64

def crepBody499_66 : CrepProg (BitVec 64) :=
.seq crepBody499_0 crepBody499_65

def crepBody499_67 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody499_66

def crepBody499_68 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody499_67

def crepBody499_69 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody499_68

def crepBody499_70 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody499_69

def data499 : CrepProg (BitVec 64) := crepBody499_70
def output499 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [111#8, 112#8, 95#8, 101#8, 120#8, 116#8, 99#8, 111#8, 100#8, 101#8, 99#8, 111#8, 112#8, 121#8], [], crepProgToHOL data499)
end InitECandidate.Proofs.FrontendStages.Crep
