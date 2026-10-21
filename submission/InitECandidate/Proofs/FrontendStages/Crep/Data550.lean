import InitECandidate.Proofs.FrontendStages.Crep.Translate534
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody550_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "require_not_static" []

def crepBody550_1 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody550_0

def crepBody550_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3, 4], none)) "stack_pop" []

def crepBody550_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6, 7, 8], none)) "stack_pop" []

def crepBody550_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9, 10, 11, 12], none)) "stack_pop" []

def crepBody550_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13, 14, 15, 16], none)) "stack_pop" []

def crepBody550_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "sat_word"
  [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12]

def crepBody550_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18, 19], none)) "extend_memory_cost1"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8,
    Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12]

def crepBody550_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "words_of" [Flapjack.CrepExp.var 17]

def crepBody550_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "add_sat"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.const 12000#64,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 6#64, Flapjack.CrepExp.var 20],
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 20]],
    Flapjack.CrepExp.var 18]

def crepBody550_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "charge_gas" [Flapjack.CrepExp.var 21]

def crepBody550_11 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody550_10

def crepBody550_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody550_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23], none)) "u256_to_be32"
  [Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16,
    Flapjack.CrepExp.var 22]

def crepBody550_14 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody550_13

def crepBody550_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23], none)) "extend_memory" [Flapjack.CrepExp.var 19]

def crepBody550_16 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody550_15

def crepBody550_17 : CrepProg (BitVec 64) :=
.seq crepBody550_14 crepBody550_16

def crepBody550_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([24], none)) "sat_word"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody550_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([25], none)) "alloc" [Flapjack.CrepExp.const 24#64]

def crepBody550_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([26], none)) "compute_create2_contract_address"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 23, Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.var 22,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.load
                (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
              Flapjack.CrepExp.const 24#64]),
        Flapjack.CrepExp.var 24],
    Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 25]

def crepBody550_21 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.const 0#64) crepBody550_20

def crepBody550_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([26], none)) "generic_create"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.var 25, Flapjack.CrepExp.var 24, Flapjack.CrepExp.var 17]

def crepBody550_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody550_24 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody550_23

def crepBody550_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody550_26 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 26) (Flapjack.CrepExp.const 0#64)) crepBody550_24 crepBody550_25

def crepBody550_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody550_28 : CrepProg (BitVec 64) :=
.seq crepBody550_26 crepBody550_27

def crepBody550_29 : CrepProg (BitVec 64) :=
.seq crepBody550_22 crepBody550_28

def crepBody550_30 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.const 0#64) crepBody550_29

def crepBody550_31 : CrepProg (BitVec 64) :=
.seq crepBody550_21 crepBody550_30

def crepBody550_32 : CrepProg (BitVec 64) :=
.seq crepBody550_19 crepBody550_31

def crepBody550_33 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.const 0#64) crepBody550_32

def crepBody550_34 : CrepProg (BitVec 64) :=
.seq crepBody550_18 crepBody550_33

def crepBody550_35 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody550_34

def crepBody550_36 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 112#64])) crepBody550_35

def crepBody550_37 : CrepProg (BitVec 64) :=
.seq crepBody550_17 crepBody550_36

def crepBody550_38 : CrepProg (BitVec 64) :=
.seq crepBody550_12 crepBody550_37

def crepBody550_39 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody550_38

def crepBody550_40 : CrepProg (BitVec 64) :=
.seq crepBody550_11 crepBody550_39

def crepBody550_41 : CrepProg (BitVec 64) :=
.seq crepBody550_9 crepBody550_40

def crepBody550_42 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody550_41

def crepBody550_43 : CrepProg (BitVec 64) :=
.seq crepBody550_8 crepBody550_42

def crepBody550_44 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody550_43

def crepBody550_45 : CrepProg (BitVec 64) :=
.seq crepBody550_7 crepBody550_44

def crepBody550_46 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody550_45

def crepBody550_47 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody550_46

def crepBody550_48 : CrepProg (BitVec 64) :=
.seq crepBody550_6 crepBody550_47

def crepBody550_49 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody550_48

def crepBody550_50 : CrepProg (BitVec 64) :=
.seq crepBody550_5 crepBody550_49

def crepBody550_51 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody550_50

def crepBody550_52 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody550_51

def crepBody550_53 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody550_52

def crepBody550_54 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody550_53

def crepBody550_55 : CrepProg (BitVec 64) :=
.seq crepBody550_4 crepBody550_54

def crepBody550_56 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody550_55

def crepBody550_57 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody550_56

def crepBody550_58 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody550_57

def crepBody550_59 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody550_58

def crepBody550_60 : CrepProg (BitVec 64) :=
.seq crepBody550_3 crepBody550_59

def crepBody550_61 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody550_60

def crepBody550_62 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody550_61

def crepBody550_63 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody550_62

def crepBody550_64 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody550_63

def crepBody550_65 : CrepProg (BitVec 64) :=
.seq crepBody550_2 crepBody550_64

def crepBody550_66 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody550_65

def crepBody550_67 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody550_66

def crepBody550_68 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody550_67

def crepBody550_69 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody550_68

def crepBody550_70 : CrepProg (BitVec 64) :=
.seq crepBody550_1 crepBody550_69

def data550 : CrepProg (BitVec 64) := crepBody550_70
def output550 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 99#8, 114#8, 101#8, 97#8, 116#8, 101#8, 50#8], [], crepProgToHOL data550)
end InitECandidate.Proofs.FrontendStages.Crep
