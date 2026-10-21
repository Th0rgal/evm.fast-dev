import InitECandidate.Proofs.FrontendStages.Crep.Translate533
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody549_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "require_not_static" []

def crepBody549_1 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody549_0

def crepBody549_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3, 4], none)) "stack_pop" []

def crepBody549_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6, 7, 8], none)) "stack_pop" []

def crepBody549_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9, 10, 11, 12], none)) "stack_pop" []

def crepBody549_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "sat_word"
  [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12]

def crepBody549_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14, 15], none)) "extend_memory_cost1"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8,
    Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12]

def crepBody549_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "words_of" [Flapjack.CrepExp.var 13]

def crepBody549_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "add_sat"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.const 12000#64,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 16]],
    Flapjack.CrepExp.var 14]

def crepBody549_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "charge_gas" [Flapjack.CrepExp.var 17]

def crepBody549_10 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody549_9

def crepBody549_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "extend_memory" [Flapjack.CrepExp.var 15]

def crepBody549_12 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody549_11

def crepBody549_13 : CrepProg (BitVec 64) :=
.seq crepBody549_10 crepBody549_12

def crepBody549_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "get_account"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 32#64])]

def crepBody549_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "alloc" [Flapjack.CrepExp.const 24#64]

def crepBody549_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "compute_contract_address"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 19, Flapjack.CrepExp.const 0#64]),
    Flapjack.CrepExp.var 20]

def crepBody549_17 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody549_16

def crepBody549_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "sat_word"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody549_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "generic_create"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 21, Flapjack.CrepExp.var 13]

def crepBody549_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody549_21 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody549_20

def crepBody549_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody549_23 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 22) (Flapjack.CrepExp.const 0#64)) crepBody549_21 crepBody549_22

def crepBody549_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody549_25 : CrepProg (BitVec 64) :=
.seq crepBody549_23 crepBody549_24

def crepBody549_26 : CrepProg (BitVec 64) :=
.seq crepBody549_19 crepBody549_25

def crepBody549_27 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody549_26

def crepBody549_28 : CrepProg (BitVec 64) :=
.seq crepBody549_18 crepBody549_27

def crepBody549_29 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody549_28

def crepBody549_30 : CrepProg (BitVec 64) :=
.seq crepBody549_17 crepBody549_29

def crepBody549_31 : CrepProg (BitVec 64) :=
.seq crepBody549_15 crepBody549_30

def crepBody549_32 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody549_31

def crepBody549_33 : CrepProg (BitVec 64) :=
.seq crepBody549_14 crepBody549_32

def crepBody549_34 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody549_33

def crepBody549_35 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 112#64])) crepBody549_34

def crepBody549_36 : CrepProg (BitVec 64) :=
.seq crepBody549_13 crepBody549_35

def crepBody549_37 : CrepProg (BitVec 64) :=
.seq crepBody549_8 crepBody549_36

def crepBody549_38 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody549_37

def crepBody549_39 : CrepProg (BitVec 64) :=
.seq crepBody549_7 crepBody549_38

def crepBody549_40 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody549_39

def crepBody549_41 : CrepProg (BitVec 64) :=
.seq crepBody549_6 crepBody549_40

def crepBody549_42 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody549_41

def crepBody549_43 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody549_42

def crepBody549_44 : CrepProg (BitVec 64) :=
.seq crepBody549_5 crepBody549_43

def crepBody549_45 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody549_44

def crepBody549_46 : CrepProg (BitVec 64) :=
.seq crepBody549_4 crepBody549_45

def crepBody549_47 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody549_46

def crepBody549_48 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody549_47

def crepBody549_49 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody549_48

def crepBody549_50 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody549_49

def crepBody549_51 : CrepProg (BitVec 64) :=
.seq crepBody549_3 crepBody549_50

def crepBody549_52 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody549_51

def crepBody549_53 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody549_52

def crepBody549_54 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody549_53

def crepBody549_55 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody549_54

def crepBody549_56 : CrepProg (BitVec 64) :=
.seq crepBody549_2 crepBody549_55

def crepBody549_57 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody549_56

def crepBody549_58 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody549_57

def crepBody549_59 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody549_58

def crepBody549_60 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody549_59

def crepBody549_61 : CrepProg (BitVec 64) :=
.seq crepBody549_1 crepBody549_60

def data549 : CrepProg (BitVec 64) := crepBody549_61
def output549 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 99#8, 114#8, 101#8, 97#8, 116#8, 101#8], [], crepProgToHOL data549)
end InitECandidate.Proofs.FrontendStages.Crep
