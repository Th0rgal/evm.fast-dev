import InitECandidate.Proofs.FrontendStages.Crep.Translate439
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody455_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3, 4], none)) "stack_pop" []

def crepBody455_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6, 7, 8], none)) "stack_pop" []

def crepBody455_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "sat_word"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody455_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "words_of" [Flapjack.CrepExp.var 9]

def crepBody455_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11, 12], none)) "extend_memory_cost1"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody455_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "add_sat"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.const 30#64,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 6#64, Flapjack.CrepExp.var 10]],
    Flapjack.CrepExp.var 11]

def crepBody455_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "charge_gas" [Flapjack.CrepExp.var 13]

def crepBody455_7 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody455_6

def crepBody455_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "extend_memory" [Flapjack.CrepExp.var 12]

def crepBody455_9 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody455_8

def crepBody455_10 : CrepProg (BitVec 64) :=
.seq crepBody455_7 crepBody455_9

def crepBody455_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "heap_mark" []

def crepBody455_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody455_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "sat_word"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody455_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "keccak256"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.load
                (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
              Flapjack.CrepExp.const 24#64]),
        Flapjack.CrepExp.var 16],
    Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 15]

def crepBody455_15 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody455_14

def crepBody455_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17, 18, 19, 20], none)) "u256_from_be"
  [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 32#64]

def crepBody455_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "heap_release" [Flapjack.CrepExp.var 14]

def crepBody455_18 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody455_17

def crepBody455_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "stack_push"
  [Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20]

def crepBody455_20 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody455_19

def crepBody455_21 : CrepProg (BitVec 64) :=
.seq crepBody455_18 crepBody455_20

def crepBody455_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody455_23 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody455_22

def crepBody455_24 : CrepProg (BitVec 64) :=
.seq crepBody455_21 crepBody455_23

def crepBody455_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody455_26 : CrepProg (BitVec 64) :=
.seq crepBody455_24 crepBody455_25

def crepBody455_27 : CrepProg (BitVec 64) :=
.seq crepBody455_16 crepBody455_26

def crepBody455_28 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody455_27

def crepBody455_29 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody455_28

def crepBody455_30 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody455_29

def crepBody455_31 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody455_30

def crepBody455_32 : CrepProg (BitVec 64) :=
.seq crepBody455_15 crepBody455_31

def crepBody455_33 : CrepProg (BitVec 64) :=
.seq crepBody455_13 crepBody455_32

def crepBody455_34 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody455_33

def crepBody455_35 : CrepProg (BitVec 64) :=
.seq crepBody455_12 crepBody455_34

def crepBody455_36 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody455_35

def crepBody455_37 : CrepProg (BitVec 64) :=
.seq crepBody455_11 crepBody455_36

def crepBody455_38 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody455_37

def crepBody455_39 : CrepProg (BitVec 64) :=
.seq crepBody455_10 crepBody455_38

def crepBody455_40 : CrepProg (BitVec 64) :=
.seq crepBody455_5 crepBody455_39

def crepBody455_41 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody455_40

def crepBody455_42 : CrepProg (BitVec 64) :=
.seq crepBody455_4 crepBody455_41

def crepBody455_43 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody455_42

def crepBody455_44 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody455_43

def crepBody455_45 : CrepProg (BitVec 64) :=
.seq crepBody455_3 crepBody455_44

def crepBody455_46 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody455_45

def crepBody455_47 : CrepProg (BitVec 64) :=
.seq crepBody455_2 crepBody455_46

def crepBody455_48 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody455_47

def crepBody455_49 : CrepProg (BitVec 64) :=
.seq crepBody455_1 crepBody455_48

def crepBody455_50 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody455_49

def crepBody455_51 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody455_50

def crepBody455_52 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody455_51

def crepBody455_53 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody455_52

def crepBody455_54 : CrepProg (BitVec 64) :=
.seq crepBody455_0 crepBody455_53

def crepBody455_55 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody455_54

def crepBody455_56 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody455_55

def crepBody455_57 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody455_56

def crepBody455_58 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody455_57

def data455 : CrepProg (BitVec 64) := crepBody455_58
def output455 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 107#8, 101#8, 99#8, 99#8, 97#8, 107#8], [], crepProgToHOL data455)
end InitECandidate.Proofs.FrontendStages.Crep
