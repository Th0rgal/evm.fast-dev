import InitECandidate.Proofs.FrontendStages.Crep.Translate476
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody492_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3, 4, 5, 6], none)) "stack_pop" []

def crepBody492_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7, 8, 9, 10], none)) "stack_pop" []

def crepBody492_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11, 12, 13, 14], none)) "stack_pop" []

def crepBody492_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "sat_word"
  [Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14]

def crepBody492_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "words_of" [Flapjack.CrepExp.var 15]

def crepBody492_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17, 18], none)) "extend_memory_cost1"
  [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14]

def crepBody492_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "add_sat"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 0,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 3#64, Flapjack.CrepExp.var 16]],
    Flapjack.CrepExp.var 17]

def crepBody492_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "charge_gas" [Flapjack.CrepExp.var 19]

def crepBody492_8 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody492_7

def crepBody492_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "extend_memory" [Flapjack.CrepExp.var 18]

def crepBody492_10 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody492_9

def crepBody492_11 : CrepProg (BitVec 64) :=
.seq crepBody492_8 crepBody492_10

def crepBody492_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "sat_word"
  [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6]

def crepBody492_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "sat_word"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10]

def crepBody492_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "buffer_read"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 21, Flapjack.CrepExp.var 15,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.load
                (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
              Flapjack.CrepExp.const 24#64]),
        Flapjack.CrepExp.var 20]]

def crepBody492_15 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody492_14

def crepBody492_16 : CrepProg (BitVec 64) :=
.seq crepBody492_13 crepBody492_15

def crepBody492_17 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody492_16

def crepBody492_18 : CrepProg (BitVec 64) :=
.seq crepBody492_12 crepBody492_17

def crepBody492_19 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody492_18

def crepBody492_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody492_21 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 15) (Flapjack.CrepExp.const 0#64)) crepBody492_19 crepBody492_20

def crepBody492_22 : CrepProg (BitVec 64) :=
.seq crepBody492_11 crepBody492_21

def crepBody492_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody492_24 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody492_23

def crepBody492_25 : CrepProg (BitVec 64) :=
.seq crepBody492_22 crepBody492_24

def crepBody492_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody492_27 : CrepProg (BitVec 64) :=
.seq crepBody492_25 crepBody492_26

def crepBody492_28 : CrepProg (BitVec 64) :=
.seq crepBody492_6 crepBody492_27

def crepBody492_29 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody492_28

def crepBody492_30 : CrepProg (BitVec 64) :=
.seq crepBody492_5 crepBody492_29

def crepBody492_31 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody492_30

def crepBody492_32 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody492_31

def crepBody492_33 : CrepProg (BitVec 64) :=
.seq crepBody492_4 crepBody492_32

def crepBody492_34 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody492_33

def crepBody492_35 : CrepProg (BitVec 64) :=
.seq crepBody492_3 crepBody492_34

def crepBody492_36 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody492_35

def crepBody492_37 : CrepProg (BitVec 64) :=
.seq crepBody492_2 crepBody492_36

def crepBody492_38 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody492_37

def crepBody492_39 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody492_38

def crepBody492_40 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody492_39

def crepBody492_41 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody492_40

def crepBody492_42 : CrepProg (BitVec 64) :=
.seq crepBody492_1 crepBody492_41

def crepBody492_43 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody492_42

def crepBody492_44 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody492_43

def crepBody492_45 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody492_44

def crepBody492_46 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody492_45

def crepBody492_47 : CrepProg (BitVec 64) :=
.seq crepBody492_0 crepBody492_46

def crepBody492_48 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody492_47

def crepBody492_49 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody492_48

def crepBody492_50 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody492_49

def crepBody492_51 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody492_50

def data492 : CrepProg (BitVec 64) := crepBody492_51
def output492 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [99#8, 111#8, 112#8, 121#8, 95#8, 102#8, 114#8, 111#8, 109#8, 95#8, 98#8, 117#8, 102#8, 102#8, 101#8, 114#8], [0, 1, 2], crepProgToHOL data492)
end InitECandidate.Proofs.FrontendStages.Crep
