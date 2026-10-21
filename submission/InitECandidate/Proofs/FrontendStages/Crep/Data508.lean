import InitECandidate.Proofs.FrontendStages.Crep.Translate492
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody508_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3, 4], none)) "stack_pop" []

def crepBody508_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "charge_gas" [Flapjack.CrepExp.const 20#64]

def crepBody508_2 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody508_1

def crepBody508_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "block_env" []

def crepBody508_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "sat_word"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody508_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "stack_push"
  [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64]

def crepBody508_6 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody508_5

def crepBody508_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody508_8 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody508_7

def crepBody508_9 : CrepProg (BitVec 64) :=
.seq crepBody508_6 crepBody508_8

def crepBody508_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody508_11 : CrepProg (BitVec 64) :=
.seq crepBody508_9 crepBody508_10

def crepBody508_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody508_13 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.var 6),
      Flapjack.CrepExp.cmp Flapjack.Cmp.lower
        (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 256#64])
        (Flapjack.CrepExp.var 6),
      Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 7)
        (Flapjack.CrepExp.const 18446744073709551615#64)])) crepBody508_11 crepBody508_12

def crepBody508_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 10)

def crepBody508_15 : CrepProg (BitVec 64) :=
.seq crepBody508_14 crepBody508_12

def crepBody508_16 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 50#64) crepBody508_15

def crepBody508_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 4#64

def crepBody508_18 : CrepProg (BitVec 64) :=
.seq crepBody508_16 crepBody508_17

def crepBody508_19 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.var 8)) crepBody508_18 crepBody508_12

def crepBody508_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10, 11, 12, 13], none)) "u256_from_be"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 16#64]),
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
          [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 8],
            Flapjack.CrepExp.const 32#64]],
    Flapjack.CrepExp.const 32#64]

def crepBody508_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "track_ancestor_access" [Flapjack.CrepExp.var 8]

def crepBody508_22 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody508_21

def crepBody508_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "stack_push"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13]

def crepBody508_24 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody508_23

def crepBody508_25 : CrepProg (BitVec 64) :=
.seq crepBody508_22 crepBody508_24

def crepBody508_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody508_27 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody508_26

def crepBody508_28 : CrepProg (BitVec 64) :=
.seq crepBody508_25 crepBody508_27

def crepBody508_29 : CrepProg (BitVec 64) :=
.seq crepBody508_28 crepBody508_10

def crepBody508_30 : CrepProg (BitVec 64) :=
.seq crepBody508_20 crepBody508_29

def crepBody508_31 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody508_30

def crepBody508_32 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody508_31

def crepBody508_33 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody508_32

def crepBody508_34 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody508_33

def crepBody508_35 : CrepProg (BitVec 64) :=
.seq crepBody508_19 crepBody508_34

def crepBody508_36 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 24#64])) crepBody508_35

def crepBody508_37 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7]) crepBody508_36

def crepBody508_38 : CrepProg (BitVec 64) :=
.seq crepBody508_13 crepBody508_37

def crepBody508_39 : CrepProg (BitVec 64) :=
.seq crepBody508_4 crepBody508_38

def crepBody508_40 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody508_39

def crepBody508_41 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 40#64])) crepBody508_40

def crepBody508_42 : CrepProg (BitVec 64) :=
.seq crepBody508_3 crepBody508_41

def crepBody508_43 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody508_42

def crepBody508_44 : CrepProg (BitVec 64) :=
.seq crepBody508_2 crepBody508_43

def crepBody508_45 : CrepProg (BitVec 64) :=
.seq crepBody508_0 crepBody508_44

def crepBody508_46 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody508_45

def crepBody508_47 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody508_46

def crepBody508_48 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody508_47

def crepBody508_49 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody508_48

def data508 : CrepProg (BitVec 64) := crepBody508_49
def output508 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [111#8, 112#8, 95#8, 98#8, 108#8, 111#8, 99#8, 107#8, 104#8, 97#8, 115#8, 104#8], [], crepProgToHOL data508)
end InitECandidate.Proofs.FrontendStages.Crep
