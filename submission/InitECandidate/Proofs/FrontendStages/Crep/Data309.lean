import InitECandidate.Proofs.FrontendStages.Crep.Translate293
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody309_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.const 1#64,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64])]

def crepBody309_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody309_2 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody309_0 crepBody309_1

def crepBody309_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "u256_fits_word"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody309_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64]

def crepBody309_5 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 27#64),
      Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 28#64)])) crepBody309_4 crepBody309_1

def crepBody309_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 6)

def crepBody309_7 : CrepProg (BitVec 64) :=
.seq crepBody309_6 crepBody309_1

def crepBody309_8 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 44#64) crepBody309_7

def crepBody309_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 6#64

def crepBody309_10 : CrepProg (BitVec 64) :=
.seq crepBody309_8 crepBody309_9

def crepBody309_11 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 35#64)) crepBody309_10 crepBody309_1

def crepBody309_12 : CrepProg (BitVec 64) :=
.seq crepBody309_5 crepBody309_11

def crepBody309_13 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64)) crepBody309_12 crepBody309_1

def crepBody309_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6, 7, 8, 9], none)) "u256_sub"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.const 35#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64]

def crepBody309_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10, 11, 12, 13], none)) "u256_shr"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9,
    Flapjack.CrepExp.const 1#64]

def crepBody309_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "u256_fits_word"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13]

def crepBody309_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 14)

def crepBody309_18 : CrepProg (BitVec 64) :=
.seq crepBody309_17 crepBody309_1

def crepBody309_19 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 45#64) crepBody309_18

def crepBody309_20 : CrepProg (BitVec 64) :=
.seq crepBody309_19 crepBody309_9

def crepBody309_21 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64)) crepBody309_20 crepBody309_1

def crepBody309_22 : CrepProg (BitVec 64) :=
.seq crepBody309_16 crepBody309_21

def crepBody309_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.var 10]

def crepBody309_24 : CrepProg (BitVec 64) :=
.seq crepBody309_22 crepBody309_23

def crepBody309_25 : CrepProg (BitVec 64) :=
.seq crepBody309_15 crepBody309_24

def crepBody309_26 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody309_25

def crepBody309_27 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody309_26

def crepBody309_28 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody309_27

def crepBody309_29 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody309_28

def crepBody309_30 : CrepProg (BitVec 64) :=
.seq crepBody309_14 crepBody309_29

def crepBody309_31 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody309_30

def crepBody309_32 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody309_31

def crepBody309_33 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody309_32

def crepBody309_34 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody309_33

def crepBody309_35 : CrepProg (BitVec 64) :=
.seq crepBody309_13 crepBody309_34

def crepBody309_36 : CrepProg (BitVec 64) :=
.seq crepBody309_3 crepBody309_35

def crepBody309_37 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody309_36

def crepBody309_38 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 288#64],
      Flapjack.CrepExp.const 24#64])) crepBody309_37

def crepBody309_39 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 288#64],
      Flapjack.CrepExp.const 16#64])) crepBody309_38

def crepBody309_40 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 288#64],
      Flapjack.CrepExp.const 8#64])) crepBody309_39

def crepBody309_41 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 288#64])) crepBody309_40

def crepBody309_42 : CrepProg (BitVec 64) :=
.seq crepBody309_2 crepBody309_41

def data309 : CrepProg (BitVec 64) := crepBody309_42
def output309 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 99#8, 104#8, 97#8, 105#8, 110#8, 95#8, 105#8, 100#8], [0], crepProgToHOL data309)
end InitECandidate.Proofs.FrontendStages.Crep
