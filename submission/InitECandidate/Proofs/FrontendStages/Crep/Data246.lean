import InitECandidate.Proofs.FrontendStages.Crep.Translate230
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody246_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "node_new_branch" []

def crepBody246_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.var 12)

def crepBody246_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody246_3 : CrepProg (BitVec 64) :=
.seq crepBody246_1 crepBody246_2

def crepBody246_4 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.var 8) crepBody246_3

def crepBody246_5 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 32#64,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.loadByte
          (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 5]),
        Flapjack.CrepExp.const 8#64]]) crepBody246_4

def crepBody246_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 1#64)) crepBody246_5 crepBody246_2

def crepBody246_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "node_new_ext"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 1#64],
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 1#64],
    Flapjack.CrepExp.var 8]

def crepBody246_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 12) (Flapjack.CrepExp.var 13)

def crepBody246_9 : CrepProg (BitVec 64) :=
.seq crepBody246_8 crepBody246_2

def crepBody246_10 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.var 11) crepBody246_9

def crepBody246_11 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 32#64,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.loadByte
          (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 5]),
        Flapjack.CrepExp.const 8#64]]) crepBody246_10

def crepBody246_12 : CrepProg (BitVec 64) :=
.seq crepBody246_7 crepBody246_11

def crepBody246_13 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody246_12

def crepBody246_14 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 1#64) (Flapjack.CrepExp.var 10)) crepBody246_13 crepBody246_2

def crepBody246_15 : CrepProg (BitVec 64) :=
.seq crepBody246_6 crepBody246_14

def crepBody246_16 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.var 3) crepBody246_9

def crepBody246_17 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 160#64]) crepBody246_16

def crepBody246_18 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.var 4) crepBody246_9

def crepBody246_19 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 168#64]) crepBody246_18

def crepBody246_20 : CrepProg (BitVec 64) :=
.seq crepBody246_17 crepBody246_19

def crepBody246_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "mpt_fail" [Flapjack.CrepExp.const 11#64]

def crepBody246_22 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody246_21

def crepBody246_23 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 32#64,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 8#64]]))
  (Flapjack.CrepExp.const 0#64)) crepBody246_22 crepBody246_2

def crepBody246_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "node_new_leaf"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 1#64],
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 1#64],
    Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody246_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 14) (Flapjack.CrepExp.var 15)

def crepBody246_26 : CrepProg (BitVec 64) :=
.seq crepBody246_25 crepBody246_2

def crepBody246_27 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.var 13) crepBody246_26

def crepBody246_28 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 32#64,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 8#64]]) crepBody246_27

def crepBody246_29 : CrepProg (BitVec 64) :=
.seq crepBody246_24 crepBody246_28

def crepBody246_30 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody246_29

def crepBody246_31 : CrepProg (BitVec 64) :=
.seq crepBody246_23 crepBody246_30

def crepBody246_32 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.loadByte (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 5])) crepBody246_31

def crepBody246_33 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.const 0#64)) crepBody246_20 crepBody246_32

def crepBody246_34 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 9]

def crepBody246_35 : CrepProg (BitVec 64) :=
.seq crepBody246_33 crepBody246_34

def crepBody246_36 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 5]) crepBody246_35

def crepBody246_37 : CrepProg (BitVec 64) :=
.seq crepBody246_15 crepBody246_36

def crepBody246_38 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 5]) crepBody246_37

def crepBody246_39 : CrepProg (BitVec 64) :=
.seq crepBody246_0 crepBody246_38

def crepBody246_40 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody246_39

def crepBody246_41 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64])) crepBody246_40

def crepBody246_42 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 40#64])) crepBody246_41

def crepBody246_43 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64])) crepBody246_42

def data246 : CrepProg (BitVec 64) := crepBody246_43
def output246 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [95#8, 115#8, 112#8, 108#8, 105#8, 116#8, 95#8, 101#8, 120#8, 116#8, 101#8, 110#8, 115#8, 105#8, 111#8, 110#8], [0, 1, 2, 3, 4, 5], crepProgToHOL data246)
end InitECandidate.Proofs.FrontendStages.Crep
