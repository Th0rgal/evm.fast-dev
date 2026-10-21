import InitECandidate.Proofs.FrontendStages.Crep.Translate643
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody659_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "is_zero_bytes" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 16#64]

def crepBody659_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody659_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody659_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody659_1 crepBody659_2

def crepBody659_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3, 4, 5, 6, 7, 8], none)) "bls_fp_from_be48"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 16#64]]

def crepBody659_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "bls_fp_lt_raw"
  [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 13402431016077863595#64,
    Flapjack.CrepExp.const 2210141511517208575#64, Flapjack.CrepExp.const 7435674573564081700#64,
    Flapjack.CrepExp.const 7239337960414712511#64, Flapjack.CrepExp.const 5412103778470702295#64,
    Flapjack.CrepExp.const 1873798617647539866#64]

def crepBody659_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.const 0#64)) crepBody659_1 crepBody659_2

def crepBody659_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10, 11, 12, 13, 14, 15], none)) "bls_fp_to_mont"
  [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody659_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 16) (Flapjack.CrepExp.var 17)

def crepBody659_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 16, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 18)

def crepBody659_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 16, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 19)

def crepBody659_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 16, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 20)

def crepBody659_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 16, Flapjack.CrepExp.const 32#64])
  (Flapjack.CrepExp.var 21)

def crepBody659_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 16, Flapjack.CrepExp.const 40#64])
  (Flapjack.CrepExp.var 22)

def crepBody659_14 : CrepProg (BitVec 64) :=
.seq crepBody659_13 crepBody659_2

def crepBody659_15 : CrepProg (BitVec 64) :=
.seq crepBody659_12 crepBody659_14

def crepBody659_16 : CrepProg (BitVec 64) :=
.seq crepBody659_11 crepBody659_15

def crepBody659_17 : CrepProg (BitVec 64) :=
.seq crepBody659_10 crepBody659_16

def crepBody659_18 : CrepProg (BitVec 64) :=
.seq crepBody659_9 crepBody659_17

def crepBody659_19 : CrepProg (BitVec 64) :=
.seq crepBody659_8 crepBody659_18

def crepBody659_20 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.var 15) crepBody659_19

def crepBody659_21 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.var 14) crepBody659_20

def crepBody659_22 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 13) crepBody659_21

def crepBody659_23 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.var 12) crepBody659_22

def crepBody659_24 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.var 11) crepBody659_23

def crepBody659_25 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.var 10) crepBody659_24

def crepBody659_26 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.var 1) crepBody659_25

def crepBody659_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1#64]

def crepBody659_28 : CrepProg (BitVec 64) :=
.seq crepBody659_26 crepBody659_27

def crepBody659_29 : CrepProg (BitVec 64) :=
.seq crepBody659_7 crepBody659_28

def crepBody659_30 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody659_29

def crepBody659_31 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody659_30

def crepBody659_32 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody659_31

def crepBody659_33 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody659_32

def crepBody659_34 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody659_33

def crepBody659_35 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody659_34

def crepBody659_36 : CrepProg (BitVec 64) :=
.seq crepBody659_6 crepBody659_35

def crepBody659_37 : CrepProg (BitVec 64) :=
.seq crepBody659_5 crepBody659_36

def crepBody659_38 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody659_37

def crepBody659_39 : CrepProg (BitVec 64) :=
.seq crepBody659_4 crepBody659_38

def crepBody659_40 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody659_39

def crepBody659_41 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody659_40

def crepBody659_42 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody659_41

def crepBody659_43 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody659_42

def crepBody659_44 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody659_43

def crepBody659_45 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody659_44

def crepBody659_46 : CrepProg (BitVec 64) :=
.seq crepBody659_3 crepBody659_45

def crepBody659_47 : CrepProg (BitVec 64) :=
.seq crepBody659_0 crepBody659_46

def crepBody659_48 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody659_47

def data659 : CrepProg (BitVec 64) := crepBody659_48
def output659 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [98#8, 108#8, 115#8, 95#8, 102#8, 112#8, 95#8, 100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 54#8, 52#8], [0, 1], crepProgToHOL data659)
end InitECandidate.Proofs.FrontendStages.Crep
