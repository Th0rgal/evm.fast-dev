import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify843
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body859_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body859_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "fb"
  (Flapjack.Exp.loadByte
    (Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "txs",
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64]])))

def body859_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body859_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 0#64)) body859_1 body859_2

def body859_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "el"), none)) "rlp_bytes_encoded_len"
  [Flapjack.Exp.var Flapjack.VarKind.local "fb", Flapjack.Exp.var Flapjack.VarKind.local "n"]

def body859_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "fb") (Flapjack.Exp.const 192#64)])) body859_4 body859_2

def body859_6 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "tl"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "tl", Flapjack.Exp.var Flapjack.VarKind.local "el"])

def body859_7 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body859_8 : Prog (BitVec 64) :=
.seq body859_6 body859_7

def body859_9 : Prog (BitVec 64) :=
.seq body859_5 body859_8

def body859_10 : Prog (BitVec 64) :=
.dec ("el") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "n") body859_9

def body859_11 : Prog (BitVec 64) :=
.seq body859_3 body859_10

def body859_12 : Prog (BitVec 64) :=
.dec ("fb") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body859_11

def body859_13 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "txs",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64],
      Flapjack.Exp.const 8#64])) body859_12

def body859_14 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "ntx")) body859_13

def body859_15 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "total"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "total", Flapjack.Exp.var Flapjack.VarKind.local "hl",
      Flapjack.Exp.var Flapjack.VarKind.local "tl"])

def body859_16 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "total"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "total", Flapjack.Exp.const 1#64])

def body859_17 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i" (Flapjack.Exp.const 0#64)

def body859_18 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "wl"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "wl", Flapjack.Exp.var Flapjack.VarKind.local "wlen"])

def body859_19 : Prog (BitVec 64) :=
.seq body859_18 body859_7

def body859_20 : Prog (BitVec 64) :=
.decCall ("wlen") (Flapjack.Shape.one) ("withdrawal_rlp_len") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 48#64]),
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 44#64]]]) body859_19

def body859_21 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "nwd")) body859_20

def body859_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "hl"), none)) "rlp_list_header_len"
  [Flapjack.Exp.var Flapjack.VarKind.local "wl"]

def body859_23 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "total"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "total", Flapjack.Exp.var Flapjack.VarKind.local "hl",
      Flapjack.Exp.var Flapjack.VarKind.local "wl"])

def body859_24 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "hl"), none)) "rlp_list_header_len"
  [Flapjack.Exp.var Flapjack.VarKind.local "total"]

def body859_25 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "total", Flapjack.Exp.var Flapjack.VarKind.local "hl"])

def body859_26 : Prog (BitVec 64) :=
.seq body859_24 body859_25

def body859_27 : Prog (BitVec 64) :=
.seq body859_23 body859_26

def body859_28 : Prog (BitVec 64) :=
.seq body859_22 body859_27

def body859_29 : Prog (BitVec 64) :=
.seq body859_21 body859_28

def body859_30 : Prog (BitVec 64) :=
.seq body859_17 body859_29

def body859_31 : Prog (BitVec 64) :=
.dec ("wl") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body859_30

def body859_32 : Prog (BitVec 64) :=
.dec ("nwd") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 56#64])) body859_31

def body859_33 : Prog (BitVec 64) :=
.seq body859_16 body859_32

def body859_34 : Prog (BitVec 64) :=
.seq body859_15 body859_33

def body859_35 : Prog (BitVec 64) :=
.decCall ("hl") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.var Flapjack.VarKind.local "tl"]) body859_34

def body859_36 : Prog (BitVec 64) :=
.seq body859_14 body859_35

def body859_37 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body859_36

def body859_38 : Prog (BitVec 64) :=
.dec ("tl") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body859_37

def body859_39 : Prog (BitVec 64) :=
.dec ("ntx") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 40#64])) body859_38

def body859_40 : Prog (BitVec 64) :=
.dec ("txs") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 32#64])) body859_39

def body859_41 : Prog (BitVec 64) :=
.dec ("total") (Flapjack.Shape.one) (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "he")) body859_40

def body859_42 : Prog (BitVec 64) :=
.seq body859_0 body859_41

def body859_43 : Prog (BitVec 64) :=
.decCall ("he") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("encode_header") ([Flapjack.Exp.var Flapjack.VarKind.local "hdr"]) body859_42

def body859_44 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body859_43

def body859_45 : Prog (BitVec 64) :=
.seq body859_5 body859_6

def body859_46 : Prog (BitVec 64) :=
.seq body859_45 body859_7

def body859_47 : Prog (BitVec 64) :=
.dec ("el") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "n") body859_46

def body859_48 : Prog (BitVec 64) :=
.seq body859_3 body859_47

def body859_49 : Prog (BitVec 64) :=
.dec ("fb") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body859_48

def body859_50 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "txs",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64],
      Flapjack.Exp.const 8#64])) body859_49

def body859_51 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "ntx")) body859_50

def body859_52 : Prog (BitVec 64) :=
.seq body859_15 body859_16

def body859_53 : Prog (BitVec 64) :=
.seq body859_17 body859_21

def body859_54 : Prog (BitVec 64) :=
.seq body859_53 body859_22

def body859_55 : Prog (BitVec 64) :=
.seq body859_54 body859_23

def body859_56 : Prog (BitVec 64) :=
.seq body859_55 body859_24

def body859_57 : Prog (BitVec 64) :=
.seq body859_56 body859_25

def body859_58 : Prog (BitVec 64) :=
.dec ("wl") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body859_57

def body859_59 : Prog (BitVec 64) :=
.dec ("nwd") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 56#64])) body859_58

def body859_60 : Prog (BitVec 64) :=
.seq body859_52 body859_59

def body859_61 : Prog (BitVec 64) :=
.decCall ("hl") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.var Flapjack.VarKind.local "tl"]) body859_60

def body859_62 : Prog (BitVec 64) :=
.seq body859_51 body859_61

def body859_63 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body859_62

def body859_64 : Prog (BitVec 64) :=
.dec ("tl") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body859_63

def body859_65 : Prog (BitVec 64) :=
.dec ("ntx") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 40#64])) body859_64

def body859_66 : Prog (BitVec 64) :=
.dec ("txs") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 32#64])) body859_65

def body859_67 : Prog (BitVec 64) :=
.dec ("total") (Flapjack.Shape.one) (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "he")) body859_66

def body859_68 : Prog (BitVec 64) :=
.seq body859_0 body859_67

def body859_69 : Prog (BitVec 64) :=
.decCall ("he") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("encode_header") ([Flapjack.Exp.var Flapjack.VarKind.local "hdr"]) body859_68

def body859_70 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body859_69

def originalData859 : Decl (BitVec 64) :=
.function { name := "block_rlp_length", inline := false, exported := false, params := [("hdr", Flapjack.Shape.one), ("pl", Flapjack.Shape.one)], body := body859_44, returnShape := (Flapjack.Shape.one) }
def simplifiedData859 : Decl (BitVec 64) :=
.function { name := "block_rlp_length", inline := false, exported := false, params := [("hdr", Flapjack.Shape.one), ("pl", Flapjack.Shape.one)], body := body859_70, returnShape := (Flapjack.Shape.one) }
def original859 := Pancake.PanLang.declToHOL originalData859
def simplified859 := Pancake.PanLang.declToHOL simplifiedData859
end InitECandidate.Proofs.FrontendStages.Declarations
