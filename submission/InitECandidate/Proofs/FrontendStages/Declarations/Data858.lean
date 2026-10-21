import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify842
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body858_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "zero32"), none)) "alloc" [Flapjack.Exp.const 32#64]

def body858_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.global "zero32", Flapjack.Exp.const 32#64]

def body858_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "precompile_addrs"), none)) "alloc"
  [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 18#64, Flapjack.Exp.const 20#64]]

def body858_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.global "precompile_addrs",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 18#64, Flapjack.Exp.const 20#64]]

def body858_4 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "precompile_addrs",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 20#64],
      Flapjack.Exp.const 19#64])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body858_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body858_6 : Prog (BitVec 64) :=
.seq body858_4 body858_5

def body858_7 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 17#64)) body858_6

def body858_8 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "precompile_addrs",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 17#64, Flapjack.Exp.const 20#64],
      Flapjack.Exp.const 18#64])
  (Flapjack.Exp.const 1#64)

def body858_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "beacon_roots_address"), none)) "alloc"
  [Flapjack.Exp.const 24#64]

def body858_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "addr_from_words"
  [Flapjack.Exp.var Flapjack.VarKind.global "beacon_roots_address", Flapjack.Exp.const 998902#64,
    Flapjack.Exp.const 15506597749690834871#64, Flapjack.Exp.const 13311379508201171970#64]

def body858_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "history_storage_address"), none)) "alloc"
  [Flapjack.Exp.const 24#64]

def body858_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "addr_from_words"
  [Flapjack.Exp.var Flapjack.VarKind.global "history_storage_address", Flapjack.Exp.const 63752#64,
    Flapjack.Exp.const 2878298490047003138#64, Flapjack.Exp.const 3700577164601600309#64]

def body858_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "withdrawal_request_address"), none)) "alloc"
  [Flapjack.Exp.const 24#64]

def body858_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "addr_from_words"
  [Flapjack.Exp.var Flapjack.VarKind.global "withdrawal_request_address", Flapjack.Exp.const 2401#64,
    Flapjack.Exp.const 17242047345525313946#64, Flapjack.Exp.const 15579492241104728066#64]

def body858_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "consolidation_request_address"), none)) "alloc"
  [Flapjack.Exp.const 24#64]

def body858_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "addr_from_words"
  [Flapjack.Exp.var Flapjack.VarKind.global "consolidation_request_address", Flapjack.Exp.const 48093#64,
    Flapjack.Exp.const 14397524800236640159#64, Flapjack.Exp.const 10016273463683084881#64]

def body858_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "builder_deposit_address"), none)) "alloc"
  [Flapjack.Exp.const 24#64]

def body858_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "addr_from_words"
  [Flapjack.Exp.var Flapjack.VarKind.global "builder_deposit_address", Flapjack.Exp.const 49140#64,
    Flapjack.Exp.const 7603452151126424148#64, Flapjack.Exp.const 760111669195932290#64]

def body858_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "builder_exit_address"), none)) "alloc"
  [Flapjack.Exp.const 24#64]

def body858_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "addr_from_words"
  [Flapjack.Exp.var Flapjack.VarKind.global "builder_exit_address", Flapjack.Exp.const 25814#64,
    Flapjack.Exp.const 8669529151676140297#64, Flapjack.Exp.const 4307224735379260034#64]

def body858_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "deposit_contract_address"), none)) "alloc"
  [Flapjack.Exp.const 24#64]

def body858_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "addr_from_words"
  [Flapjack.Exp.var Flapjack.VarKind.global "deposit_contract_address", Flapjack.Exp.const 0#64,
    Flapjack.Exp.const 2421447037043915651#64, Flapjack.Exp.const 11294470620239562234#64]

def body858_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "deposit_event_signature_hash"), none)) "alloc"
  [Flapjack.Exp.const 32#64]

def body858_24 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.global "deposit_event_signature_hash", Flapjack.Exp.const 0#64],
    Flapjack.Exp.const 7249595157780304706#64]

def body858_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.global "deposit_event_signature_hash", Flapjack.Exp.const 8#64],
    Flapjack.Exp.const 12676030261858484297#64]

def body858_26 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.global "deposit_event_signature_hash", Flapjack.Exp.const 16#64],
    Flapjack.Exp.const 16708898399860066458#64]

def body858_27 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.global "deposit_event_signature_hash", Flapjack.Exp.const 24#64],
    Flapjack.Exp.const 12074291595689605317#64]

def body858_28 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body858_29 : Prog (BitVec 64) :=
.seq body858_27 body858_28

def body858_30 : Prog (BitVec 64) :=
.seq body858_26 body858_29

def body858_31 : Prog (BitVec 64) :=
.seq body858_25 body858_30

def body858_32 : Prog (BitVec 64) :=
.seq body858_24 body858_31

def body858_33 : Prog (BitVec 64) :=
.seq body858_23 body858_32

def body858_34 : Prog (BitVec 64) :=
.seq body858_22 body858_33

def body858_35 : Prog (BitVec 64) :=
.seq body858_21 body858_34

def body858_36 : Prog (BitVec 64) :=
.seq body858_20 body858_35

def body858_37 : Prog (BitVec 64) :=
.seq body858_19 body858_36

def body858_38 : Prog (BitVec 64) :=
.seq body858_18 body858_37

def body858_39 : Prog (BitVec 64) :=
.seq body858_17 body858_38

def body858_40 : Prog (BitVec 64) :=
.seq body858_16 body858_39

def body858_41 : Prog (BitVec 64) :=
.seq body858_15 body858_40

def body858_42 : Prog (BitVec 64) :=
.seq body858_14 body858_41

def body858_43 : Prog (BitVec 64) :=
.seq body858_13 body858_42

def body858_44 : Prog (BitVec 64) :=
.seq body858_12 body858_43

def body858_45 : Prog (BitVec 64) :=
.seq body858_11 body858_44

def body858_46 : Prog (BitVec 64) :=
.seq body858_10 body858_45

def body858_47 : Prog (BitVec 64) :=
.seq body858_9 body858_46

def body858_48 : Prog (BitVec 64) :=
.seq body858_8 body858_47

def body858_49 : Prog (BitVec 64) :=
.seq body858_7 body858_48

def body858_50 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body858_49

def body858_51 : Prog (BitVec 64) :=
.seq body858_3 body858_50

def body858_52 : Prog (BitVec 64) :=
.seq body858_2 body858_51

def body858_53 : Prog (BitVec 64) :=
.seq body858_1 body858_52

def body858_54 : Prog (BitVec 64) :=
.seq body858_0 body858_53

def body858_55 : Prog (BitVec 64) :=
.seq body858_0 body858_1

def body858_56 : Prog (BitVec 64) :=
.seq body858_55 body858_2

def body858_57 : Prog (BitVec 64) :=
.seq body858_56 body858_3

def body858_58 : Prog (BitVec 64) :=
.seq body858_7 body858_8

def body858_59 : Prog (BitVec 64) :=
.seq body858_58 body858_9

def body858_60 : Prog (BitVec 64) :=
.seq body858_59 body858_10

def body858_61 : Prog (BitVec 64) :=
.seq body858_60 body858_11

def body858_62 : Prog (BitVec 64) :=
.seq body858_61 body858_12

def body858_63 : Prog (BitVec 64) :=
.seq body858_62 body858_13

def body858_64 : Prog (BitVec 64) :=
.seq body858_63 body858_14

def body858_65 : Prog (BitVec 64) :=
.seq body858_64 body858_15

def body858_66 : Prog (BitVec 64) :=
.seq body858_65 body858_16

def body858_67 : Prog (BitVec 64) :=
.seq body858_66 body858_17

def body858_68 : Prog (BitVec 64) :=
.seq body858_67 body858_18

def body858_69 : Prog (BitVec 64) :=
.seq body858_68 body858_19

def body858_70 : Prog (BitVec 64) :=
.seq body858_69 body858_20

def body858_71 : Prog (BitVec 64) :=
.seq body858_70 body858_21

def body858_72 : Prog (BitVec 64) :=
.seq body858_71 body858_22

def body858_73 : Prog (BitVec 64) :=
.seq body858_72 body858_23

def body858_74 : Prog (BitVec 64) :=
.seq body858_73 body858_24

def body858_75 : Prog (BitVec 64) :=
.seq body858_74 body858_25

def body858_76 : Prog (BitVec 64) :=
.seq body858_75 body858_26

def body858_77 : Prog (BitVec 64) :=
.seq body858_76 body858_27

def body858_78 : Prog (BitVec 64) :=
.seq body858_77 body858_28

def body858_79 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body858_78

def body858_80 : Prog (BitVec 64) :=
.seq body858_57 body858_79

def originalData858 : Decl (BitVec 64) :=
.function { name := "fork_init", inline := false, exported := false, params := [], body := body858_54, returnShape := (Flapjack.Shape.one) }
def simplifiedData858 : Decl (BitVec 64) :=
.function { name := "fork_init", inline := false, exported := false, params := [], body := body858_80, returnShape := (Flapjack.Shape.one) }
def original858 := Pancake.PanLang.declToHOL originalData858
def simplified858 := Pancake.PanLang.declToHOL simplifiedData858
end InitECandidate.Proofs.FrontendStages.Declarations
