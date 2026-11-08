import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk06
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk07
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk08
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk09
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk10
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk11
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk12
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk13
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk14
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk15
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk16
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk17
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk18
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk19
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk20
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk21
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk22
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk23
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk24
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk25
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk26
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk27
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames05
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames06
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames07
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames08
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames09
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames10
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames11
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames12
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames13
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames14
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames15
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames16
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames17
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames18
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames19
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames20
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames21
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames22
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames23
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames24
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames25
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames26
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames27
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Table05_27
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition

noncomputable def words05 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := Chunk05.words
noncomputable def bodies05 : List (Nat × HolProg 64) := Chunk05.bodies
noncomputable def frames05 : List Nat := Chunk05.frames
noncomputable def bitmapDelta05 : AppList (BitVec 64) := Chunk05.bitmapDelta
def oracles05 : List (Option (Spt Nat)) := [oracle144, oracle145, oracle146, oracle147, oracle148, oracle149, oracle150, oracle151, oracle152, oracle153, oracle154, oracle155, oracle156, oracle157, oracle158, oracle159]

theorem compiled05 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words05 (prefixList, 107) =
    (bodies05, frames05, (BitmapPrepend.prependAppList prefixList bitmapDelta05, 146)) :=
  Chunk05.compiled prefixList

theorem collected05 :
    StackRawCall.collectInfo bodies05 Frames04.info = Frames05.info :=
  Frames05.info_eq

theorem words05_eq :
    (((ConcreteCompilerWord.source.drop 80).take 16).zip oracles05).map
      (fun p => wordFunction p.2 p.1) = words05 :=
  Chunk05.words_eq

noncomputable def words06 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words05 ++ Chunk06.words
noncomputable def bodies06 : List (Nat × HolProg 64) := bodies05 ++ Chunk06.bodies
noncomputable def frames06 : List Nat := frames05 ++ Chunk06.frames
noncomputable def bitmapDelta06 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta05 Chunk06.bitmapDelta
def chunkOracles06 : List (Option (Spt Nat)) := [oracle160, oracle161, oracle162, oracle163, oracle164, oracle165, oracle166, oracle167, oracle168, oracle169, oracle170, oracle171, oracle172, oracle173, oracle174, oracle175]
def oracles06 : List (Option (Spt Nat)) := oracles05 ++ chunkOracles06

theorem compiled06 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words06 (prefixList, 107) =
    (bodies06, frames06, (BitmapPrepend.prependAppList prefixList bitmapDelta06, 196)) := by
  unfold words06 bodies06 frames06 bitmapDelta06
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled05 prefixList)
    (Chunk06.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta05))

theorem collected06 :
    StackRawCall.collectInfo bodies06 Frames04.info = Frames06.info := by
  unfold bodies06
  rw [TableComposition.collectInfo_append, collected05, Frames06.info_eq]

theorem words06_eq :
    (((ConcreteCompilerWord.source.drop 80).take 32).zip oracles06).map
      (fun p => wordFunction p.2 p.1) = words06 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 80).take 16).length = oracles05.length := by decide
  unfold words06 oracles06 chunkOracles06
  rw [← words05_eq, ← Chunk06.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words07 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words06 ++ Chunk07.words
noncomputable def bodies07 : List (Nat × HolProg 64) := bodies06 ++ Chunk07.bodies
noncomputable def frames07 : List Nat := frames06 ++ Chunk07.frames
noncomputable def bitmapDelta07 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta06 Chunk07.bitmapDelta
def chunkOracles07 : List (Option (Spt Nat)) := [oracle176, oracle177, oracle178, oracle179, oracle180, oracle181, oracle182, oracle183, oracle184, oracle185, oracle186, oracle187, oracle188, oracle189, oracle190, oracle191]
def oracles07 : List (Option (Spt Nat)) := oracles06 ++ chunkOracles07

theorem compiled07 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words07 (prefixList, 107) =
    (bodies07, frames07, (BitmapPrepend.prependAppList prefixList bitmapDelta07, 224)) := by
  unfold words07 bodies07 frames07 bitmapDelta07
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled06 prefixList)
    (Chunk07.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta06))

theorem collected07 :
    StackRawCall.collectInfo bodies07 Frames04.info = Frames07.info := by
  unfold bodies07
  rw [TableComposition.collectInfo_append, collected06, Frames07.info_eq]

theorem words07_eq :
    (((ConcreteCompilerWord.source.drop 80).take 48).zip oracles07).map
      (fun p => wordFunction p.2 p.1) = words07 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 80).take 32).length = oracles06.length := by decide
  unfold words07 oracles07 chunkOracles07
  rw [← words06_eq, ← Chunk07.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words08 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words07 ++ Chunk08.words
noncomputable def bodies08 : List (Nat × HolProg 64) := bodies07 ++ Chunk08.bodies
noncomputable def frames08 : List Nat := frames07 ++ Chunk08.frames
noncomputable def bitmapDelta08 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta07 Chunk08.bitmapDelta
def chunkOracles08 : List (Option (Spt Nat)) := [oracle192, oracle193, oracle194, oracle195, oracle196, oracle197, oracle198, oracle199, oracle200, oracle201, oracle202, oracle203, oracle204, oracle205, oracle206, oracle207]
def oracles08 : List (Option (Spt Nat)) := oracles07 ++ chunkOracles08

theorem compiled08 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words08 (prefixList, 107) =
    (bodies08, frames08, (BitmapPrepend.prependAppList prefixList bitmapDelta08, 258)) := by
  unfold words08 bodies08 frames08 bitmapDelta08
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled07 prefixList)
    (Chunk08.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta07))

theorem collected08 :
    StackRawCall.collectInfo bodies08 Frames04.info = Frames08.info := by
  unfold bodies08
  rw [TableComposition.collectInfo_append, collected07, Frames08.info_eq]

theorem words08_eq :
    (((ConcreteCompilerWord.source.drop 80).take 64).zip oracles08).map
      (fun p => wordFunction p.2 p.1) = words08 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 80).take 48).length = oracles07.length := by decide
  unfold words08 oracles08 chunkOracles08
  rw [← words07_eq, ← Chunk08.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words09 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words08 ++ Chunk09.words
noncomputable def bodies09 : List (Nat × HolProg 64) := bodies08 ++ Chunk09.bodies
noncomputable def frames09 : List Nat := frames08 ++ Chunk09.frames
noncomputable def bitmapDelta09 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta08 Chunk09.bitmapDelta
def chunkOracles09 : List (Option (Spt Nat)) := [oracle208, oracle209, oracle210, oracle211, oracle212, oracle213, oracle214, oracle215, oracle216, oracle217, oracle218, oracle219, oracle220, oracle221, oracle222, oracle223]
def oracles09 : List (Option (Spt Nat)) := oracles08 ++ chunkOracles09

theorem compiled09 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words09 (prefixList, 107) =
    (bodies09, frames09, (BitmapPrepend.prependAppList prefixList bitmapDelta09, 298)) := by
  unfold words09 bodies09 frames09 bitmapDelta09
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled08 prefixList)
    (Chunk09.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta08))

theorem collected09 :
    StackRawCall.collectInfo bodies09 Frames04.info = Frames09.info := by
  unfold bodies09
  rw [TableComposition.collectInfo_append, collected08, Frames09.info_eq]

theorem words09_eq :
    (((ConcreteCompilerWord.source.drop 80).take 80).zip oracles09).map
      (fun p => wordFunction p.2 p.1) = words09 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 80).take 64).length = oracles08.length := by decide
  unfold words09 oracles09 chunkOracles09
  rw [← words08_eq, ← Chunk09.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words10 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words09 ++ Chunk10.words
noncomputable def bodies10 : List (Nat × HolProg 64) := bodies09 ++ Chunk10.bodies
noncomputable def frames10 : List Nat := frames09 ++ Chunk10.frames
noncomputable def bitmapDelta10 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta09 Chunk10.bitmapDelta
def chunkOracles10 : List (Option (Spt Nat)) := [oracle224, oracle225, oracle226, oracle227, oracle228, oracle229, oracle230, oracle231, oracle232, oracle233, oracle234, oracle235, oracle236, oracle237, oracle238, oracle239]
def oracles10 : List (Option (Spt Nat)) := oracles09 ++ chunkOracles10

theorem compiled10 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words10 (prefixList, 107) =
    (bodies10, frames10, (BitmapPrepend.prependAppList prefixList bitmapDelta10, 460)) := by
  unfold words10 bodies10 frames10 bitmapDelta10
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled09 prefixList)
    (Chunk10.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta09))

theorem collected10 :
    StackRawCall.collectInfo bodies10 Frames04.info = Frames10.info := by
  unfold bodies10
  rw [TableComposition.collectInfo_append, collected09, Frames10.info_eq]

theorem words10_eq :
    (((ConcreteCompilerWord.source.drop 80).take 96).zip oracles10).map
      (fun p => wordFunction p.2 p.1) = words10 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 80).take 80).length = oracles09.length := by decide
  unfold words10 oracles10 chunkOracles10
  rw [← words09_eq, ← Chunk10.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words11 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words10 ++ Chunk11.words
noncomputable def bodies11 : List (Nat × HolProg 64) := bodies10 ++ Chunk11.bodies
noncomputable def frames11 : List Nat := frames10 ++ Chunk11.frames
noncomputable def bitmapDelta11 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta10 Chunk11.bitmapDelta
def chunkOracles11 : List (Option (Spt Nat)) := [oracle240, oracle241, oracle242, oracle243, oracle244, oracle245, oracle246, oracle247, oracle248, oracle249, oracle250, oracle251, oracle252, oracle253, oracle254, oracle255]
def oracles11 : List (Option (Spt Nat)) := oracles10 ++ chunkOracles11

theorem compiled11 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words11 (prefixList, 107) =
    (bodies11, frames11, (BitmapPrepend.prependAppList prefixList bitmapDelta11, 534)) := by
  unfold words11 bodies11 frames11 bitmapDelta11
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled10 prefixList)
    (Chunk11.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta10))

theorem collected11 :
    StackRawCall.collectInfo bodies11 Frames04.info = Frames11.info := by
  unfold bodies11
  rw [TableComposition.collectInfo_append, collected10, Frames11.info_eq]

theorem words11_eq :
    (((ConcreteCompilerWord.source.drop 80).take 112).zip oracles11).map
      (fun p => wordFunction p.2 p.1) = words11 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 80).take 96).length = oracles10.length := by decide
  unfold words11 oracles11 chunkOracles11
  rw [← words10_eq, ← Chunk11.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words12 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words11 ++ Chunk12.words
noncomputable def bodies12 : List (Nat × HolProg 64) := bodies11 ++ Chunk12.bodies
noncomputable def frames12 : List Nat := frames11 ++ Chunk12.frames
noncomputable def bitmapDelta12 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta11 Chunk12.bitmapDelta
def chunkOracles12 : List (Option (Spt Nat)) := [oracle256, oracle257, oracle258, oracle259, oracle260, oracle261, oracle262, oracle263, oracle264, oracle265, oracle266, oracle267, oracle268, oracle269, oracle270, oracle271]
def oracles12 : List (Option (Spt Nat)) := oracles11 ++ chunkOracles12

theorem compiled12 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words12 (prefixList, 107) =
    (bodies12, frames12, (BitmapPrepend.prependAppList prefixList bitmapDelta12, 658)) := by
  unfold words12 bodies12 frames12 bitmapDelta12
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled11 prefixList)
    (Chunk12.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta11))

theorem collected12 :
    StackRawCall.collectInfo bodies12 Frames04.info = Frames12.info := by
  unfold bodies12
  rw [TableComposition.collectInfo_append, collected11, Frames12.info_eq]

theorem words12_eq :
    (((ConcreteCompilerWord.source.drop 80).take 128).zip oracles12).map
      (fun p => wordFunction p.2 p.1) = words12 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 80).take 112).length = oracles11.length := by decide
  unfold words12 oracles12 chunkOracles12
  rw [← words11_eq, ← Chunk12.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words13 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words12 ++ Chunk13.words
noncomputable def bodies13 : List (Nat × HolProg 64) := bodies12 ++ Chunk13.bodies
noncomputable def frames13 : List Nat := frames12 ++ Chunk13.frames
noncomputable def bitmapDelta13 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta12 Chunk13.bitmapDelta
def chunkOracles13 : List (Option (Spt Nat)) := [oracle272, oracle273, oracle274, oracle275, oracle276, oracle277, oracle278, oracle279, oracle280, oracle281, oracle282, oracle283, oracle284, oracle285, oracle286, oracle287]
def oracles13 : List (Option (Spt Nat)) := oracles12 ++ chunkOracles13

theorem compiled13 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words13 (prefixList, 107) =
    (bodies13, frames13, (BitmapPrepend.prependAppList prefixList bitmapDelta13, 789)) := by
  unfold words13 bodies13 frames13 bitmapDelta13
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled12 prefixList)
    (Chunk13.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta12))

theorem collected13 :
    StackRawCall.collectInfo bodies13 Frames04.info = Frames13.info := by
  unfold bodies13
  rw [TableComposition.collectInfo_append, collected12, Frames13.info_eq]

theorem words13_eq :
    (((ConcreteCompilerWord.source.drop 80).take 144).zip oracles13).map
      (fun p => wordFunction p.2 p.1) = words13 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 80).take 128).length = oracles12.length := by decide
  unfold words13 oracles13 chunkOracles13
  rw [← words12_eq, ← Chunk13.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words14 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words13 ++ Chunk14.words
noncomputable def bodies14 : List (Nat × HolProg 64) := bodies13 ++ Chunk14.bodies
noncomputable def frames14 : List Nat := frames13 ++ Chunk14.frames
noncomputable def bitmapDelta14 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta13 Chunk14.bitmapDelta
def chunkOracles14 : List (Option (Spt Nat)) := [oracle288, oracle289, oracle290, oracle291, oracle292, oracle293, oracle294, oracle295, oracle296, oracle297, oracle298, oracle299, oracle300, oracle301, oracle302, oracle303]
def oracles14 : List (Option (Spt Nat)) := oracles13 ++ chunkOracles14

theorem compiled14 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words14 (prefixList, 107) =
    (bodies14, frames14, (BitmapPrepend.prependAppList prefixList bitmapDelta14, 834)) := by
  unfold words14 bodies14 frames14 bitmapDelta14
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled13 prefixList)
    (Chunk14.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta13))

theorem collected14 :
    StackRawCall.collectInfo bodies14 Frames04.info = Frames14.info := by
  unfold bodies14
  rw [TableComposition.collectInfo_append, collected13, Frames14.info_eq]

theorem words14_eq :
    (((ConcreteCompilerWord.source.drop 80).take 160).zip oracles14).map
      (fun p => wordFunction p.2 p.1) = words14 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 80).take 144).length = oracles13.length := by decide
  unfold words14 oracles14 chunkOracles14
  rw [← words13_eq, ← Chunk14.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words15 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words14 ++ Chunk15.words
noncomputable def bodies15 : List (Nat × HolProg 64) := bodies14 ++ Chunk15.bodies
noncomputable def frames15 : List Nat := frames14 ++ Chunk15.frames
noncomputable def bitmapDelta15 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta14 Chunk15.bitmapDelta
def chunkOracles15 : List (Option (Spt Nat)) := [oracle304, oracle305, oracle306, oracle307, oracle308, oracle309, oracle310, oracle311, oracle312, oracle313, oracle314, oracle315, oracle316, oracle317, oracle318, oracle319]
def oracles15 : List (Option (Spt Nat)) := oracles14 ++ chunkOracles15

theorem compiled15 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words15 (prefixList, 107) =
    (bodies15, frames15, (BitmapPrepend.prependAppList prefixList bitmapDelta15, 895)) := by
  unfold words15 bodies15 frames15 bitmapDelta15
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled14 prefixList)
    (Chunk15.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta14))

theorem collected15 :
    StackRawCall.collectInfo bodies15 Frames04.info = Frames15.info := by
  unfold bodies15
  rw [TableComposition.collectInfo_append, collected14, Frames15.info_eq]

theorem words15_eq :
    (((ConcreteCompilerWord.source.drop 80).take 176).zip oracles15).map
      (fun p => wordFunction p.2 p.1) = words15 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 80).take 160).length = oracles14.length := by decide
  unfold words15 oracles15 chunkOracles15
  rw [← words14_eq, ← Chunk15.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words16 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words15 ++ Chunk16.words
noncomputable def bodies16 : List (Nat × HolProg 64) := bodies15 ++ Chunk16.bodies
noncomputable def frames16 : List Nat := frames15 ++ Chunk16.frames
noncomputable def bitmapDelta16 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta15 Chunk16.bitmapDelta
def chunkOracles16 : List (Option (Spt Nat)) := [oracle320, oracle321, oracle322, oracle323, oracle324, oracle325, oracle326, oracle327, oracle328, oracle329, oracle330, oracle331, oracle332, oracle333, oracle334, oracle335]
def oracles16 : List (Option (Spt Nat)) := oracles15 ++ chunkOracles16

theorem compiled16 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words16 (prefixList, 107) =
    (bodies16, frames16, (BitmapPrepend.prependAppList prefixList bitmapDelta16, 969)) := by
  unfold words16 bodies16 frames16 bitmapDelta16
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled15 prefixList)
    (Chunk16.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta15))

theorem collected16 :
    StackRawCall.collectInfo bodies16 Frames04.info = Frames16.info := by
  unfold bodies16
  rw [TableComposition.collectInfo_append, collected15, Frames16.info_eq]

theorem words16_eq :
    (((ConcreteCompilerWord.source.drop 80).take 192).zip oracles16).map
      (fun p => wordFunction p.2 p.1) = words16 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 80).take 176).length = oracles15.length := by decide
  unfold words16 oracles16 chunkOracles16
  rw [← words15_eq, ← Chunk16.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words17 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words16 ++ Chunk17.words
noncomputable def bodies17 : List (Nat × HolProg 64) := bodies16 ++ Chunk17.bodies
noncomputable def frames17 : List Nat := frames16 ++ Chunk17.frames
noncomputable def bitmapDelta17 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta16 Chunk17.bitmapDelta
def chunkOracles17 : List (Option (Spt Nat)) := [oracle336, oracle337, oracle338, oracle339, oracle340, oracle341, oracle342, oracle343, oracle344, oracle345, oracle346, oracle347, oracle348, oracle349, oracle350, oracle351]
def oracles17 : List (Option (Spt Nat)) := oracles16 ++ chunkOracles17

theorem compiled17 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words17 (prefixList, 107) =
    (bodies17, frames17, (BitmapPrepend.prependAppList prefixList bitmapDelta17, 1026)) := by
  unfold words17 bodies17 frames17 bitmapDelta17
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled16 prefixList)
    (Chunk17.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta16))

theorem collected17 :
    StackRawCall.collectInfo bodies17 Frames04.info = Frames17.info := by
  unfold bodies17
  rw [TableComposition.collectInfo_append, collected16, Frames17.info_eq]

theorem words17_eq :
    (((ConcreteCompilerWord.source.drop 80).take 208).zip oracles17).map
      (fun p => wordFunction p.2 p.1) = words17 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 80).take 192).length = oracles16.length := by decide
  unfold words17 oracles17 chunkOracles17
  rw [← words16_eq, ← Chunk17.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words18 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words17 ++ Chunk18.words
noncomputable def bodies18 : List (Nat × HolProg 64) := bodies17 ++ Chunk18.bodies
noncomputable def frames18 : List Nat := frames17 ++ Chunk18.frames
noncomputable def bitmapDelta18 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta17 Chunk18.bitmapDelta
def chunkOracles18 : List (Option (Spt Nat)) := [oracle352, oracle353, oracle354, oracle355, oracle356, oracle357, oracle358, oracle359, oracle360, oracle361, oracle362, oracle363, oracle364, oracle365, oracle366, oracle367]
def oracles18 : List (Option (Spt Nat)) := oracles17 ++ chunkOracles18

theorem compiled18 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words18 (prefixList, 107) =
    (bodies18, frames18, (BitmapPrepend.prependAppList prefixList bitmapDelta18, 1083)) := by
  unfold words18 bodies18 frames18 bitmapDelta18
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled17 prefixList)
    (Chunk18.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta17))

theorem collected18 :
    StackRawCall.collectInfo bodies18 Frames04.info = Frames18.info := by
  unfold bodies18
  rw [TableComposition.collectInfo_append, collected17, Frames18.info_eq]

theorem words18_eq :
    (((ConcreteCompilerWord.source.drop 80).take 224).zip oracles18).map
      (fun p => wordFunction p.2 p.1) = words18 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 80).take 208).length = oracles17.length := by decide
  unfold words18 oracles18 chunkOracles18
  rw [← words17_eq, ← Chunk18.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words19 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words18 ++ Chunk19.words
noncomputable def bodies19 : List (Nat × HolProg 64) := bodies18 ++ Chunk19.bodies
noncomputable def frames19 : List Nat := frames18 ++ Chunk19.frames
noncomputable def bitmapDelta19 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta18 Chunk19.bitmapDelta
def chunkOracles19 : List (Option (Spt Nat)) := [oracle368, oracle369, oracle370, oracle371, oracle372, oracle373, oracle374, oracle375, oracle376, oracle377, oracle378, oracle379, oracle380, oracle381, oracle382, oracle383]
def oracles19 : List (Option (Spt Nat)) := oracles18 ++ chunkOracles19

theorem compiled19 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words19 (prefixList, 107) =
    (bodies19, frames19, (BitmapPrepend.prependAppList prefixList bitmapDelta19, 1129)) := by
  unfold words19 bodies19 frames19 bitmapDelta19
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled18 prefixList)
    (Chunk19.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta18))

theorem collected19 :
    StackRawCall.collectInfo bodies19 Frames04.info = Frames19.info := by
  unfold bodies19
  rw [TableComposition.collectInfo_append, collected18, Frames19.info_eq]

theorem words19_eq :
    (((ConcreteCompilerWord.source.drop 80).take 240).zip oracles19).map
      (fun p => wordFunction p.2 p.1) = words19 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 80).take 224).length = oracles18.length := by decide
  unfold words19 oracles19 chunkOracles19
  rw [← words18_eq, ← Chunk19.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words20 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words19 ++ Chunk20.words
noncomputable def bodies20 : List (Nat × HolProg 64) := bodies19 ++ Chunk20.bodies
noncomputable def frames20 : List Nat := frames19 ++ Chunk20.frames
noncomputable def bitmapDelta20 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta19 Chunk20.bitmapDelta
def chunkOracles20 : List (Option (Spt Nat)) := [oracle384, oracle385, oracle386, oracle387, oracle388, oracle389, oracle390, oracle391, oracle392, oracle393, oracle394, oracle395, oracle396, oracle397, oracle398, oracle399]
def oracles20 : List (Option (Spt Nat)) := oracles19 ++ chunkOracles20

theorem compiled20 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words20 (prefixList, 107) =
    (bodies20, frames20, (BitmapPrepend.prependAppList prefixList bitmapDelta20, 1184)) := by
  unfold words20 bodies20 frames20 bitmapDelta20
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled19 prefixList)
    (Chunk20.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta19))

theorem collected20 :
    StackRawCall.collectInfo bodies20 Frames04.info = Frames20.info := by
  unfold bodies20
  rw [TableComposition.collectInfo_append, collected19, Frames20.info_eq]

theorem words20_eq :
    (((ConcreteCompilerWord.source.drop 80).take 256).zip oracles20).map
      (fun p => wordFunction p.2 p.1) = words20 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 80).take 240).length = oracles19.length := by decide
  unfold words20 oracles20 chunkOracles20
  rw [← words19_eq, ← Chunk20.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words21 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words20 ++ Chunk21.words
noncomputable def bodies21 : List (Nat × HolProg 64) := bodies20 ++ Chunk21.bodies
noncomputable def frames21 : List Nat := frames20 ++ Chunk21.frames
noncomputable def bitmapDelta21 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta20 Chunk21.bitmapDelta
def chunkOracles21 : List (Option (Spt Nat)) := [oracle400, oracle401, oracle402, oracle403, oracle404, oracle405, oracle406, oracle407, oracle408, oracle409, oracle410, oracle411, oracle412, oracle413, oracle414, oracle415]
def oracles21 : List (Option (Spt Nat)) := oracles20 ++ chunkOracles21

theorem compiled21 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words21 (prefixList, 107) =
    (bodies21, frames21, (BitmapPrepend.prependAppList prefixList bitmapDelta21, 1240)) := by
  unfold words21 bodies21 frames21 bitmapDelta21
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled20 prefixList)
    (Chunk21.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta20))

theorem collected21 :
    StackRawCall.collectInfo bodies21 Frames04.info = Frames21.info := by
  unfold bodies21
  rw [TableComposition.collectInfo_append, collected20, Frames21.info_eq]

theorem words21_eq :
    (((ConcreteCompilerWord.source.drop 80).take 272).zip oracles21).map
      (fun p => wordFunction p.2 p.1) = words21 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 80).take 256).length = oracles20.length := by decide
  unfold words21 oracles21 chunkOracles21
  rw [← words20_eq, ← Chunk21.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words22 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words21 ++ Chunk22.words
noncomputable def bodies22 : List (Nat × HolProg 64) := bodies21 ++ Chunk22.bodies
noncomputable def frames22 : List Nat := frames21 ++ Chunk22.frames
noncomputable def bitmapDelta22 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta21 Chunk22.bitmapDelta
def chunkOracles22 : List (Option (Spt Nat)) := [oracle416, oracle417, oracle418, oracle419, oracle420, oracle421, oracle422, oracle423, oracle424, oracle425, oracle426, oracle427, oracle428, oracle429, oracle430, oracle431]
def oracles22 : List (Option (Spt Nat)) := oracles21 ++ chunkOracles22

theorem compiled22 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words22 (prefixList, 107) =
    (bodies22, frames22, (BitmapPrepend.prependAppList prefixList bitmapDelta22, 1300)) := by
  unfold words22 bodies22 frames22 bitmapDelta22
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled21 prefixList)
    (Chunk22.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta21))

theorem collected22 :
    StackRawCall.collectInfo bodies22 Frames04.info = Frames22.info := by
  unfold bodies22
  rw [TableComposition.collectInfo_append, collected21, Frames22.info_eq]

theorem words22_eq :
    (((ConcreteCompilerWord.source.drop 80).take 288).zip oracles22).map
      (fun p => wordFunction p.2 p.1) = words22 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 80).take 272).length = oracles21.length := by decide
  unfold words22 oracles22 chunkOracles22
  rw [← words21_eq, ← Chunk22.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words23 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words22 ++ Chunk23.words
noncomputable def bodies23 : List (Nat × HolProg 64) := bodies22 ++ Chunk23.bodies
noncomputable def frames23 : List Nat := frames22 ++ Chunk23.frames
noncomputable def bitmapDelta23 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta22 Chunk23.bitmapDelta
def chunkOracles23 : List (Option (Spt Nat)) := [oracle432, oracle433, oracle434, oracle435, oracle436, oracle437, oracle438, oracle439, oracle440, oracle441, oracle442, oracle443, oracle444, oracle445, oracle446, oracle447]
def oracles23 : List (Option (Spt Nat)) := oracles22 ++ chunkOracles23

theorem compiled23 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words23 (prefixList, 107) =
    (bodies23, frames23, (BitmapPrepend.prependAppList prefixList bitmapDelta23, 1348)) := by
  unfold words23 bodies23 frames23 bitmapDelta23
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled22 prefixList)
    (Chunk23.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta22))

theorem collected23 :
    StackRawCall.collectInfo bodies23 Frames04.info = Frames23.info := by
  unfold bodies23
  rw [TableComposition.collectInfo_append, collected22, Frames23.info_eq]

theorem words23_eq :
    (((ConcreteCompilerWord.source.drop 80).take 304).zip oracles23).map
      (fun p => wordFunction p.2 p.1) = words23 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 80).take 288).length = oracles22.length := by decide
  unfold words23 oracles23 chunkOracles23
  rw [← words22_eq, ← Chunk23.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words24 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words23 ++ Chunk24.words
noncomputable def bodies24 : List (Nat × HolProg 64) := bodies23 ++ Chunk24.bodies
noncomputable def frames24 : List Nat := frames23 ++ Chunk24.frames
noncomputable def bitmapDelta24 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta23 Chunk24.bitmapDelta
def chunkOracles24 : List (Option (Spt Nat)) := [oracle448, oracle449, oracle450, oracle451, oracle452, oracle453, oracle454, oracle455, oracle456, oracle457, oracle458, oracle459, oracle460, oracle461, oracle462, oracle463]
def oracles24 : List (Option (Spt Nat)) := oracles23 ++ chunkOracles24

theorem compiled24 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words24 (prefixList, 107) =
    (bodies24, frames24, (BitmapPrepend.prependAppList prefixList bitmapDelta24, 1487)) := by
  unfold words24 bodies24 frames24 bitmapDelta24
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled23 prefixList)
    (Chunk24.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta23))

theorem collected24 :
    StackRawCall.collectInfo bodies24 Frames04.info = Frames24.info := by
  unfold bodies24
  rw [TableComposition.collectInfo_append, collected23, Frames24.info_eq]

theorem words24_eq :
    (((ConcreteCompilerWord.source.drop 80).take 320).zip oracles24).map
      (fun p => wordFunction p.2 p.1) = words24 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 80).take 304).length = oracles23.length := by decide
  unfold words24 oracles24 chunkOracles24
  rw [← words23_eq, ← Chunk24.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words25 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words24 ++ Chunk25.words
noncomputable def bodies25 : List (Nat × HolProg 64) := bodies24 ++ Chunk25.bodies
noncomputable def frames25 : List Nat := frames24 ++ Chunk25.frames
noncomputable def bitmapDelta25 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta24 Chunk25.bitmapDelta
def chunkOracles25 : List (Option (Spt Nat)) := [oracle464, oracle465, oracle466, oracle467, oracle468, oracle469, oracle470, oracle471, oracle472, oracle473, oracle474, oracle475, oracle476, oracle477, oracle478, oracle479]
def oracles25 : List (Option (Spt Nat)) := oracles24 ++ chunkOracles25

theorem compiled25 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words25 (prefixList, 107) =
    (bodies25, frames25, (BitmapPrepend.prependAppList prefixList bitmapDelta25, 1503)) := by
  unfold words25 bodies25 frames25 bitmapDelta25
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled24 prefixList)
    (Chunk25.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta24))

theorem collected25 :
    StackRawCall.collectInfo bodies25 Frames04.info = Frames25.info := by
  unfold bodies25
  rw [TableComposition.collectInfo_append, collected24, Frames25.info_eq]

theorem words25_eq :
    (((ConcreteCompilerWord.source.drop 80).take 336).zip oracles25).map
      (fun p => wordFunction p.2 p.1) = words25 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 80).take 320).length = oracles24.length := by decide
  unfold words25 oracles25 chunkOracles25
  rw [← words24_eq, ← Chunk25.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words26 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words25 ++ Chunk26.words
noncomputable def bodies26 : List (Nat × HolProg 64) := bodies25 ++ Chunk26.bodies
noncomputable def frames26 : List Nat := frames25 ++ Chunk26.frames
noncomputable def bitmapDelta26 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta25 Chunk26.bitmapDelta
def chunkOracles26 : List (Option (Spt Nat)) := [oracle480, oracle481, oracle482, oracle483, oracle484, oracle485, oracle486, oracle487, oracle488, oracle489, oracle490, oracle491, oracle492, oracle493, oracle494, oracle495]
def oracles26 : List (Option (Spt Nat)) := oracles25 ++ chunkOracles26

theorem compiled26 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words26 (prefixList, 107) =
    (bodies26, frames26, (BitmapPrepend.prependAppList prefixList bitmapDelta26, 1542)) := by
  unfold words26 bodies26 frames26 bitmapDelta26
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled25 prefixList)
    (Chunk26.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta25))

theorem collected26 :
    StackRawCall.collectInfo bodies26 Frames04.info = Frames26.info := by
  unfold bodies26
  rw [TableComposition.collectInfo_append, collected25, Frames26.info_eq]

theorem words26_eq :
    (((ConcreteCompilerWord.source.drop 80).take 352).zip oracles26).map
      (fun p => wordFunction p.2 p.1) = words26 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 80).take 336).length = oracles25.length := by decide
  unfold words26 oracles26 chunkOracles26
  rw [← words25_eq, ← Chunk26.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words27 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words26 ++ Chunk27.words
noncomputable def bodies27 : List (Nat × HolProg 64) := bodies26 ++ Chunk27.bodies
noncomputable def frames27 : List Nat := frames26 ++ Chunk27.frames
noncomputable def bitmapDelta27 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta26 Chunk27.bitmapDelta
def chunkOracles27 : List (Option (Spt Nat)) := [oracle496, oracle497, oracle498, oracle499, oracle500, oracle501, oracle502, oracle503, oracle504, oracle505, oracle506, oracle507, oracle508, oracle509, oracle510, oracle511]
def oracles27 : List (Option (Spt Nat)) := oracles26 ++ chunkOracles27

theorem compiled27 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words27 (prefixList, 107) =
    (bodies27, frames27, (BitmapPrepend.prependAppList prefixList bitmapDelta27, 1637)) := by
  unfold words27 bodies27 frames27 bitmapDelta27
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled26 prefixList)
    (Chunk27.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta26))

theorem collected27 :
    StackRawCall.collectInfo bodies27 Frames04.info = Frames27.info := by
  unfold bodies27
  rw [TableComposition.collectInfo_append, collected26, Frames27.info_eq]

theorem words27_eq :
    (((ConcreteCompilerWord.source.drop 80).take 368).zip oracles27).map
      (fun p => wordFunction p.2 p.1) = words27 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 80).take 352).length = oracles26.length := by decide
  unfold words27 oracles27 chunkOracles27
  rw [← words26_eq, ← Chunk27.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable abbrev words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words27
noncomputable abbrev bodies : List (Nat × HolProg 64) := bodies27
noncomputable abbrev frames : List Nat := frames27
noncomputable abbrev bitmapDelta : AppList (BitVec 64) := bitmapDelta27
abbrev oracles : List (Option (Spt Nat)) := oracles27

theorem oracles_length : oracles.length = 368 := by decide

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 107) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 1637)) :=
  compiled27 prefixList

theorem collected :
    StackRawCall.collectInfo bodies Frames04.info = FrameState27.info :=
  collected27.trans Frames27.info_eq_frameState27

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 80).take 368).zip oracles).map
      (fun p => wordFunction p.2 p.1) = words :=
  words27_eq

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Table05_27
