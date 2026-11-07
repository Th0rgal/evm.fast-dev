import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk28
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk29
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk30
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk31
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk32
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk33
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk34
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk35
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk36
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk37
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk38
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk39
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk40
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk41
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk42
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk43
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk44
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk45
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk46
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk47
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk48
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk49
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk50
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames28
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames29
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames30
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames31
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames32
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames33
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames34
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames35
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames36
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames37
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames38
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames39
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames40
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames41
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames42
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames43
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames44
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames45
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames46
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames47
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames48
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames49
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames50
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend

/-! Assembled Wave 8 Stage 5 backend slice for Stream D (`Chunk28..Chunk50`, functions `512..877`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Table28_50
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition

noncomputable def words28 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := Chunk28.words
noncomputable def bodies28 : List (Nat × HolProg 64) := Chunk28.bodies
noncomputable def frames28 : List Nat := Chunk28.frames
noncomputable def bitmapDelta28 : AppList (BitVec 64) := Chunk28.bitmapDelta
def oracles28 : List (Option (Spt Nat)) := [oracle512, oracle513, oracle514, oracle515, oracle516, oracle517, oracle518, oracle519, oracle520, oracle521, oracle522, oracle523, oracle524, oracle525, oracle526, oracle527]

theorem compiled28 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words28 (prefixList, 1637) =
    (bodies28, frames28, (BitmapPrepend.prependAppList prefixList bitmapDelta28, 1729)) :=
  Chunk28.compiled prefixList

theorem collected28 :
    StackRawCall.collectInfo bodies28 FrameState27.info = Frames28.info :=
  Frames28.info_eq

theorem words28_eq :
    (((ConcreteCompilerWord.source.drop 448).take 16).zip oracles28).map
      (fun p => wordFunction p.2 p.1) = words28 :=
  Chunk28.words_eq

noncomputable def words29 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words28 ++ Chunk29.words
noncomputable def bodies29 : List (Nat × HolProg 64) := bodies28 ++ Chunk29.bodies
noncomputable def frames29 : List Nat := frames28 ++ Chunk29.frames
noncomputable def bitmapDelta29 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta28 Chunk29.bitmapDelta
def chunkOracles29 : List (Option (Spt Nat)) := [oracle528, oracle529, oracle530, oracle531, oracle532, oracle533, oracle534, oracle535, oracle536, oracle537, oracle538, oracle539, oracle540, oracle541, oracle542, oracle543]
def oracles29 : List (Option (Spt Nat)) := oracles28 ++ chunkOracles29

theorem compiled29 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words29 (prefixList, 1637) =
    (bodies29, frames29, (BitmapPrepend.prependAppList prefixList bitmapDelta29, 1799)) := by
  unfold words29 bodies29 frames29 bitmapDelta29
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled28 prefixList)
    (Chunk29.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta28))

theorem collected29 :
    StackRawCall.collectInfo bodies29 FrameState27.info = Frames29.info := by
  unfold bodies29
  rw [TableComposition.collectInfo_append, collected28, Frames29.info_eq]

theorem words29_eq :
    (((ConcreteCompilerWord.source.drop 448).take 32).zip oracles29).map
      (fun p => wordFunction p.2 p.1) = words29 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 448).take 16).length = oracles28.length := by decide
  unfold words29 oracles29
  rw [← words28_eq, ← Chunk29.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words30 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words29 ++ Chunk30.words
noncomputable def bodies30 : List (Nat × HolProg 64) := bodies29 ++ Chunk30.bodies
noncomputable def frames30 : List Nat := frames29 ++ Chunk30.frames
noncomputable def bitmapDelta30 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta29 Chunk30.bitmapDelta
def chunkOracles30 : List (Option (Spt Nat)) := [oracle544, oracle545, oracle546, oracle547, oracle548, oracle549, oracle550, oracle551, oracle552, oracle553, oracle554, oracle555, oracle556, oracle557, oracle558, oracle559]
def oracles30 : List (Option (Spt Nat)) := oracles29 ++ chunkOracles30

theorem compiled30 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words30 (prefixList, 1637) =
    (bodies30, frames30, (BitmapPrepend.prependAppList prefixList bitmapDelta30, 1910)) := by
  unfold words30 bodies30 frames30 bitmapDelta30
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled29 prefixList)
    (Chunk30.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta29))

theorem collected30 :
    StackRawCall.collectInfo bodies30 FrameState27.info = Frames30.info := by
  unfold bodies30
  rw [TableComposition.collectInfo_append, collected29, Frames30.info_eq]

theorem words30_eq :
    (((ConcreteCompilerWord.source.drop 448).take 48).zip oracles30).map
      (fun p => wordFunction p.2 p.1) = words30 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 448).take 32).length = oracles29.length := by decide
  unfold words30 oracles30
  rw [← words29_eq, ← Chunk30.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words31 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words30 ++ Chunk31.words
noncomputable def bodies31 : List (Nat × HolProg 64) := bodies30 ++ Chunk31.bodies
noncomputable def frames31 : List Nat := frames30 ++ Chunk31.frames
noncomputable def bitmapDelta31 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta30 Chunk31.bitmapDelta
def chunkOracles31 : List (Option (Spt Nat)) := [oracle560, oracle561, oracle562, oracle563, oracle564, oracle565, oracle566, oracle567, oracle568, oracle569, oracle570, oracle571, oracle572, oracle573, oracle574, oracle575]
def oracles31 : List (Option (Spt Nat)) := oracles30 ++ chunkOracles31

theorem compiled31 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words31 (prefixList, 1637) =
    (bodies31, frames31, (BitmapPrepend.prependAppList prefixList bitmapDelta31, 2007)) := by
  unfold words31 bodies31 frames31 bitmapDelta31
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled30 prefixList)
    (Chunk31.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta30))

theorem collected31 :
    StackRawCall.collectInfo bodies31 FrameState27.info = Frames31.info := by
  unfold bodies31
  rw [TableComposition.collectInfo_append, collected30, Frames31.info_eq]

theorem words31_eq :
    (((ConcreteCompilerWord.source.drop 448).take 64).zip oracles31).map
      (fun p => wordFunction p.2 p.1) = words31 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 448).take 48).length = oracles30.length := by decide
  unfold words31 oracles31
  rw [← words30_eq, ← Chunk31.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words32 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words31 ++ Chunk32.words
noncomputable def bodies32 : List (Nat × HolProg 64) := bodies31 ++ Chunk32.bodies
noncomputable def frames32 : List Nat := frames31 ++ Chunk32.frames
noncomputable def bitmapDelta32 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta31 Chunk32.bitmapDelta
def chunkOracles32 : List (Option (Spt Nat)) := [oracle576, oracle577, oracle578, oracle579, oracle580, oracle581, oracle582, oracle583, oracle584, oracle585, oracle586, oracle587, oracle588, oracle589, oracle590, oracle591]
def oracles32 : List (Option (Spt Nat)) := oracles31 ++ chunkOracles32

theorem compiled32 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words32 (prefixList, 1637) =
    (bodies32, frames32, (BitmapPrepend.prependAppList prefixList bitmapDelta32, 2127)) := by
  unfold words32 bodies32 frames32 bitmapDelta32
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled31 prefixList)
    (Chunk32.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta31))

theorem collected32 :
    StackRawCall.collectInfo bodies32 FrameState27.info = Frames32.info := by
  unfold bodies32
  rw [TableComposition.collectInfo_append, collected31, Frames32.info_eq]

theorem words32_eq :
    (((ConcreteCompilerWord.source.drop 448).take 80).zip oracles32).map
      (fun p => wordFunction p.2 p.1) = words32 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 448).take 64).length = oracles31.length := by decide
  unfold words32 oracles32
  rw [← words31_eq, ← Chunk32.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words33 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words32 ++ Chunk33.words
noncomputable def bodies33 : List (Nat × HolProg 64) := bodies32 ++ Chunk33.bodies
noncomputable def frames33 : List Nat := frames32 ++ Chunk33.frames
noncomputable def bitmapDelta33 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta32 Chunk33.bitmapDelta
def chunkOracles33 : List (Option (Spt Nat)) := [oracle592, oracle593, oracle594, oracle595, oracle596, oracle597, oracle598, oracle599, oracle600, oracle601, oracle602, oracle603, oracle604, oracle605, oracle606, oracle607]
def oracles33 : List (Option (Spt Nat)) := oracles32 ++ chunkOracles33

theorem compiled33 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words33 (prefixList, 1637) =
    (bodies33, frames33, (BitmapPrepend.prependAppList prefixList bitmapDelta33, 2334)) := by
  unfold words33 bodies33 frames33 bitmapDelta33
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled32 prefixList)
    (Chunk33.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta32))

theorem collected33 :
    StackRawCall.collectInfo bodies33 FrameState27.info = Frames33.info := by
  unfold bodies33
  rw [TableComposition.collectInfo_append, collected32, Frames33.info_eq]

theorem words33_eq :
    (((ConcreteCompilerWord.source.drop 448).take 96).zip oracles33).map
      (fun p => wordFunction p.2 p.1) = words33 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 448).take 80).length = oracles32.length := by decide
  unfold words33 oracles33
  rw [← words32_eq, ← Chunk33.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words34 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words33 ++ Chunk34.words
noncomputable def bodies34 : List (Nat × HolProg 64) := bodies33 ++ Chunk34.bodies
noncomputable def frames34 : List Nat := frames33 ++ Chunk34.frames
noncomputable def bitmapDelta34 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta33 Chunk34.bitmapDelta
def chunkOracles34 : List (Option (Spt Nat)) := [oracle608, oracle609, oracle610, oracle611, oracle612, oracle613, oracle614, oracle615, oracle616, oracle617, oracle618, oracle619, oracle620, oracle621, oracle622, oracle623]
def oracles34 : List (Option (Spt Nat)) := oracles33 ++ chunkOracles34

theorem compiled34 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words34 (prefixList, 1637) =
    (bodies34, frames34, (BitmapPrepend.prependAppList prefixList bitmapDelta34, 2525)) := by
  unfold words34 bodies34 frames34 bitmapDelta34
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled33 prefixList)
    (Chunk34.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta33))

theorem collected34 :
    StackRawCall.collectInfo bodies34 FrameState27.info = Frames34.info := by
  unfold bodies34
  rw [TableComposition.collectInfo_append, collected33, Frames34.info_eq]

theorem words34_eq :
    (((ConcreteCompilerWord.source.drop 448).take 112).zip oracles34).map
      (fun p => wordFunction p.2 p.1) = words34 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 448).take 96).length = oracles33.length := by decide
  unfold words34 oracles34
  rw [← words33_eq, ← Chunk34.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words35 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words34 ++ Chunk35.words
noncomputable def bodies35 : List (Nat × HolProg 64) := bodies34 ++ Chunk35.bodies
noncomputable def frames35 : List Nat := frames34 ++ Chunk35.frames
noncomputable def bitmapDelta35 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta34 Chunk35.bitmapDelta
def chunkOracles35 : List (Option (Spt Nat)) := [oracle624, oracle625, oracle626, oracle627, oracle628, oracle629, oracle630, oracle631, oracle632, oracle633, oracle634, oracle635, oracle636, oracle637, oracle638, oracle639]
def oracles35 : List (Option (Spt Nat)) := oracles34 ++ chunkOracles35

theorem compiled35 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words35 (prefixList, 1637) =
    (bodies35, frames35, (BitmapPrepend.prependAppList prefixList bitmapDelta35, 2592)) := by
  unfold words35 bodies35 frames35 bitmapDelta35
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled34 prefixList)
    (Chunk35.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta34))

theorem collected35 :
    StackRawCall.collectInfo bodies35 FrameState27.info = Frames35.info := by
  unfold bodies35
  rw [TableComposition.collectInfo_append, collected34, Frames35.info_eq]

theorem words35_eq :
    (((ConcreteCompilerWord.source.drop 448).take 128).zip oracles35).map
      (fun p => wordFunction p.2 p.1) = words35 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 448).take 112).length = oracles34.length := by decide
  unfold words35 oracles35
  rw [← words34_eq, ← Chunk35.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words36 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words35 ++ Chunk36.words
noncomputable def bodies36 : List (Nat × HolProg 64) := bodies35 ++ Chunk36.bodies
noncomputable def frames36 : List Nat := frames35 ++ Chunk36.frames
noncomputable def bitmapDelta36 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta35 Chunk36.bitmapDelta
def chunkOracles36 : List (Option (Spt Nat)) := [oracle640, oracle641, oracle642, oracle643, oracle644, oracle645, oracle646, oracle647, oracle648, oracle649, oracle650, oracle651, oracle652, oracle653, oracle654, oracle655]
def oracles36 : List (Option (Spt Nat)) := oracles35 ++ chunkOracles36

theorem compiled36 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words36 (prefixList, 1637) =
    (bodies36, frames36, (BitmapPrepend.prependAppList prefixList bitmapDelta36, 2733)) := by
  unfold words36 bodies36 frames36 bitmapDelta36
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled35 prefixList)
    (Chunk36.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta35))

theorem collected36 :
    StackRawCall.collectInfo bodies36 FrameState27.info = Frames36.info := by
  unfold bodies36
  rw [TableComposition.collectInfo_append, collected35, Frames36.info_eq]

theorem words36_eq :
    (((ConcreteCompilerWord.source.drop 448).take 144).zip oracles36).map
      (fun p => wordFunction p.2 p.1) = words36 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 448).take 128).length = oracles35.length := by decide
  unfold words36 oracles36
  rw [← words35_eq, ← Chunk36.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words37 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words36 ++ Chunk37.words
noncomputable def bodies37 : List (Nat × HolProg 64) := bodies36 ++ Chunk37.bodies
noncomputable def frames37 : List Nat := frames36 ++ Chunk37.frames
noncomputable def bitmapDelta37 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta36 Chunk37.bitmapDelta
def chunkOracles37 : List (Option (Spt Nat)) := [oracle656, oracle657, oracle658, oracle659, oracle660, oracle661, oracle662, oracle663, oracle664, oracle665, oracle666, oracle667, oracle668, oracle669, oracle670, oracle671]
def oracles37 : List (Option (Spt Nat)) := oracles36 ++ chunkOracles37

theorem compiled37 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words37 (prefixList, 1637) =
    (bodies37, frames37, (BitmapPrepend.prependAppList prefixList bitmapDelta37, 2787)) := by
  unfold words37 bodies37 frames37 bitmapDelta37
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled36 prefixList)
    (Chunk37.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta36))

theorem collected37 :
    StackRawCall.collectInfo bodies37 FrameState27.info = Frames37.info := by
  unfold bodies37
  rw [TableComposition.collectInfo_append, collected36, Frames37.info_eq]

theorem words37_eq :
    (((ConcreteCompilerWord.source.drop 448).take 160).zip oracles37).map
      (fun p => wordFunction p.2 p.1) = words37 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 448).take 144).length = oracles36.length := by decide
  unfold words37 oracles37
  rw [← words36_eq, ← Chunk37.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words38 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words37 ++ Chunk38.words
noncomputable def bodies38 : List (Nat × HolProg 64) := bodies37 ++ Chunk38.bodies
noncomputable def frames38 : List Nat := frames37 ++ Chunk38.frames
noncomputable def bitmapDelta38 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta37 Chunk38.bitmapDelta
def chunkOracles38 : List (Option (Spt Nat)) := [oracle672, oracle673, oracle674, oracle675, oracle676, oracle677, oracle678, oracle679, oracle680, oracle681, oracle682, oracle683, oracle684, oracle685, oracle686, oracle687]
def oracles38 : List (Option (Spt Nat)) := oracles37 ++ chunkOracles38

theorem compiled38 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words38 (prefixList, 1637) =
    (bodies38, frames38, (BitmapPrepend.prependAppList prefixList bitmapDelta38, 2926)) := by
  unfold words38 bodies38 frames38 bitmapDelta38
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled37 prefixList)
    (Chunk38.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta37))

theorem collected38 :
    StackRawCall.collectInfo bodies38 FrameState27.info = Frames38.info := by
  unfold bodies38
  rw [TableComposition.collectInfo_append, collected37, Frames38.info_eq]

theorem words38_eq :
    (((ConcreteCompilerWord.source.drop 448).take 176).zip oracles38).map
      (fun p => wordFunction p.2 p.1) = words38 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 448).take 160).length = oracles37.length := by decide
  unfold words38 oracles38
  rw [← words37_eq, ← Chunk38.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words39 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words38 ++ Chunk39.words
noncomputable def bodies39 : List (Nat × HolProg 64) := bodies38 ++ Chunk39.bodies
noncomputable def frames39 : List Nat := frames38 ++ Chunk39.frames
noncomputable def bitmapDelta39 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta38 Chunk39.bitmapDelta
def chunkOracles39 : List (Option (Spt Nat)) := [oracle688, oracle689, oracle690, oracle691, oracle692, oracle693, oracle694, oracle695, oracle696, oracle697, oracle698, oracle699, oracle700, oracle701, oracle702, oracle703]
def oracles39 : List (Option (Spt Nat)) := oracles38 ++ chunkOracles39

theorem compiled39 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words39 (prefixList, 1637) =
    (bodies39, frames39, (BitmapPrepend.prependAppList prefixList bitmapDelta39, 3150)) := by
  unfold words39 bodies39 frames39 bitmapDelta39
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled38 prefixList)
    (Chunk39.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta38))

theorem collected39 :
    StackRawCall.collectInfo bodies39 FrameState27.info = Frames39.info := by
  unfold bodies39
  rw [TableComposition.collectInfo_append, collected38, Frames39.info_eq]

theorem words39_eq :
    (((ConcreteCompilerWord.source.drop 448).take 192).zip oracles39).map
      (fun p => wordFunction p.2 p.1) = words39 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 448).take 176).length = oracles38.length := by decide
  unfold words39 oracles39
  rw [← words38_eq, ← Chunk39.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words40 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words39 ++ Chunk40.words
noncomputable def bodies40 : List (Nat × HolProg 64) := bodies39 ++ Chunk40.bodies
noncomputable def frames40 : List Nat := frames39 ++ Chunk40.frames
noncomputable def bitmapDelta40 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta39 Chunk40.bitmapDelta
def chunkOracles40 : List (Option (Spt Nat)) := [oracle704, oracle705, oracle706, oracle707, oracle708, oracle709, oracle710, oracle711, oracle712, oracle713, oracle714, oracle715, oracle716, oracle717, oracle718, oracle719]
def oracles40 : List (Option (Spt Nat)) := oracles39 ++ chunkOracles40

theorem compiled40 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words40 (prefixList, 1637) =
    (bodies40, frames40, (BitmapPrepend.prependAppList prefixList bitmapDelta40, 3231)) := by
  unfold words40 bodies40 frames40 bitmapDelta40
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled39 prefixList)
    (Chunk40.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta39))

theorem collected40 :
    StackRawCall.collectInfo bodies40 FrameState27.info = Frames40.info := by
  unfold bodies40
  rw [TableComposition.collectInfo_append, collected39, Frames40.info_eq]

theorem words40_eq :
    (((ConcreteCompilerWord.source.drop 448).take 208).zip oracles40).map
      (fun p => wordFunction p.2 p.1) = words40 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 448).take 192).length = oracles39.length := by decide
  unfold words40 oracles40
  rw [← words39_eq, ← Chunk40.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words41 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words40 ++ Chunk41.words
noncomputable def bodies41 : List (Nat × HolProg 64) := bodies40 ++ Chunk41.bodies
noncomputable def frames41 : List Nat := frames40 ++ Chunk41.frames
noncomputable def bitmapDelta41 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta40 Chunk41.bitmapDelta
def chunkOracles41 : List (Option (Spt Nat)) := [oracle720, oracle721, oracle722, oracle723, oracle724, oracle725, oracle726, oracle727, oracle728, oracle729, oracle730, oracle731, oracle732, oracle733, oracle734, oracle735]
def oracles41 : List (Option (Spt Nat)) := oracles40 ++ chunkOracles41

theorem compiled41 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words41 (prefixList, 1637) =
    (bodies41, frames41, (BitmapPrepend.prependAppList prefixList bitmapDelta41, 3267)) := by
  unfold words41 bodies41 frames41 bitmapDelta41
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled40 prefixList)
    (Chunk41.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta40))

theorem collected41 :
    StackRawCall.collectInfo bodies41 FrameState27.info = Frames41.info := by
  unfold bodies41
  rw [TableComposition.collectInfo_append, collected40, Frames41.info_eq]

theorem words41_eq :
    (((ConcreteCompilerWord.source.drop 448).take 224).zip oracles41).map
      (fun p => wordFunction p.2 p.1) = words41 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 448).take 208).length = oracles40.length := by decide
  unfold words41 oracles41
  rw [← words40_eq, ← Chunk41.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words42 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words41 ++ Chunk42.words
noncomputable def bodies42 : List (Nat × HolProg 64) := bodies41 ++ Chunk42.bodies
noncomputable def frames42 : List Nat := frames41 ++ Chunk42.frames
noncomputable def bitmapDelta42 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta41 Chunk42.bitmapDelta
def chunkOracles42 : List (Option (Spt Nat)) := [oracle736, oracle737, oracle738, oracle739, oracle740, oracle741, oracle742, oracle743, oracle744, oracle745, oracle746, oracle747, oracle748, oracle749, oracle750, oracle751]
def oracles42 : List (Option (Spt Nat)) := oracles41 ++ chunkOracles42

theorem compiled42 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words42 (prefixList, 1637) =
    (bodies42, frames42, (BitmapPrepend.prependAppList prefixList bitmapDelta42, 3319)) := by
  unfold words42 bodies42 frames42 bitmapDelta42
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled41 prefixList)
    (Chunk42.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta41))

theorem collected42 :
    StackRawCall.collectInfo bodies42 FrameState27.info = Frames42.info := by
  unfold bodies42
  rw [TableComposition.collectInfo_append, collected41, Frames42.info_eq]

theorem words42_eq :
    (((ConcreteCompilerWord.source.drop 448).take 240).zip oracles42).map
      (fun p => wordFunction p.2 p.1) = words42 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 448).take 224).length = oracles41.length := by decide
  unfold words42 oracles42
  rw [← words41_eq, ← Chunk42.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words43 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words42 ++ Chunk43.words
noncomputable def bodies43 : List (Nat × HolProg 64) := bodies42 ++ Chunk43.bodies
noncomputable def frames43 : List Nat := frames42 ++ Chunk43.frames
noncomputable def bitmapDelta43 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta42 Chunk43.bitmapDelta
def chunkOracles43 : List (Option (Spt Nat)) := [oracle752, oracle753, oracle754, oracle755, oracle756, oracle757, oracle758, oracle759, oracle760, oracle761, oracle762, oracle763, oracle764, oracle765, oracle766, oracle767]
def oracles43 : List (Option (Spt Nat)) := oracles42 ++ chunkOracles43

theorem compiled43 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words43 (prefixList, 1637) =
    (bodies43, frames43, (BitmapPrepend.prependAppList prefixList bitmapDelta43, 3453)) := by
  unfold words43 bodies43 frames43 bitmapDelta43
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled42 prefixList)
    (Chunk43.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta42))

theorem collected43 :
    StackRawCall.collectInfo bodies43 FrameState27.info = Frames43.info := by
  unfold bodies43
  rw [TableComposition.collectInfo_append, collected42, Frames43.info_eq]

theorem words43_eq :
    (((ConcreteCompilerWord.source.drop 448).take 256).zip oracles43).map
      (fun p => wordFunction p.2 p.1) = words43 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 448).take 240).length = oracles42.length := by decide
  unfold words43 oracles43
  rw [← words42_eq, ← Chunk43.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words44 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words43 ++ Chunk44.words
noncomputable def bodies44 : List (Nat × HolProg 64) := bodies43 ++ Chunk44.bodies
noncomputable def frames44 : List Nat := frames43 ++ Chunk44.frames
noncomputable def bitmapDelta44 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta43 Chunk44.bitmapDelta
def chunkOracles44 : List (Option (Spt Nat)) := [oracle768, oracle769, oracle770, oracle771, oracle772, oracle773, oracle774, oracle775, oracle776, oracle777, oracle778, oracle779, oracle780, oracle781, oracle782, oracle783]
def oracles44 : List (Option (Spt Nat)) := oracles43 ++ chunkOracles44

theorem compiled44 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words44 (prefixList, 1637) =
    (bodies44, frames44, (BitmapPrepend.prependAppList prefixList bitmapDelta44, 3617)) := by
  unfold words44 bodies44 frames44 bitmapDelta44
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled43 prefixList)
    (Chunk44.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta43))

theorem collected44 :
    StackRawCall.collectInfo bodies44 FrameState27.info = Frames44.info := by
  unfold bodies44
  rw [TableComposition.collectInfo_append, collected43, Frames44.info_eq]

theorem words44_eq :
    (((ConcreteCompilerWord.source.drop 448).take 272).zip oracles44).map
      (fun p => wordFunction p.2 p.1) = words44 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 448).take 256).length = oracles43.length := by decide
  unfold words44 oracles44
  rw [← words43_eq, ← Chunk44.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words45 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words44 ++ Chunk45.words
noncomputable def bodies45 : List (Nat × HolProg 64) := bodies44 ++ Chunk45.bodies
noncomputable def frames45 : List Nat := frames44 ++ Chunk45.frames
noncomputable def bitmapDelta45 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta44 Chunk45.bitmapDelta
def chunkOracles45 : List (Option (Spt Nat)) := [oracle784, oracle785, oracle786, oracle787, oracle788, oracle789, oracle790, oracle791, oracle792, oracle793, oracle794, oracle795, oracle796, oracle797, oracle798, oracle799]
def oracles45 : List (Option (Spt Nat)) := oracles44 ++ chunkOracles45

theorem compiled45 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words45 (prefixList, 1637) =
    (bodies45, frames45, (BitmapPrepend.prependAppList prefixList bitmapDelta45, 3840)) := by
  unfold words45 bodies45 frames45 bitmapDelta45
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled44 prefixList)
    (Chunk45.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta44))

theorem collected45 :
    StackRawCall.collectInfo bodies45 FrameState27.info = Frames45.info := by
  unfold bodies45
  rw [TableComposition.collectInfo_append, collected44, Frames45.info_eq]

theorem words45_eq :
    (((ConcreteCompilerWord.source.drop 448).take 288).zip oracles45).map
      (fun p => wordFunction p.2 p.1) = words45 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 448).take 272).length = oracles44.length := by decide
  unfold words45 oracles45
  rw [← words44_eq, ← Chunk45.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words46 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words45 ++ Chunk46.words
noncomputable def bodies46 : List (Nat × HolProg 64) := bodies45 ++ Chunk46.bodies
noncomputable def frames46 : List Nat := frames45 ++ Chunk46.frames
noncomputable def bitmapDelta46 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta45 Chunk46.bitmapDelta
def chunkOracles46 : List (Option (Spt Nat)) := [oracle800, oracle801, oracle802, oracle803, oracle804, oracle805, oracle806, oracle807, oracle808, oracle809, oracle810, oracle811, oracle812, oracle813, oracle814, oracle815]
def oracles46 : List (Option (Spt Nat)) := oracles45 ++ chunkOracles46

theorem compiled46 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words46 (prefixList, 1637) =
    (bodies46, frames46, (BitmapPrepend.prependAppList prefixList bitmapDelta46, 4058)) := by
  unfold words46 bodies46 frames46 bitmapDelta46
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled45 prefixList)
    (Chunk46.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta45))

theorem collected46 :
    StackRawCall.collectInfo bodies46 FrameState27.info = Frames46.info := by
  unfold bodies46
  rw [TableComposition.collectInfo_append, collected45, Frames46.info_eq]

theorem words46_eq :
    (((ConcreteCompilerWord.source.drop 448).take 304).zip oracles46).map
      (fun p => wordFunction p.2 p.1) = words46 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 448).take 288).length = oracles45.length := by decide
  unfold words46 oracles46
  rw [← words45_eq, ← Chunk46.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words47 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words46 ++ Chunk47.words
noncomputable def bodies47 : List (Nat × HolProg 64) := bodies46 ++ Chunk47.bodies
noncomputable def frames47 : List Nat := frames46 ++ Chunk47.frames
noncomputable def bitmapDelta47 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta46 Chunk47.bitmapDelta
def chunkOracles47 : List (Option (Spt Nat)) := [oracle816, oracle817, oracle818, oracle819, oracle820, oracle821, oracle822, oracle823, oracle824, oracle825, oracle826, oracle827, oracle828, oracle829, oracle830, oracle831]
def oracles47 : List (Option (Spt Nat)) := oracles46 ++ chunkOracles47

theorem compiled47 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words47 (prefixList, 1637) =
    (bodies47, frames47, (BitmapPrepend.prependAppList prefixList bitmapDelta47, 4127)) := by
  unfold words47 bodies47 frames47 bitmapDelta47
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled46 prefixList)
    (Chunk47.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta46))

theorem collected47 :
    StackRawCall.collectInfo bodies47 FrameState27.info = Frames47.info := by
  unfold bodies47
  rw [TableComposition.collectInfo_append, collected46, Frames47.info_eq]

theorem words47_eq :
    (((ConcreteCompilerWord.source.drop 448).take 320).zip oracles47).map
      (fun p => wordFunction p.2 p.1) = words47 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 448).take 304).length = oracles46.length := by decide
  unfold words47 oracles47
  rw [← words46_eq, ← Chunk47.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words48 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words47 ++ Chunk48.words
noncomputable def bodies48 : List (Nat × HolProg 64) := bodies47 ++ Chunk48.bodies
noncomputable def frames48 : List Nat := frames47 ++ Chunk48.frames
noncomputable def bitmapDelta48 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta47 Chunk48.bitmapDelta
def chunkOracles48 : List (Option (Spt Nat)) := [oracle832, oracle833, oracle834, oracle835, oracle836, oracle837, oracle838, oracle839, oracle840, oracle841, oracle842, oracle843, oracle844, oracle845, oracle846, oracle847]
def oracles48 : List (Option (Spt Nat)) := oracles47 ++ chunkOracles48

theorem compiled48 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words48 (prefixList, 1637) =
    (bodies48, frames48, (BitmapPrepend.prependAppList prefixList bitmapDelta48, 4240)) := by
  unfold words48 bodies48 frames48 bitmapDelta48
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled47 prefixList)
    (Chunk48.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta47))

theorem collected48 :
    StackRawCall.collectInfo bodies48 FrameState27.info = Frames48.info := by
  unfold bodies48
  rw [TableComposition.collectInfo_append, collected47, Frames48.info_eq]

theorem words48_eq :
    (((ConcreteCompilerWord.source.drop 448).take 336).zip oracles48).map
      (fun p => wordFunction p.2 p.1) = words48 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 448).take 320).length = oracles47.length := by decide
  unfold words48 oracles48
  rw [← words47_eq, ← Chunk48.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words49 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words48 ++ Chunk49.words
noncomputable def bodies49 : List (Nat × HolProg 64) := bodies48 ++ Chunk49.bodies
noncomputable def frames49 : List Nat := frames48 ++ Chunk49.frames
noncomputable def bitmapDelta49 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta48 Chunk49.bitmapDelta
def chunkOracles49 : List (Option (Spt Nat)) := [oracle848, oracle849, oracle850, oracle851, oracle852, oracle853, oracle854, oracle855, oracle856, oracle857, oracle858, oracle859, oracle860, oracle861, oracle862, oracle863]
def oracles49 : List (Option (Spt Nat)) := oracles48 ++ chunkOracles49

theorem compiled49 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words49 (prefixList, 1637) =
    (bodies49, frames49, (BitmapPrepend.prependAppList prefixList bitmapDelta49, 4519)) := by
  unfold words49 bodies49 frames49 bitmapDelta49
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled48 prefixList)
    (Chunk49.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta48))

theorem collected49 :
    StackRawCall.collectInfo bodies49 FrameState27.info = Frames49.info := by
  unfold bodies49
  rw [TableComposition.collectInfo_append, collected48, Frames49.info_eq]

theorem words49_eq :
    (((ConcreteCompilerWord.source.drop 448).take 352).zip oracles49).map
      (fun p => wordFunction p.2 p.1) = words49 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 448).take 336).length = oracles48.length := by decide
  unfold words49 oracles49
  rw [← words48_eq, ← Chunk49.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable def words50 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words49 ++ Chunk50.words
noncomputable def bodies50 : List (Nat × HolProg 64) := bodies49 ++ Chunk50.bodies
noncomputable def frames50 : List Nat := frames49 ++ Chunk50.frames
noncomputable def bitmapDelta50 : AppList (BitVec 64) := BitmapPrepend.prependAppList bitmapDelta49 Chunk50.bitmapDelta
def chunkOracles50 : List (Option (Spt Nat)) := [oracle864, oracle865, oracle866, oracle867, oracle868, oracle869, oracle870, oracle871, oracle872, oracle873, oracle874, oracle875, oracle876, oracle877]
def oracles50 : List (Option (Spt Nat)) := oracles49 ++ chunkOracles50

theorem compiled50 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words50 (prefixList, 1637) =
    (bodies50, frames50, (BitmapPrepend.prependAppList prefixList bitmapDelta50, 4603)) := by
  unfold words50 bodies50 frames50 bitmapDelta50
  rw [BitmapPrepend.prependAppList_assoc]
  exact TableComposition.compile_append _ _ _ _ _ _ _ _ _
    (compiled49 prefixList)
    (Chunk50.compiled (BitmapPrepend.prependAppList prefixList bitmapDelta49))

theorem collected50 :
    StackRawCall.collectInfo bodies50 FrameState27.info = Frames50.info := by
  unfold bodies50
  rw [TableComposition.collectInfo_append, collected49, Frames50.info_eq]

theorem words50_eq :
    (((ConcreteCompilerWord.source.drop 448).take 366).zip oracles50).map
      (fun p => wordFunction p.2 p.1) = words50 := by
  have hlen1 : ((ConcreteCompilerWord.source.drop 448).take 352).length = oracles49.length := by decide
  unfold words50 oracles50
  rw [← words49_eq, ← Chunk50.words_eq, ← List.map_append, ← List.zip_append hlen1]
  congr 1

noncomputable abbrev words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := words50
noncomputable abbrev bodies : List (Nat × HolProg 64) := bodies50
noncomputable abbrev frames : List Nat := frames50
noncomputable abbrev bitmapDelta : AppList (BitVec 64) := bitmapDelta50
abbrev oracles : List (Option (Spt Nat)) := oracles50

theorem oracles_length : oracles.length = 366 := by decide

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 1637) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 4603)) :=
  compiled50 prefixList

theorem collected :
    StackRawCall.collectInfo bodies FrameState27.info = GlobalFrameInfo.info :=
  collected50.trans Frames50.info_eq_global

theorem words_eq :
    ((ConcreteCompilerWord.source.drop 448).zip oracles).map
      (fun p => wordFunction p.2 p.1) = words := by
  have htake : (ConcreteCompilerWord.source.drop 448).take 366 = ConcreteCompilerWord.source.drop 448 := by
    apply List.take_of_length_le
    decide
  rw [← htake]
  exact words50_eq

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Table28_50
