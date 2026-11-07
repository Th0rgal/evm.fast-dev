import InitECandidate.Solver.Wave8Stage.ConcreteM7313.AllTables
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.AllBounded
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Table04
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Table05_27
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded00_27
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Table28_50
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Bounded28_50
import InitECandidate.Solver.Wave8Stage.DirectBackendBound

/-!
# Proofs-free concrete Stage 5 backend bound assembly (`ConcreteBackendBound`)

Bridges the Proofs-free concrete `M = 7313` table/frame/cost infrastructure
(`AllTables` + `AllBounded`) directly to `DirectBackendBound.concreteBackendBound`
and `ConcreteStageTransferBridge.BackendBound`, without importing `InitECandidate.Proofs`
or `ConcreteOracleWitness`.

Two turnkey entry points are exposed:
1. `concreteBackendBound_of_table`: closes `DirectBackendBound.concreteBackendBound` from
   a complete `Table50`-style `(words, bodies, frames, bitmaps, info = GlobalFrameInfo.info)`
   plus `Bounded GlobalFrameInfo.info bodies` (native stubs are already discharged by
   `AllBounded.nativeStubs_bounded`).
2. `concreteBackendBound_of_missing_segments`: closes `DirectBackendBound.concreteBackendBound`
   directly from the two remaining parallel stream obligations (`Segment00To27` for
   `Chunk00..27` and `Segment34To49` for `Chunk34..49`), with `Chunk28..33`, `Chunk50`,
   `Frames28..33`, `Bounded28..33`, `Bounded50`, and `nativeStubs_bounded` already wired in.
-/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteBackendBound
open InitE Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8Stage
open InitECandidate.Solver.Wave8Stage.ConcreteM7313
open InitECandidate.Solver.Wave8Stage.ConcreteM7313.BackendDecomposition
open InitECandidate.Solver.Wave8Stage.ConcreteM7313.StackPasses
open InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget

/-- Certified obligations for the `Chunk00..27` prefix (`448` guest functions `64..511`,
bitmap offset `1 → 1637`, frame map `.ln → FrameState27.info`). -/
structure Segment00To27 : Prop where
  exists_segment :
    ∃ (words : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
      (bodies : List (Nat × HolProg 64))
      (frames : List Nat)
      (bitmap27 : AppList (BitVec 64)),
      ((ConcreteCompilerWord.source.take 448).zip (oracles.take 448)).map
        (fun p => wordFunction p.2 p.1) = words ∧
      WordToStack.Native.compileWordToStackNative riscvConfig false registers
        words (.list [4], 1) = (bodies, frames, (bitmap27, 1637)) ∧
      StackRawCall.collectInfo (nativeStubs ++ bodies) .ln = FrameState27.info ∧
      Bounded GlobalFrameInfo.info bodies

/-- Construct `Segment00To27` from `Table02` (`Chunk00..02`, already certified) plus the
remaining `Chunk03..27` tail (`400` guest functions `112..511`). -/
theorem segment00To27_of_03To27
    (words03To27 : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (bodies03To27 : List (Nat × HolProg 64))
    (frames03To27 : List Nat)
    (bitmap27 : AppList (BitVec 64))
    (hw03To27 : (((ConcreteCompilerWord.source.drop 48).take 400).zip
      ((oracles.drop 48).take 400)).map (fun p => wordFunction p.2 p.1) = words03To27)
    (hc03To27 : WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words03To27 Function111.stackResult.2.2 = (bodies03To27, frames03To27, (bitmap27, 1637)))
    (hcol03To27 : StackRawCall.collectInfo bodies03To27 Frames02.info = FrameState27.info)
    (hb00To02 : Bounded GlobalFrameInfo.info Table02.bodies)
    (hb03To27 : Bounded GlobalFrameInfo.info bodies03To27) :
    Segment00To27 := by
  refine ⟨⟨Table02.words ++ words03To27, Table02.bodies ++ bodies03To27,
    Table02.frames ++ frames03To27, bitmap27,
    AllTables.words00To27_of_03To27 words03To27 hw03To27,
    TableComposition.compile_append _ _ _ _ _ _ _ _ _ Table02.compiled hc03To27,
    ?_, bounded_append GlobalFrameInfo.info _ _ hb00To02 hb03To27⟩⟩
  rw [← List.append_assoc, TableComposition.collectInfo_append, Table02.collected, hcol03To27]

/-- Construct `Segment00To27` from Stream B (`Chunk00..04`, `80` functions `64..143`) and
Stream C (`Chunk05..27`, `368` functions `144..511`). -/
theorem segment00To27_of_streamB_and_streamC
    (words00To04 words05To27 : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (bodies00To04 bodies05To27 : List (Nat × HolProg 64))
    (frames00To04 frames05To27 : List Nat)
    (state04 : AppList (BitVec 64) × Nat)
    (bitmap27 : AppList (BitVec 64))
    (info04 : Spt Nat)
    (hw00To04 : ((ConcreteCompilerWord.source.take 80).zip (oracles.take 80)).map
      (fun p => wordFunction p.2 p.1) = words00To04)
    (hw05To27 : (((ConcreteCompilerWord.source.drop 80).take 368).zip
      ((oracles.drop 80).take 368)).map (fun p => wordFunction p.2 p.1) = words05To27)
    (hc00To04 : WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words00To04 (.list [4], 1) = (bodies00To04, frames00To04, state04))
    (hc05To27 : WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words05To27 state04 = (bodies05To27, frames05To27, (bitmap27, 1637)))
    (hcol00To04 : StackRawCall.collectInfo (nativeStubs ++ bodies00To04) .ln = info04)
    (hcol05To27 : StackRawCall.collectInfo bodies05To27 info04 = FrameState27.info)
    (hb00To04 : Bounded GlobalFrameInfo.info bodies00To04)
    (hb05To27 : Bounded GlobalFrameInfo.info bodies05To27) :
    Segment00To27 := by
  refine ⟨⟨words00To04 ++ words05To27, bodies00To04 ++ bodies05To27,
    frames00To04 ++ frames05To27, bitmap27,
    AllTables.words00To27_of_00To04_and_05To27 words00To04 words05To27 hw00To04 hw05To27,
    TableComposition.compile_append _ _ _ _ _ _ _ _ _ hc00To04 hc05To27,
    ?_, bounded_append GlobalFrameInfo.info _ _ hb00To04 hb05To27⟩⟩
  rw [← List.append_assoc, TableComposition.collectInfo_append, hcol00To04, hcol05To27]

/-- Certified obligations for the `Chunk34..49` middle-tail segment (`256` guest functions
`608..863`, bitmap offset `2334 → 4519`, frame map `Frames33.info → GlobalFrameInfo.info`
after `Chunk50`). -/
structure Segment34To49 : Prop where
  exists_segment :
    ∃ (words : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
      (bodies : List (Nat × HolProg 64))
      (frames : List Nat)
      (bitmapDelta : AppList (BitVec 64)),
      (((ConcreteCompilerWord.source.drop 544).take 256).zip
        ((oracles.drop 544).take 256)).map (fun p => wordFunction p.2 p.1) = words ∧
      (∀ prefixList : AppList (BitVec 64),
        WordToStack.Native.compileWordToStackNative riscvConfig false registers
          words (prefixList, 2334) =
          (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 4519))) ∧
      StackRawCall.collectInfo (bodies ++ Chunk50.bodies) Frames33.info = GlobalFrameInfo.info ∧
      Bounded GlobalFrameInfo.info bodies

/-- Close `DirectBackendBound.concreteBackendBound` from any full-guest table whose
frame map equals `GlobalFrameInfo.info`; `nativeStubs` are discharged automatically by
`AllBounded.nativeStubs_bounded`. -/
theorem concreteBackendBound_of_table
    (words : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (bodies : List (Nat × HolProg 64))
    (frames : List Nat)
    (bitmaps : AppList (BitVec 64) × Nat)
    (info : Spt Nat)
    (hwords : (ConcreteCompilerWord.source.zip oracles).map (fun p => wordFunction p.2 p.1) = words)
    (hcompiled : WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (.list [4], 1) = (bodies, frames, bitmaps))
    (hcollected : StackRawCall.collectInfo (nativeStubs ++ bodies) .ln = info)
    (hinfo : info = GlobalFrameInfo.info)
    (hbounded : Bounded GlobalFrameInfo.info bodies) :
    DirectBackendBound.concreteBackendBound := by
  refine ⟨bodies, frames, bitmaps, GlobalFrameInfo.info, ?_, ?_, ?_⟩
  · rw [hwords]
    exact hcompiled
  · rw [hcollected, hinfo]
  · exact bounded_append GlobalFrameInfo.info nativeStubs bodies
      AllBounded.nativeStubs_bounded hbounded

/-- Close `DirectBackendBound.concreteBackendBound` from `Segment00To27` (`Chunk00..27`)
and `Segment34To49` (`Chunk34..49`), composing the already-certified `Chunk28..33`,
`Chunk50`, `Frames28..33`, `Bounded28..33`, `Bounded50`, and `nativeStubs_bounded`. -/
theorem concreteBackendBound_of_missing_segments
    (seg00To27 : Segment00To27)
    (seg34To49 : Segment34To49) :
    DirectBackendBound.concreteBackendBound := by
  rcases seg00To27.exists_segment with
    ⟨words00To27, bodies00To27, frames00To27, bitmap27, hw00, hc00, hcol00, hb00⟩
  rcases seg34To49.exists_segment with
    ⟨words34To49, bodies34To49, frames34To49, delta34To49, hw34, hc34, hcol34, hb34⟩
  let prefix34 := BitmapPrepend.prependAppList bitmap27 AllTables.bitmapDelta28To33
  let bitmap49 := BitmapPrepend.prependAppList prefix34 delta34To49
  have hcomp := AllTables.compiled_all_of_segments
    words00To27 words34To49 bodies00To27 bodies34To49 frames00To27 frames34To49
    bitmap27 bitmap49 hw00 hw34 hc00 (hc34 prefix34)
  have hcol := AllTables.collected_all_of_segments
    bodies00To27 bodies34To49 hcol00 hcol34
  have hbound : Bounded GlobalFrameInfo.info
      (nativeStubs ++
        (bodies00To27 ++ AllTables.bodies28To33 ++ bodies34To49 ++ Chunk50.bodies)) := by
    simpa only [AllTables.bodies28To33, AllBounded.bodies28To33] using
      AllBounded.all_bounded_of_segments bodies00To27 bodies34To49 hb00 hb34
  exact ⟨bodies00To27 ++ AllTables.bodies28To33 ++ bodies34To49 ++ Chunk50.bodies,
    frames00To27 ++ AllTables.frames28To33 ++ frames34To49 ++ Chunk50.frames,
    (BitmapPrepend.prependAppList bitmap49 Chunk50.bitmapDelta, 4603),
    GlobalFrameInfo.info, hcomp, hcol, hbound⟩

/-- `BackendBound w` for any concrete compilation witness with `w.oracles = ConcreteM7313.oracles`
once `Segment00To27` and `Segment34To49` are supplied. -/
theorem backendBound_of_missing_segments
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = oracles)
    (seg00To27 : Segment00To27)
    (seg34To49 : Segment34To49) :
    ConcreteStageTransferBridge.BackendBound w :=
  DirectBackendBound.backendBound_of_concrete w same
    (concreteBackendBound_of_missing_segments seg00To27 seg34To49)

theorem oracles_drop_48_take_16 :
    (oracles.drop 48).take 16 = [oracle112, oracle113, oracle114, oracle115, oracle116, oracle117, oracle118, oracle119,
      oracle120, oracle121, oracle122, oracle123, oracle124, oracle125, oracle126, oracle127] := rfl

theorem oracles_drop_64_take_16 :
    (oracles.drop 64).take 16 = [oracle128, oracle129, oracle130, oracle131, oracle132, oracle133, oracle134, oracle135,
      oracle136, oracle137, oracle138, oracle139, oracle140, oracle141, oracle142, oracle143] := rfl

theorem words03_eq :
    ((ConcreteCompilerWord.source.take 64).zip (oracles.take 64)).map
      (fun p => wordFunction p.2 p.1) = Table03.words := by
  have hs : ConcreteCompilerWord.source.length = 814 := rfl
  have ho : oracles.length = 814 := oracles_length
  have ht1 : (ConcreteCompilerWord.source.take 64).take 48 = ConcreteCompilerWord.source.take 48 := by
    simp [List.take_take]
  have ho1 : (oracles.take 64).take 48 = oracles.take 48 := by
    simp [List.take_take]
  have ht2 : (ConcreteCompilerWord.source.take 64).drop 48 = (ConcreteCompilerWord.source.drop 48).take 16 := by
    simp [List.drop_take]
  have ho2 : (oracles.take 64).drop 48 = (oracles.drop 48).take 16 := by
    simp [List.drop_take]
  rw [AllTables.zip_map_split (fun p => wordFunction p.2 p.1) 48
      (ConcreteCompilerWord.source.take 64) (oracles.take 64) (by simp [hs, ho]),
      ht1, ho1, ht2, ho2, AllTables.words02_eq, oracles_drop_48_take_16, Chunk03.words_eq]
  rfl

theorem words04_eq :
    ((ConcreteCompilerWord.source.take 80).zip (oracles.take 80)).map
      (fun p => wordFunction p.2 p.1) = Table04.words := by
  have hs : ConcreteCompilerWord.source.length = 814 := rfl
  have ho : oracles.length = 814 := oracles_length
  have ht1 : (ConcreteCompilerWord.source.take 80).take 64 = ConcreteCompilerWord.source.take 64 := by
    simp [List.take_take]
  have ho1 : (oracles.take 80).take 64 = oracles.take 64 := by
    simp [List.take_take]
  have ht2 : (ConcreteCompilerWord.source.take 80).drop 64 = (ConcreteCompilerWord.source.drop 64).take 16 := by
    simp [List.drop_take]
  have ho2 : (oracles.take 80).drop 64 = (oracles.drop 64).take 16 := by
    simp [List.drop_take]
  rw [AllTables.zip_map_split (fun p => wordFunction p.2 p.1) 64
      (ConcreteCompilerWord.source.take 80) (oracles.take 80) (by simp [hs, ho]),
      ht1, ho1, ht2, ho2, words03_eq, oracles_drop_64_take_16, Chunk04.words_eq]
  rfl

theorem oracles_05_27_eq : (oracles.drop 80).take 368 = Table05_27.oracles := rfl

theorem oracles_28_50_eq : oracles.drop 448 = Table28_50.oracles := rfl

theorem words05_27_eq :
    (((ConcreteCompilerWord.source.drop 80).take 368).zip
      ((oracles.drop 80).take 368)).map (fun p => wordFunction p.2 p.1) = Table05_27.words := by
  rw [oracles_05_27_eq]
  exact Table05_27.words_eq

theorem stackResult143_offset : Function143.stackResult.2.2 = (Function143.stackResult.2.2.1, 107) := by
  apply Prod.ext rfl
  decide

theorem segment00To27_proved : Segment00To27 := by
  refine segment00To27_of_streamB_and_streamC
    Table04.words Table05_27.words Table04.bodies Table05_27.bodies
    Table04.frames Table05_27.frames Function143.stackResult.2.2
    (BitmapPrepend.prependAppList Function143.stackResult.2.2.1 Table05_27.bitmapDelta)
    Frames04.info
    words04_eq words05_27_eq Table04.compiled ?_ Table04.collected Table05_27.collected
    Bounded00_27.bounded04 Bounded00_27.bounded05_27
  rw [stackResult143_offset]
  exact Table05_27.compiled Function143.stackResult.2.2.1

theorem concreteBackendBound : DirectBackendBound.concreteBackendBound := by
  rcases segment00To27_proved.exists_segment with
    ⟨words00To27, bodies00To27, frames00To27, bitmap27, hw00, hc00, hcol00, hb00⟩
  have hs : ConcreteCompilerWord.source.length = 814 := rfl
  have ho : oracles.length = 814 := oracles_length
  have hwords :
      (ConcreteCompilerWord.source.zip oracles).map (fun p => wordFunction p.2 p.1) =
        words00To27 ++ Table28_50.words := by
    rw [AllTables.zip_map_split (fun p => wordFunction p.2 p.1) 448
        ConcreteCompilerWord.source oracles (by simp [hs, ho]),
        hw00, oracles_28_50_eq, Table28_50.words_eq]
  have hcompiled :=
    TableComposition.compile_append _ _ _ _ _ _ _ _ _ hc00 (Table28_50.compiled bitmap27)
  have hcollected :
      StackRawCall.collectInfo (nativeStubs ++ (bodies00To27 ++ Table28_50.bodies)) .ln =
        GlobalFrameInfo.info := by
    rw [← List.append_assoc, TableComposition.collectInfo_append, hcol00, Table28_50.collected]
  have hbounded :=
    bounded_append GlobalFrameInfo.info _ _ hb00 Bounded28_50.bounded
  exact concreteBackendBound_of_table
    (words00To27 ++ Table28_50.words)
    (bodies00To27 ++ Table28_50.bodies)
    (frames00To27 ++ Table28_50.frames)
    (BitmapPrepend.prependAppList bitmap27 Table28_50.bitmapDelta, 4603)
    GlobalFrameInfo.info
    hwords hcompiled hcollected rfl hbounded

theorem backendBound
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = oracles) :
    ConcreteStageTransferBridge.BackendBound w :=
  DirectBackendBound.backendBound_of_concrete w same concreteBackendBound

end InitECandidate.Solver.Wave8Stage.ConcreteBackendBound
