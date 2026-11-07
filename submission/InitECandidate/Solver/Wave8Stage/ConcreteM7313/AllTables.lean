import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Oracles
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Table02
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames33
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk50
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo

/-!
# Proofs-free Stage 5 word/stack/frame table composition (`AllTables`)

Composes the landed word-to-stack compilation, oracle-zip list-slice spine, and
`StackRawCall.collectInfo` frame-discovery tables across:
* `Table02` (`Chunk00..02`, functions `64..111`, `48` functions),
* `Chunk28..33` + `Frames28..33` (functions `512..607`, `96` functions, bitmap offsets
  `1637 → 2334`, frame discovery `FrameState27.info → Frames33.info`), and
* `Chunk50` (functions `864..877`, `14` functions, bitmap offsets `4519 → 4603`),

and provides the exact four-segment composition combinators (`0..447`, `448..543`,
`544..799`, `800..813` = `814` guest functions) that `ConcreteBackendBound` uses to close
`DirectBackendBound.concreteBackendBound` once `Chunk03..27` and `Chunk34..49` plug in.
Nothing in this module imports `InitECandidate.Proofs`.
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.AllTables
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition

/-! ## Generic `zip`/`map`/`drop`/`take` list-slice spine lemmas -/

theorem zip_map_split {α β γ : Type} (f : α × β → γ)
    (n : Nat) (xs : List α) (ys : List β)
    (hn : (xs.take n).length = (ys.take n).length) :
    (xs.zip ys).map f =
      ((xs.take n).zip (ys.take n)).map f ++
        ((xs.drop n).zip (ys.drop n)).map f := by
  have hx : xs = xs.take n ++ xs.drop n := (List.take_append_drop n xs).symm
  have hy : ys = ys.take n ++ ys.drop n := (List.take_append_drop n ys).symm
  conv => lhs; rw [hx, hy]
  rw [List.zip_append hn, List.map_append]

theorem zip_map_drop_split {α β γ : Type} (f : α × β → γ)
    (d k : Nat) (xs : List α) (ys : List β)
    (hk : ((xs.drop d).take k).length = ((ys.drop d).take k).length) :
    ((xs.drop d).zip (ys.drop d)).map f =
      (((xs.drop d).take k).zip ((ys.drop d).take k)).map f ++
        ((xs.drop (d + k)).zip (ys.drop (d + k))).map f := by
  have h := zip_map_split f k (xs.drop d) (ys.drop d) hk
  simpa only [List.drop_drop] using h

theorem four_way_zip_map_split {α β γ : Type} (f : α × β → γ)
    (xs : List α) (ys : List β)
    (hx : xs.length = 814) (hy : ys.length = 814) :
    (xs.zip ys).map f =
      ((xs.take 448).zip (ys.take 448)).map f ++
      (((xs.drop 448).take 96).zip ((ys.drop 448).take 96)).map f ++
      (((xs.drop 544).take 256).zip ((ys.drop 544).take 256)).map f ++
      (((xs.drop 800).take 14).zip ((ys.drop 800).take 14)).map f := by
  have h1 : (xs.take 448).length = (ys.take 448).length := by simp [hx, hy]
  have h2 : ((xs.drop 448).take 96).length = ((ys.drop 448).take 96).length := by simp [hx, hy]
  have h3 : ((xs.drop 544).take 256).length = ((ys.drop 544).take 256).length := by simp [hx, hy]
  have h4x : xs.drop 814 = [] := List.drop_eq_nil_of_le (by omega)
  have h4y : ys.drop 814 = [] := List.drop_eq_nil_of_le (by omega)
  have h5x : (xs.drop 800).take 14 = xs.drop 800 := List.take_of_length_le (by simp [hx])
  have h5y : (ys.drop 800).take 14 = ys.drop 800 := List.take_of_length_le (by simp [hy])
  rw [zip_map_split f 448 xs ys h1]
  rw [zip_map_drop_split f 448 96 xs ys h2]
  rw [show 448 + 96 = 544 from rfl]
  rw [zip_map_drop_split f 544 256 xs ys h3]
  rw [show 544 + 256 = 800 from rfl]
  rw [h5x, h5y]
  simp only [List.append_assoc]

/-! ## Concrete `Table02` (`Chunk00..02`, functions `64..111`, `0..47`) -/

theorem oracles_take_16 :
    oracles.take 16 = [oracle64, oracle65, oracle66, oracle67, oracle68, oracle69, oracle70, oracle71,
      oracle72, oracle73, oracle74, oracle75, oracle76, oracle77, oracle78, oracle79] := rfl

theorem oracles_drop_16_take_16 :
    (oracles.drop 16).take 16 = [oracle80, oracle81, oracle82, oracle83, oracle84, oracle85, oracle86, oracle87,
      oracle88, oracle89, oracle90, oracle91, oracle92, oracle93, oracle94, oracle95] := rfl

theorem oracles_drop_32_take_16 :
    (oracles.drop 32).take 16 = [oracle96, oracle97, oracle98, oracle99, oracle100, oracle101, oracle102, oracle103,
      oracle104, oracle105, oracle106, oracle107, oracle108, oracle109, oracle110, oracle111] := rfl

theorem words02_eq :
    ((ConcreteCompilerWord.source.take 48).zip (oracles.take 48)).map
      (fun p => wordFunction p.2 p.1) = Table02.words := by
  have hs : ConcreteCompilerWord.source.length = 814 := rfl
  have ho : oracles.length = 814 := oracles_length
  have h16 : (ConcreteCompilerWord.source.take 16).length = (oracles.take 16).length := by simp [hs, ho]
  have h32 : ((ConcreteCompilerWord.source.drop 16).take 16).length = ((oracles.drop 16).take 16).length := by simp [hs, ho]
  have hsplit48 :
      ((ConcreteCompilerWord.source.take 48).zip (oracles.take 48)).map (fun p => wordFunction p.2 p.1) =
        ((ConcreteCompilerWord.source.take 16).zip (oracles.take 16)).map (fun p => wordFunction p.2 p.1) ++
        (((ConcreteCompilerWord.source.drop 16).take 16).zip ((oracles.drop 16).take 16)).map (fun p => wordFunction p.2 p.1) ++
        (((ConcreteCompilerWord.source.drop 32).take 16).zip ((oracles.drop 32).take 16)).map (fun p => wordFunction p.2 p.1) := by
    have ht1 : (ConcreteCompilerWord.source.take 48).take 16 = ConcreteCompilerWord.source.take 16 := by simp [List.take_take]
    have ho1 : (oracles.take 48).take 16 = oracles.take 16 := by simp [List.take_take]
    have ht2 : ((ConcreteCompilerWord.source.take 48).drop 16).take 16 = (ConcreteCompilerWord.source.drop 16).take 16 := by
      simp [List.drop_take, List.take_take]
    have ho2 : ((oracles.take 48).drop 16).take 16 = (oracles.drop 16).take 16 := by
      simp [List.drop_take, List.take_take]
    have ht3 : ((ConcreteCompilerWord.source.take 48).drop 16).drop 16 = (ConcreteCompilerWord.source.drop 32).take 16 := by
      simp [List.drop_drop, List.drop_take]
    have ho3 : ((oracles.take 48).drop 16).drop 16 = (oracles.drop 32).take 16 := by
      simp [List.drop_drop, List.drop_take]
    rw [zip_map_split (fun p => wordFunction p.2 p.1) 16 (ConcreteCompilerWord.source.take 48) (oracles.take 48) (by simp [hs, ho])]
    rw [ht1, ho1]
    rw [zip_map_split (fun p => wordFunction p.2 p.1) 16 ((ConcreteCompilerWord.source.take 48).drop 16) ((oracles.take 48).drop 16) (by simp [ht2, ho2, hs, ho])]
    rw [ht2, ho2, ht3, ho3, List.append_assoc]
  rw [hsplit48, oracles_take_16, oracles_drop_16_take_16, oracles_drop_32_take_16,
      Chunk00.words_eq, Chunk01.words_eq, Chunk02.words_eq]
  rfl

/-- Further split `0..447` (`Chunk00..27`) into `Table02` (`Chunk00..02`, `0..47`) and
`48..447` (`Chunk03..27`, `400` functions). -/
theorem words00To27_of_03To27
    (words03To27 : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (hw03To27 : (((ConcreteCompilerWord.source.drop 48).take 400).zip
      ((oracles.drop 48).take 400)).map (fun p => wordFunction p.2 p.1) = words03To27) :
    ((ConcreteCompilerWord.source.take 448).zip (oracles.take 448)).map
      (fun p => wordFunction p.2 p.1) = Table02.words ++ words03To27 := by
  have hs : ConcreteCompilerWord.source.length = 814 := rfl
  have ho : oracles.length = 814 := oracles_length
  have ht1 : (ConcreteCompilerWord.source.take 448).take 48 = ConcreteCompilerWord.source.take 48 := by
    simp [List.take_take]
  have ho1 : (oracles.take 448).take 48 = oracles.take 48 := by
    simp [List.take_take]
  have ht2 : (ConcreteCompilerWord.source.take 448).drop 48 = (ConcreteCompilerWord.source.drop 48).take 400 := by
    simp [List.drop_take]
  have ho2 : (oracles.take 448).drop 48 = (oracles.drop 48).take 400 := by
    simp [List.drop_take]
  rw [zip_map_split (fun p => wordFunction p.2 p.1) 48
      (ConcreteCompilerWord.source.take 448) (oracles.take 448) (by simp [hs, ho]),
      ht1, ho1, ht2, ho2, words02_eq, hw03To27]

/-- Further split `0..447` (`Chunk00..27`) into `0..79` (`Chunk00..04`, Stream B) and
`80..447` (`Chunk05..27`, Stream C). -/
theorem words00To27_of_00To04_and_05To27
    (words00To04 words05To27 : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (hw00To04 : ((ConcreteCompilerWord.source.take 80).zip (oracles.take 80)).map
      (fun p => wordFunction p.2 p.1) = words00To04)
    (hw05To27 : (((ConcreteCompilerWord.source.drop 80).take 368).zip
      ((oracles.drop 80).take 368)).map (fun p => wordFunction p.2 p.1) = words05To27) :
    ((ConcreteCompilerWord.source.take 448).zip (oracles.take 448)).map
      (fun p => wordFunction p.2 p.1) = words00To04 ++ words05To27 := by
  have hs : ConcreteCompilerWord.source.length = 814 := rfl
  have ho : oracles.length = 814 := oracles_length
  have ht1 : (ConcreteCompilerWord.source.take 448).take 80 = ConcreteCompilerWord.source.take 80 := by
    simp [List.take_take]
  have ho1 : (oracles.take 448).take 80 = oracles.take 80 := by
    simp [List.take_take]
  have ht2 : (ConcreteCompilerWord.source.take 448).drop 80 = (ConcreteCompilerWord.source.drop 80).take 368 := by
    simp [List.drop_take]
  have ho2 : (oracles.take 448).drop 80 = (oracles.drop 80).take 368 := by
    simp [List.drop_take]
  rw [zip_map_split (fun p => wordFunction p.2 p.1) 80
      (ConcreteCompilerWord.source.take 448) (oracles.take 448) (by simp [hs, ho]),
      ht1, ho1, ht2, ho2, hw00To04, hw05To27]

/-! ## Concrete `Table28To33` (`Chunk28..33`, functions `512..607`, indices `448..543`) -/

noncomputable def words28To33 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) :=
  Chunk28.words ++ Chunk29.words ++ Chunk30.words ++
    Chunk31.words ++ Chunk32.words ++ Chunk33.words

noncomputable def bodies28To33 : List (Nat × HolProg 64) :=
  Chunk28.bodies ++ Chunk29.bodies ++ Chunk30.bodies ++
    Chunk31.bodies ++ Chunk32.bodies ++ Chunk33.bodies

noncomputable def frames28To33 : List Nat :=
  Chunk28.frames ++ Chunk29.frames ++ Chunk30.frames ++
    Chunk31.frames ++ Chunk32.frames ++ Chunk33.frames

noncomputable def bitmapDelta28To33 : AppList (BitVec 64) :=
  BitmapPrepend.prependAppList
    (BitmapPrepend.prependAppList
      (BitmapPrepend.prependAppList
        (BitmapPrepend.prependAppList
          (BitmapPrepend.prependAppList Chunk28.bitmapDelta Chunk29.bitmapDelta)
          Chunk30.bitmapDelta)
        Chunk31.bitmapDelta)
      Chunk32.bitmapDelta)
    Chunk33.bitmapDelta

theorem compiled28To33 (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words28To33 (prefixList, 1637) =
      (bodies28To33, frames28To33,
        (BitmapPrepend.prependAppList prefixList bitmapDelta28To33, 2334)) := by
  have h28_29 := TableComposition.compile_append Chunk28.words Chunk29.words
    (prefixList, 1637)
    (BitmapPrepend.prependAppList prefixList Chunk28.bitmapDelta, 1729)
    (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList prefixList Chunk28.bitmapDelta) Chunk29.bitmapDelta, 1799)
    Chunk28.bodies Chunk29.bodies Chunk28.frames Chunk29.frames
    (Chunk28.compiled prefixList)
    (Chunk29.compiled (BitmapPrepend.prependAppList prefixList Chunk28.bitmapDelta))
  have h28_30 := TableComposition.compile_append (Chunk28.words ++ Chunk29.words) Chunk30.words
    (prefixList, 1637) _ _ _ Chunk30.bodies _ Chunk30.frames h28_29
    (Chunk30.compiled _)
  have h28_31 := TableComposition.compile_append (Chunk28.words ++ Chunk29.words ++ Chunk30.words) Chunk31.words
    (prefixList, 1637) _ _ _ Chunk31.bodies _ Chunk31.frames h28_30
    (Chunk31.compiled _)
  have h28_32 := TableComposition.compile_append (Chunk28.words ++ Chunk29.words ++ Chunk30.words ++ Chunk31.words) Chunk32.words
    (prefixList, 1637) _ _ _ Chunk32.bodies _ Chunk32.frames h28_31
    (Chunk32.compiled _)
  have h28_33 := TableComposition.compile_append
    (Chunk28.words ++ Chunk29.words ++ Chunk30.words ++ Chunk31.words ++ Chunk32.words) Chunk33.words
    (prefixList, 1637) _ _ _ Chunk33.bodies _ Chunk33.frames h28_32
    (Chunk33.compiled _)
  unfold words28To33 bodies28To33 frames28To33 bitmapDelta28To33
  simpa only [BitmapPrepend.prependAppList_assoc] using h28_33

theorem collected28To33 :
    StackRawCall.collectInfo bodies28To33 FrameState27.info = Frames33.info := by
  unfold bodies28To33
  rw [TableComposition.collectInfo_append,
      TableComposition.collectInfo_append,
      TableComposition.collectInfo_append,
      TableComposition.collectInfo_append,
      TableComposition.collectInfo_append]
  rw [Frames28.info_eq, Frames29.info_eq, Frames30.info_eq,
      Frames31.info_eq, Frames32.info_eq, Frames33.info_eq]

theorem oracles_28 : (oracles.drop 448).take 16 =
    [oracle512, oracle513, oracle514, oracle515, oracle516, oracle517, oracle518, oracle519,
     oracle520, oracle521, oracle522, oracle523, oracle524, oracle525, oracle526, oracle527] := rfl
theorem oracles_29 : (oracles.drop 464).take 16 =
    [oracle528, oracle529, oracle530, oracle531, oracle532, oracle533, oracle534, oracle535,
     oracle536, oracle537, oracle538, oracle539, oracle540, oracle541, oracle542, oracle543] := rfl
theorem oracles_30 : (oracles.drop 480).take 16 =
    [oracle544, oracle545, oracle546, oracle547, oracle548, oracle549, oracle550, oracle551,
     oracle552, oracle553, oracle554, oracle555, oracle556, oracle557, oracle558, oracle559] := rfl
theorem oracles_31 : (oracles.drop 496).take 16 =
    [oracle560, oracle561, oracle562, oracle563, oracle564, oracle565, oracle566, oracle567,
     oracle568, oracle569, oracle570, oracle571, oracle572, oracle573, oracle574, oracle575] := rfl
theorem oracles_32 : (oracles.drop 512).take 16 =
    [oracle576, oracle577, oracle578, oracle579, oracle580, oracle581, oracle582, oracle583,
     oracle584, oracle585, oracle586, oracle587, oracle588, oracle589, oracle590, oracle591] := rfl
theorem oracles_33 : (oracles.drop 528).take 16 =
    [oracle592, oracle593, oracle594, oracle595, oracle596, oracle597, oracle598, oracle599,
     oracle600, oracle601, oracle602, oracle603, oracle604, oracle605, oracle606, oracle607] := rfl
theorem oracles_50 : (oracles.drop 800).take 14 =
    [oracle864, oracle865, oracle866, oracle867, oracle868, oracle869, oracle870, oracle871,
     oracle872, oracle873, oracle874, oracle875, oracle876, oracle877] := rfl

theorem six_chunks_split {α β γ : Type} (f : α × β → γ)
    (d : Nat) (xs : List α) (ys : List β)
    (hx : d + 96 ≤ xs.length) (hy : d + 96 ≤ ys.length) :
    (((xs.drop d).take 96).zip ((ys.drop d).take 96)).map f =
      (((xs.drop d).take 16).zip ((ys.drop d).take 16)).map f ++
      (((xs.drop (d + 16)).take 16).zip ((ys.drop (d + 16)).take 16)).map f ++
      (((xs.drop (d + 32)).take 16).zip ((ys.drop (d + 32)).take 16)).map f ++
      (((xs.drop (d + 48)).take 16).zip ((ys.drop (d + 48)).take 16)).map f ++
      (((xs.drop (d + 64)).take 16).zip ((ys.drop (d + 64)).take 16)).map f ++
      (((xs.drop (d + 80)).take 16).zip ((ys.drop (d + 80)).take 16)).map f := by
  let a := (xs.drop d).take 96
  let b := (ys.drop d).take 96
  have ha : a.length = 96 := by simp [a]; omega
  have hb : b.length = 96 := by simp [b]; omega
  have s1 := zip_map_split f 16 a b (by simp [ha, hb])
  have s2 := zip_map_drop_split f 16 16 a b (by simp [ha, hb])
  have s3 := zip_map_drop_split f 32 16 a b (by simp [ha, hb])
  have s4 := zip_map_drop_split f 48 16 a b (by simp [ha, hb])
  have s5 := zip_map_drop_split f 64 16 a b (by simp [ha, hb])
  have e6a : a.drop 80 = (xs.drop (d + 80)).take 16 := by
    simp only [a, List.drop_take, List.drop_drop, show 96 - 80 = 16 from rfl]
  have e6b : b.drop 80 = (ys.drop (d + 80)).take 16 := by
    simp only [b, List.drop_take, List.drop_drop, show 96 - 80 = 16 from rfl]
  change (a.zip b).map f = _
  rw [s1, s2, show 16 + 16 = 32 from rfl, s3, show 32 + 16 = 48 from rfl,
      s4, show 48 + 16 = 64 from rfl, s5, show 64 + 16 = 80 from rfl, e6a, e6b]
  simp only [a, b, List.take_take, List.drop_take, List.drop_drop, Nat.min_eq_left (by decide : 16 ≤ 96),
    Nat.min_eq_left (by decide : 16 ≤ 80), Nat.min_eq_left (by decide : 16 ≤ 64),
    Nat.min_eq_left (by decide : 16 ≤ 48), Nat.min_eq_left (by decide : 16 ≤ 32),
    List.append_assoc]

theorem words28To33_eq :
    (((ConcreteCompilerWord.source.drop 448).take 96).zip
      ((oracles.drop 448).take 96)).map (fun p => wordFunction p.2 p.1) =
      words28To33 := by
  have hs : 448 + 96 ≤ ConcreteCompilerWord.source.length := by
    rw [show ConcreteCompilerWord.source.length = 814 from rfl]; decide
  have ho : 448 + 96 ≤ oracles.length := by rw [oracles_length]; decide
  rw [six_chunks_split (fun p => wordFunction p.2 p.1) 448 ConcreteCompilerWord.source oracles hs ho]
  simp only [show 448 + 16 = 464 from rfl, show 448 + 32 = 480 from rfl,
    show 448 + 48 = 496 from rfl, show 448 + 64 = 512 from rfl, show 448 + 80 = 528 from rfl]
  rw [oracles_28, oracles_29, oracles_30, oracles_31, oracles_32, oracles_33,
      Chunk28.words_eq, Chunk29.words_eq, Chunk30.words_eq,
      Chunk31.words_eq, Chunk32.words_eq, Chunk33.words_eq]
  rfl

theorem words50_eq :
    (((ConcreteCompilerWord.source.drop 800).take 14).zip
      ((oracles.drop 800).take 14)).map (fun p => wordFunction p.2 p.1) =
      Chunk50.words := by
  rw [oracles_50, Chunk50.words_eq]

/-! ## Four-segment full-guest assembly (`0..447`, `448..543`, `544..799`, `800..813`) -/

/-- Full 814-function word-to-word output decomposed into `0..447` (`Chunk00..27`),
`words28To33` (`Chunk28..33`), `544..799` (`Chunk34..49`), and `Chunk50.words`. -/
theorem source_words_eq_of_segments
    (words00To27 words34To49 : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (hw00To27 : ((ConcreteCompilerWord.source.take 448).zip (oracles.take 448)).map
      (fun p => wordFunction p.2 p.1) = words00To27)
    (hw34To49 : (((ConcreteCompilerWord.source.drop 544).take 256).zip
      ((oracles.drop 544).take 256)).map (fun p => wordFunction p.2 p.1) = words34To49) :
    (ConcreteCompilerWord.source.zip oracles).map (fun p => wordFunction p.2 p.1) =
      words00To27 ++ words28To33 ++ words34To49 ++ Chunk50.words := by
  rw [four_way_zip_map_split (fun p => wordFunction p.2 p.1)
      ConcreteCompilerWord.source oracles rfl oracles_length,
      hw00To27, words28To33_eq, hw34To49, words50_eq]

/-- Compose full 814-function `compileWordToStackNative` from `(.list [4], 1)` across the
four segments, automatically inserting `compiled28To33` (`1637 → 2334`) and `Chunk50.compiled`
(`4519 → 4603`). -/
theorem compiled_all_of_segments
    (words00To27 words34To49 : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (bodies00To27 bodies34To49 : List (Nat × HolProg 64))
    (frames00To27 frames34To49 : List Nat)
    (bitmap27 bitmap49 : AppList (BitVec 64))
    (hw00To27 : ((ConcreteCompilerWord.source.take 448).zip (oracles.take 448)).map
      (fun p => wordFunction p.2 p.1) = words00To27)
    (hw34To49 : (((ConcreteCompilerWord.source.drop 544).take 256).zip
      ((oracles.drop 544).take 256)).map (fun p => wordFunction p.2 p.1) = words34To49)
    (hc00To27 : WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words00To27 (.list [4], 1) = (bodies00To27, frames00To27, (bitmap27, 1637)))
    (hc34To49 : WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words34To49 (BitmapPrepend.prependAppList bitmap27 bitmapDelta28To33, 2334) =
      (bodies34To49, frames34To49, (bitmap49, 4519))) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      ((ConcreteCompilerWord.source.zip oracles).map (fun p => wordFunction p.2 p.1))
      (.list [4], 1) =
      (bodies00To27 ++ bodies28To33 ++ bodies34To49 ++ Chunk50.bodies,
       frames00To27 ++ frames28To33 ++ frames34To49 ++ Chunk50.frames,
       (BitmapPrepend.prependAppList bitmap49 Chunk50.bitmapDelta, 4603)) := by
  rw [source_words_eq_of_segments words00To27 words34To49 hw00To27 hw34To49]
  have h1 := TableComposition.compile_append words00To27 words28To33
    (.list [4], 1) (bitmap27, 1637)
    (BitmapPrepend.prependAppList bitmap27 bitmapDelta28To33, 2334)
    bodies00To27 bodies28To33 frames00To27 frames28To33
    hc00To27 (compiled28To33 bitmap27)
  have h2 := TableComposition.compile_append (words00To27 ++ words28To33) words34To49
    (.list [4], 1)
    (BitmapPrepend.prependAppList bitmap27 bitmapDelta28To33, 2334)
    (bitmap49, 4519)
    (bodies00To27 ++ bodies28To33) bodies34To49
    (frames00To27 ++ frames28To33) frames34To49
    h1 hc34To49
  exact TableComposition.compile_append
    (words00To27 ++ words28To33 ++ words34To49) Chunk50.words
    (.list [4], 1) (bitmap49, 4519)
    (BitmapPrepend.prependAppList bitmap49 Chunk50.bitmapDelta, 4603)
    (bodies00To27 ++ bodies28To33 ++ bodies34To49) Chunk50.bodies
    (frames00To27 ++ frames28To33 ++ frames34To49) Chunk50.frames
    h2 (Chunk50.compiled bitmap49)

/-- Compose full-guest `StackRawCall.collectInfo` from `StackPasses.nativeStubs` to
`GlobalFrameInfo.info`, automatically discharging `Chunk28..33` via `collected28To33`. -/
theorem collected_all_of_segments
    (bodies00To27 bodies34To49 : List (Nat × HolProg 64))
    (hcol00To27 : StackRawCall.collectInfo (StackPasses.nativeStubs ++ bodies00To27) .ln =
      FrameState27.info)
    (hcol34To50 : StackRawCall.collectInfo (bodies34To49 ++ Chunk50.bodies) Frames33.info =
      GlobalFrameInfo.info) :
    StackRawCall.collectInfo
      (StackPasses.nativeStubs ++ (bodies00To27 ++ bodies28To33 ++ bodies34To49 ++ Chunk50.bodies))
      .ln = GlobalFrameInfo.info := by
  have hassoc :
      StackPasses.nativeStubs ++ (bodies00To27 ++ bodies28To33 ++ bodies34To49 ++ Chunk50.bodies) =
        ((StackPasses.nativeStubs ++ bodies00To27) ++ bodies28To33) ++
          (bodies34To49 ++ Chunk50.bodies) := by
    simp only [List.append_assoc]
  rw [hassoc,
      TableComposition.collectInfo_append
        ((StackPasses.nativeStubs ++ bodies00To27) ++ bodies28To33)
        (bodies34To49 ++ Chunk50.bodies),
      TableComposition.collectInfo_append
        (StackPasses.nativeStubs ++ bodies00To27) bodies28To33,
      hcol00To27, collected28To33, hcol34To50]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.AllTables
