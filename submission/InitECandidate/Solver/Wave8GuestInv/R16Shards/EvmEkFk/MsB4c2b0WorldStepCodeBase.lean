import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB4c2aCodeBounded0
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.AccountWk
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21

/-!
# Scratch Rung B4c2b: `CodeRootsValsEq`, `WorldStepCodeSc`, `ProgWStepCode`, & Read/Lookup Callees

Strengthens `WorldStepSc` with `CodeRootsValsEq` (preservation of `htabValues` on live
code-DB roots `ws+16`, `bs+48`, `ts+48`), proves compositional `ProgWStepCode` combinators
and leaf bridges (`WorldEff`, `ReadOnlyFn`, `sk_make`, non-code `htab_set`), and derives
`WorldKeepsCodeSc` for all read/lookup world callees.
-/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.EvmBase
open InitECandidate.Solver.Wave8GuestInv.EvmStepLemmas
open InitECandidate.Solver.Wave8GuestInv.EvmFrameSpecs
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8M19.Htab
open InitECandidate.Solver.Wave8GuestInv.HtabC00Ports
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

/-! ## 1. `CodeRootsValsEq`, `WorldStepCodeSc`, & Code-Root Preservation -/

/-- `WorldStep` extra postcondition asserting that every live code-DB root
(`ws+16`, `bs+48`, `ts+48`) keeps its exact `htabValues` list. -/
def CodeRootsValsEq {F : Type}
    (s : PanSemStateFiniteExact 64 F) (_ : Option (PanSemResultExact 64))
    (post : PanSemStateFiniteExact 64 F) (_ _ : List Nat) : Prop :=
  ∀ g k, (g, k) ∈ ([("ws", 16), ("bs", 48), ("ts", 48)] : List (String × Nat)) →
    globN s g ≠ 0 → memW s (globN s g + k) ≠ 0 →
    htabValues post (memW s (globN s g + k)) = htabValues s (memW s (globN s g + k))

/-- Non-trie world owned intervals: table footprints on `S` plus `fixedObjects s`. -/
def nonTrieOwned {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) : List Ivl :=
  S.flatMap (htabFootprint s) ++ fixedObjects s

/-- Non-trie table+fixed growth and frame clause paired with `WorldStepSc`: for every `(S, Nd)`
satisfying `WorldTypedWith s S Nd`, there is a post node set `Nd'` such that `WorldTypedWith post S Nd'`
(`S` itself is preserved!), `nonTrieOwned post S` grows only inside `nonTrieOwned s S` or fresh heap,
and memory cells outside `nonTrieOwned s S ++ bufRegions B s ++ [freeGap s]` and `heapFree s` are unchanged. -/
def NonTrieStep (B : BufList) {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ S Nd, WorldTypedWith s S Nd → IvlsDisj (bufRegions B s) (worldTypedIvls s S Nd) →
    (∃ Nd', WorldTypedWith post S Nd') ∧
    OwnedGrows s post (nonTrieOwned s S) (nonTrieOwned post S) ∧
    FrameOutside s post (nonTrieOwned s S ++ bufRegions B s ++ [freeGap s]) (heapFree s)

def WorldStepCodeSc (B : BufList) (gw : List String) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (r : Option (PanSemResultExact 64))
    (post : PanSemStateFiniteExact 64 F) : Prop :=
  WorldStepSc (bufRegions B) gw R10Shards.P26_P28.stdKeep CodeRootsValsEq s r post ∧
    NonTrieStep B s post

def WorldKeepsCodeSc (B : BufList) (gw : List String) (fname : MlS) : Prop :=
  FunSpec WorldOK (fun s r post => Resumes r → WorldStepCodeSc B gw s r post) fname

theorem WorldStepCodeSc.worldOK_bufs {F : Type}
    {B : BufList} {gw : List String}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hB : ValidBufList B) (hs : WorldOK s)
    (h : WorldStepCodeSc B gw s r post) :
    WorldOK post :=
  h.1.worldOK_bufs hB hs

def PosBufList (B : BufList) : Prop :=
  ValidBufList B ∧ ∀ p ∈ B, 0 < p.2

theorem typed_record_field_avoids_validBufList {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hWT : WorldTypedWith s S Nd) {B : BufList} (hB : PosBufList B)
    (g : String) (sz k : Nat) (hg : (g, sz) ∈ typedRecords)
    (hn : globN s g ≠ 0) (hk : k + 8 ≤ sz) :
    ∀ i ∈ bufRegions B s, ¬ CellHits (globN s g + k) i := by
  have hi : (globN s g, sz) ∈ worldTypedIvls s S Nd := by
    unfold worldTypedIvls
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map.2 ⟨(g, sz), hg, by simp [hn]⟩)))))
  intro i him hit
  have hd := validBufList_disj hB.1 hWT i him _ hi
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 him
  by_cases hz : globN s b.1 = 0
  · simp [Wave8GuestInv.bufferRegion, hz, CellHits] at hit
  · simp only [Wave8GuestInv.bufferRegion, hz, ↓reduceIte] at hd hit
    have hbp := hB.2 b hb
    unfold Disj at hd
    unfold CellHits at hit
    dsimp only at hd hit
    rcases hd with hd | hd | hd | hd <;> omega

theorem code_roots_kept_of_safeGlobals {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {B : BufList} {gw : List String}
    (hWT : WorldTypedWith s S Nd) (hB : PosBufList B) (hgw : SafeStepGlobals gw)
    (hR : RecordsKept (bufRegions B) R10Shards.P26_P28.stdKeep s post)
    (hG : GlobalsKept gw s post) :
    ∀ g k, (g, k) ∈ ([("ws", 16), ("ts", 40), ("ts", 48), ("bs", 48)] : List (String × Nat)) →
      globN post g = globN s g ∧
      (globN s g ≠ 0 → memW post (globN post g + k) = memW s (globN s g + k)) := by
  intro g k hm
  have hnot_step : ofString g ∉ (["heap_ptr", "scratch_ptr", "journal_n"] : List String).map ofString := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hg : globN post g = globN s g :=
    globN_eq_of_lookup (hG (ofString g) (hgw.not_mem_map hnot_step))
  refine ⟨hg, fun hn => ?_⟩
  rw [hg]
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hR ("ws", [0, 8, 16, 24, 32]) (by decide) hn 16 (by decide)
      (typed_record_field_avoids_validBufList hWT hB "ws" 40 16 (by simp [typedRecords]) hn (by omega))
  · exact hR ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]) (by decide) hn 40 (by decide)
      (typed_record_field_avoids_validBufList hWT hB "ts" 72 40 (by simp [typedRecords]) hn (by omega))
  · exact hR ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]) (by decide) hn 48 (by decide)
      (typed_record_field_avoids_validBufList hWT hB "ts" 72 48 (by simp [typedRecords]) hn (by omega))
  · exact hR ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]) (by decide) hn 48 (by decide)
      (typed_record_field_avoids_validBufList hWT hB "bs" 80 48 (by simp [typedRecords]) hn (by omega))

theorem codeRoot_mem_S {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hT : TablesTyped s S) {g : String} {k : Nat}
    (hm : (g, k) ∈ ([("ws", 16), ("bs", 48), ("ts", 48)] : List (String × Nat)))
    (hgnz : globN s g ≠ 0) (htnz : memW s (globN s g + k) ≠ 0) :
    memW s (globN s g + k) ∈ S := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases hT.2.2.2.1 16 (by simp [wsTableSlots]) hgnz with h0 | hS
    · exact absurd h0 htnz
    · exact hS
  · rcases hT.2.2.2.2.1 48 (by simp [bsTableSlots]) hgnz with h0 | hS
    · exact absurd h0 htnz
    · exact hS
  · rcases hT.2.2.2.2.2.1 48 (by simp [tsTableSlots]) hgnz with h0 | hS
    · exact absurd h0 htnz
    · exact hS

theorem codeRootsValsEq_of_all_unhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {S Nd : List Nat} (hT : TablesTyped s S)
    (hu : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i) :
    CodeRootsValsEq s r post S Nd := by
  intro g k hm hgnz htnz
  have htS := codeRoot_mem_S hT hm hgnz htnz
  exact R10Shards.Fast_GbodyC17ToC21.htabValues_eq_of_unhit (hT.2.1 _ htS).1 (hu _ htS)

theorem worldStepCodeSc_refl {F : Type}
    (B : BufList) (gw : List String)
    (s : PanSemStateFiniteExact 64 F) (r : Option (PanSemResultExact 64))
    (hA : ArenaReady s) :
    WorldStepCodeSc B gw s r s := by
  refine ⟨⟨⟨hA, le_rfl, fun _ _ => rfl, fun _ _ _ _ _ _ => rfl, fun S Nd hWT _ => ?_⟩, le_rfl⟩,
      fun S Nd hWT _ => ⟨⟨Nd, hWT⟩, fun o ho => Or.inr (Or.inl ⟨o, ho, le_rfl, le_rfl⟩),
        fun _ _ _ => rfl⟩⟩
  exact ⟨S, Nd, fun _ h => h, hWT,
    fun o ho => Or.inr (Or.inl ⟨o, ho, le_rfl, le_rfl⟩),
    fun _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

theorem worldStepCodeSc_with_locals_clock {F : Type}
    {B : BufList} {gw : List String}
    {s post : PanSemStateFiniteExact 64 F} {r r' : Option (PanSemResultExact 64)}
    (h : WorldStepCodeSc B gw s r post)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    WorldStepCodeSc B gw s r' { post with locals := L, clock := k } := by
  obtain ⟨⟨⟨hAp, hhp, hG, hK, hW⟩, hsc⟩, hNT⟩ := h
  refine ⟨⟨⟨localsFree_arenaReady post L k hAp, hhp, hG, hK, fun S Nd hWT hD => ?_⟩, hsc⟩, ?_⟩
  · obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hCR⟩ := hW S Nd hWT hD
    obtain ⟨hT', hJ', hF', hNH', hndisj', hws'⟩ := hWT'
    have hWT'' : WorldTypedWith { post with locals := L, clock := k } S' Nd' :=
      ⟨(tablesTyped_with_locals post L k S').2 hT', hJ', hF', hNH', hndisj', hws'⟩
    exact ⟨S', Nd', hsub, hWT'', hOG, hFO, hCR⟩
  · intro S Nd hWT hD
    obtain ⟨⟨Nd', hWT'⟩, hOG, hFO⟩ := hNT S Nd hWT hD
    obtain ⟨hT', hJ', hF', hNH', hndisj', hws'⟩ := hWT'
    exact ⟨⟨Nd', ⟨(tablesTyped_with_locals post L k S).2 hT', hJ', hF', hNH', hndisj', hws'⟩⟩,
      hOG, hFO⟩

theorem worldStepCodeSc_of_pre_locals_clock {F : Type}
    {B : BufList} {gw : List String}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {L : HolFiniteMapExact MlS (ValueHOL 64)} {k : Nat}
    (h : WorldStepCodeSc B gw { s with locals := L, clock := k } r post) :
    WorldStepCodeSc B gw s r post := by
  obtain ⟨⟨⟨hAp, hhp, hG, hK, hW⟩, hsc⟩, hNT⟩ := h
  refine ⟨⟨⟨hAp, hhp, hG, hK, fun S Nd hWT hD => ?_⟩, hsc⟩, ?_⟩
  · obtain ⟨hT, hJ, hF, hNH, hndisj, hws⟩ := hWT
    have hWT' : WorldTypedWith { s with locals := L, clock := k } S Nd :=
      ⟨(tablesTyped_with_locals s L k S).2 hT, hJ, hF, hNH, hndisj, hws⟩
    exact hW S Nd hWT' hD
  · intro S Nd hWT hD
    obtain ⟨hT, hJ, hF, hNH, hndisj, hws⟩ := hWT
    exact hNT S Nd ⟨(tablesTyped_with_locals s L k S).2 hT, hJ, hF, hNH, hndisj, hws⟩ hD

theorem worldStepCodeSc_from_entry {F : Type}
    {B : BufList} {gw : List String}
    {s post : PanSemStateFiniteExact 64 F} {r r' : Option (PanSemResultExact 64)}
    {callee L : HolFiniteMapExact MlS (ValueHOL 64)} {k : Nat}
    (h : WorldStepCodeSc B gw (callEntryStateHOLFinite s callee) r post) :
    WorldStepCodeSc B gw s r' { post with locals := L, clock := k } :=
  worldStepCodeSc_with_locals_clock (r' := r') (worldStepCodeSc_of_pre_locals_clock h) L k

theorem worldStepCodeSc_mono_bufs {F : Type}
    {B1 B2 : BufList} {gw1 gw2 : List String}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hB : ∀ p ∈ B1, p ∈ B2)
    (hgw : ∀ g ∈ gw1, g ∈ gw2)
    (h : WorldStepCodeSc B1 gw1 s r post) :
    WorldStepCodeSc B2 gw2 s r post := by
  obtain ⟨⟨⟨hAp, hhp, hG, hK, hW⟩, hsc⟩, hNT⟩ := h
  have hsubR : ∀ i ∈ bufRegions B1 s, i ∈ bufRegions B2 s := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
    exact List.mem_map.2 ⟨p, hB p hp, rfl⟩
  refine ⟨⟨⟨hAp, hhp, ?_, ?_, ?_⟩, hsc⟩, ?_⟩
  · intro k hk
    apply hG k
    intro hm
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hm
    exact hk (List.mem_map.2 ⟨g, hgw g hg, rfl⟩)
  · intro rec hrec hnz k hk hno
    exact hK rec hrec hnz k hk (fun i hi => hno i (hsubR i hi))
  · intro S Nd hWT hD
    have hD1 : IvlsDisj (bufRegions B1 s) (worldTypedIvls s S Nd) :=
      fun i hi j hj => hD i (hsubR i hi) j hj
    obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hCR⟩ := hW S Nd hWT hD1
    refine ⟨S', Nd', hsub, hWT', hOG, ?_, hCR⟩
    intro a ha hhf
    apply hFO a _ hhf
    intro i hi
    rcases List.mem_append.1 hi with hi1 | hfg
    · rcases List.mem_append.1 hi1 with hwo | hR1
      · exact ha i (List.mem_append_left _ (List.mem_append_left _ hwo))
      · exact ha i (List.mem_append_left _ (List.mem_append_right _ (hsubR i hR1)))
    · exact ha i (List.mem_append_right _ hfg)
  · intro S Nd hWT hD
    have hD1 : IvlsDisj (bufRegions B1 s) (worldTypedIvls s S Nd) :=
      fun i hi j hj => hD i (hsubR i hi) j hj
    obtain ⟨hWT', hOG, hFO⟩ := hNT S Nd hWT hD1
    refine ⟨hWT', hOG, ?_⟩
    intro a ha hhf
    apply hFO a _ hhf
    intro i hi
    rcases List.mem_append.1 hi with hi1 | hfg
    · rcases List.mem_append.1 hi1 with hwo | hR1
      · exact ha i (List.mem_append_left _ (List.mem_append_left _ hwo))
      · exact ha i (List.mem_append_left _ (List.mem_append_right _ (hsubR i hR1)))
    · exact ha i (List.mem_append_right _ hfg)

theorem worldStepCodeSc_trans {F : Type}
    {B : BufList} {gw : List String}
    {s1 s2 s3 : PanSemStateFiniteExact 64 F}
    {r1 r2 : Option (PanSemResultExact 64)}
    (hB : PosBufList B) (hgw : SafeStepGlobals gw)
    (h12 : WorldStepCodeSc B gw s1 r1 s2)
    (h23 : WorldStepCodeSc B gw s2 r2 s3) :
    WorldStepCodeSc B gw s1 r2 s3 := by
  obtain ⟨⟨⟨hA2, hhp12, hG12, hK12, hW12⟩, hsc12⟩, hNT12⟩ := h12
  obtain ⟨⟨⟨hA3, hhp23, hG23, hK23, hW23⟩, hsc23⟩, hNT23⟩ := h23
  have hbuf21 : bufRegions B s2 = bufRegions B s1 := bufRegions_eq_of_safeGlobals hB.1 hgw hG12
  have hfmp21 : globN s2 "frame_mem_ptr" = globN s1 "frame_mem_ptr" :=
    globN_eq_of_lookup (hG12 (ofString "frame_mem_ptr") (hgw.not_mem_map (by decide)))
  refine ⟨⟨⟨hA3, le_trans hhp12 hhp23,
    fun k hk => (hG12 k hk).trans (hG23 k hk), ?_, ?_⟩, le_trans hsc23 hsc12⟩, ?_⟩
  · intro rec hrec hnz k hk hno
    have hrec_not : ofString rec.1 ∉ (["heap_ptr", "scratch_ptr", "journal_n"] : List String).map ofString := by
      simp only [R10Shards.P26_P28.stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl <;> decide
    have hg_rec : globN s2 rec.1 = globN s1 rec.1 :=
      globN_eq_of_lookup (hG12 (ofString rec.1) (hgw.not_mem_map hrec_not))
    have h2 : memW s3 (globN s2 rec.1 + k) = memW s2 (globN s2 rec.1 + k) :=
      hK23 rec hrec (by rw [hg_rec]; exact hnz) k hk
        (by change ∀ i ∈ bufRegions B s2, ¬ CellHits (globN s2 rec.1 + k) i
            rw [hbuf21, hg_rec]; exact hno)
    rw [hg_rec] at h2
    exact h2.trans (hK12 rec hrec hnz k hk hno)
  · intro S Nd hWT1 hD1
    obtain ⟨S2, Nd2, hsub12, hWT2, hOG12, hFO12, hCR12⟩ := hW12 S Nd hWT1 hD1
    have hD2 : IvlsDisj (bufRegions B s2) (worldTypedIvls s2 S2 Nd2) := validBufList_disj hB.1 hWT2
    obtain ⟨S3, Nd3, hsub23, hWT3, hOG23, hFO23, hCR23⟩ := hW23 S2 Nd2 hWT2 hD2
    refine ⟨S3, Nd3, fun t ht => hsub23 t (hsub12 t ht), hWT3, ?_, ?_, ?_⟩
    · intro o ho
      rcases hOG23 o ho with rfl | ⟨j, hj, hin_oj⟩ | hin_o23
      · exact Or.inl rfl
      · rcases hOG12 j hj with rfl | ⟨k, hk, hin_jk⟩ | hin_j12
        · left
          rcases o with ⟨o1, o2⟩
          dsimp only [Inside] at hin_oj
          have ho1 : o1 = 0 := by omega
          have ho2 : o2 = 0 := by omega
          rw [ho1, ho2]
        · exact Or.inr (Or.inl ⟨k, hk, le_trans hin_jk.1 hin_oj.1, le_trans hin_oj.2 hin_jk.2⟩)
        · exact Or.inr (Or.inr ⟨le_trans hin_j12.1 hin_oj.1,
            le_trans hin_oj.2 (le_trans hin_j12.2 hhp23)⟩)
      · exact Or.inr (Or.inr ⟨le_trans hhp12 hin_o23.1, hin_o23.2⟩)
    · intro a ha hhf
      have hm12 : s2.memory a = s1.memory a := hFO12 a ha hhf
      have hm23 : s3.memory a = s2.memory a := by
        apply hFO23 a
        · intro i hi hch
          obtain ⟨hc1, hc2⟩ := hch
          rcases List.mem_append.1 hi with hi1 | hfg2
          · rcases List.mem_append.1 hi1 with hwo2 | hR2
            · rcases hOG12 i hwo2 with rfl | ⟨k, hk, hin_ik⟩ | hin_i12
              · dsimp only at hc2; omega
              · exact ha k (List.mem_append_left _ (List.mem_append_left _ hk))
                  ⟨by dsimp only [Inside] at hin_ik; omega,
                   by dsimp only [Inside] at hin_ik; omega⟩
              · have hp2_lim : globN s2 "heap_ptr" ≤ heapLimit := hA2.2.2.1
                exact hhf ⟨by unfold heapFree; dsimp only [Inside] at hin_i12 ⊢; omega,
                           by unfold heapFree; dsimp only [Inside] at hin_i12 ⊢; omega⟩
            · change i ∈ bufRegions B s2 at hR2
              rw [hbuf21] at hR2
              exact ha i (List.mem_append_left _ (List.mem_append_right _ hR2)) ⟨hc1, hc2⟩
          · simp only [List.mem_singleton] at hfg2
            subst hfg2
            exact ha (freeGap s1) (List.mem_append_right _ (List.mem_singleton.2 rfl))
              ⟨by unfold freeGap at hc1 ⊢; dsimp only at hc1 ⊢; omega,
               by unfold freeGap at hc2 ⊢; dsimp only at hc2 ⊢; omega⟩
        · intro ⟨hc1, hc2⟩
          have hp2_lim : globN s2 "heap_ptr" ≤ heapLimit := hA2.2.2.1
          exact hhf ⟨by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega,
                     by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega⟩
      exact hm23.trans hm12
    · intro g k hm hgnz htnz
      have hm4 : (g, k) ∈ ([("ws", 16), ("ts", 40), ("ts", 48), ("bs", 48)] : List (String × Nat)) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm ⊢
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
      obtain ⟨hg12, hm12_cell⟩ := code_roots_kept_of_safeGlobals hWT1 hB hgw hK12 hG12 g k hm4
      have hcell_eq := hm12_cell hgnz
      have h23_eq : htabValues s3 (memW s2 (globN s2 g + k)) = htabValues s2 (memW s2 (globN s2 g + k)) :=
        hCR23 g k hm (by rwa [hg12]) (by rwa [hcell_eq])
      rw [hcell_eq] at h23_eq
      exact h23_eq.trans (hCR12 g k hm hgnz htnz)
  · intro S Nd hWT1 hD1
    obtain ⟨⟨Nd2, hWT2⟩, hOG12, hFO12⟩ := hNT12 S Nd hWT1 hD1
    have hD2 : IvlsDisj (bufRegions B s2) (worldTypedIvls s2 S Nd2) := validBufList_disj hB.1 hWT2
    obtain ⟨hWT3_ex, hOG23, hFO23⟩ := hNT23 S Nd2 hWT2 hD2
    refine ⟨hWT3_ex, ?_, ?_⟩
    · intro o ho
      rcases hOG23 o ho with rfl | ⟨j, hj, hin_oj⟩ | hin_o23
      · exact Or.inl rfl
      · rcases hOG12 j hj with rfl | ⟨k, hk, hin_jk⟩ | hin_j12
        · left
          rcases o with ⟨o1, o2⟩
          dsimp only [Inside] at hin_oj
          have ho1 : o1 = 0 := by omega
          have ho2 : o2 = 0 := by omega
          rw [ho1, ho2]
        · exact Or.inr (Or.inl ⟨k, hk, le_trans hin_jk.1 hin_oj.1, le_trans hin_oj.2 hin_jk.2⟩)
        · exact Or.inr (Or.inr ⟨le_trans hin_j12.1 hin_oj.1,
            le_trans hin_oj.2 (le_trans hin_j12.2 hhp23)⟩)
      · exact Or.inr (Or.inr ⟨le_trans hhp12 hin_o23.1, hin_o23.2⟩)
    · intro a ha hhf
      have hm12 : s2.memory a = s1.memory a := hFO12 a ha hhf
      have hm23 : s3.memory a = s2.memory a := by
        apply hFO23 a
        · intro i hi hch
          obtain ⟨hc1, hc2⟩ := hch
          rcases List.mem_append.1 hi with hi1 | hfg2
          · rcases List.mem_append.1 hi1 with hno2 | hR2
            · rcases hOG12 i hno2 with rfl | ⟨k, hk, hin_ik⟩ | hin_i12
              · dsimp only at hc2; omega
              · exact ha k (List.mem_append_left _ (List.mem_append_left _ hk))
                  ⟨by dsimp only [Inside] at hin_ik; omega,
                   by dsimp only [Inside] at hin_ik; omega⟩
              · have hp2_lim : globN s2 "heap_ptr" ≤ heapLimit := hA2.2.2.1
                exact hhf ⟨by unfold heapFree; dsimp only [Inside] at hin_i12 ⊢; omega,
                           by unfold heapFree; dsimp only [Inside] at hin_i12 ⊢; omega⟩
            · change i ∈ bufRegions B s2 at hR2
              rw [hbuf21] at hR2
              exact ha i (List.mem_append_left _ (List.mem_append_right _ hR2)) ⟨hc1, hc2⟩
          · simp only [List.mem_singleton] at hfg2
            subst hfg2
            exact ha (freeGap s1) (List.mem_append_right _ (List.mem_singleton.2 rfl))
              ⟨by unfold freeGap at hc1 ⊢; dsimp only at hc1 ⊢; omega,
               by unfold freeGap at hc2 ⊢; dsimp only at hc2 ⊢; omega⟩
        · intro ⟨hc1, hc2⟩
          have hp2_lim : globN s2 "heap_ptr" ≤ heapLimit := hA2.2.2.1
          exact hhf ⟨by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega,
                     by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega⟩
      exact hm23.trans hm12

/-! ## 2. `ProgWStepCode` Control-Flow Combinators -/

def ProgWStepCode (B : BufList) (gw : List String) (prog : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    s.code = originalRuntimeCode → WorldOK s →
    (evaluateHOLFiniteState s prog).1 ≠ some .timeOut →
    FlowingOrResumes (evaluateHOLFiniteState s prog).1 →
    WorldStepCodeSc B gw s (evaluateHOLFiniteState s prog).1 (evaluateHOLFiniteState s prog).2

theorem progWStepCode_mono {B1 B2 : BufList} {gw1 gw2 : List String} {prog : ProgHOL 64}
    (hB : ∀ p ∈ B1, p ∈ B2) (hgw : ∀ g ∈ gw1, g ∈ gw2)
    (h : ProgWStepCode B1 gw1 prog) : ProgWStepCode B2 gw2 prog :=
  fun s hc hW hnt hfr => worldStepCodeSc_mono_bufs hB hgw (h s hc hW hnt hfr)

theorem progWStepCode_skip (B : BufList) (gw : List String) : ProgWStepCode B gw .skip := by
  intro F s _ hW _ _
  rw [evaluateHOLFiniteState_skip]
  exact worldStepCodeSc_refl B gw s none hW.1

theorem progWStepCode_continue (B : BufList) (gw : List String) : ProgWStepCode B gw .continue := by
  intro F s _ hW _ _
  rw [evaluateHOLFiniteState_continue]
  exact worldStepCodeSc_refl B gw s (some .continue) hW.1

theorem progWStepCode_break (B : BufList) (gw : List String) : ProgWStepCode B gw .break := by
  intro F s _ hW _ _
  rw [evaluateHOLFiniteState_break]
  exact worldStepCodeSc_refl B gw s (some .break) hW.1

theorem progWStepCode_return (B : BufList) (gw : List String) (e : ExpHOL 64) :
    ProgWStepCode B gw (.return e) := by
  intro F s _ hW _ hfr
  rw [evaluateHOLFiniteState_return] at hfr ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | v
  · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hev] at hfr ⊢
    split
    · exact worldStepCodeSc_with_locals_clock (worldStepCodeSc_refl B gw s none hW.1) _ s.clock
    · rename_i hbad; simp [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem progWStepCode_raise (B : BufList) (gw : List String) (eid : MlS) (e : ExpHOL 64) :
    ProgWStepCode B gw (.raise eid e) := by
  intro F s _ hW _ hfr
  rw [evaluateHOLFiniteState_raise] at hfr ⊢
  rcases hsh : s.eshapes.lookup eid with _ | sh
  · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hsh] at hfr ⊢
    rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | v
    · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hev] at hfr ⊢
      split
      · exact worldStepCodeSc_with_locals_clock (worldStepCodeSc_refl B gw s none hW.1) _ s.clock
      · rename_i hbad; simp [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem progWStepCode_assign_local (B : BufList) (gw : List String) (x : MlS) (e : ExpHOL 64) :
    ProgWStepCode B gw (.assign .local x e) := by
  intro F s _ hW _ hfr
  rw [evaluateHOLFiniteState_assign] at hfr ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | v
  · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hev] at hfr ⊢
    by_cases hv : s.isValidValueHOLFinite .local x v = true
    · rw [if_pos hv]
      exact worldStepCodeSc_with_locals_clock (worldStepCodeSc_refl B gw s none hW.1) _ s.clock
    · rw [if_neg hv] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem progWStepCode_dec {B : BufList} {gw : List String} {x : MlS} {sh : ShapeHOL} {e : ExpHOL 64}
    {body : ProgHOL 64} (hb : ProgWStepCode B gw body) :
    ProgWStepCode B gw (.dec x sh e body) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_dec_total] at hnt hfr ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | val
  · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hev] at hnt hfr ⊢
    by_cases hok : shapeEqHOL sh (shapeOfHOLExact val) = true
    · simp only [hok, ↓reduceIte] at hnt hfr ⊢
      set s1 := setVarHOLFinite x val s
      have hW1 : WorldOK s1 := localsFree_worldOK s _ s.clock hW
      have hstep := hb s1 hc hW1 hnt hfr
      exact worldStepCodeSc_with_locals_clock (worldStepCodeSc_of_pre_locals_clock hstep)
        _ (evaluateHOLFiniteState s1 body).2.clock
    · simp [hok] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem progWStepCode_ite {B : BufList} {gw : List String} {cond : ExpHOL 64} {yes no : ProgHOL 64}
    (hy : ProgWStepCode B gw yes) (hn : ProgWStepCode B gw no) :
    ProgWStepCode B gw (.ite cond yes no) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_ite] at hnt hfr ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond with _ | cv
  · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
  · rcases cv with ⟨⟨w⟩⟩ | _ | _
    · simp only [hev] at hnt hfr ⊢
      by_cases hw : w = 0
      · simp only [hw, ↓reduceIte] at hnt hfr ⊢; exact hn s hc hW hnt hfr
      · simp only [hw, ↓reduceIte] at hnt hfr ⊢; exact hy s hc hW hnt hfr
    · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem progWStepCode_seq {B : BufList} {gw : List String} {p1 p2 : ProgHOL 64}
    (hB : PosBufList B) (hgw : SafeStepGlobals gw)
    (h1 : ProgWStepCode B gw p1) (h2 : ProgWStepCode B gw p2) :
    ProgWStepCode B gw (.seq p1 p2) := by
  intro F s hc hW hnt hfr
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s p1).1
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, mid⟩
  simp only [hr1] at hmeta hnt hfr ⊢
  cases r1 with
  | none =>
    have hs1 := h1 s hc hW (by rw [hr1]; simp) (by rw [hr1]; exact Or.inl rfl)
    rw [hr1] at hs1; dsimp only at hs1
    have hW_mid : WorldOK mid := hs1.worldOK_bufs hB.1 hW
    have hs2 := h2 mid (hmeta.trans hc) hW_mid hnt hfr
    exact worldStepCodeSc_trans hB hgw hs1 hs2
  | some r =>
    have hs1 := h1 s hc hW (by rw [hr1]; exact hnt) (by rw [hr1]; exact hfr)
    rw [hr1] at hs1
    exact hs1

theorem progWStepCode_while {B : BufList} {gw : List String} {cond : ExpHOL 64} {body : ProgHOL 64}
    (hB : PosBufList B) (hgw : SafeStepGlobals gw)
    (hb : ProgWStepCode B gw body) :
    ProgWStepCode B gw (.while cond body) := by
  intro F s0 hc0 hW0 hnt0 hfr0
  suffices ∀ (k : Nat) (s : PanSemStateFiniteExact 64 F),
      s.clock = k → s.code = originalRuntimeCode → WorldOK s →
      (evaluateHOLFiniteState s (.while cond body)).1 ≠ some .timeOut →
      FlowingOrResumes (evaluateHOLFiniteState s (.while cond body)).1 →
      WorldStepCodeSc B gw s
        (evaluateHOLFiniteState s (.while cond body)).1
        (evaluateHOLFiniteState s (.while cond body)).2 from
    this s0.clock s0 rfl hc0 hW0 hnt0 hfr0
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro s hclk hc hW hnt hfr
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt hfr ⊢
    rcases hev : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) cond with
      _ | cv
    · simp only [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hev] at hnt hfr ⊢
      rcases cv with ⟨⟨w⟩⟩ | _ | _
      · dsimp only at hnt hfr ⊢
        by_cases hw : w = 0
        · subst hw; exact worldStepCodeSc_refl B gw s none hW.1
        · rw [if_pos hw] at hnt hfr ⊢
          by_cases hk0 : s.clock = 0
          · simp [hk0] at hnt
          · rw [if_neg hk0] at hnt hfr ⊢
            set sd := decClockHOLFinite s
            have hWd : WorldOK sd := localsFree_worldOK s s.locals (s.clock - 1) hW
            have hclk_le := evaluateHOLFiniteState_clock_le sd body
            have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata sd body).1
            rcases hbo : evaluateHOLFiniteState sd body with ⟨rb, mid⟩
            have hbo' : evaluateHOLFiniteState (decClockHOLFinite s) body = (rb, mid) := hbo
            simp only [sd, hbo'] at hnt hfr hclk_le hmeta ⊢
            have hmid_lt : mid.clock < k := by
              change mid.clock ≤ s.clock - 1 at hclk_le; omega
            have hnt_b : (evaluateHOLFiniteState sd body).1 ≠ some .timeOut := by
              rw [hbo]; rintro rfl; exact hnt rfl
            cases rb with
            | none =>
              have hsb := hb sd hc hWd hnt_b (by rw [hbo]; exact Or.inl rfl)
              rw [hbo] at hsb
              have hW_mid : WorldOK mid := hsb.worldOK_bufs hB.1 hWd
              have hsb' : WorldStepCodeSc B gw s none mid :=
                worldStepCodeSc_with_locals_clock (worldStepCodeSc_of_pre_locals_clock hsb) mid.locals mid.clock
              have htail := ih mid.clock hmid_lt mid rfl (hmeta.trans hc) hW_mid hnt hfr
              exact worldStepCodeSc_trans hB hgw hsb' htail
            | some r =>
              cases r with
              | «continue» =>
                have hsb := hb sd hc hWd hnt_b (by rw [hbo]; exact Or.inr (Or.inl rfl))
                rw [hbo] at hsb
                have hW_mid : WorldOK mid := hsb.worldOK_bufs hB.1 hWd
                have hsb' : WorldStepCodeSc B gw s (some .continue) mid :=
                  worldStepCodeSc_with_locals_clock (worldStepCodeSc_of_pre_locals_clock hsb) mid.locals mid.clock
                have htail := ih mid.clock hmid_lt mid rfl (hmeta.trans hc) hW_mid hnt hfr
                exact worldStepCodeSc_trans hB hgw hsb' htail
              | «break» =>
                have hsb := hb sd hc hWd hnt_b (by rw [hbo]; exact Or.inr (Or.inr (Or.inl rfl)))
                rw [hbo] at hsb
                exact worldStepCodeSc_with_locals_clock (worldStepCodeSc_of_pre_locals_clock hsb) mid.locals mid.clock
              | timeOut => exact absurd rfl hnt
              | error => exact absurd hfr not_flowingOrResumes_error
              | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
              | returned v =>
                have hsb := hb sd hc hWd hnt_b (by rw [hbo]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rfl⟩))))
                rw [hbo] at hsb
                exact worldStepCodeSc_with_locals_clock (worldStepCodeSc_of_pre_locals_clock hsb) mid.locals mid.clock
              | exception eid ev =>
                have hres_ex : Resumes (some (.exception eid ev)) := by
                  rcases hfr with h | h | h | hr <;> try simp at h
                  exact hr
                have hsb := hb sd hc hWd hnt_b (by rw [hbo]; exact Or.inr (Or.inr (Or.inr hres_ex)))
                rw [hbo] at hsb
                exact worldStepCodeSc_with_locals_clock (worldStepCodeSc_of_pre_locals_clock hsb) mid.locals mid.clock
      · exact absurd hfr not_flowingOrResumes_error
      · exact absurd hfr not_flowingOrResumes_error

theorem progWStepCode_call0 {B Bf : BufList} {gw gwf : List String} {fname : MlS}
    {args : List (ExpHOL 64)}
    (hB : ∀ p ∈ Bf, p ∈ B) (hgw : ∀ g ∈ gwf, g ∈ gw)
    (hf : WorldKeepsCodeSc Bf gwf fname) :
    ProgWStepCode B gw (.call (some (none, none)) fname args) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        let ent := callEntryStateHOLFinite s callee
        have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hW
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, cpost⟩
        simp only [ent] at hrun
        simp only [hrun] at hnt hfr ⊢
        have hnt_c : (evaluateHOLFiniteState ent body').1 ≠ some .timeOut := by
          simp only [ent, hrun]; rintro rfl; simp at hnt
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | returned v =>
            dsimp only at hfr ⊢
            split
            · have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
              simp only [ent, hrun] at hspec
              exact worldStepCodeSc_from_entry (worldStepCodeSc_mono_bufs hB hgw (hspec (Or.inl ⟨v, rfl⟩)))
            · rename_i hbad; simp [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hres_ex : Resumes (some (.exception eid ev)) := by
              rcases hfr with h | h | h | hr <;> try simp at h
              exact hr
            have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
            simp only [ent, hrun] at hspec
            exact worldStepCodeSc_from_entry (worldStepCodeSc_mono_bufs hB hgw (hspec hres_ex))

theorem progWStepCode_call_local {B Bf : BufList} {gw gwf : List String} {x fname : MlS}
    {args : List (ExpHOL 64)}
    (hB : ∀ p ∈ Bf, p ∈ B) (hgw : ∀ g ∈ gwf, g ∈ gw)
    (hf : WorldKeepsCodeSc Bf gwf fname) :
    ProgWStepCode B gw (.call (some (some (.local, x), none)) fname args) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        let ent := callEntryStateHOLFinite s callee
        have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hW
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, cpost⟩
        simp only [ent] at hrun
        simp only [hrun] at hnt hfr ⊢
        have hnt_c : (evaluateHOLFiniteState ent body').1 ≠ some .timeOut := by
          simp only [ent, hrun]; rintro rfl; simp at hnt
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | returned v =>
            dsimp only at hfr ⊢
            split
            · split
              · have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
                simp only [ent, hrun] at hspec
                have hstep : WorldStepCodeSc B gw ent (some (.returned v)) cpost :=
                  worldStepCodeSc_mono_bufs hB hgw (hspec (Or.inl ⟨v, rfl⟩))
                simpa only [setKvarHOLFinite, setVarHOLFinite] using
                  (worldStepCodeSc_from_entry (r' := none) (callee := callee)
                    (L := s.locals.update (x, v)) (k := cpost.clock) hstep)
              · rename_i hb2; simp [‹shapeEqHOL _ _ = true›, hb2] at hfr; exact absurd hfr not_flowingOrResumes_error
            · rename_i hb1; simp [hb1] at hfr; exact absurd hfr not_flowingOrResumes_error
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hres_ex : Resumes (some (.exception eid ev)) := by
              rcases hfr with h | h | h | hr <;> try simp at h
              exact hr
            have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
            simp only [ent, hrun] at hspec
            have hstep : WorldStepCodeSc B gw ent (some (.exception eid ev)) cpost :=
              worldStepCodeSc_mono_bufs hB hgw (hspec hres_ex)
            exact worldStepCodeSc_from_entry hstep

theorem progWStepCode_decCall {B Bf : BufList} {gw gwf : List String}
    {x : MlS} {sh : ShapeHOL} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hBvalid : PosBufList B) (hgwSafe : SafeStepGlobals gw)
    (hB : ∀ p ∈ Bf, p ∈ B) (hgw : ∀ g ∈ gwf, g ∈ gw)
    (hf : WorldKeepsCodeSc Bf gwf fname)
    (hcont : ProgWStepCode B gw cont) :
    ProgWStepCode B gw (.decCall x sh fname args cont) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        let ent := callEntryStateHOLFinite s callee
        have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hW
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata ent body').1
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, cpost⟩
        simp only [ent] at hrun hmeta
        simp only [hrun] at hmeta hnt hfr ⊢
        have hnt_c : (evaluateHOLFiniteState ent body').1 ≠ some .timeOut := by
          simp only [ent, hrun]; rintro rfl; simp at hnt
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) sh && shapeEqHOL (shapeOfHOLExact v) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
              simp only [ent, hrun] at hspec
              have hstep1 : WorldStepCodeSc B gw ent (some (.returned v)) cpost :=
                worldStepCodeSc_mono_bufs hB hgw (hspec (Or.inl ⟨v, rfl⟩))
              set s1 := setVarHOLFinite x v { cpost with locals := s.locals }
              have hs1_step : WorldStepCodeSc B gw s none s1 := by
                simpa only [s1, setVarHOLFinite] using
                  (worldStepCodeSc_from_entry (r' := none) (callee := callee)
                    (L := s.locals.update (x, v)) (k := cpost.clock) hstep1)
              have hWs1 : WorldOK s1 := hs1_step.worldOK_bufs hBvalid.1 hW
              have hs1_code : s1.code = originalRuntimeCode := hmeta.trans hc
              have hstep2 := hcont s1 hs1_code hWs1 hnt hfr
              have hstep2' := worldStepCodeSc_with_locals_clock (r' := (evaluateHOLFiniteState s1 cont).1) hstep2
                (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s1 cont).2.locals (x, s.locals.lookup x))
                (evaluateHOLFiniteState s1 cont).2.clock
              exact worldStepCodeSc_trans hBvalid hgwSafe hs1_step hstep2'
            · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hres_ex : Resumes (some (.exception eid ev)) := by
              rcases hfr with h | h | h | hr <;> try simp at h
              exact hr
            have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
            simp only [ent, hrun] at hspec
            exact worldStepCodeSc_from_entry (worldStepCodeSc_mono_bufs hB hgw (hspec hres_ex))

theorem worldKeepsCodeSc_of_progWStepCode {B : BufList} {gw : List String}
    {fname : MlS} {params : List (MlS × ShapeHOL)} {body : ProgHOL 64} {ret : ShapeHOL}
    (hlook : originalRuntimeCode.lookup fname = some (params, body, ret))
    (hp : ProgWStepCode B gw body) :
    WorldKeepsCodeSc B gw fname :=
  ⟨params, body, ret, hlook, fun s hc hW _ hnt hres =>
    hp s hc hW hnt (Or.inr (Or.inr (Or.inr hres)))⟩

theorem worldKeepsCodeSc_of_readOnly {fname : MlS} (hro : ReadOnlyFn fname) :
    WorldKeepsCodeSc [] [] fname := by
  obtain ⟨ps, body, ret, hl, hb⟩ := hro
  refine ⟨ps, body, ret, hl, fun s hc hW hex hnt hres => ?_⟩
  have heq := hb s hc hW.1.1 hex hnt hres
  set post := (evaluateHOLFiniteState s body).2
  have h0 : WorldStepCodeSc [] [] s (evaluateHOLFiniteState s body).1
      { s with locals := post.locals, clock := post.clock } :=
    worldStepCodeSc_with_locals_clock (worldStepCodeSc_refl [] [] s none hW.1) post.locals post.clock
  rwa [← heq] at h0

/-! ## 3. Leaf Bridges: `WorldEff`, `sk_make`, & Non-Code `htab_set` -/

theorem worldEff_to_worldStepCodeSc {F : Type}
    {B B_eff : BufList} {gw : List String}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hWOK : WorldOK s)
    (hB_eff_ok : ∀ gs ∈ B_eff, gs ∈ globalBuffers ∧ gs.1 ∉ typedRecords.map Prod.fst)
    (hB_eff_valid : ValidBufList B_eff)
    (hcore_out : ∀ g ∈ R10Shards.P26_P28.coreWorldGlobals, ofString g ∉ gw.map ofString)
    (heff : WorldEff s post (bufRegions B s) B_eff gw) :
    WorldStepCodeSc B gw s r post := by
  have hAs := hWOK.1
  have hag : AllocatorGrows s post := ⟨heff.hp_lo, heff.sp_hi⟩
  have hcore : ∀ g ∈ R10Shards.P26_P28.coreWorldGlobals, globN post g = globN s g :=
    fun g hg => globN_eq_of_lookup (heff.gw_kept (ofString g) (hcore_out g hg))
  have hlow : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 :=
    ⟨mem_low_eq_of_domain_writes heff.out_dom hAs.1 (by rw [EvmBase.sourceBase_val]; omega),
     mem_low_eq_of_domain_writes heff.out_dom hAs.1 (by rw [EvmBase.sourceBase_val]; omega)⟩
  have hunhit_wti : ∀ {S Nd : List Nat}, WorldTypedWith s S Nd →
      IvlsDisj (bufRegions B s) (worldTypedIvls s S Nd) →
      ∀ i ∈ worldTypedIvls s S Nd, Allocated s i → i.1 % 8 = 0 → i.2 % 8 = 0 →
      IvlUnhit s post i := by
    intro S Nd hWT hD i hi hal hi1 hi2 a ha8 hhit
    by_contra hne
    have hin_a : i.1 ≤ a.toNat ∧ a.toNat + 8 ≤ i.1 + i.2 := by unfold CellHits at hhit; omega
    rcases heff.cell_frame a hne with ⟨iv, hiv, hch⟩ | ⟨gs, hgs, hch⟩ | hfg | hhf
    · exact not_cellHitsPos_of_disj hin_a (hD iv hiv i hi).flip hch
    · have hmem_b : bufferRegion s gs ∈ bufRegions B_eff s := List.mem_map.2 ⟨gs, hgs, rfl⟩
      exact not_cellHitsPos_of_disj hin_a (validBufList_disj hB_eff_valid hWT _ hmem_b i hi).flip hch
    · exact not_cellHitsPos_of_disj hin_a (disj_allocated_freeGap hAs.2 hal) hfg
    · exact not_cellHitsPos_of_disj hin_a (disj_allocated_heapFree hAs.2 hal) hhf
  have hu_tab_all : ∀ {S Nd : List Nat}, WorldTypedWith s S Nd →
      IvlsDisj (bufRegions B s) (worldTypedIvls s S Nd) →
      ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i := by
    intro S Nd hWT hD t ht i hi
    have hal := ((hWT.1.2.1 t ht).2 i hi).1
    have hw := ((hWT.1.2.1 t ht).1.1 i hi).2
    refine hunhit_wti hWT hD i ?_ hal hw.1 hw.2.1
    unfold worldTypedIvls
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨t, ht, hi⟩)))))
  refine ⟨⟨heff.to_worldStep_Q hWOK hB_eff_ok hcore_out
      (fun S Nd hWT hD _ _ _ _ => codeRootsValsEq_of_all_unhit hWT.1 (hu_tab_all hWT hD)),
    heff.sp_hi⟩, ?_⟩
  intro S Nd hWT hD
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  have hu_fix_wti : ∀ i ∈ worldTypedIvls s S Nd, i ∈ fixedObjects s → i.2 ≠ 0 → IvlUnhit s post i := by
    intro i hwti hfi hpos
    rcases hF.1 i hfi with h0 | ⟨hal, hw⟩
    · exact absurd h0 hpos
    · exact hunhit_wti ⟨hT, hJ, hF, hTr⟩ hD i hwti hal hw.1 hw.2.1
  have hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i :=
    hu_tab_all ⟨hT, hJ, hF, hTr⟩ hD
  have hu_ws : globN s "ws" ≠ 0 → IvlUnhit s post (globN s "ws", 40) := fun hnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("ws", 40), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using typedRecord_mem_fixedObjects s (r := ("ws", 40)) (by simp [typedRecords]))
      (by simp)
  have hu_bs : globN s "bs" ≠ 0 → IvlUnhit s post (globN s "bs", 80) := fun hnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("bs", 80), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using typedRecord_mem_fixedObjects s (r := ("bs", 80)) (by simp [typedRecords]))
      (by simp)
  have hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72) := fun hnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("ts", 72), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using typedRecord_mem_fixedObjects s (r := ("ts", 72)) (by simp [typedRecords]))
      (by simp)
  have hu_bo : globN s "bo" ≠ 0 → IvlUnhit s post (globN s "bo", 88) := fun hnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("bo", 88), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by simp [typedRecords]))
      (by simp)
  have hu_jr : globN s "journal_cap" ≠ 0 → IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap") := fun hcnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; right; simp [hcnz])
      (by unfold fixedObjects; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; right; simp [hcnz])
      (by dsimp only; omega)
  have hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → IvlUnhit s post i := fun i hi h24 =>
    hu_fix_wti i
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; right; exact hi)
      (by unfold fixedObjects; apply List.mem_append.2; left; apply List.mem_append.2; right; exact hi)
      (by omega)
  have hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → IvlUnhit s post i := fun i hi hpos =>
    hu_fix_wti i
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; right; exact hi)
      (by unfold fixedObjects; exact List.mem_append.2 (Or.inr hi))
      hpos
  have hu_nd_rec : ∀ n ∈ Nd, IvlUnhit s post (nodeIvl s n) := fun n hn => by
    have hal := (hTr.1.1 n hn).2.1
    have hw := (hTr.1.1 n hn).2.2.2.1
    refine hunhit_wti ⟨hT, hJ, hF, hTr⟩ hD _ ?_ hal hw.1 hw.2.1
    unfold worldTypedIvls; refine List.mem_append.2 (Or.inr ?_)
    unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodeIvl]⟩
  have hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k) := by
    intro n hn h12 hlen0 k hk
    have hhl_lt : heapLimit < 2 ^ 64 := by decide
    rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_p, hin_p, _⟩
    · exact absurd h0 hlen0
    · have hp_wti : (memW s (n + 32), memW s (n + 40)) ∈ worldTypedIvls s S Nd := by
        unfold worldTypedIvls; refine List.mem_append.2 (Or.inr ?_)
        unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩
      by_contra hne_b
      have ha_lt : memW s (n + 32) + k < 2 ^ 64 := by have := hin_p.2; dsimp at this; omega
      have hbfr := heff.byte_frame (memW s (n + 32) + k) ha_lt hne_b
      rcases hbfr with ⟨ivl, hivl, hin⟩ | ⟨gs, hgs, hin⟩ | hfg | hhf
      · have hdj := hD ivl hivl _ hp_wti
        simp only [Wave8GuestInv.InIvl] at hin
        rcases hdj with h0 | h0 | h1 | h2 <;> omega
      · have hmem_b : Wave8GuestInv.bufferRegion s gs ∈ bufRegions B_eff s := List.mem_map.2 ⟨gs, hgs, rfl⟩
        have hdj := validBufList_disj hB_eff_valid ⟨hT, hJ, hF, hTr⟩ _ hmem_b _ hp_wti
        simp only [Wave8GuestInv.InIvl] at hin
        rcases hdj with h0 | h0 | h1 | h2 <;> omega
      · have hdj := disj_allocated_freeGap hAs.2 hal_p
        simp only [Wave8GuestInv.InIvl] at hfg
        rcases hdj with h0 | h0 | h1 | h2 <;> omega
      · have hdj := disj_allocated_heapFree hAs.2 hal_p
        simp only [Wave8GuestInv.InIvl] at hhf
        rcases hdj with h0 | h0 | h1 | h2 <;> omega
  have hbo_eq := (Fast_C08WkShard03.blockOutObjects_eq_of_bo_unhit hAs.2 hF (hcore "bo" (by decide))
    hT.2.2.2.2.2.2.2.2.2.2.1 hu_bo hu_bo_lst).1
  have hbal_eq := (Fast_C08WkShard03.balObjects_eq_of_unhit hAs.2 hT hF (hcore "bal_accounts" (by decide))
    hu_tab hu_bal hlow).1
  obtain ⟨hF_post, hfix_new⟩ := Fast_C08WkShard03.fixedTyped_of_freshBufsOK hAs heff.arena hag hF
    (hcore "journal" (by decide)) (hcore "journal_cap" (by decide)) hbo_eq hbal_eq heff.fresh_bufs
  obtain ⟨hWT_post, _, _, hfp_eq⟩ := Fast_C08WkShard03.worldTypedWith_congr_w1 hAs heff.arena hag hcore
    ⟨hT, hJ, hF, hTr⟩ hu_tab hu_ws hu_bs hu_ts hu_bo hu_jr hu_bo_lst hu_bal hu_nd_rec hu_nd_byte
    hlow hF_post hfix_new
  refine ⟨⟨Nd, hWT_post⟩, ?_, ?_⟩
  · intro o ho
    unfold nonTrieOwned at ho
    rcases List.mem_append.1 ho with ho_tab | ho_fix
    · obtain ⟨t, ht, hi⟩ := List.mem_flatMap.1 ho_tab
      rw [hfp_eq t ht] at hi
      refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
      unfold nonTrieOwned
      exact List.mem_append_left _ (List.mem_flatMap.2 ⟨t, ht, hi⟩)
    · rcases hfix_new o ho_fix with ho_old | rfl | ho_fr
      · refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
        unfold nonTrieOwned
        exact List.mem_append_right _ ho_old
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ho_fr)
  · intro a hkeep hfresh
    by_contra hne
    rcases heff.cell_frame a hne with ⟨ivl, hivl, _, hhit⟩ | ⟨gs, hgs, _, hhit⟩ | ⟨_, hfg⟩ | ⟨_, hhf⟩
    · exact hkeep ivl (List.mem_append_left _ (List.mem_append_right _ hivl)) hhit
    · have hfo_gs : bufferRegion s gs ∈ fixedObjects s := by
        unfold fixedObjects; apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_map.2 ⟨gs, (hB_eff_ok gs hgs).1, rfl⟩
      have hno_gs : bufferRegion s gs ∈ nonTrieOwned s S := by
        unfold nonTrieOwned; exact List.mem_append_right _ hfo_gs
      exact hkeep _ (List.mem_append_left _ (List.mem_append_left _ hno_gs)) hhit
    · exact hkeep (freeGap s) (List.mem_append_right _ List.mem_cons_self) hfg
    · exact hfresh hhf

theorem wkCodeSc_sk_make :
    WorldKeepsCodeSc [("sk_buf", 52)] [] (ofString "sk_make") := by
  refine ⟨_, _, _, EvmFrameSpecs.lookup_sk_make, fun {F} s hc hW _ hnt hres => ?_⟩
  have hsk_fit : ∀ (_ : globN s "sk_buf" ≠ 0), globN s "sk_buf" + 52 ≤ 2 ^ 64 := by
    intro hz
    obtain ⟨hA0, S0, hWT0⟩ := hW
    have hmem_fix : (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 64) ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.2 ⟨("sk_buf", 64), by decide, rfl⟩
    rw [if_neg hz] at hmem_fix
    rcases fixedObject_le_2pow64 hA0.2 hWT0.2.2.1 hmem_fix with h0 | hbnd
    · dsimp only at h0; omega
    · dsimp only at hbnd; omega
  obtain ⟨_, _, _, hnz, heff⟩ := eval_sk_make_body_evm s hc hW.1.1.memaddrs hsk_fit hnt hres
  set post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make)).2
  have hbeff : Fast_C08WkShard03.ByteEff s post [(globN s "sk_buf", 52)] := by
    refine ⟨heff.code, heff.memaddrs, heff.shMemaddrs, heff.baseAddr, heff.be, heff.globals,
      (PanRunBounded.evaluateHOLFiniteState_metadata s
        (sourceFnBody Guest.Software.guestFn_sk_make)).2.2.2.2,
      (fun a hne => by by_contra hna; exact hne (heff.out_dom a hna)),
      (fun a hne => by
        by_contra hno
        apply hne
        exact heff.cell_frame a (fun i hi hpos hh => hno ⟨i, hi, Nat.pos_of_ne_zero hpos, hh⟩)),
      (fun b hb64 hne => by
        by_contra hno
        apply hne
        exact heff.byte_frame b hb64 (fun i hi hh => hno ⟨i, hi, hh⟩))⟩
  have hweff : WorldEff s post (bufRegions [("sk_buf", 52)] s) [] [] :=
    (WorldEff.refl s (bufRegions [("sk_buf", 52)] s) [] [] hW.1 hc).of_byteEff hbeff
      (fun iv hiv _ => by
        simp only [List.mem_singleton] at hiv
        subst hiv
        exact Or.inl ⟨(globN s "sk_buf", 52), by
          unfold bufRegions
          exact List.mem_map.2 ⟨("sk_buf", 52), by simp, by simp [Wave8GuestInv.bufferRegion, hnz]⟩,
          le_rfl, le_rfl⟩)
  exact worldEff_to_worldStepCodeSc hW (by decide) (by intro p hp; cases hp) (by decide) hweff

theorem posBufList_nil : PosBufList [] :=
  And.intro (fun _ hp => nomatch hp) (fun _ hp => nomatch hp)

theorem posBufList_sk : PosBufList [("sk_buf", 52)] :=
  ⟨fun p hp => by simp at hp; subst hp; exact ⟨64, by decide, by decide, by decide⟩, by decide⟩

theorem posBufList_wsAcctBufs : PosBufList wsAcctBufs :=
  ⟨validBufList_wsAcctBufs, by decide⟩

theorem posBufList_extCodeBufs : PosBufList extCodeBufs :=
  ⟨validBufList_extCodeBufs, by decide⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
