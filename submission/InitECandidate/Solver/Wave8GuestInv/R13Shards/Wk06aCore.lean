import InitECandidate.Solver.Wave8GuestInv.MemoryViews
import InitECandidate.Solver.Wave8GuestInv.EntryDefs
import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.WorldFrame
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.Exec
import InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.DelSpecs
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M25.nz_htab_set
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M25.rt_alloc
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.rt_scratch_alloc
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M12.wk_st_le64
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.RlpMemcpyLemmas
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M08.wk_memzero
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M08.wk_memcpy
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_htab_get
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_htab_item
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_memeq
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_stor_lookup
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_u256_is_zero
import InitECandidate.Solver.Wave8GuestInv.R13Shards.HtabSetSpec

/-! Shared zero-sorry relational `WorldStep` composition, W1/W2/W4 world-typing preservation,
and Hoare/execution combinators for `WkShard06a`.
Imports only prebuilt zero-sorry modules (`MemoryViews`, `EntryDefs`, `Expressions`, `Deliveries/*`,
and `R13Shards/HtabSetSpec`). -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

/-! ## 1. Verbatim `WorldStep` / `WorldKeeps` definitions in `Wave8GuestInv` namespace
(definitionally `rfl`-equal to `ContractParts/C00`–`C03` and `Primitives.lean`, without importing `C00`) -/

abbrev FunSpec := @M13.FunSpec
abbrev OnReturn := @M13.OnReturn
abbrev Resumes := @M13.Resumes
abbrev ArgNonNull := @M13.ArgNonNull
abbrev ReadOnlyFn := @M13.ReadOnlyFn
abbrev FreshBlock := @M13.FreshBlock
abbrev RetWord := @M13.RetWord
abbrev Returns := @M13.Returns
abbrev WorldTypedWith := @M13.WorldTypedWith
abbrev typedRecords := M13.typedRecords
abbrev worldTypedIvls := @M13.worldTypedIvls
abbrev worldOwned := @M13.worldOwned
abbrev IvlsDisj := M13.IvlsDisj
abbrev freeGap := @M13.freeGap
abbrev heapFree := @M13.heapFree
abbrev GlobalsKept := @M13.GlobalsKept
abbrev RecordsKept := @M13.RecordsKept
abbrev OwnedGrows := @M13.OwnedGrows
abbrev NoExtra := @M13.NoExtra
abbrev WorldStep := @M13.WorldStep
abbrev WorldKeeps := @M13.WorldKeeps
abbrev RetAvoids := @M13.RetAvoids
abbrev RetAvoidsIf := @M13.RetAvoidsIf

namespace R13Wk06a

abbrev stdKeep : List (String × List Nat) := M13.stdKeep
abbrev coreWorldGlobals : List String := M13.coreWorldGlobals

def bufferRegion {F : Type} (s : PanSemStateFiniteExact 64 F) (gn : String × Nat) : Ivl :=
  (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)

theorem worldTyped_iff_with {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) :
    WorldTyped s S ↔ ∃ Nd, WorldTypedWith s S Nd := by
  simp only [WorldTyped, TriesTyped, WorldTypedWith, M13.WorldTypedWith]
  constructor
  · rintro ⟨h1, h2, h3, Nd, h4⟩; exact ⟨Nd, h1, h2, h3, h4⟩
  · rintro ⟨Nd, h1, h2, h3, h4⟩; exact ⟨h1, h2, h3, Nd, h4⟩

/-! ## 2. Basic interval, alignment, and local-invariance helpers -/

theorem not_resumes_error : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

theorem not_resumes_none : ¬ Resumes (none : Option (PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

theorem disj_flip {i j : Ivl} (h : Disj i j) : Disj j i := M13.Disj.symm h

theorem disj_zero_left (j : Ivl) : Disj (0, 0) j := Or.inl rfl
theorem disj_zero_right (i : Ivl) : Disj i (0, 0) := Or.inr (Or.inl rfl)

theorem disj_of_inside_left {i i' j : Ivl} (hin : Inside i i'.1 (i'.1 + i'.2))
    (hd : Disj i' j) : Disj i j := by
  rcases hin with ⟨h1, h2⟩
  rcases hd with h0 | h0 | hle | hge
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl h0)
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

theorem disj_of_inside_right {i j j' : Ivl} (hin : Inside j j'.1 (j'.1 + j'.2))
    (hd : Disj i j') : Disj i j :=
  disj_flip (disj_of_inside_left hin (disj_flip hd))

theorem inside_trans {i j : Ivl} {lo hi : Nat}
    (h1 : Inside i j.1 (j.1 + j.2)) (h2 : Inside j lo hi) : Inside i lo hi :=
  ⟨le_trans h2.1 h1.1, le_trans h1.2 h2.2⟩

theorem cellHits_of_inside {a : Nat} {i : Ivl} {lo hi : Nat}
    (hc : CellHits a i) (hin : Inside i lo hi) : CellHits a (lo, hi - lo) := by
  obtain ⟨h1, h2⟩ := hc
  obtain ⟨hlo, hhi⟩ := hin
  exact ⟨by omega, by dsimp; omega⟩

theorem not_cellHits_zero_aligned {a : Nat} {x : Nat}
    (ha8 : a % 8 = 0) (hx8 : x % 8 = 0) : ¬ CellHits a (x, 0) := by
  intro ⟨h1, h2⟩
  dsimp only at h1 h2
  omega

theorem not_cellHits_of_disj_aligned {a : Nat} {i j : Ivl}
    (ha8 : a % 8 = 0) (hj1 : j.1 % 8 = 0)
    (hin1 : i.1 ≤ a) (hin2 : a + 8 ≤ i.1 + i.2) (hd : Disj i j) :
    ¬ CellHits a j :=
  M13.not_cellHits_of_disj_aligned ha8 hj1 hin1 hin2 hd

theorem globN_eq_of_lookup {F : Type} {s post : PanSemStateFiniteExact 64 F} {name : String}
    (h : s.globals.lookup (ofString name) = post.globals.lookup (ofString name)) :
    globN post name = globN s name := by
  simp only [globN, ← h]

theorem freeChain_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k nodes : Nat) :
    ∀ (Fr : List Nat) (head : Nat),
      FreeChain { s with locals := locals, clock := k } nodes head Fr ↔ FreeChain s nodes head Fr
  | [], _ => Iff.rfl
  | f :: rest, head => by
    simp only [FreeChain]
    exact and_congr Iff.rfl (freeChain_with_locals s locals k nodes rest _)

theorem htabWF_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k t : Nat) :
    HtabWF { s with locals := locals, clock := k } t ↔ HtabWF s t := by
  simp only [HtabWF, freeChain_with_locals]; exact Iff.rfl

theorem worldTypedWith_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S Nd : List Nat) :
    WorldTypedWith { s with locals := locals, clock := k } S Nd ↔ WorldTypedWith s S Nd := by
  simp only [WorldTypedWith, M13.WorldTypedWith, TablesTyped, htabWF_with_locals]
  exact Iff.rfl

theorem arenaReady_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    ArenaReady { s with locals := locals, clock := k } ↔ ArenaReady s :=
  ⟨fun h => ⟨guestInv_congr (s := { s with locals := locals, clock := k }) rfl rfl rfl rfl h.1, h.2⟩,
   fun h => ⟨guestInv_with_locals_clock s locals k h.1, h.2⟩⟩

theorem worldOK_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    WorldOK { s with locals := locals, clock := k } ↔ WorldOK s := by
  simp only [WorldOK, arenaReady_with_locals, worldTyped_iff_with, worldTypedWith_with_locals]

theorem worldStep_with_locals_right {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (hQ : ∀ S' Nd', Q s r post S' Nd' → Q s r { post with locals := L, clock := k } S' Nd')
    (h : WorldStep R gw keep Q s r post) :
    WorldStep R gw keep Q s r { post with locals := L, clock := k } := by
  obtain ⟨hAp, hhp, hgw, hrk, hws⟩ := h
  refine ⟨(arenaReady_with_locals post L k).2 hAp, hhp, hgw, hrk, fun S Nd hWT hD => ?_⟩
  obtain ⟨S', Nd', hsub, hWT', hog, hfr, hq⟩ := hws S Nd hWT hD
  exact ⟨S', Nd', hsub, (worldTypedWith_with_locals post L k S' Nd').2 hWT', hog, hfr, hQ S' Nd' hq⟩

theorem worldStep_with_locals_left {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {s s' post : PanSemStateFiniteExact 64 F} {r r' : Option (PanSemResultExact 64)}
    (hs' : s' = { s with locals := s'.locals, clock := s'.clock })
    (hR : R s' = R s)
    (hQ : ∀ S' Nd', Q s' r' post S' Nd' → Q s r post S' Nd')
    (h : WorldStep R gw keep Q s' r' post) :
    WorldStep R gw keep Q s r post := by
  obtain ⟨hAp, hhp, hgw, hrk, hws⟩ := h
  have hgn : ∀ nm, globN s' nm = globN s nm := fun nm => by rw [hs']; rfl
  have hm : s'.memory = s.memory := by rw [hs']
  have hg : s'.globals = s.globals := by rw [hs']
  refine ⟨hAp, by rw [← hgn]; exact hhp, fun k hk => by rw [← hg]; exact hgw k hk, ?_, ?_⟩
  · intro rec hrec hnz k hk hnoR
    have h1 := hrk rec hrec (by rw [hgn]; exact hnz) k hk (by
      change ∀ i ∈ R s', ¬ CellHits (globN s' rec.1 + k) i
      rw [hR, hgn]; exact hnoR)
    rw [hgn] at h1
    exact h1.trans (by unfold memW; rw [hm])
  · intro S Nd hWT hD
    have hWT' : WorldTypedWith s' S Nd := by
      rw [hs']; exact (worldTypedWith_with_locals s s'.locals s'.clock S Nd).2 hWT
    have hwti_eq : M13.worldTypedIvls s' S Nd = M13.worldTypedIvls s S Nd := by
      rw [hs']; rfl
    have hwo_eq : M13.worldOwned s' S Nd = M13.worldOwned s S Nd := by
      rw [hs']; rfl
    have hfg_eq : M13.freeGap s' = M13.freeGap s := by rw [hs']; rfl
    have hhf_eq : M13.heapFree s' = M13.heapFree s := by rw [hs']; rfl
    obtain ⟨S', Nd', hsub, hWTp, hog, hfr, hq⟩ := hws S Nd hWT' (by
      change M13.IvlsDisj (R s') (M13.worldTypedIvls s' S Nd)
      rw [hR, hwti_eq]; exact hD)
    refine ⟨S', Nd', hsub, hWTp, ?_, ?_, hQ S' Nd' hq⟩
    · intro o ho
      rcases hog o ho with rfl | ⟨j, hj, hin⟩ | hinh
      · exact Or.inl rfl
      · rw [hwo_eq] at hj; exact Or.inr (Or.inl ⟨j, hj, hin⟩)
      · rw [hgn] at hinh; exact Or.inr (Or.inr hinh)
    · intro a hkeep hfresh
      rw [← hm]
      exact hfr a (by
        change ∀ i ∈ M13.worldOwned s' S Nd ++ R s' ++ [M13.freeGap s'], ¬ CellHits a.toNat i
        rw [hwo_eq, hR, hfg_eq]; exact hkeep) (by rw [hhf_eq]; exact hfresh)

theorem worldStep_refl {F : Type}
    (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl)
    (gw : List String)
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hAR : ArenaReady s)
    (heq : post = { s with locals := post.locals, clock := post.clock }) :
    WorldStep R gw stdKeep NoExtra s r post := by
  have hARp : ArenaReady post := by rw [heq]; exact (arenaReady_with_locals s _ _).2 hAR
  have hgn : ∀ nm, globN post nm = globN s nm := fun nm => by rw [heq]; rfl
  have hm : post.memory = s.memory := by rw [heq]
  have hg : post.globals = s.globals := by rw [heq]
  refine ⟨hARp, by rw [hgn], fun _ _ => by rw [hg],
    fun _ _ _ _ _ _ => by unfold memW; rw [hm],
    fun S Nd hWT _ => ⟨S, Nd, fun _ h => h, ?_, ?_, fun _ _ _ => by rw [hm], trivial⟩⟩
  · rw [heq]; exact (worldTypedWith_with_locals s _ _ S Nd).2 hWT
  · intro o ho
    have hwo : M13.worldOwned post S Nd = M13.worldOwned s S Nd := by rw [heq]; rfl
    rw [hwo] at ho
    exact Or.inr (Or.inl ⟨o, ho, le_rfl, le_rfl⟩)

/-! ## 3. Untyped buffer separation & `WorldStep` monotonicity / composition -/

theorem bufferRegion_in_fixedObjects {F : Type} (s : PanSemStateFiniteExact 64 F)
    {gn : String × Nat} (hgb : gn ∈ globalBuffers) :
    bufferRegion s gn ∈ fixedObjects s := by
  unfold fixedObjects bufferRegion
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  exact List.mem_map.2 ⟨gn, hgb, rfl⟩

theorem bufferRegion_disj_worldTypedIvls {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hWT : WorldTypedWith s S Nd)
    {gn : String × Nat} (hgb : gn ∈ globalBuffers)
    (huntyped : gn.1 ∉ ["ws", "bs", "ts", "bo"])
    {n : Nat} (hle : n ≤ gn.2) :
    ∀ j ∈ worldTypedIvls s S Nd, Disj (bufferRegion s (gn.1, n)) j := by
  intro j hj
  by_cases hz : globN s gn.1 = 0
  · exact Or.inl (by simp [bufferRegion, hz])
  · rcases M13.untypedGlobalBuf_disj_worldTypedIvls hWT hgb huntyped j hj with hj0 | hdj
    · exact Or.inr (Or.inl hj0)
    · simp only [bufferRegion, hz, ↓reduceIte] at hdj ⊢
      rcases hdj with h0 | h0 | h | h
      · exact Or.inl (by dsimp at h0 ⊢; omega)
      · exact Or.inr (Or.inl h0)
      · exact Or.inr (Or.inr (Or.inl (by dsimp at h ⊢; omega)))
      · exact Or.inr (Or.inr (Or.inr (by dsimp at h ⊢; omega)))

theorem bufferRegion_sub_fixedObject {F : Type} (s : PanSemStateFiniteExact 64 F)
    {gn : String × Nat} (hgb : gn ∈ globalBuffers) {n : Nat} (hle : n ≤ gn.2) :
    ∃ f ∈ fixedObjects s, Inside (bufferRegion s (gn.1, n)) f.1 (f.1 + f.2) := by
  refine ⟨bufferRegion s gn, bufferRegion_in_fixedObjects s hgb, ?_⟩
  by_cases hz : globN s gn.1 = 0 <;> (simp [bufferRegion, hz, Inside]; try omega)

theorem bufferRegion_zero_or_allocated {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hWT : WorldTypedWith s S Nd)
    {gn : String × Nat} (hgb : gn ∈ globalBuffers) {n : Nat} (hle : n ≤ gn.2) :
    (bufferRegion s (gn.1, n)).2 = 0 ∨ Allocated s (bufferRegion s (gn.1, n)) := by
  by_cases hz : globN s gn.1 = 0
  · exact Or.inl (by simp [bufferRegion, hz])
  · rcases hWT.2.2.1.1 _ (bufferRegion_in_fixedObjects s hgb) with h0 | ⟨hal, _⟩
    · simp only [bufferRegion, hz, ↓reduceIte] at h0 ⊢; omega
    · simp only [bufferRegion, hz, ↓reduceIte] at hal ⊢
      rcases hal with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr (Or.inl ⟨h1, by dsimp at h2 ⊢; omega⟩)
      · exact Or.inr (Or.inr ⟨h1, by dsimp at h2 ⊢; omega⟩)

theorem worldOwned_zero_or_allocated {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hWT : WorldTypedWith s S Nd) {o : Ivl} (ho : o ∈ worldOwned s S Nd) :
    o.2 = 0 ∨ Allocated s o := by
  obtain ⟨hT, _, hF, hTr⟩ := hWT
  unfold worldOwned at ho
  rcases List.mem_append.1 ho with h12 | hnd
  · rcases List.mem_append.1 h12 with htab | hfix
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 htab
      exact Or.inr (((hT.2.1 t ht).2 o hfp).1)
    · rcases hF.1 o hfix with h0 | ⟨hal, _⟩
      · exact Or.inl h0
      · exact Or.inr hal
  · unfold nodeExtents at hnd
    obtain ⟨n, hn, hni⟩ := List.mem_flatMap.1 hnd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hni
    rcases hni with rfl | rfl
    · exact Or.inr (hTr.1.1 n hn).2.1
    · unfold nodePath
      split_ifs with hp
      · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hp.1 with h0 | ⟨_, hal, _, _⟩
        · exact absurd h0 hp.2
        · exact Or.inr hal
      · exact Or.inl rfl

/-- Monotonicity of `WorldStep` in `gw`, `R`, and `Q`. -/
theorem worldStep_weaken {F : Type}
    {R1 R2 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw1 gw2 : List String}
    {Q1 Q2 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hgw : ∀ g ∈ gw1, g ∈ gw2)
    (hR_disj : ∀ S Nd, WorldTypedWith s S Nd → IvlsDisj (R2 s) (worldTypedIvls s S Nd) →
      IvlsDisj (R1 s) (worldTypedIvls s S Nd))
    (hR_rec : ∀ rec ∈ stdKeep, globN s rec.1 ≠ 0 → ∀ k ∈ rec.2,
      (∀ i ∈ R2 s, ¬ CellHits (globN s rec.1 + k) i) →
      (∀ i ∈ R1 s, ¬ CellHits (globN s rec.1 + k) i))
    (hR_frame : ∀ S Nd, WorldTypedWith s S Nd → ∀ i ∈ R1 s,
      (i.2 = 0 ∧ i.1 = 0) ∨
      (∃ j ∈ R2 s, Inside i j.1 (j.1 + j.2)) ∨
      (∃ j ∈ worldOwned s S Nd, Inside i j.1 (j.1 + j.2)))
    (hQ : ∀ S' Nd', Q1 s r post S' Nd' → Q2 s r post S' Nd')
    (h : WorldStep R1 gw1 stdKeep Q1 s r post) :
    WorldStep R2 gw2 stdKeep Q2 s r post := by
  obtain ⟨hAp, hhp, hgk1, hrk1, hws1⟩ := h
  refine ⟨hAp, hhp, ?_, ?_, ?_⟩
  · intro k hk
    apply hgk1 k
    intro hmem
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hmem
    exact hk (List.mem_map.2 ⟨g, hgw g hg, rfl⟩)
  · intro rec hrec hnz k hk hno2
    exact hrk1 rec hrec hnz k hk (hR_rec rec hrec hnz k hk hno2)
  · intro S Nd hWT hD2
    obtain ⟨S', Nd', hsub, hWT', hog, hfr1, hq1⟩ := hws1 S Nd hWT (hR_disj S Nd hWT hD2)
    refine ⟨S', Nd', hsub, hWT', hog, ?_, hQ S' Nd' hq1⟩
    intro a hkeep2 hfresh
    apply hfr1 a _ hfresh
    intro i hi hch
    rcases List.mem_append.1 hi with hi12 | hfg
    · rcases List.mem_append.1 hi12 with hi_wo | hi_R1
      · exact hkeep2 i (List.mem_append_left _ (List.mem_append_left _ hi_wo)) hch
      · rcases hR_frame S Nd hWT i hi_R1 with ⟨hz2, hz1⟩ | ⟨j, hj2, hin⟩ | ⟨j, hj_wo, hin⟩
        · obtain ⟨_, c2⟩ := hch; change a.toNat < i.1 + i.2 at c2; omega
        · obtain ⟨c1, c2⟩ := hch; obtain ⟨n1, n2⟩ := hin
          exact hkeep2 j (List.mem_append_left _ (List.mem_append_right _ hj2)) ⟨by omega, by omega⟩
        · obtain ⟨c1, c2⟩ := hch; obtain ⟨n1, n2⟩ := hin
          exact hkeep2 j (List.mem_append_left _ (List.mem_append_left _ hj_wo)) ⟨by omega, by omega⟩
    · exact hkeep2 i (List.mem_append_right _ hfg) hch

/-- Sequential composition of two `WorldStep` transitions `s -> m -> post` where `R` consists of
untyped global buffers (so `IvlsDisj (R m) (worldTypedIvls m S' Nd')` holds automatically for any
exit typing `(S', Nd')`, and `R m = R s`) and `gw` excludes `ws`, `bs`, `ts`, `bo`, `frame_mem_ptr`. -/
theorem worldStep_trans_bufs {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String}
    {Q Q1 Q2 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {s m post : PanSemStateFiniteExact 64 F}
    {r1 r2 : Option (PanSemResultExact 64)}
    (hAs : ArenaOK s)
    (h1 : WorldStep R gw stdKeep Q1 s r1 m)
    (h2 : WorldStep R gw stdKeep Q2 m r2 post)
    (hsp_le : globN m "scratch_ptr" ≤ globN s "scratch_ptr")
    (hR_eq : R m = R s)
    (hR_disj_m : ∀ S' Nd', WorldTypedWith m S' Nd' → IvlsDisj (R m) (worldTypedIvls m S' Nd'))
    (hgw_recs : ∀ g ∈ ["ws", "bs", "ts", "bo", "frame_mem_ptr"], ofString g ∉ gw.map ofString)
    (hQ : ∀ S' Nd' S'' Nd'', Q1 s r1 m S' Nd' → Q2 m r2 post S'' Nd'' → Q s r2 post S'' Nd'') :
    WorldStep R gw stdKeep Q s r2 post := by
  obtain ⟨hAm, hhp1, hgk1, hrk1, hws1⟩ := h1
  obtain ⟨hAp, hhp2, hgk2, hrk2, hws2⟩ := h2
  have hhp : globN s "heap_ptr" ≤ globN post "heap_ptr" := le_trans hhp1 hhp2
  have hgk : GlobalsKept gw s post := fun k hk => (hgk1 k hk).trans (hgk2 k hk)
  have hfmp_eq : globN m "frame_mem_ptr" = globN s "frame_mem_ptr" :=
    globN_eq_of_lookup (hgk1 (ofString "frame_mem_ptr") (hgw_recs "frame_mem_ptr" (by decide)))
  have hrk : RecordsKept R stdKeep s post := by
    intro rec hrec hnz k hk hnoR
    have hrec_not : ofString rec.1 ∉ gw.map ofString := by
      apply hgw_recs rec.1
      simp only [stdKeep, M13.stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl <;> decide
    have hg_rec : globN m rec.1 = globN s rec.1 :=
      globN_eq_of_lookup (hgk1 (ofString rec.1) hrec_not)
    have e1 := hrk1 rec hrec hnz k hk hnoR
    have e2 := hrk2 rec hrec (by rw [hg_rec]; exact hnz) k hk (by
      change ∀ i ∈ R m, ¬ CellHits (globN m rec.1 + k) i
      rw [hg_rec, hR_eq]; exact hnoR)
    rw [hg_rec] at e2
    exact e2.trans e1
  refine ⟨hAp, hhp, hgk, hrk, fun S Nd hWT hD => ?_⟩
  obtain ⟨S', Nd', hsub1, hWT1, hog1, hfr1, hq1⟩ := hws1 S Nd hWT hD
  obtain ⟨S'', Nd'', hsub2, hWT2, hog2, hfr2, hq2⟩ := hws2 S' Nd' hWT1 (hR_disj_m S' Nd' hWT1)
  refine ⟨S'', Nd'', fun t ht => hsub2 t (hsub1 t ht), hWT2, ?_, ?_, hQ S' Nd' S'' Nd'' hq1 hq2⟩
  · -- `OwnedGrows s post (worldOwned s S Nd) (worldOwned post S'' Nd'')`
    intro o ho2
    rcases hog2 o ho2 with rfl | ⟨j1, hj1, hin1⟩ | hinh2
    · exact Or.inl rfl
    · rcases hog1 j1 hj1 with rfl | ⟨j0, hj0, hin0⟩ | hinh1
      · have ho0 : o.2 = 0 := by dsimp [Inside] at hin1; omega
        exact Or.inl (Prod.ext (by dsimp [Inside] at hin1; omega) ho0)
      · exact Or.inr (Or.inl ⟨j0, hj0, inside_trans hin1 hin0⟩)
      · exact Or.inr (Or.inr ⟨le_trans hinh1.1 hin1.1, le_trans hin1.2 (le_trans hinh1.2 hhp2)⟩)
    · exact Or.inr (Or.inr ⟨le_trans hhp1 hinh2.1, hinh2.2⟩)
  · intro a hkeep_s hfresh_s
    have hnot_fresh_m : ¬ CellHits a.toNat (M13.heapFree m) := by
      intro ⟨hc1, hc2⟩
      change globN m "heap_ptr" < a.toNat + 8 at hc1
      change a.toNat < globN m "heap_ptr" + (heapLimit - globN m "heap_ptr") at hc2
      apply hfresh_s
      unfold M13.heapFree CellHits
      dsimp only
      have hm_hi : globN m "heap_ptr" ≤ heapLimit := hAm.2.2.1
      exact ⟨by omega, by omega⟩
    have hnot_keep_m : ∀ i ∈ M13.worldOwned m S' Nd' ++ R m ++ [M13.freeGap m], ¬ CellHits a.toNat i := by
      intro i hi hch
      rcases List.mem_append.1 hi with hi12 | hfg
      · rcases List.mem_append.1 hi12 with hi_wo | hi_Rm
        · rcases hog1 i hi_wo with rfl | ⟨j, hj, hin⟩ | hinh
          · obtain ⟨_, c2⟩ := hch; dsimp only at c2; omega
          · obtain ⟨hc1, hc2⟩ := hch
            obtain ⟨hn1, hn2⟩ := hin
            apply hkeep_s j (List.mem_append_left _ (List.mem_append_left _ hj))
            exact ⟨by omega, by omega⟩
          · obtain ⟨hc1, hc2⟩ := hch
            obtain ⟨hn1, hn2⟩ := hinh
            apply hfresh_s
            unfold M13.heapFree CellHits
            dsimp only
            have hm_hi : globN m "heap_ptr" ≤ heapLimit := hAm.2.2.1
            exact ⟨by omega, by omega⟩
        · rw [hR_eq] at hi_Rm
          exact hkeep_s i (List.mem_append_left _ (List.mem_append_right _ hi_Rm)) hch
      · simp only [List.mem_singleton] at hfg
        subst hfg
        obtain ⟨hc1, hc2⟩ := hch
        change globN m "frame_mem_ptr" < a.toNat + 8 at hc1
        change a.toNat < globN m "frame_mem_ptr" + (globN m "scratch_ptr" - globN m "frame_mem_ptr") at hc2
        apply hkeep_s (M13.freeGap s) (List.mem_append_right _ (List.mem_singleton.2 rfl))
        unfold M13.freeGap CellHits
        dsimp only
        rw [hfmp_eq] at hc1 hc2
        have hfm_le_sp_m : globN m "frame_mem_ptr" ≤ globN m "scratch_ptr" := hAm.2.2.2.2.1
        rw [hfmp_eq] at hfm_le_sp_m
        exact ⟨by omega, by omega⟩
    exact (hfr2 a hnot_keep_m hnot_fresh_m).trans (hfr1 a hkeep_s hfresh_s)

end R13Wk06a
end InitECandidate.Solver.Wave8GuestInv
