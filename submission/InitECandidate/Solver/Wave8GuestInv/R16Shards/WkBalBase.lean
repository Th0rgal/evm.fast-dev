import InitECandidate.Solver.Wave8GuestInv.ContractParts.C00Defs
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M08.wk_memcpy
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M08.wk_memzero
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.RlpMemcpyLemmas
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M12.wk_st_le64
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.WorldFrame
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.Exec
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_htab_get
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M19.htab_del_spec
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M25.nz_htab_set
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01AllocMpt
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.rt_lst_new
import InitECandidate.Solver.Wave8GuestInv.R10Shards.SoloHtabNew
import InitECandidate.Solver.Wave8GuestInv.R10Shards.SoloHtabSetFinal

/-! Shared zero-sorry BAL & WorldStep foundation for `R16eShards`, importing only fast
prebuilt modules (no `EntryDefs` / `C00`). All contract abbreviations are definitionally
`rfl`-equal to `ContractParts/C00`–`C03`. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Verbatim contract abbreviations (`rfl`-equal to `C00`–`C03`) -/

abbrev Resumes := @M13.Resumes
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
abbrev stdKeep : List (String × List Nat) := M13.stdKeep
abbrev M08IvlUnhit {F : Type} := @InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit F

def BalChangeArg : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ ((locN s "which" = 16 ∧ locN s "esz" = 40) ∨
    (locN s "which" = 24 ∧ locN s "esz" = 16) ∨ (locN s "which" = 32 ∧ locN s "esz" = 24))

def WorldStepIn (T : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat)
    (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) (gw : List String)
    (keep : List (String × List Nat))
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop :=
  fun s r post =>
    ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    GlobalsKept gw s post ∧ RecordsKept R keep s post ∧
    ∀ S Nd, WorldTypedWith s S Nd → (∀ t ∈ T s, t ∈ S) → IvlsDisj (R s) (worldTypedIvls s S Nd) →
      ∃ S' Nd', (∀ t ∈ S, t ∈ S') ∧ WorldTypedWith post S' Nd' ∧
        OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd') ∧
        FrameOutside s post (worldOwned s S Nd ++ R s ++ [freeGap s]) (heapFree s) ∧
        Q s r post S' Nd'

def WorldReturnsIn (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (T : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat)
    (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) (gw : List String)
    (keep : List (String × List Nat))
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop) (fname : MlS) : Prop :=
  FunSpec P (fun s r post => (∃ v, r = some (.returned v)) → WorldStepIn T R gw keep Q s r post) fname

def RetNodeDb : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S' Nd' => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    HtabWF post w.toNat ∧ hdr post w.toNat 0 = 32 ∧
    (∀ i ∈ htabFootprint post w.toNat, Inside i (globN s "heap_ptr") (globN post "heap_ptr")) ∧
    IvlsDisj (htabFootprint post w.toNat) (worldOwned post S' Nd')

def StateInitReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S Nd, WorldTypedWith s S Nd ∧
    (locN s "codedb" = 0 ∨
      (HtabWF s (locN s "codedb") ∧ hdr s (locN s "codedb") 0 = 32 ∧
       (∀ i ∈ htabFootprint s (locN s "codedb"), Inside i sourceBase (globN s "heap_ptr")) ∧
       IvlsDisj (htabFootprint s (locN s "codedb")) (worldOwned s S Nd)))

def RetStateInit : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun _ r post _ _ => ∀ v, r = some (.returned v) → globN post "journal_cap" ≠ 0

def bufferRegion {F : Type} (s : PanSemStateFiniteExact 64 F) (gn : String × Nat) : Ivl :=
  (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)

theorem worldTyped_iff_with {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) :
    WorldTyped s S ↔ ∃ Nd, WorldTypedWith s S Nd := by
  simp only [WorldTyped, TriesTyped, WorldTypedWith, M13.WorldTypedWith]
  exact ⟨fun ⟨h1, h2, h3, Nd, h4⟩ => ⟨Nd, h1, h2, h3, h4⟩,
         fun ⟨Nd, h1, h2, h3, h4⟩ => ⟨h1, h2, h3, Nd, h4⟩⟩

/-! ## 2. Basic interval, local-invariance, and `WorldStep` combinators -/

theorem not_resumes_error : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

theorem not_resumes_none : ¬ Resumes (none : Option (PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

theorem disj_flip {i j : Ivl} (h : Disj i j) : Disj j i := M13.Disj.symm h
theorem disj_zero_left (j : Ivl) : Disj (0, 0) j := Or.inl rfl
theorem disj_zero_right (i : Ivl) : Disj i (0, 0) := Or.inr (Or.inl rfl)

theorem inside_trans {i j : Ivl} {lo hi : Nat}
    (h1 : Inside i j.1 (j.1 + j.2)) (h2 : Inside j lo hi) : Inside i lo hi :=
  ⟨le_trans h2.1 h1.1, le_trans h1.2 h2.2⟩

theorem globN_eq_of_lookup {F : Type} {s post : PanSemStateFiniteExact 64 F} {name : String}
    (h : s.globals.lookup (ofString name) = post.globals.lookup (ofString name)) :
    globN post name = globN s name := by
  simp only [globN, ← h]

theorem freeChain_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k nodes : Nat) :
    ∀ (Fr : List Nat) (head : Nat),
      FreeChain { s with locals := locals, clock := k } nodes head Fr ↔ FreeChain s nodes head Fr
  | [], _ => Iff.rfl
  | _ :: rest, _ => by
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
    have hwti_eq : M13.worldTypedIvls s' S Nd = M13.worldTypedIvls s S Nd := by rw [hs']; rfl
    have hwo_eq : M13.worldOwned s' S Nd = M13.worldOwned s S Nd := by rw [hs']; rfl
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
  · intro o ho2
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

/-! ## 3. `htab_get` lookup, non-null guard, read-only frame, and `htabValues` membership -/

theorem lookup_htab_find_leaf :
    originalRuntimeCode.lookup (ofString "htab_find_leaf") =
      some ([(ofString "t", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_htab_find_leaf, .one) :=
  lookup_of_guestAst_getElem 131 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_find_leaf) rfl

theorem lookup_htab_get :
    originalRuntimeCode.lookup (ofString "htab_get") =
      some ([(ofString "t", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_htab_get, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 132 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_get) rfl

theorem lookup_memeq :
    originalRuntimeCode.lookup (ofString "memeq") =
      some ([(ofString "a", .one), (ofString "b", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memeq, .one) :=
  lookup_of_guestAst_getElem 18 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memeq) rfl

theorem funLocFrame_htab_find_leaf : M13.FunLocFrame (ofString "htab_find_leaf") :=
  M13.funLocFrame_of_locOnlyW 131 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htab_find_leaf rfl rfl

theorem funLocFrame_memeq : M13.FunLocFrame (ofString "memeq") :=
  M13.funLocFrame_of_locOnlyW 18 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_memeq rfl rfl

theorem locFrame_htab_get {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) :
    M13.LocFrame s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_get)).2 :=
  InitECandidate.Solver.Wave8Contracts.M15.evaluate_readOnlyProg
    InitECandidate.Solver.Wave8Contracts.M15.htabGetCallees
    InitECandidate.Solver.Wave8Contracts.M15.htabGetCallees_good
    (sourceFnBody Guest.Software.guestFn_htab_get) rfl s hcode

def noCatchableRaise (good : MlS → Bool) : ProgHOL 64 → Bool
  | .dec _ _ _ b => noCatchableRaise good b
  | .seq a b => noCatchableRaise good a && noCatchableRaise good b
  | .ite _ a b => noCatchableRaise good a && noCatchableRaise good b
  | .while _ b => noCatchableRaise good b
  | .decCall _ _ f _ cont => good f && noCatchableRaise good cont
  | .call (some (_, none)) f _ => good f
  | .raise eid _ => eid == ofString "TrapErr"
  | .skip | .break | .continue | .annot _ _ | .return _
  | .assign _ _ _ | .store _ _ | .storeByte _ _ | .store32 _ _
  | .shMemStore _ _ _ => true
  | _ => false

private theorem lex_ncr {a1 a2 b1 b2 : Nat} (h : a1 < a2 ∨ a1 = a2 ∧ b1 < b2) :
    Prod.Lex (· < ·) (· < ·) (a1, b1) (a2, b2) := by
  rcases h with h | ⟨rfl, h⟩
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ h

theorem evaluate_noCatchableRaise {F : Type} (good : MlS → Bool)
    (hgood : ∀ f, good f = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      noCatchableRaise good body = true)
    (p : ProgHOL 64) (hp : noCatchableRaise good p = true)
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode) :
    ∀ eid v, eid ≠ ofString "TrapErr" → (evaluateHOLFiniteState s p).1 ≠ some (.exception eid v) := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; simp
  | «break» => rw [evaluateHOLFiniteState_break]; simp
  | «continue» => rw [evaluateHOLFiniteState_continue]; simp
  | annot _ _ => rw [evaluateHOLFiniteState_annot]; simp
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · simp
    · split <;> simp
  | assign _ _ _ =>
    rw [evaluateHOLFiniteState_assign]
    split
    · simp
    · split <;> simp
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | store32 _ _ =>
    rw [evaluateHOLFiniteState_store32]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | shMemStore _ _ _ =>
    rw [evaluateHOLFiniteState_shMemStore_total]; dsimp only
    split
    · unfold shMemStoreHOLExact
      split <;> split
      all_goals simp [ofExact, toExact]
      all_goals split <;> simp
    · simp
  | raise name _ =>
    have htrap : name = ofString "TrapErr" := by
      simpa [shape, noCatchableRaise, beq_iff_eq] using hp
    subst htrap
    intro eid v hne
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only
      split
      · simp [hne.symm]
      · simp
    · simp
  | dec name _ _ body =>
    have hb : noCatchableRaise good body = true := by simpa [shape, noCatchableRaise] using hp
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · simp
    · rename_i val _
      split
      · exact evaluate_noCatchableRaise good hgood body hb (setVarHOLFinite name val s) hcode
      · simp
  | seq a b =>
    have hab : noCatchableRaise good a = true ∧ noCatchableRaise good b = true := by
      simpa [shape, noCatchableRaise, Bool.and_eq_true] using hp
    have ih1 := evaluate_noCatchableRaise good hgood a hab.1 s hcode
    have rem := evaluateHOLFiniteState_clock_le s a
    have meta' := PanRunBounded.evaluateHOLFiniteState_metadata s a
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hr : evaluateHOLFiniteState s a with ⟨r1, mid⟩
    rw [hr] at ih1 rem meta'
    dsimp only at ih1 rem meta' ⊢
    cases r1 with
    | none =>
      have mclock : mid.clock ≤ s.clock := rem
      exact evaluate_noCatchableRaise good hgood b hab.2 mid (meta'.1.trans hcode)
    | some _ => exact ih1
  | ite _ yes no =>
    have hy : noCatchableRaise good yes = true ∧ noCatchableRaise good no = true := by
      simpa [shape, noCatchableRaise, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noCatchableRaise good hgood no hy.2 s hcode
      · exact evaluate_noCatchableRaise good hgood yes hy.1 s hcode
    · simp
  | «while» cond body =>
    have hb : noCatchableRaise good body = true := by simpa [shape, noCatchableRaise] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_noCatchableRaise good hgood body hb (decClockHOLFinite s) hcode
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have meta' := PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem meta'
          dsimp only at ih1 rem meta' ⊢
          have smaller : mid.clock < s.clock := by change mid.clock ≤ s.clock - 1 at rem; omega
          have mCode : mid.code = originalRuntimeCode := meta'.1.trans hcode
          cases r1 with
          | none =>
            exact evaluate_noCatchableRaise good hgood (.while cond body) (by simpa [noCatchableRaise] using hb) mid mCode
          | some r =>
            cases r with
            | «continue» =>
              exact evaluate_noCatchableRaise good hgood (.while cond body) (by simpa [noCatchableRaise] using hb) mid mCode
            | «break» => simp
            | _ => exact ih1
      · simp
    · simp
  | decCall name _ fn args cont =>
    have hc : good fn = true ∧ noCatchableRaise good cont = true := by
      simpa [shape, noCatchableRaise, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
    · simp
    · dsimp only
      rcases hl : lookupCodeHOLFinite s.code.lookup fn values with _ | ⟨body, callee, rs⟩
      · simp
      · dsimp only
        have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup fn values = some (body, callee, rs) := by rwa [← hcode]
        have bodyOk := hgood fn hc.1 values body callee rs hl'
        split
        · simp
        · have ih1 := evaluate_noCatchableRaise good hgood body bodyOk (callEntryStateHOLFinite s callee) hcode
          have meta' := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, st⟩
          rw [hrun] at ih1 meta' cl
          dsimp only at ih1 meta' cl ⊢
          change st.clock ≤ s.clock - 1 at cl
          have small : st.clock < s.clock := by omega
          have stCode : st.code = originalRuntimeCode := meta'.1.trans hcode
          cases res with
          | none => simp
          | some r =>
            cases r with
            | returned v =>
              dsimp only
              split
              · set resumed := setVarHOLFinite name v { st with locals := s.locals }
                have smallR : resumed.clock < s.clock := small
                have rCode : resumed.code = originalRuntimeCode := stCode
                exact evaluate_noCatchableRaise good hgood cont hc.2 resumed rCode
              · simp
            | «break» => simp
            | «continue» => simp
            | _ => exact ih1
  | call tail fn args =>
    cases tail with
    | none => simp [shape, noCatchableRaise] at hp
    | some th =>
      rcases th with ⟨dest, handler⟩
      cases handler with
      | some _ => simp [shape, noCatchableRaise] at hp
      | none =>
        have hf : good fn = true := by simpa [shape, noCatchableRaise] using hp
        rw [evaluateHOLFiniteState_call]
        rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
        · simp
        · dsimp only
          rcases hl : lookupCodeHOLFinite s.code.lookup fn values with _ | ⟨body, callee, rs⟩
          · simp
          · dsimp only
            have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup fn values = some (body, callee, rs) := by rwa [← hcode]
            have bodyOk := hgood fn hf values body callee rs hl'
            split
            · simp
            · have ih1 := evaluate_noCatchableRaise good hgood body bodyOk (callEntryStateHOLFinite s callee) hcode
              have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
              rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, st⟩
              rw [hrun] at ih1 cl
              dsimp only at ih1 cl ⊢
              change st.clock ≤ s.clock - 1 at cl
              have small : st.clock < s.clock := by omega
              cases res with
              | none => simp
              | some r =>
                cases r with
                | returned retVal =>
                  dsimp only
                  split
                  · cases dest with
                    | none => simp
                    | some kv =>
                      rcases kv with ⟨vk, vn⟩
                      dsimp only
                      by_cases hval : isValidValueHOLExact s.toExact vk vn retVal = true
                      · rw [if_pos hval]; simp
                      · rw [if_neg hval]; simp
                  · simp
                | «break» => simp
                | «continue» => simp
                | _ => exact ih1
  | _ => simp [shape, noCatchableRaise] at hp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply lex_ncr
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite,
      ProgHOL.seq.sizeOf_spec, ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec,
      ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec, ProgHOL.call.sizeOf_spec, true_and]
    first
      | exact Or.inl smallR
      | exact Or.inl smaller
      | exact Or.inl small
      | omega
      | (rcases Nat.lt_or_eq_of_le mclock with h | h
         · exact Or.inl h
         · exact Or.inr ⟨h, by simp +arith⟩)
      | exact Or.inr ⟨rfl, by simp +arith⟩

theorem htab_get_no_catchable_exn {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (e : MlS) (v : ValueHOL 64)
    (hne : e ≠ ofString "TrapErr") :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_get)).1 ≠
      some (.exception e v) := by
  refine evaluate_noCatchableRaise
    InitECandidate.Solver.Wave8Contracts.M15.htabGetCallees
    ?_ (sourceFnBody Guest.Software.guestFn_htab_get) rfl s hcode e v hne
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ :=
    InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
  simp only [InitECandidate.Solver.Wave8Contracts.M15.htabGetCallees,
    Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with rfl | rfl
  · rw [lookup_htab_find_leaf] at hinst
    have hbody := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
    rw [← hbody]; rfl
  · rw [lookup_memeq] at hinst
    have hbody := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
    rw [← hbody]; rfl

theorem htab_get_t_nonzero {F : Type}
    (s : PanSemStateFiniteExact 64 F) (tw kw : BitVec 64)
    (hG : GuestInv s)
    (ht : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hk : s.locals.lookup (ofString "key") = some (.val (.word kw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_get)).1 = some (.returned v)) :
    tw ≠ 0 := by
  rintro rfl
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_htab_get,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map] at hret
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "t"), .var .local (ofString "key")] =
      some [.val (.word 0), .val (.word kw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ht, hk]
  have hlook := pan_two_word_lookup s.code.lookup (ofString "htab_find_leaf")
    (ofString "t") (ofString "key") (sourceFnBody Guest.Software.guestFn_htab_find_leaf) 0 kw
    (by decide) (by rw [hG.code]; exact lookup_htab_find_leaf)
  rw [hargs] at hret; dsimp only at hret; rw [hlook] at hret; dsimp only at hret
  split at hret
  · simp at hret
  · let cmap := (HolFiniteMapExact.empty.update (ofString "t", ValueHOL.val (.word 0))).update
      (ofString "key", ValueHOL.val (.word kw))
    let ent := callEntryStateHOLFinite s cmap
    have hent_t : ent.locals.lookup (ofString "t") = some (.val (.word 0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "key" ≠ ofString "t" by decide]
    have hnot0 : ¬ ent.memaddrs 0#64 := by
      change ¬ s.memaddrs 0#64
      rw [hG.memaddrs, M13.ordinaryDomain_iff]
      simp
    have hfl_err : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_htab_find_leaf)).1 =
        some .error := by
      dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_htab_find_leaf,
        InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
      rw [evaluateHOLFiniteState_dec_total]
      have hev0 : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
          (.panop .mul [.load .one (.op .add [.var .local (ofString "t"), .const 0#64]), .const 8#64]) = none := by
        simp [evalHOLExact, evalListHOLExact, hent_t, valueIsWord, valueWord, wordOpHOL, wordOp,
          memLoadHOLExact, hnot0]
      dsimp only; rw [hev0]
    rcases hfl : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_htab_find_leaf) with ⟨rfl_res, s_fl⟩
    have hfl_eq : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_htab_find_leaf) = (rfl_res, s_fl) := hfl
    rw [hfl] at hfl_err; rw [hfl_eq] at hret
    dsimp only at hfl_err
    subst hfl_err
    simp at hret

theorem htab_get_ret_in_values {F : Type}
    (s : PanSemStateFiniteExact 64 F) (tw kw : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (ht : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hk : s.locals.lookup (ofString "key") = some (.val (.word kw)))
    (hW : HtabWF s tw.toNat)
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_get)).1 = some (.returned v)) :
    ∃ f0 f1 : BitVec 64, v = .rStruct [.val (.word f0), .val (.word f1)] ∧
      (f0 ≠ 0 → f1.toNat ∈ htabValues s tw.toNat) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_htab_get,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map] at hret
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "t"), .var .local (ofString "key")] =
      some [.val (.word tw), .val (.word kw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ht, hk]
  have hlook := pan_two_word_lookup s.code.lookup (ofString "htab_find_leaf")
    (ofString "t") (ofString "key") (sourceFnBody Guest.Software.guestFn_htab_find_leaf) tw kw
    (by decide) (by rw [hcode]; exact lookup_htab_find_leaf)
  rw [hargs] at hret; dsimp only at hret; rw [hlook] at hret; dsimp only at hret
  by_cases hcz : s.clock = 0
  · simp [hcz] at hret
  · rw [if_neg hcz] at hret
    let cmap := (HolFiniteMapExact.empty.update (ofString "t", ValueHOL.val (.word tw))).update
      (ofString "key", ValueHOL.val (.word kw))
    let ent := callEntryStateHOLFinite s cmap
    have hent_t : ent.locals.lookup (ofString "t") = some (.val (.word tw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "key" ≠ ofString "t" by decide]
    have hent_W : HtabWF ent tw.toNat := by
      simpa [ent, callEntryStateHOLFinite, htabWF_with_locals] using hW
    rcases hfl : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_htab_find_leaf) with ⟨rfl_res, s_fl⟩
    have hfl_eq : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_htab_find_leaf) = (rfl_res, s_fl) := hfl
    rw [hfl_eq] at hret
    rcases rfl_res with _ | rfl_r
    · simp at hret
    · cases rfl_r with
      | returned v_fl =>
        obtain ⟨lw, rfl, hlf_fl, hfl_spec⟩ :=
          SoloHtabSet.find_leaf_spec_wf ent tw hent_t hent_W v_fl (by rw [hfl])
        have hfl2 : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_htab_find_leaf)).2 = s_fl :=
          congrArg Prod.snd hfl
        have hfl_lf' : SoloHtabSet.LocFrame s s_fl := by
          rw [hfl2] at hlf_fl
          unfold SoloHtabSet.LocFrame at hlf_fl ⊢
          rw [hlf_fl]; rfl
        dsimp only at hret
        have hsh1 : (shapeEqHOL (shapeOfHOLExact (.val (.word lw))) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word lw))) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hsh1] at hret; dsimp only at hret
        let s1 := setVarHOLFinite (ofString "leaf") (.val (.word lw)) { s_fl with locals := s.locals }
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
        have hs1_lw : s1.locals.lookup (ofString "leaf") = some (.val (.word lw)) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hev_lw0 : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
            (.cmp .equal (.var .local (ofString "leaf")) (.const 0#64)) =
            some (.val (.word (if lw = 0 then 1 else 0))) := by
          simp [evalHOLExact, hs1_lw, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [hev_lw0] at hret; dsimp only at hret
        by_cases hlw0 : lw = 0
        · rw [if_pos hlw0, if_neg (by decide : ¬ ((1 : BitVec 64) = 0)), evaluateHOLFiniteState_return] at hret
          simp [evalHOLExact, evalListHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hret
          exact ⟨0, 0, hret.symm, fun h => absurd rfl h⟩
        · rw [if_neg hlw0, if_pos rfl, evaluateHOLFiniteState_skip] at hret
          dsimp only at hret
          rcases hfl_spec with ⟨h0, _⟩ | ⟨_, _, hmemL⟩
          · exact absurd h0 hlw0
          · have ⟨hB, L0, I0, Fr0, hT0⟩ := (SoloHtabSet.htabWF_iff ent tw.toNat).mp hent_W
            have hlw_L0 : lw.toNat ∈ L0 := hmemL L0 I0 Fr0 hT0
            rw [evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
            split at hret
            · simp at hret
            · rename_i v_kl _
              split at hret
              · rw [evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
                split at hret
                · simp at hret
                · rename_i v_st _
                  split at hret
                  · rw [evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
                    split at hret
                    · simp at hret
                    · rename_i v_ks _
                      split at hret
                      · rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
                        split at hret
                        · simp at hret
                        · rename_i vs_m _
                          split at hret
                          · simp at hret
                          · rename_i b_m c_m rs_m hl_m
                            split at hret
                            · simp at hret
                            · have hs_m_code : s_fl.code = originalRuntimeCode := by
                                have h1 : s_fl.code = s.code := by rw [hfl_lf']
                                exact h1.trans hcode
                              have hsame_m := lookupCodeHOLFinite_installed_body s_fl.code.lookup
                                (ofString "memeq") _ (sourceFnBody Guest.Software.guestFn_memeq) b_m
                                .one rs_m vs_m c_m (by rw [hs_m_code]; exact lookup_memeq) hl_m
                              subst hsame_m
                              have hlf_m : InitECandidate.Solver.Wave8Contracts.M15.LocFrame
                                  (callEntryStateHOLFinite
                                    (setVarHOLFinite (ofString "keys") v_ks
                                      (setVarHOLFinite (ofString "stride") v_st
                                        (setVarHOLFinite (ofString "klen") v_kl s1))) c_m)
                                  (evaluateHOLFiniteState
                                    (callEntryStateHOLFinite
                                      (setVarHOLFinite (ofString "keys") v_ks
                                        (setVarHOLFinite (ofString "stride") v_st
                                          (setVarHOLFinite (ofString "klen") v_kl s1))) c_m)
                                    (sourceFnBody Guest.Software.guestFn_memeq)).2 :=
                                InitECandidate.Solver.Wave8Contracts.M15.evaluate_readOnlyProg
                                  InitECandidate.Solver.Wave8Contracts.M15.htabGetCallees
                                  InitECandidate.Solver.Wave8Contracts.M15.htabGetCallees_good
                                  (sourceFnBody Guest.Software.guestFn_memeq) rfl _ hs_m_code
                              dsimp only at hret
                              rcases hm_run : evaluateHOLFiniteState
                                  (callEntryStateHOLFinite
                                    (setVarHOLFinite (ofString "keys") v_ks
                                      (setVarHOLFinite (ofString "stride") v_st
                                        (setVarHOLFinite (ofString "klen") v_kl s1))) c_m)
                                  (sourceFnBody Guest.Software.guestFn_memeq) with ⟨rm, sm⟩
                              have hm_snd := congrArg Prod.snd hm_run
                              rw [hm_snd] at hlf_m
                              dsimp only [s1] at hm_run
                              rw [hm_run] at hret
                              dsimp only at hret
                              rcases rm with _ | rm
                              · simp at hret
                              · cases rm with
                                | returned vm =>
                                  dsimp only at hret
                                  split at hret
                                  · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
                                    split at hret
                                    · split at hret
                                      · rw [evaluateHOLFiniteState_skip] at hret; dsimp only at hret
                                        rw [evaluateHOLFiniteState_return] at hret
                                        split at hret
                                        · simp at hret
                                        · rename_i retV hretV
                                          split at hret
                                          · simp only [Prod.mk.injEq, Option.some.injEq,
                                              PanSemResultExact.returned.injEq] at hret
                                            subst hret
                                            let s_eq := setVarHOLFinite (ofString "eq") vm
                                              { s with clock := sm.clock,
                                                       locals := (setVarHOLFinite (ofString "keys") v_ks
                                                         (setVarHOLFinite (ofString "stride") v_st
                                                           (setVarHOLFinite (ofString "klen") v_kl s1))).locals }
                                            have hs_eq_orig : setVarHOLFinite (ofString "eq") vm
                                                { sm with locals := (setVarHOLFinite (ofString "keys") v_ks
                                                    (setVarHOLFinite (ofString "stride") v_st
                                                      (setVarHOLFinite (ofString "klen") v_kl
                                                        (setVarHOLFinite (ofString "leaf") (.val (.word lw))
                                                          { s_fl with locals := s.locals })))).locals } = s_eq := by
                                              dsimp only [s_eq]
                                              congr 1
                                              unfold InitECandidate.Solver.Wave8Contracts.M15.LocFrame at hlf_m
                                              dsimp only at hlf_m
                                              unfold SoloHtabSet.LocFrame at hfl_lf'
                                              rw [hlf_m]
                                              dsimp only [s1, callEntryStateHOLFinite, setVarHOLFinite]
                                              rw [hfl_lf']
                                            rw [hs_eq_orig] at hretV
                                            have ht_sm : s_eq.locals.lookup (ofString "t") =
                                                some (.val (.word tw)) := by
                                              simp [s_eq, setVarHOLFinite, s1, HolFiniteMapExact.lookup_update, FUPDATE, ht,
                                                show ofString "eq" ≠ ofString "t" by decide,
                                                show ofString "keys" ≠ ofString "t" by decide,
                                                show ofString "stride" ≠ ofString "t" by decide,
                                                show ofString "klen" ≠ ofString "t" by decide,
                                                show ofString "leaf" ≠ ofString "t" by decide]
                                            have hleaf_sm : s_eq.locals.lookup (ofString "leaf") =
                                                some (.val (.word lw)) := by
                                              simp [s_eq, setVarHOLFinite, s1, HolFiniteMapExact.lookup_update, FUPDATE,
                                                show ofString "eq" ≠ ofString "leaf" by decide,
                                                show ofString "keys" ≠ ofString "leaf" by decide,
                                                show ofString "stride" ≠ ofString "leaf" by decide,
                                                show ofString "klen" ≠ ofString "leaf" by decide]
                                            have hma_eq : s_eq.memaddrs = s.memaddrs := rfl
                                            have hmem_eq : s_eq.memory = s.memory := rfl
                                            simp only [evalHOLExact, evalListHOLExact, ht_sm, hleaf_sm,
                                              valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
                                              memLoadHOLExact, isWfShapeExactHOL, List.all, List.map, Option.map,
                                              Bool.and_self, List.foldr, BitVec.add_zero, ↓reduceIte, hmem_eq] at hretV
                                            rcases hm40 : s.memory (tw + (40#64 + 0)) with ⟨ndw⟩
                                            by_cases hd40 : s_eq.memaddrs (tw + (40#64 + 0))
                                            · rw [if_pos hd40, hm40] at hretV
                                              simp only [List.all, List.map, Option.map,
                                                valueIsWord, valueWord, Bool.and_self, List.foldr, ↓reduceIte] at hretV
                                              rcases hm_val : s.memory (ndw + (lw * 32#64 + (8#64 + 0))) with ⟨valw⟩
                                              by_cases hd_val : s_eq.memaddrs (ndw + (lw * 32#64 + (8#64 + 0)))
                                              · rw [if_pos hd_val, hm_val] at hretV
                                                simp only [Option.some.injEq] at hretV
                                                refine ⟨1, valw, hretV.symm, fun _ => ?_⟩
                                                obtain ⟨idx, hidx, hLidx⟩ := List.getElem_of_mem hlw_L0
                                                have hcnt_eq : L0.length = hdr s tw.toNat 3 := hT0.1
                                                have hord_eq : memW s (hdr s tw.toNat 6 + 8 * idx) = lw.toNat := by
                                                  rw [← hLidx]; exact (hT0.2.2.2.2.1 idx hidx).1
                                                unfold htabValues
                                                refine List.mem_map.2 ⟨idx, List.mem_range.2 (by omega), ?_⟩
                                                rw [hord_eq]
                                                have hhdr5 : hdr s tw.toNat 5 = ndw.toNat := by
                                                  unfold hdr memW
                                                  have htw8 : (tw + (40#64 + 0) : BitVec 64) = BitVec.ofNat 64 (tw.toNat + 40) := by
                                                    have htb := (hB.1 (tw.toNat, 88) (by simp [htabFootprint])).1
                                                    have h264 : heapEnd ≤ 2 ^ 64 := by decide
                                                    apply BitVec.eq_of_toNat_eq
                                                    simp only [BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat]
                                                    rfl
                                                  rw [← htw8, hm40]
                                                rw [hhdr5]
                                                unfold nodeF memW
                                                have hlw_lt : lw.toNat ≤ hdr s tw.toNat 10 := by
                                                  have h1 : lw.toNat < hdr ent tw.toNat 8 :=
                                                    ((hT0.2.2.1 lw.toNat).1 (List.mem_append_left _ (List.mem_append_left _ hlw_L0))).2
                                                  have h2 : hdr ent tw.toNat 8 ≤ hdr ent tw.toNat 10 + 1 := hB.2.2.2.2.2.2.2
                                                  have he1 : hdr ent tw.toNat 8 = hdr s tw.toNat 8 := rfl
                                                  have he2 : hdr ent tw.toNat 10 = hdr s tw.toNat 10 := rfl
                                                  omega
                                                have hfp2 : (hdr s tw.toNat 5, (hdr s tw.toNat 10 + 1) * 32) ∈ htabFootprint s tw.toNat := by
                                                  simp [htabFootprint]
                                                have hnd_bnd : ndw.toNat + (hdr s tw.toNat 10 + 1) * 32 ≤ heapEnd := by
                                                  have h := (hB.1 _ hfp2).1.2
                                                  change hdr ent tw.toNat 5 + (hdr ent tw.toNat 10 + 1) * 32 ≤ heapEnd at h
                                                  have he5 : hdr ent tw.toNat 5 = hdr s tw.toNat 5 := rfl
                                                  have he10 : hdr ent tw.toNat 10 = hdr s tw.toNat 10 := rfl
                                                  rw [he5, he10, hhdr5] at h
                                                  exact h
                                                have h264 : heapEnd ≤ 2 ^ 64 := by decide
                                                have had_eq : BitVec.ofNat 64 (ndw.toNat + 32 * lw.toNat + 8) =
                                                    ndw + (lw * 32#64 + (8#64 + 0)) := by
                                                  apply BitVec.eq_of_toNat_eq
                                                  have hfit : ndw.toNat + 32 * lw.toNat + 8 < 2 ^ 64 := by omega
                                                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
                                                  have hm1 : (lw * 32#64).toNat = 32 * lw.toNat := by
                                                    rw [BitVec.toNat_mul]
                                                    change (lw.toNat * 32) % 2 ^ 64 = _
                                                    rw [Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
                                                  have hm2 : (lw * 32#64 + (8#64 + 0)).toNat = 32 * lw.toNat + 8 := by
                                                    change (lw * 32#64 + 8#64).toNat = _
                                                    rw [BitVec.toNat_add, hm1]
                                                    change (32 * lw.toNat + 8) % 2 ^ 64 = _
                                                    exact Nat.mod_eq_of_lt (by omega)
                                                  rw [BitVec.toNat_add, hm2, Nat.mod_eq_of_lt (by omega)]
                                                  omega
                                                rw [had_eq, hm_val]
                                              · rw [if_neg hd_val] at hretV; simp at hretV
                                            · rw [if_neg hd40] at hretV; simp at hretV
                                          · simp at hret
                                      · rw [evaluateHOLFiniteState_return] at hret
                                        simp [evalHOLExact, evalListHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hret
                                        exact ⟨0, 0, hret.symm, fun h => absurd rfl h⟩
                                    · simp at hret
                                  · simp at hret
                                | _ => simp at hret
                      · simp at hret
                  · simp at hret
              · simp at hret
      | _ => simp at hret

/-- Unified `decCall x (.comb [.one, .one]) "htab_get" [tExp, keyExp] cont` stepper:
when the `decCall` does not time out and `Resumes`, both arguments evaluated to words `tw, kw`,
`tw ≠ 0`, `htab_get` returned `<f0, f1>` without changing memory or globals, and if `HtabWF s tw.toNat`,
`f0 ≠ 0 → f1.toNat ∈ htabValues s tw.toNat`. -/
theorem decCall_htab_get_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (x : MlS) (tExp keyExp : ExpHOL 64) (cont : ProgHOL 64)
    (hG : GuestInv s)
    (hnt : (evaluateHOLFiniteState s
      (.decCall x (.comb [.one, .one]) (ofString "htab_get") [tExp, keyExp] cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall x (.comb [.one, .one]) (ofString "htab_get") [tExp, keyExp] cont)).1) :
    ∃ (tw kw f0 f1 : BitVec 64) (ck : Nat),
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) tExp =
        some (.val (.word tw)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) keyExp =
        some (.val (.word kw)) ∧
      tw ≠ 0 ∧
      (∀ (hW : HtabWF s tw.toNat), f0 ≠ 0 → f1.toNat ∈ htabValues s tw.toNat) ∧
      let s_cont := setVarHOLFinite x (.rStruct [.val (.word f0), .val (.word f1)])
        { s with clock := ck }
      (evaluateHOLFiniteState s_cont cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState s_cont cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x (.comb [.one, .one]) (ofString "htab_get") [tExp, keyExp] cont)).1 =
        (evaluateHOLFiniteState s_cont cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x (.comb [.one, .one]) (ofString "htab_get") [tExp, keyExp] cont)).2 =
        { (evaluateHOLFiniteState s_cont cont).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState s_cont cont).2.locals (x, s.locals.lookup x) } := by
  dsimp only
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [tExp, keyExp] with _ | vals
  · rw [hargs] at hres; exact absurd hres not_resumes_error
  · rw [hargs] at hnt hres; dsimp only at hnt hres
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_get") vals with _ | ⟨body, callee, rs⟩
    · rw [hl] at hres; exact absurd hres not_resumes_error
    · rw [hl] at hnt hres; dsimp only at hnt hres
      by_cases hcz : s.clock = 0
      · rw [if_pos hcz] at hnt; exact absurd rfl hnt
      · rw [if_neg hcz] at hnt hres
        have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "htab_get") vals =
            some (body, callee, rs) := by rwa [← hG.code]
        have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "htab_get") vals body callee rs hl'
        simp only [lookupCodeHOLExact, lookup_htab_get] at hx
        rcases vals with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
        · simp at hx
        · simp at hx
        · rcases v1 with ⟨⟨tw⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨kw⟩⟩ | _ | _ <;>
            simp [shapeOfHOLExact, shapeEqHOL] at hx
          obtain ⟨rfl, hc_eq, rfl⟩ := hx
          have hev_pair : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
              [tExp, keyExp] = some [.val (.word tw), .val (.word kw)] := hargs
          have hev_t : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) tExp =
              some (.val (.word tw)) := by
            rcases he1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) tExp with _ | x1
            · simp [evalListHOLExact, he1] at hev_pair
            · rcases he2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) keyExp with _ | x2
              · simp [evalListHOLExact, he1, he2] at hev_pair
              · simp [evalListHOLExact, he1, he2] at hev_pair
                exact congrArg some hev_pair.1
          have hev_k : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) keyExp =
              some (.val (.word kw)) := by
            rcases he2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) keyExp with _ | x2
            · simp [evalListHOLExact, hev_t, he2] at hev_pair
            · simp [evalListHOLExact, hev_t, he2] at hev_pair
              exact congrArg some hev_pair
          have hc_t : (callEntryStateHOLFinite s callee).locals.lookup (ofString "t") =
              some (.val (.word tw)) := by
            simp [callEntryStateHOLFinite, ← hc_eq, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "key" ≠ ofString "t" by decide]
          have hc_k : (callEntryStateHOLFinite s callee).locals.lookup (ofString "key") =
              some (.val (.word kw)) := by
            simp [callEntryStateHOLFinite, ← hc_eq, HolFiniteMapExact.lookup_update, FUPDATE]
          have hlf := locFrame_htab_get (callEntryStateHOLFinite s callee) hG.code
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
              (sourceFnBody Guest.Software.guestFn_htab_get) with ⟨rg, sg⟩
          have hrun2 : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
              (sourceFnBody Guest.Software.guestFn_htab_get)).2 = sg := congrArg Prod.snd hrun
          rw [hrun] at hnt hres; rw [hrun2] at hlf
          cases rg with
          | none => exact absurd hres not_resumes_error
          | some rg' =>
            cases rg' with
            | timeOut => exact absurd rfl hnt
            | exception e ev =>
              exfalso
              rcases hres with ⟨_, hh⟩ | ⟨e', ev', hh, hne⟩
              · simp at hh
              · dsimp only at hh
                injection hh with hh'; injection hh' with he1 he2
                subst he1 he2
                exact htab_get_no_catchable_exn (callEntryStateHOLFinite s callee) hG.code e ev hne
                  (congrArg Prod.fst hrun)
            | returned vg =>
              dsimp only at hnt hres
              split at hnt
              · rename_i hsh
                rw [if_pos hsh] at hres
                have htw_nz : tw ≠ 0 :=
                  htab_get_t_nonzero (callEntryStateHOLFinite s callee) tw kw
                    (guestInv_callEntry s callee hG) hc_t hc_k vg (congrArg Prod.fst hrun)
                have hvg_shape : ∃ f0 f1 : BitVec 64, vg = .rStruct [.val (.word f0), .val (.word f1)] := by
                  rcases vg with _ | vs_g | _
                  · simp [shapeOfHOLExact, shapeEqHOL] at hsh
                  · rcases vs_g with _ | ⟨x0, _ | ⟨x1, _ | _⟩⟩
                    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
                    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
                    · rcases x0 with ⟨⟨f0⟩⟩ | _ | _ <;> rcases x1 with ⟨⟨f1⟩⟩ | _ | _ <;>
                        simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
                      exact ⟨f0, f1, rfl⟩
                    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
                  · simp [shapeOfHOLExact, shapeEqHOL] at hsh
                obtain ⟨f0, f1, rfl⟩ := hvg_shape
                have hsg_eq : { sg with locals := s.locals } = { s with clock := sg.clock } := by
                  unfold M13.LocFrame at hlf
                  rw [hlf]; rfl
                rw [hsg_eq] at hnt hres
                let s_cont := setVarHOLFinite x (.rStruct [.val (.word f0), .val (.word f1)]) { s with clock := sg.clock }
                let co := evaluateHOLFiniteState s_cont cont
                have heval_eq : evaluateHOLFiniteState s
                    (.decCall x (.comb [.one, .one]) (ofString "htab_get") [tExp, keyExp] cont) =
                    (co.1, { co.2 with locals := HolFiniteMapExact.resVarEq co.2.locals (x, s.locals.lookup x) }) := by
                  rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs]
                  dsimp only
                  rw [hl]; dsimp only
                  rw [if_neg hcz, hrun]; dsimp only
                  rw [if_pos hsh, hsg_eq]
                refine ⟨tw, kw, f0, f1, sg.clock, hev_t, hev_k, htw_nz, fun hW hf0 => ?_,
                  by intro hto; rw [hto] at hnt; exact hnt rfl,
                  hres, by rw [heval_eq], by rw [heval_eq]⟩
                have hent_W : HtabWF (callEntryStateHOLFinite s callee) tw.toNat :=
                  (htabWF_with_locals s callee (s.clock - 1) tw.toNat).2 hW
                obtain ⟨f0', f1', hveq, hin_val⟩ :=
                  htab_get_ret_in_values (callEntryStateHOLFinite s callee) tw kw hG.code hc_t hc_k hent_W
                    (.rStruct [.val (.word f0), .val (.word f1)]) (congrArg Prod.fst hrun)
                simp only [ValueHOL.rStruct.injEq, List.cons.injEq, ValueHOL.val.injEq,
                  HolWordLab.word.injEq, and_true] at hveq
                obtain ⟨rfl, rfl⟩ := hveq
                exact hin_val hf0
              · rename_i hsh
                rw [if_neg hsh] at hres
                exact absurd hres not_resumes_error
            | «break» | «continue» | error =>
              exact absurd hres not_resumes_error
            | finalFfi _ =>
              exfalso
              rcases hres with ⟨_, hh⟩ | ⟨_, _, hh, _⟩ <;> simp at hh
        · simp at hx

end InitECandidate.Solver.Wave8GuestInv.R16Shards
