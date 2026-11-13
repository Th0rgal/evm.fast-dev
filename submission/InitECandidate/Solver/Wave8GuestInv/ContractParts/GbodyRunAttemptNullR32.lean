import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptR32

/-! Wave 8 R32: `run_attempt` at a null-tolerant guard.

`R16Shards.TopGbodyWk.gbody_run_attempt_strong_of` proves the `run_attempt`
bound at `InputReadyStrong`, which asks every `runAttemptCells` cell to be
`Inside` the heap window. The empty-list encoding `(0, 0)` is never `Inside`
(`sourceBase > 0`), so the three null-list sub-cases of
`GbodyRunAttemptR32Empty` (`TxNullCase`, `WitNullCase`, `AccNullCase`) fall
outside that proof.

This module replays the whole strong proof at the guard `InputReadyNull Z`:
every run-attempt cell is either the null pair `(0, 0)` or `Inside`. The proof
uses `Inside` of the four list cells only to carry them across world steps
(`heap_ivl_survives_step`: still `Inside`, disjoint from the grown world, and
unhit); all three facts are trivial for the null pair, since a zero-length
interval is disjoint from everything and contains no cell. The three header
cells `(si, 96)`, `(pl, 136)`, `(rq, 80)` have nonzero sizes, so they are
never null and the loads through them are unchanged.

The parameter `Z : Prop` says whether the *transaction* cell may be null:

* `Z := False`: the tx cell is `Inside`, the witness / access-list / vh cells
  may be null. Then `InputReadyZ False ↔ InputReady` and
  `InputReadyNwdZ False ↔ InputReadyNwd`, so the `payload_header` leaves are
  the original ones.
* `Z := True`: every list cell may be null; `InputReadyNull True` holds in
  every `GbodyRunAttemptR32.InputReadyR32` state
  (`GbodyRunAttemptNullR32Close.inputReadyNull_true_of_r32`).

What the replay cannot do is reuse the callee leaves whose own guard asks
`Inside` of a cell that is now allowed to be null. Those are restated at the
relaxed guard (each relaxed guard is implied by the original one, so each
restated leaf implies the original leaf):

* `hexec` — `execute_block`, at `BlockReadyExecAttemptNull Z` (was
  `BlockReadyExecAttemptStrong`, which contains `InputReadyStrong`),
* `hph`, `wph` — `payload_header`, at `InputReadyNwdZ Z` / `InputReadyZ Z`
  (the originals when `Z := False`).

All other leaf premises of `gbody_run_attempt_strong_of` are taken verbatim. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNullR32

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21
open InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

variable {Z : Prop}

/-! ### Null cells -/

/-- The null pair contains no cell, so it is unhit by every step. -/
theorem ivlUnhit_null {F : Type} {s post : PanSemStateFiniteExact 64 F} {b : Ivl}
    (h : b.1 = 0 ∧ b.2 = 0) : R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post b := by
  obtain ⟨b1, b2⟩ := b
  dsimp only at h
  obtain ⟨rfl, rfl⟩ := h
  exact fun a _ hhit => absurd hhit (R10Shards.Fast_GbodyC17ToC21.not_cellHits_zero _)

/-- `heap_ivl_survives_step` for a cell that is the null pair or `Inside`. -/
theorem nullOrInside_survives_step {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {old new R : List Ivl}
    (hog : OwnedGrows s post old new)
    (hfr : FrameOutside s post (old ++ R ++ [freeGap s]) (heapFree s))
    (hold_z : ∀ j ∈ old, j.2 = 0 → j.1 % 8 = 0)
    (hR_z : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    {b : Ivl} (hb1 : b.1 % 8 = 0) (hb2 : b.2 % 8 = 0)
    (hb_in : (b.1 = 0 ∧ b.2 = 0) ∨ Inside b sourceBase (globN s "heap_ptr"))
    (hb_old : ∀ j ∈ old, Disj b j)
    (hb_R : ∀ j ∈ R, Disj b j) :
    ((b.1 = 0 ∧ b.2 = 0) ∨ Inside b sourceBase (globN post "heap_ptr")) ∧
    (∀ o ∈ new, Disj b o) ∧
    R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post b := by
  rcases hb_in with hz | hb_in
  · exact ⟨Or.inl hz, fun _ _ => Or.inl hz.2, ivlUnhit_null hz⟩
  · obtain ⟨h1, h2, h3⟩ := R10Shards.Fast_GbodyC17ToC21.heap_ivl_survives_step
      hAs hhp hog hfr hold_z hR_z hb1 hb2 hb_in hb_old hb_R
    exact ⟨Or.inr h1, h2, h3⟩

/-- A cell of nonzero size is not the null pair. -/
theorem inside_of_nullOrInside {i : Ivl} {lo hi : Nat} (hne : i.2 ≠ 0)
    (h : (i.1 = 0 ∧ i.2 = 0) ∨ Inside i lo hi) : Inside i lo hi :=
  h.resolve_left (fun hz => hne hz.2)

/-! ### The `Z`-relaxed `InputAt` layer

`InputAtWith` / `InputAt` / `InputReady` / `InputReadyNwd` / `BlockReadyStrong`
with the `Inside` requirement on the `inputCells` relaxed to "null pair (only
if `Z`) or `Inside`". Only the transaction cell can be null: the other three
`inputCells` have nonzero sizes. -/

def InputAtWithZ (Z : Prop) {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) (si : Nat) : Prop :=
  ArenaReady s ∧ WorldTypedWith s S Nd ∧
    (∀ i ∈ inputCells s si,
      ((Z ∧ i.1 = 0 ∧ i.2 = 0) ∨ Inside i sourceBase (globN s "heap_ptr")) ∧ WordsOK s i) ∧
    IvlsDisj (inputCells s si) (worldOwned s S Nd) ∧
    memW s (memW s si + 40) < 2 ^ 63 ∧
    PayloadAt s (memW s si) ∧ RequestsAt s (memW s (si + 32))

def InputAtZ (Z : Prop) {F : Type} (s : PanSemStateFiniteExact 64 F) (si : Nat) : Prop :=
  ArenaReady s ∧ ∃ S Nd, WorldTypedWith s S Nd ∧
    (∀ i ∈ inputCells s si,
      ((Z ∧ i.1 = 0 ∧ i.2 = 0) ∨ Inside i sourceBase (globN s "heap_ptr")) ∧ WordsOK s i) ∧
    IvlsDisj (inputCells s si) (worldOwned s S Nd) ∧
    memW s (memW s si + 40) < 2 ^ 63 ∧
    PayloadAt s (memW s si) ∧ RequestsAt s (memW s (si + 32))

def InputReadyZ (Z : Prop) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => InputAtZ Z s (locN s "si")

def InputAtNwdZ (Z : Prop) {F : Type} (s : PanSemStateFiniteExact 64 F) (si : Nat) : Prop :=
  InputAtZ Z s si ∧ memW s (si + 16) < 2 ^ 32 ∧ memW s (memW s si + 56) < 2 ^ 32

def InputReadyNwdZ (Z : Prop) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => InputAtNwdZ Z s (locN s "si")

def BlockReadyStrongZ (Z : Prop) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => BlockReady s ∧ InputReadyZ Z s ∧ HeaderAt s (locN s "hdr")

theorem inputAtZ_iff_with {F : Type} (s : PanSemStateFiniteExact 64 F) (si : Nat) :
    InputAtZ Z s si ↔ ∃ S Nd, InputAtWithZ Z s S Nd si := by
  simp only [InputAtZ, InputAtWithZ]
  constructor
  · rintro ⟨hA, S, Nd, hW, h1, h2, h3, h4, h5⟩; exact ⟨S, Nd, hA, hW, h1, h2, h3, h4, h5⟩
  · rintro ⟨S, Nd, hA, hW, h1, h2, h3, h4, h5⟩; exact ⟨hA, S, Nd, hW, h1, h2, h3, h4, h5⟩

theorem inputAtWithZ_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S Nd : List Nat) (si : Nat) :
    InputAtWithZ Z { s with locals := locals, clock := k } S Nd si ↔ InputAtWithZ Z s S Nd si := by
  simp only [InputAtWithZ, worldTypedWith_with_locals, arenaReady_with_locals]
  exact Iff.rfl

theorem inputAtZ_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k si : Nat) :
    InputAtZ Z { s with locals := locals, clock := k } si ↔ InputAtZ Z s si := by
  simp only [InputAtZ, WorldTypedWith, tablesTyped_with_locals, arenaReady_with_locals]
  exact Iff.rfl

theorem inputReadyZ_worldOK {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : InputReadyZ Z s) : WorldOK s := by
  obtain ⟨hA, S, Nd, hT, -⟩ := h
  exact ⟨hA, S, (worldTyped_iff_with s S).2 ⟨Nd, hT⟩⟩

theorem inputReadyZ_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : InputReadyZ Z s) : GuestInv s := h.1.1

theorem localsOnly_inputReadyZ : LocalsOnly ["si"] (InputReadyZ Z) := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "si" (hl "si" (by simp))
  show InputAtZ Z _ _
  rw [ht]
  exact (inputAtZ_with_locals s locals k _).2 hP

theorem localsOnly_blockReadyStrongZ : LocalsOnly ["si", "hdr"] (BlockReadyStrongZ Z) := by
  intro F s locals k hl hP
  have hsi := locN_congr s locals k "si" (hl "si" (by simp))
  have hh := locN_congr s locals k "hdr" (hl "hdr" (by simp))
  refine ⟨localsOnly_blockReady s locals k (fun n hn => hl n (by simp_all)) hP.1, ?_, ?_⟩
  · show InputAtZ Z _ _
    rw [hsi]
    exact (inputAtZ_with_locals s locals k _).2 hP.2.1
  · change HeaderAt _ (locN { s with locals := locals, clock := k } "hdr")
    rw [hh]
    exact hP.2.2

/-- With `Z := False` the relaxed layer is the original one. -/
theorem inputAtZ_false_iff {F : Type} (s : PanSemStateFiniteExact 64 F) (si : Nat) :
    InputAtZ False s si ↔ InputAt s si := by
  simp only [InputAtZ, InputAt, false_and, false_or]

theorem inputReadyZ_false_iff {F : Type} (s : PanSemStateFiniteExact 64 F) :
    InputReadyZ False s ↔ InputReady s :=
  inputAtZ_false_iff s _

theorem inputReadyNwdZ_false_iff {F : Type} (s : PanSemStateFiniteExact 64 F) :
    InputReadyNwdZ False s ↔ InputReadyNwd s := by
  show (InputAtZ False s _ ∧ _) ↔ (InputAt s _ ∧ _)
  rw [inputAtZ_false_iff]

theorem blockReadyStrongZ_false_iff {F : Type} (s : PanSemStateFiniteExact 64 F) :
    BlockReadyStrongZ False s ↔ BlockReadyStrong s := by
  show (BlockReady s ∧ InputReadyZ False s ∧ _) ↔ (BlockReady s ∧ InputReady s ∧ _)
  rw [inputReadyZ_false_iff]

/-- `WorldStep.preserves_inputAtWith` at the relaxed layer: a null transaction
cell survives trivially, and `PayloadAt`'s per-transaction clause is vacuous
on it (`16 * ntx = 0`). -/
theorem worldStep_preserves_inputAtWithZ
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {S Nd : List Nat} {si : Nat}
    (hIA : InputAtWithZ Z s S Nd si)
    (hws : WorldStep R gw keep Q s r post)
    (hR_z : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (hR_ti : IvlsDisj (R s) (worldTypedIvls s S Nd))
    (hR_in : IvlsDisj (inputCells s si) (R s)) :
    ∃ S' Nd', (∀ t ∈ S, t ∈ S') ∧ InputAtWithZ Z post S' Nd' si ∧
      OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd') ∧
      FrameOutside s post (worldOwned s S Nd ++ R s ++ [freeGap s]) (heapFree s) ∧
      Q s r post S' Nd' := by
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  obtain ⟨hAs, hWT, hcells, hdisj_ow, hntx63, hPay, hReq⟩ := hIA
  obtain ⟨hAp, hhp, _, _, hStep⟩ := hws
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
  obtain ⟨S', Nd', hsub, hWT', hog, hfr, hQ⟩ := hStep S Nd hWT hR_ti
  have hold_z := worldOwned_zero_aligned hWT
  -- Each of the 4 inputCells survives the step:
  have h_surv : ∀ b ∈ inputCells s si,
      ((Z ∧ b.1 = 0 ∧ b.2 = 0) ∨ Inside b sourceBase (globN post "heap_ptr")) ∧
      (∀ o ∈ worldOwned post S' Nd', Disj b o) ∧
      IvlUnhit s post b := by
    intro b hb
    obtain ⟨hb_in, hb_w⟩ := hcells b hb
    rcases hb_in with hz | hb_in
    · exact ⟨Or.inl hz, fun _ _ => Or.inl hz.2.2, ivlUnhit_null hz.2⟩
    · obtain ⟨h1, h2, h3⟩ := heap_ivl_survives_step hAs.2 hhp hog hfr hold_z hR_z
        hb_w.1 hb_w.2.1 hb_in (fun j hj => hdisj_ow b hb j hj) (fun j hj => hR_in b hb j hj)
      exact ⟨Or.inr h1, h2, h3⟩
  have hsi_mem : (si, 40) ∈ inputCells s si := by simp [inputCells]
  obtain ⟨hsi_in_s', hsi_w_s⟩ := hcells (si, 40) hsi_mem
  have hsi_in_s : Inside (si, 40) sourceBase (globN s "heap_ptr") :=
    hsi_in_s'.resolve_left (fun hz => absurd hz.2.2 (by simp))
  obtain ⟨_, _, hsi_u⟩ := h_surv (si, 40) hsi_mem
  have hsi_eq0 : memW post si = memW s si :=
    memW_eq_of_ivlUnhit hsi_u hsi_w_s.1 (by unfold Inside at hsi_in_s; omega) ⟨le_rfl, by omega⟩
  have hsi_eq32 : memW post (si + 32) = memW s (si + 32) :=
    memW_eq_of_ivlUnhit hsi_u (by have := hsi_w_s.1; omega) (by unfold Inside at hsi_in_s; omega)
      ⟨by omega, by omega⟩
  set pl := memW s si
  set rq := memW s (si + 32)
  have hpl_mem : (pl, 136) ∈ inputCells s si := by simp [inputCells, pl]
  obtain ⟨hpl_in_s', hpl_w_s⟩ := hcells (pl, 136) hpl_mem
  have hpl_in_s : Inside (pl, 136) sourceBase (globN s "heap_ptr") :=
    hpl_in_s'.resolve_left (fun hz => absurd hz.2.2 (by simp))
  obtain ⟨_, _, hpl_u⟩ := h_surv (pl, 136) hpl_mem
  have hpl_word : ∀ off, off % 8 = 0 → off + 8 ≤ 136 → memW post (pl + off) = memW s (pl + off) :=
    fun off hoff8 hoff_hi =>
      memW_eq_of_ivlUnhit hpl_u (by have := hpl_w_s.1; omega)
        (by unfold Inside at hpl_in_s; omega) ⟨by omega, by omega⟩
  have hpl24 : memW post (pl + 24) = memW s (pl + 24) := hpl_word 24 (by omega) (by omega)
  have hpl32 : memW post (pl + 32) = memW s (pl + 32) := hpl_word 32 (by omega) (by omega)
  have hpl40 : memW post (pl + 40) = memW s (pl + 40) := hpl_word 40 (by omega) (by omega)
  have hic_eq : inputCells post si = inputCells s si := by
    simp only [inputCells, hsi_eq0, hsi_eq32]
    change [(si, 40), (pl, 136), (rq, 80), (memW post (pl + 32), 16 * memW post (pl + 40))] =
           [(si, 40), (pl, 136), (rq, 80), (memW s (pl + 32), 16 * memW s (pl + 40))]
    rw [hpl32, hpl40]
  have hrq_mem : (rq, 80) ∈ inputCells s si := by simp [inputCells, rq]
  obtain ⟨hrq_in_s', hrq_w_s⟩ := hcells (rq, 80) hrq_mem
  have hrq_in_s : Inside (rq, 80) sourceBase (globN s "heap_ptr") :=
    hrq_in_s'.resolve_left (fun hz => absurd hz.2.2 (by simp))
  obtain ⟨_, _, hrq_u⟩ := h_surv (rq, 80) hrq_mem
  have hptxs_mem : (memW s (pl + 32), 16 * memW s (pl + 40)) ∈ inputCells s si := by
    simp [inputCells, pl]
  obtain ⟨hptxs_in_s, hptxs_w_s⟩ := hcells _ hptxs_mem
  obtain ⟨_, _, hptxs_u⟩ := h_surv _ hptxs_mem
  refine ⟨S', Nd', hsub, ⟨hAp, hWT', ?_, ?_, ?_, ?_, ?_⟩, hog, hfr, hQ⟩
  · rw [hic_eq]
    intro i hi
    exact ⟨(h_surv i hi).1, wordsOK_transfer hAs.1 hAp.1 (hcells i hi).2⟩
  · rw [hic_eq]
    intro i hi o ho
    exact (h_surv i hi).2.1 o ho
  · rw [hsi_eq0, hpl40]; exact hntx63
  · rw [hsi_eq0]
    refine ⟨wordsOK_transfer hAs.1 hAp.1 hPay.1, ?_, ?_, ?_⟩
    · rw [hpl24]; exact hPay.2.1
    · rw [hpl40]; exact hPay.2.2.1
    · rw [hpl32, hpl40]
      intro idx hidx
      rcases hptxs_in_s with hz | hptxs_in_s
      · have h16 : 16 * memW s (pl + 40) = 0 := hz.2.2
        omega
      · have hcell_eq : memW post (memW s (pl + 32) + 16 * idx + 8) =
            memW s (memW s (pl + 32) + 16 * idx + 8) :=
          memW_eq_of_ivlUnhit hptxs_u (by have := hptxs_w_s.1; omega)
            (by unfold Inside at hptxs_in_s; omega) ⟨by dsimp; omega, by dsimp; omega⟩
        rw [hcell_eq]
        exact hPay.2.2.2 idx hidx
  · rw [hsi_eq32]
    refine ⟨wordsOK_transfer hAs.1 hAp.1 hReq.1, fun idx hidx => ?_⟩
    have hcell_eq : memW post (rq + 16 * idx + 8) = memW s (rq + 16 * idx + 8) :=
      memW_eq_of_ivlUnhit hrq_u (by have := hrq_w_s.1; omega)
        (by unfold Inside at hrq_in_s; omega) ⟨by omega, by omega⟩
    rw [hcell_eq]
    exact hReq.2 idx hidx

/-! ### The null-tolerant `run_attempt` guard -/

def InputAtNull (Z : Prop) {F : Type} (s : PanSemStateFiniteExact 64 F) (si : Nat) : Prop :=
  (InputAtZ Z) s si ∧
  memW s (si + 16) < 2 ^ 32 ∧
  memW s (memW s si + 56) < 2 ^ 32 ∧
  ∃ S Nd, WorldTypedWith s S Nd ∧
    (∀ i ∈ runAttemptCells s si,
      i.1 % 8 = 0 ∧ ((i.1 = 0 ∧ i.2 = 0) ∨
        Inside i sourceBase (globN s "heap_ptr")) ∧ WordsOK s i) ∧
    IvlsDisj (runAttemptCells s si) (worldOwned s S Nd)

def InputReadyNull (Z : Prop) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => (InputAtNull Z) s (locN s "si")

theorem inputAtNull_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k si : Nat) :
    (InputAtNull Z) { s with locals := locals, clock := k } si ↔ (InputAtNull Z) s si := by
  simp only [InputAtNull, inputAtZ_with_locals, WorldTypedWith,
    tablesTyped_with_locals]
  exact Iff.rfl

theorem localsOnly_inputReadyNull : LocalsOnly ["si"] (InputReadyNull Z) := by
  intro F s locals k hl hP
  have hsi := locN_congr s locals k "si" (hl "si" (by simp))
  show (InputAtNull Z) _ _
  rw [hsi]
  exact (inputAtNull_with_locals s locals k _).2 hP

theorem inputReadyNull_inputReady {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : (InputReadyNull Z) s) : (InputReadyZ Z) s := h.1

theorem inputReadyNull_inputReadyNwd {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : (InputReadyNull Z) s) : (InputReadyNwdZ Z) s := ⟨h.1, h.2.1, h.2.2.1⟩

theorem inputReadyNull_worldOK {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : (InputReadyNull Z) s) : WorldOK s := inputReadyZ_worldOK s h.1

theorem inputReadyNull_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : (InputReadyNull Z) s) : GuestInv s := inputReadyZ_guestInv s h.1

def BlockReadyExecAttemptNull (Z : Prop) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => (BlockReadyStrongZ Z) s ∧ (InputReadyNull Z) s ∧ globN s "journal_cap" ≠ 0

theorem localsOnly_blockReadyExecAttemptNull : LocalsOnly ["si", "hdr"] (BlockReadyExecAttemptNull Z) := by
  intro F s locals k hl hP
  refine ⟨localsOnly_blockReadyStrongZ s locals k hl hP.1, ?_, hP.2.2⟩
  exact localsOnly_inputReadyNull s locals k (fun n hn => hl n (by simp_all)) hP.2.1

theorem inputReadyNull_tx_count {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : (InputReadyNull Z) s) : memW s (memW s (locN s "si") + 40) < 2 ^ 32 := by
  obtain ⟨_, _, _, _, _, _, _, hPay, _⟩ := h.1
  exact hPay.2.2.1

theorem inputReadyNull_blockReady {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : (InputReadyNull Z) s) : BlockReady s := by
  refine ⟨inputReadyNull_worldOK s h, ?_⟩
  have hn := inputReadyNull_tx_count s h
  omega

theorem blockReadyExecNull_of {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : (InputReadyNull Z) s) (hh : HeaderAt s (locN s "hdr"))
    (hj : globN s "journal_cap" ≠ 0) : (BlockReadyExecAttemptNull Z) s :=
  ⟨⟨inputReadyNull_blockReady s h, h.1, hh⟩, h, hj⟩

theorem callEntryOn_inputReadyNull
    {fname : MlS} {e : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL}
    (hl : originalRuntimeCode.lookup fname = some e)
    (hp : e.1 = [(ofString "si", .one)]) :
    CallEntryOn (InputReadyNull Z) (InputReadyNull Z) fname [.var .local (ofString "si")] := by
  obtain ⟨ps, b, r⟩ := e
  dsimp only at hp
  subst hp
  intro F state values body' callee ret' hcode hP hargs hlook
  have hc := callee_param_one state fname (ofString "si") .one b r
    (by rw [hcode]; exact hl) values body' callee ret' hargs hlook
  have hsi : locN (callEntryStateHOLFinite state callee) "si" = locN state "si" := by
    simp only [locN, callEntryStateHOLFinite, hc]
  show (InputAtNull Z) (callEntryStateHOLFinite state callee)
    (locN (callEntryStateHOLFinite state callee) "si")
  rw [hsi]
  exact (inputAtNull_with_locals state callee (state.clock - 1) _).2 hP

theorem runAttemptCells_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {si : Nat} (h : (InputAtNull Z) s si)
    (hu : ∀ c ∈ runAttemptCells s si,
      R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post c) :
    runAttemptCells post si = runAttemptCells s si := by
  obtain ⟨hIA, _, _, S, Nd, _, hc, _⟩ := h
  have hs := hc (si, 96) (by simp [runAttemptCells])
  have hp := hc (memW s si, 136) (by simp [runAttemptCells])
  have hsI := inside_of_nullOrInside (by simp) hs.2.1
  have hpI := inside_of_nullOrInside (by simp) hp.2.1
  have hlim : globN s "heap_ptr" ≤ 2 ^ 64 := by
    have ha := hIA.1.2.2.1
    have hb : heapLimit ≤ 2 ^ 64 := by decide
    omega
  have hsi : ∀ off, off % 8 = 0 → off + 8 ≤ 96 →
      memW post (si + off) = memW s (si + off) := by
    intro off ho hb
    exact R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit
      (hu (si, 96) (by simp [runAttemptCells]))
      (by omega) (by have := hsI.2; omega) ⟨by omega, by omega⟩
  have h0 : memW post si = memW s si := by
    simpa using hsi 0 (by decide) (by decide)
  have hpl : ∀ off, off % 8 = 0 → off + 8 ≤ 136 →
      memW post (memW s si + off) = memW s (memW s si + off) := by
    intro off ho hb
    exact R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit
      (hu (memW s si, 136) (by simp [runAttemptCells]))
      (by have := hp.1; omega) (by have := hpI.2; omega) ⟨by omega, by omega⟩
  simp only [runAttemptCells, h0, hsi 32 (by decide) (by decide),
    hsi 40 (by decide) (by decide), hsi 48 (by decide) (by decide),
    hsi 56 (by decide) (by decide), hsi 64 (by decide) (by decide),
    hsi 72 (by decide) (by decide), hsi 80 (by decide) (by decide),
    hpl 32 (by decide) (by decide), hpl 40 (by decide) (by decide)]

def InputAtNullWith (Z : Prop) {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) (si : Nat) : Prop :=
  (InputAtWithZ Z) s S Nd si ∧
    (∀ i ∈ runAttemptCells s si,
      i.1 % 8 = 0 ∧ ((i.1 = 0 ∧ i.2 = 0) ∨
        Inside i sourceBase (globN s "heap_ptr")) ∧ WordsOK s i) ∧
    IvlsDisj (runAttemptCells s si) (worldOwned s S Nd) ∧
    memW s (si + 16) < 2 ^ 32 ∧
    memW s (memW s si + 56) < 2 ^ 32

/-- The header cell `(si, 96)` has nonzero size, so it is `Inside`. -/
theorem inputAtNullWith_si_inside {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si : Nat} (h : InputAtNullWith Z s S Nd si) :
    Inside (si, 96) sourceBase (globN s "heap_ptr") :=
  inside_of_nullOrInside (by simp) (h.2.1 (si, 96) (by simp [runAttemptCells])).2.1

/-- The payload cell `(pl, 136)` has nonzero size, so it is `Inside`. -/
theorem inputAtNullWith_pl_inside {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si : Nat} (h : InputAtNullWith Z s S Nd si) :
    Inside (memW s si, 136) sourceBase (globN s "heap_ptr") :=
  inside_of_nullOrInside (by simp) (h.2.1 (memW s si, 136) (by simp [runAttemptCells])).2.1

theorem inputAtNullWith_strong {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si : Nat} (h : (InputAtNullWith Z) s S Nd si) :
    (InputAtNull Z) s si :=
  ⟨(inputAtZ_iff_with s si).2 ⟨S, Nd, h.1⟩,
    h.2.2.2.1, h.2.2.2.2, S, Nd, h.1.2.1, h.2.1, h.2.2.1⟩

theorem inputAtNull_iff_with {F : Type} (s : PanSemStateFiniteExact 64 F) (si : Nat) :
    (InputAtNull Z) s si ↔ ∃ S Nd, (InputAtNullWith Z) s S Nd si := by
  constructor
  · rintro ⟨hIA, hnvh, hnwd, S, Nd, hWT, hcs, hd⟩
    obtain ⟨hA, _, _, _, hsmall, _, hn, hp, hr⟩ := hIA
    refine ⟨S, Nd, ⟨⟨hA, hWT, hsmall, ?_, hn, hp, hr⟩, hcs, hd, hnvh, hnwd⟩⟩
    intro c hc o ho
    simp only [inputCells, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · have hbig := hd (si, 96) (by simp [runAttemptCells]) o ho
      unfold Disj at hbig ⊢
      dsimp only at hbig ⊢
      omega
    · exact hd _ (by simp [runAttemptCells]) o ho
    · exact hd _ (by simp [runAttemptCells]) o ho
    · exact hd _ (by simp [runAttemptCells]) o ho
  · rintro ⟨S, Nd, h⟩
    exact inputAtNullWith_strong h

theorem inputAtNullWith_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S Nd : List Nat) (si : Nat) :
    (InputAtNullWith Z) { s with locals := locals, clock := k } S Nd si ↔
      (InputAtNullWith Z) s S Nd si := by
  rw [InputAtNullWith, inputAtWithZ_with_locals]
  exact Iff.rfl

theorem worldStep_preserves_inputAtNullWith
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {S Nd : List Nat} {si : Nat}
    (h : (InputAtNullWith Z) s S Nd si) (hw : WorldStep R gw keep Q s r post)
    (hz : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (ht : IvlsDisj (R s) (worldTypedIvls s S Nd))
    (hi : IvlsDisj (inputCells s si) (R s))
    (hc : IvlsDisj (runAttemptCells s si) (R s)) :
    ∃ S' Nd', (InputAtNullWith Z) post S' Nd' si ∧
      (∀ t ∈ S, t ∈ S') ∧
      (∀ c ∈ runAttemptCells s si, R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post c) ∧
      Q s r post S' Nd' := by
  obtain ⟨S', Nd', hsub, hIA, hog, hfr, hQ⟩ :=
    worldStep_preserves_inputAtWithZ h.1 hw hz ht hi
  have hs : ∀ c ∈ runAttemptCells s si,
      ((c.1 = 0 ∧ c.2 = 0) ∨ Inside c sourceBase (globN post "heap_ptr")) ∧
      (∀ o ∈ worldOwned post S' Nd', Disj c o) ∧
      R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post c := by
    intro c hcm
    obtain ⟨ha, hin, hword⟩ := h.2.1 c hcm
    exact nullOrInside_survives_step
      h.1.1.2 hw.2.1 hog hfr
      (R10Shards.Fast_GbodyC17ToC21.worldOwned_zero_aligned h.1.2.1)
      hz ha hword.2.1 hin (h.2.2.1 c hcm) (hc c hcm)
  have heq := runAttemptCells_eq_of_unhit (inputAtNullWith_strong h)
    (fun c hcm => (hs c hcm).2.2)
  have hlim : globN s "heap_ptr" ≤ 2 ^ 64 := by
    have ha := h.1.1.2.2.1
    have hb : heapLimit ≤ 2 ^ 64 := by decide
    omega
  have hsi_rc := h.2.1 (si, 96) (by simp [runAttemptCells])
  have hpl_rc := h.2.1 (memW s si, 136) (by simp [runAttemptCells])
  have hsi_in := inputAtNullWith_si_inside h
  have hpl_in := inputAtNullWith_pl_inside h
  have hsi0_eq : memW post si = memW s si := by
    simpa using R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit
      (a := si + 0) (hs (si, 96) (by simp [runAttemptCells])).2.2
      (by omega) (by have := hsi_in.2; omega) ⟨by omega, by omega⟩
  have hsi16_eq : memW post (si + 16) = memW s (si + 16) :=
    R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit
      (hs (si, 96) (by simp [runAttemptCells])).2.2
      (by have := hsi_rc.1; omega) (by have := hsi_in.2; omega) ⟨by omega, by omega⟩
  have hpl56_eq : memW post (memW s si + 56) = memW s (memW s si + 56) :=
    R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit
      (hs (memW s si, 136) (by simp [runAttemptCells])).2.2
      (by have := hpl_rc.1; omega) (by have := hpl_in.2; omega) ⟨by omega, by omega⟩
  refine ⟨S', Nd', ⟨hIA, ?_, ?_, ?_, ?_⟩, hsub, (fun c hcm => (hs c hcm).2.2), hQ⟩
  · rw [heq]
    intro c hcm
    exact ⟨(h.2.1 c hcm).1, (hs c hcm).1,
      R10Shards.Fast_GbodyC17ToC21.wordsOK_transfer h.1.1.1 hw.1.1 (h.2.1 c hcm).2.2⟩
  · rw [heq]
    exact fun c hcm => (hs c hcm).2.1
  · rw [hsi16_eq]; exact h.2.2.2.1
  · rw [hsi0_eq, hpl56_eq]; exact h.2.2.2.2

private def AllBlocksGood {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) (bs : List Ivl) : Prop :=
  ∀ b ∈ bs, b.1 % 8 = 0 ∧ b.2 % 8 = 0 ∧
    Inside b sourceBase (globN s "heap_ptr") ∧
    WordsOK s b ∧
    IvlsDisj [b] (worldOwned s S Nd)

private theorem allBlocksGood_nil {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat) :
    AllBlocksGood s S Nd [] :=
  fun _ h => nomatch h

private theorem allBlocksGood_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S Nd : List Nat) (bs : List Ivl) :
    AllBlocksGood { s with locals := locals, clock := k } S Nd bs ↔ AllBlocksGood s S Nd bs :=
  Iff.rfl

theorem worldStepIn_preserves_nullAndBlocks
    {T : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {S Nd : List Nat} {si : Nat} {bs : List Ivl}
    (h : (InputAtNullWith Z) s S Nd si)
    (hbs : AllBlocksGood s S Nd bs)
    (hw : WorldStepIn T R gw keep Q s r post)
    (hT : ∀ t ∈ T s, t ∈ S)
    (hz : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (ht : IvlsDisj (R s) (worldTypedIvls s S Nd))
    (hc : IvlsDisj (runAttemptCells s si) (R s))
    (hb : IvlsDisj bs (R s)) :
    ∃ S' Nd', (InputAtNullWith Z) post S' Nd' si ∧
      AllBlocksGood post S' Nd' bs ∧
      (∀ t ∈ S, t ∈ S') ∧
      (∀ c ∈ runAttemptCells s si, R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post c) ∧
      (∀ b ∈ bs, R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post b) ∧
      OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd') ∧
      FrameOutside s post (worldOwned s S Nd ++ R s ++ [freeGap s]) (heapFree s) ∧
      Q s r post S' Nd' := by
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  obtain ⟨⟨hAs, hWT, hcells, hdisj_in, hntx63, hPay, hReq⟩, hrc, hrc_disj, hnvh, hnwd⟩ := h
  obtain ⟨hAp, hhp, _, _, hStep⟩ := hw
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
  obtain ⟨S', Nd', hsub, hWT', hog, hfr, hQ⟩ := hStep S Nd hWT hT ht
  have hold_z := R10Shards.Fast_GbodyC17ToC21.worldOwned_zero_aligned hWT
  have hR_in := inputCells_disj_of_runAttemptCells hc
  have h_in_surv : ∀ b ∈ inputCells s si,
      ((Z ∧ b.1 = 0 ∧ b.2 = 0) ∨ Inside b sourceBase (globN post "heap_ptr")) ∧
      (∀ o ∈ worldOwned post S' Nd', Disj b o) ∧
      R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post b := by
    intro b hbm
    obtain ⟨hb_in, hb_w⟩ := hcells b hbm
    rcases hb_in with hb0 | hb_in
    · exact ⟨Or.inl hb0, fun _ _ => Or.inl hb0.2.2, ivlUnhit_null hb0.2⟩
    · obtain ⟨h1, h2, h3⟩ := R10Shards.Fast_GbodyC17ToC21.heap_ivl_survives_step
        hAs.2 hhp hog hfr hold_z hz hb_w.1 hb_w.2.1 hb_in
        (fun j hj => hdisj_in b hbm j hj) (fun j hj => hR_in b hbm j hj)
      exact ⟨Or.inr h1, h2, h3⟩
  have h_rc_surv : ∀ c ∈ runAttemptCells s si,
      ((c.1 = 0 ∧ c.2 = 0) ∨ Inside c sourceBase (globN post "heap_ptr")) ∧
      (∀ o ∈ worldOwned post S' Nd', Disj c o) ∧
      R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post c := by
    intro c hcm
    obtain ⟨ha, hin, hword⟩ := hrc c hcm
    exact nullOrInside_survives_step
      hAs.2 hhp hog hfr hold_z hz ha hword.2.1 hin (hrc_disj c hcm) (hc c hcm)
  have h_bs_surv : ∀ b ∈ bs,
      Inside b sourceBase (globN post "heap_ptr") ∧
      (∀ o ∈ worldOwned post S' Nd', Disj b o) ∧
      R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post b := by
    intro b hbm
    obtain ⟨hb8, hbl8, hb_in, _, hb_ow⟩ := hbs b hbm
    exact R10Shards.Fast_GbodyC17ToC21.heap_ivl_survives_step
      hAs.2 hhp hog hfr hold_z hz hb8 hbl8 hb_in
      (fun j hj => hb_ow b (List.mem_singleton.2 rfl) j hj) (hb b hbm)
  have hsi_mem : (si, 40) ∈ inputCells s si := by simp [inputCells]
  obtain ⟨hsi_in_s', hsi_w_s⟩ := hcells (si, 40) hsi_mem
  have hsi_in_s : Inside (si, 40) sourceBase (globN s "heap_ptr") :=
    hsi_in_s'.resolve_left (fun hb0 => absurd hb0.2.2 (by simp))
  obtain ⟨_, _, hsi_u⟩ := h_in_surv (si, 40) hsi_mem
  have hsi_eq0 : memW post si = memW s si :=
    R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit hsi_u hsi_w_s.1
      (by unfold Inside at hsi_in_s; omega) ⟨le_rfl, by omega⟩
  have hsi_eq32 : memW post (si + 32) = memW s (si + 32) :=
    R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit hsi_u (by have := hsi_w_s.1; omega)
      (by unfold Inside at hsi_in_s; omega) ⟨by omega, by omega⟩
  set pl := memW s si
  set rq := memW s (si + 32)
  have hpl_mem : (pl, 136) ∈ inputCells s si := by simp [inputCells, pl]
  obtain ⟨hpl_in_s', hpl_w_s⟩ := hcells (pl, 136) hpl_mem
  have hpl_in_s : Inside (pl, 136) sourceBase (globN s "heap_ptr") :=
    hpl_in_s'.resolve_left (fun hb0 => absurd hb0.2.2 (by simp))
  obtain ⟨_, _, hpl_u⟩ := h_in_surv (pl, 136) hpl_mem
  have hpl_word : ∀ off, off % 8 = 0 → off + 8 ≤ 136 → memW post (pl + off) = memW s (pl + off) :=
    fun off hoff8 hoff_hi =>
      R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit hpl_u (by have := hpl_w_s.1; omega)
        (by unfold Inside at hpl_in_s; omega) ⟨by omega, by omega⟩
  have hpl24 : memW post (pl + 24) = memW s (pl + 24) := hpl_word 24 (by omega) (by omega)
  have hpl32 : memW post (pl + 32) = memW s (pl + 32) := hpl_word 32 (by omega) (by omega)
  have hpl40 : memW post (pl + 40) = memW s (pl + 40) := hpl_word 40 (by omega) (by omega)
  have hic_eq : inputCells post si = inputCells s si := by
    simp only [inputCells, hsi_eq0, hsi_eq32]
    change [(si, 40), (pl, 136), (rq, 80), (memW post (pl + 32), 16 * memW post (pl + 40))] =
           [(si, 40), (pl, 136), (rq, 80), (memW s (pl + 32), 16 * memW s (pl + 40))]
    rw [hpl32, hpl40]
  have hrq_mem : (rq, 80) ∈ inputCells s si := by simp [inputCells, rq]
  obtain ⟨hrq_in_s', hrq_w_s⟩ := hcells (rq, 80) hrq_mem
  have hrq_in_s : Inside (rq, 80) sourceBase (globN s "heap_ptr") :=
    hrq_in_s'.resolve_left (fun hb0 => absurd hb0.2.2 (by simp))
  obtain ⟨_, _, hrq_u⟩ := h_in_surv (rq, 80) hrq_mem
  have hptxs_mem : (memW s (pl + 32), 16 * memW s (pl + 40)) ∈ inputCells s si := by
    simp [inputCells, pl]
  obtain ⟨hptxs_in_s, hptxs_w_s⟩ := hcells _ hptxs_mem
  obtain ⟨_, _, hptxs_u⟩ := h_in_surv _ hptxs_mem
  have hIA' : (InputAtWithZ Z) post S' Nd' si := by
    refine ⟨hAp, hWT', ?_, ?_, ?_, ?_, ?_⟩
    · rw [hic_eq]
      exact fun i hi => ⟨(h_in_surv i hi).1,
        R10Shards.Fast_GbodyC17ToC21.wordsOK_transfer hAs.1 hAp.1 (hcells i hi).2⟩
    · rw [hic_eq]
      exact fun i hi o ho => (h_in_surv i hi).2.1 o ho
    · rw [hsi_eq0, hpl40]; exact hntx63
    · rw [hsi_eq0]
      refine ⟨R10Shards.Fast_GbodyC17ToC21.wordsOK_transfer hAs.1 hAp.1 hPay.1, ?_, ?_, ?_⟩
      · rw [hpl24]; exact hPay.2.1
      · rw [hpl40]; exact hPay.2.2.1
      · rw [hpl32, hpl40]
        intro idx hidx
        rcases hptxs_in_s with hb0 | hptxs_in_s
        · have h16 : 16 * memW s (pl + 40) = 0 := hb0.2.2
          omega
        · have hcell_eq : memW post (memW s (pl + 32) + 16 * idx + 8) =
              memW s (memW s (pl + 32) + 16 * idx + 8) :=
            R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit hptxs_u
              (by have := hptxs_w_s.1; omega) (by unfold Inside at hptxs_in_s; omega)
              ⟨by dsimp; omega, by dsimp; omega⟩
          rw [hcell_eq]; exact hPay.2.2.2 idx hidx
    · rw [hsi_eq32]
      refine ⟨R10Shards.Fast_GbodyC17ToC21.wordsOK_transfer hAs.1 hAp.1 hReq.1, fun idx hidx => ?_⟩
      have hcell_eq : memW post (rq + 16 * idx + 8) = memW s (rq + 16 * idx + 8) :=
        R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit hrq_u
          (by have := hrq_w_s.1; omega) (by unfold Inside at hrq_in_s; omega) ⟨by omega, by omega⟩
      rw [hcell_eq]; exact hReq.2 idx hidx
  have heq := runAttemptCells_eq_of_unhit (inputAtNullWith_strong ⟨⟨hAs, hWT, hcells, hdisj_in, hntx63, hPay, hReq⟩, hrc, hrc_disj, hnvh, hnwd⟩)
    (fun c hcm => (h_rc_surv c hcm).2.2)
  have hsi_eq16 : memW post (si + 16) = memW s (si + 16) :=
    R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit hsi_u (by have := hsi_w_s.1; omega)
      (by unfold Inside at hsi_in_s; omega) ⟨by omega, by omega⟩
  have hpl56 : memW post (pl + 56) = memW s (pl + 56) := hpl_word 56 (by omega) (by omega)
  refine ⟨S', Nd', ⟨hIA', ?_, ?_, ?_, ?_⟩, ?_, hsub, (fun c hcm => (h_rc_surv c hcm).2.2),
    (fun b hbm => (h_bs_surv b hbm).2.2), hog, hfr, hQ⟩
  · rw [heq]
    exact fun c hcm => ⟨(hrc c hcm).1, (h_rc_surv c hcm).1,
      R10Shards.Fast_GbodyC17ToC21.wordsOK_transfer hAs.1 hAp.1 (hrc c hcm).2.2⟩
  · rw [heq]
    exact fun c hcm => (h_rc_surv c hcm).2.1
  · rw [hsi_eq16]; exact hnvh
  · rw [hsi_eq0, hpl56]; exact hnwd
  · intro b hbm
    obtain ⟨hb8, hbl8, _, hbw, _⟩ := hbs b hbm
    exact ⟨hb8, hbl8, (h_bs_surv b hbm).1,
      R10Shards.Fast_GbodyC17ToC21.wordsOK_transfer hAs.1 hAp.1 hbw,
      fun b' hb' o ho => by rw [List.mem_singleton.1 hb']; exact (h_bs_surv b hbm).2.1 o ho⟩

theorem worldStep_preserves_nullAndBlocks
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {S Nd : List Nat} {si : Nat} {bs : List Ivl}
    (h : (InputAtNullWith Z) s S Nd si)
    (hbs : AllBlocksGood s S Nd bs)
    (hw : WorldStep R gw keep Q s r post)
    (hz : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (ht : IvlsDisj (R s) (worldTypedIvls s S Nd))
    (hc : IvlsDisj (runAttemptCells s si) (R s))
    (hb : IvlsDisj bs (R s)) :
    ∃ S' Nd', (InputAtNullWith Z) post S' Nd' si ∧
      AllBlocksGood post S' Nd' bs ∧
      (∀ t ∈ S, t ∈ S') ∧
      (∀ c ∈ runAttemptCells s si, R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post c) ∧
      (∀ b ∈ bs, R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post b) ∧
      OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd') ∧
      FrameOutside s post (worldOwned s S Nd ++ R s ++ [freeGap s]) (heapFree s) ∧
      Q s r post S' Nd' :=
  worldStepIn_preserves_nullAndBlocks h hbs (hw.stepIn (T := fun _ => []))
    (fun _ hx => nomatch hx) hz ht hc hb

theorem inputAtNullWith_cons_fresh {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si t : Nat}
    (h : (InputAtNullWith Z) s S Nd si)
    (hWF : HtabWF s t)
    (hin : ∀ i ∈ htabFootprint s t, Inside i sourceBase (globN s "heap_ptr"))
    (hd : IvlsDisj (htabFootprint s t) (worldOwned s S Nd))
    (hc : IvlsDisj (runAttemptCells s si) (htabFootprint s t)) :
    (InputAtNullWith Z) s (t :: S) Nd si := by
  have hWT := worldTypedWith_cons_fresh h.1.2.1 hWF hin hd
  have hdisj : IvlsDisj (runAttemptCells s si) (worldOwned s (t :: S) Nd) := by
    rw [worldOwned_cons]
    intro c hcm o ho
    rcases List.mem_append.1 ho with ho | ho
    · exact hc c hcm o ho
    · exact h.2.2.1 c hcm o ho
  exact ⟨⟨h.1.1, hWT, h.1.2.2.1,
    inputCells_disj_of_runAttemptCells hdisj, h.1.2.2.2.2⟩, h.2.1, hdisj, h.2.2.2.1, h.2.2.2.2⟩

theorem allBlocksGood_cons_fresh {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {bs : List Ivl} {t : Nat}
    (h : AllBlocksGood s S Nd bs)
    (hd : IvlsDisj bs (htabFootprint s t)) :
    AllBlocksGood s (t :: S) Nd bs := by
  intro b hbm
  obtain ⟨ha, hl, hin, hw, ho⟩ := h b hbm
  refine ⟨ha, hl, hin, hw, ?_⟩
  rw [worldOwned_cons]
  intro b' hb' o hom
  have heq := List.mem_singleton.1 hb'
  subst b'
  rcases List.mem_append.1 hom with hom | hom
  · exact hd b hbm o hom
  · exact ho b (by simp) o hom

theorem nullAndBlocks_bufferRegion_conditions {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {si : Nat} {bs : List Ivl}
    (h : (InputAtNullWith Z) s S Nd si) (hb : AllBlocksGood s S Nd bs)
    (gn : String × Nat) (hg : gn ∈ globalBuffers)
    (hu : gn.1 ∉ typedRecords.map Prod.fst) (hn : gn.2 ≠ 0) :
    ((bufferRegion s gn).2 = 0 → (bufferRegion s gn).1 % 8 = 0) ∧
    IvlsDisj [bufferRegion s gn] (worldTypedIvls s S Nd) ∧
    IvlsDisj (runAttemptCells s si) [bufferRegion s gn] ∧
    IvlsDisj bs [bufferRegion s gn] := by
  have hm := R10Shards.Fast_GbodyC17ToC21.bufferRegion_mem_worldOwned s S Nd hg
  refine ⟨R10Shards.Fast_GbodyC17ToC21.bufferRegion_zero_aligned s gn.1 gn.2 hn, ?_, ?_, ?_⟩
  · intro i hi j hj
    rw [List.mem_singleton.1 hi]
    exact bufferRegion_disj h.1.2.1 gn hg hu j hj
  · intro c hc i hi
    rw [List.mem_singleton.1 hi]
    exact h.2.2.1 c hc _ hm
  · intro b hbm i hi
    rw [List.mem_singleton.1 hi]
    exact (hb b hbm).2.2.2.2 b (by simp) _ hm

theorem nullAndBlocks_setGlobal_untracked {F : Type} {s : PanSemStateFiniteExact 64 F}
    {gname : MlS} {w : BitVec 64} {S Nd : List Nat} {si : Nat} {bs : List Ivl}
    (hgb : ∀ gn ∈ globalBuffers, ofString gn.1 ≠ gname)
    (hgtr : ∀ g ∈ globalTableRoots, ofString g ≠ gname)
    (hj : ofString "journal" ≠ gname)
    (hjc : ofString "journal_cap" ≠ gname)
    (hjn : ofString "journal_n" ≠ gname)
    (hhp : ofString "heap_ptr" ≠ gname)
    (hfm : ofString "frame_mem_ptr" ≠ gname)
    (hsc : ofString "scratch_ptr" ≠ gname)
    (h : (InputAtNullWith Z) s S Nd si)
    (hbs : AllBlocksGood s S Nd bs) :
    let post := setGlobalHOLFinite gname (.val (.word w)) s
    (InputAtNullWith Z) post S Nd si ∧ AllBlocksGood post S Nd bs ∧
      globN post "journal_cap" = globN s "journal_cap" := by
  intro post
  have hu := worldTypedWith_setGlobal_untracked (w := w) hgb hgtr hj hjc hjn hhp hfm hsc h.1.1 h.1.2.1
  have hhp_eq : globN post "heap_ptr" = globN s "heap_ptr" :=
    globN_setGlobal_ne s gname (.val (.word w)) "heap_ptr" hhp
  have hjc_eq : globN post "journal_cap" = globN s "journal_cap" :=
    globN_setGlobal_ne s gname (.val (.word w)) "journal_cap" hjc
  have hic_eq : inputCells post si = inputCells s si := rfl
  have hrc_eq : runAttemptCells post si = runAttemptCells s si := rfl
  refine ⟨⟨⟨hu.1, hu.2.1, ?_, ?_, h.1.2.2.2.2.1, h.1.2.2.2.2.2.1, h.1.2.2.2.2.2.2⟩,
    ?_, ?_, h.2.2.2.1, h.2.2.2.2⟩, ?_, hjc_eq⟩
  · rw [hic_eq, hhp_eq]; exact h.1.2.2.1
  · rw [hic_eq, hu.2.2]; exact h.1.2.2.2.1
  · rw [hrc_eq, hhp_eq]; exact h.2.1
  · rw [hrc_eq, hu.2.2]; exact h.2.2.1
  · intro b hb
    obtain ⟨b1, b2, bin, bw, bow⟩ := hbs b hb
    refine ⟨b1, b2, ?_, bw, ?_⟩
    · rw [hhp_eq]; exact bin
    · rw [hu.2.2]; exact bow

theorem nullAndBlocks_setGlobal_be {F : Type} {s : PanSemStateFiniteExact 64 F}
    {w : BitVec 64} {S Nd : List Nat} {si : Nat} {bs : List Ivl}
    (h : (InputAtNullWith Z) s S Nd si)
    (hbs : AllBlocksGood s S Nd bs)
    (hw8 : w.toNat % 8 = 0)
    (hwin : Inside (w.toNat, 120) sourceBase (globN s "heap_ptr"))
    (hw_ow : IvlsDisj [(w.toNat, 120)] (worldOwned s S Nd))
    (hw_rc : IvlsDisj (runAttemptCells s si) [(w.toNat, 120)])
    (hw_bs : IvlsDisj bs [(w.toNat, 120)]) :
    let post := setGlobalHOLFinite (ofString "be") (.val (.word w)) s
    (InputAtNullWith Z) post S Nd si ∧ AllBlocksGood post S Nd bs ∧
      globN post "journal_cap" = globN s "journal_cap" ∧
      globN post "be" = w.toNat ∧ w.toNat ≠ 0 := by
  intro post
  have hsb : 0 < sourceBase := by decide
  have hw_nz : w.toNat ≠ 0 := by unfold Inside at hwin; omega
  have hAs : ArenaReady s := h.1.1
  have hWT : WorldTypedWith s S Nd := h.1.2.1
  have hAp : ArenaReady post :=
    arenaReady_setGlobal_ne hAs (ofString "be") w (by decide) (by decide) (by decide)
  have hlu : ∀ n : String, ofString n ≠ ofString "be" → globN post n = globN s n :=
    fun n hne => globN_setGlobal_ne s (ofString "be") (.val (.word w)) n hne
  have hbe_lu : globN post "be" = w.toNat := globN_setGlobal_same s "be" w
  have hhp_eq : globN post "heap_ptr" = globN s "heap_ptr" := hlu "heap_ptr" (by decide)
  have hjc_eq : globN post "journal_cap" = globN s "journal_cap" := hlu "journal_cap" (by decide)
  have hag : AllocatorGrows s post := by
    unfold AllocatorGrows
    rw [hhp_eq, hlu "scratch_ptr" (by decide)]
    exact ⟨le_rfl, le_rfl⟩
  have hcore : ∀ g ∈ R10Shards.P26_P28.coreWorldGlobals, globN post g = globN s g := by
    intro g hg
    apply hlu g
    simp only [R10Shards.P26_P28.coreWorldGlobals, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hbo_eq : blockOutObjects post = blockOutObjects s := by
    have hbo_g : globN post "bo" = globN s "bo" := hlu "bo" (by decide)
    exact (R10Shards.P26_P28.blockOutObjects_eq_of_bo_unhit
      hAs.2 hWT.2.2.1 hbo_g hWT.1.2.2.2.2.2.2.2.2.2.2.1
      (fun _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl)).1
  have hbal_eq : balObjects post = balObjects s := by
    have hba_g : globN post "bal_accounts" = globN s "bal_accounts" := hlu "bal_accounts" (by decide)
    exact (R10Shards.P26_P28.balObjects_eq_of_unhit
      hAs.2 hWT.1 hWT.2.2.1 hba_g
      (fun _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl) ⟨rfl, rfl⟩).1
  have hgb_be : ∀ gn ∈ globalBuffers, ofString gn.1 = ofString "be" → gn = ("be", 120) := by
    have hall : ∀ gn ∈ globalBuffers, ofString gn.1 = ofString "be" → gn = ("be", 120) := by decide
    exact hall
  have hfix_sub : ∀ o ∈ fixedObjects post,
      o ∈ fixedObjects s ∨ o = (w.toNat, 120) := by
    intro o ho
    have hrest_eq :
        ([(if globN post "journal_cap" = 0 then 0 else globN post "journal",
            32 * globN post "journal_cap")] ++ (blockOutObjects post ++ balObjects post)) =
        ([(if globN s "journal_cap" = 0 then 0 else globN s "journal",
            32 * globN s "journal_cap")] ++ (blockOutObjects s ++ balObjects s)) := by
      rw [hlu "journal" (by decide), hjc_eq, hbo_eq, hbal_eq]
    unfold fixedObjects at ho
    rw [List.append_assoc, List.append_assoc] at ho
    rcases List.mem_append.1 ho with hmb | hmr
    · obtain ⟨gn, hgn, rfl⟩ := List.mem_map.1 hmb
      by_cases hbe : ofString gn.1 = ofString "be"
      · have hgn_eq := hgb_be gn hgn hbe
        subst hgn_eq
        right
        simp [hbe_lu, hw_nz]
      · left
        have hg_eq : globN post gn.1 = globN s gn.1 := hlu gn.1 hbe
        unfold fixedObjects
        rw [List.append_assoc, List.append_assoc]
        apply List.mem_append_left
        rw [hg_eq]
        exact List.mem_map.2 ⟨gn, hgn, rfl⟩
    · left
      rw [hrest_eq] at hmr
      unfold fixedObjects
      rw [List.append_assoc, List.append_assoc]
      exact List.mem_append_right _ hmr
  have hhl_he : heapLimit ≤ heapEnd := by decide
  have hw_words : WordsOK post (w.toNat, 120) :=
    R10Shards.P26_P28.wordsOK_of_inside_heap hAp.1 hw8 (by decide) hwin.1
      (le_trans hwin.2 (le_trans hAs.2.2.1 hhl_he))
  have hF_post : FixedTyped post := by
    have hF := hWT.2.2.1
    refine ⟨?_, ?_⟩
    · intro o ho
      rcases hfix_sub o ho with hold | rfl
      · rcases hF.1 o hold with h0 | ⟨hal, hw_o⟩
        · exact Or.inl h0
        · exact Or.inr ⟨hag.allocated hal, R10Shards.Fast_GbodyC17ToC21.wordsOK_transfer hAs.1 hAp.1 hw_o⟩
      · exact Or.inr ⟨Or.inl (by rw [hhp_eq]; exact hwin), hw_words⟩
    · let rest_s := [(if globN s "journal_cap" = 0 then 0 else globN s "journal",
          32 * globN s "journal_cap")] ++ blockOutObjects s ++ balObjects s
      let rest_p := [(if globN post "journal_cap" = 0 then 0 else globN post "journal",
          32 * globN post "journal_cap")] ++ blockOutObjects post ++ balObjects post
      have hrest_eq : rest_p = rest_s := by
        simp only [rest_p, rest_s, hlu "journal" (by decide), hjc_eq, hbo_eq, hbal_eq]
      have hfix_s : fixedObjects s = (globalBuffers.map (bufferRegion s)) ++ rest_s := by
        simp only [fixedObjects, rest_s, List.append_assoc]; rfl
      have hfix_p : fixedObjects post = (globalBuffers.map (bufferRegion post)) ++ rest_p := by
        simp only [fixedObjects, rest_p, List.append_assoc]; rfl
      have hpair_s := hF.2
      rw [hfix_s] at hpair_s
      obtain ⟨hp_buf_s, hp_rest_s, hp_cross_s⟩ := List.pairwise_append.1 hpair_s
      have hp_names_s : globalBuffers.Pairwise (fun a b => Disj (bufferRegion s a) (bufferRegion s b)) :=
        List.pairwise_map.1 hp_buf_s
      have hgb_nodup : (globalBuffers.map (fun p => ofString p.1)).Nodup := by decide
      have hidx_ne : ∀ {i1 i2 : Nat} (hi1 : i1 < globalBuffers.length) (hi2 : i2 < globalBuffers.length),
          i1 < i2 → ofString globalBuffers[i1].1 ≠ ofString globalBuffers[i2].1 := by
        intro i1 i2 hi1 hi2 hlt heq
        have hnd := List.pairwise_iff_getElem.1 hgb_nodup
        have hi1' : i1 < (globalBuffers.map (fun p => ofString p.1)).length := by simp [hi1]
        have hi2' : i2 < (globalBuffers.map (fun p => ofString p.1)).length := by simp [hi2]
        exact hnd i1 i2 hi1' hi2' hlt (by simpa using heq)
      have hbuf_item : ∀ gn ∈ globalBuffers,
          (ofString gn.1 = ofString "be" ∧ bufferRegion post gn = (w.toNat, 120)) ∨
          (ofString gn.1 ≠ ofString "be" ∧ bufferRegion post gn = bufferRegion s gn) := by
        intro gn hgn
        by_cases hbe : ofString gn.1 = ofString "be"
        · left
          refine ⟨hbe, ?_⟩
          have hgn_eq := hgb_be gn hgn hbe
          subst hgn_eq
          simp [bufferRegion, hbe_lu, hw_nz]
        · right
          refine ⟨hbe, ?_⟩
          have hg_eq : globN post gn.1 = globN s gn.1 := hlu gn.1 hbe
          simp [bufferRegion, hg_eq]
      have hw_disj_fix_s : ∀ j ∈ fixedObjects s, Disj (w.toNat, 120) j := by
        intro j hj
        exact hw_ow (w.toNat, 120) (List.mem_singleton.2 rfl) j
          (List.mem_append_left _ (List.mem_append_right _ hj))
      rw [hfix_p, hrest_eq]
      refine List.pairwise_append.2 ⟨List.pairwise_map.2 ?_, hp_rest_s, ?_⟩
      · rw [List.pairwise_iff_getElem] at hp_names_s ⊢
        intro i1 i2 hi1 hi2 hlt
        have hne12 := hidx_ne hi1 hi2 hlt
        have ha_mem : globalBuffers[i1] ∈ globalBuffers := List.getElem_mem hi1
        have hb_mem : globalBuffers[i2] ∈ globalBuffers := List.getElem_mem hi2
        rcases hbuf_item globalBuffers[i1] ha_mem with ⟨ha_be, ha_eq⟩ | ⟨ha_nbe, ha_eq⟩
        · have hb_nbe : ofString globalBuffers[i2].1 ≠ ofString "be" :=
            fun hb_be => hne12 (ha_be.trans hb_be.symm)
          rcases hbuf_item globalBuffers[i2] hb_mem with ⟨hb_be, _⟩ | ⟨_, hb_eq⟩
          · exact absurd hb_be hb_nbe
          · rw [ha_eq, hb_eq]
            exact hw_disj_fix_s _ (by rw [hfix_s]; exact List.mem_append_left _ (List.mem_map.2 ⟨_, hb_mem, rfl⟩))
        · rcases hbuf_item globalBuffers[i2] hb_mem with ⟨_, hb_eq⟩ | ⟨_, hb_eq⟩
          · rw [ha_eq, hb_eq]
            exact (hw_disj_fix_s _ (by rw [hfix_s]; exact List.mem_append_left _ (List.mem_map.2 ⟨_, ha_mem, rfl⟩))).flip
          · rw [ha_eq, hb_eq]
            exact hp_names_s i1 i2 hi1 hi2 hlt
      · intro x hx y hy
        obtain ⟨gn, hgn, rfl⟩ := List.mem_map.1 hx
        rcases hbuf_item gn hgn with ⟨_, h_eq⟩ | ⟨_, h_eq⟩
        · rw [h_eq]
          exact hw_disj_fix_s y (by rw [hfix_s]; exact List.mem_append_right _ hy)
        · rw [h_eq]
          exact hp_cross_s _ (List.mem_map.2 ⟨gn, hgn, rfl⟩) y hy
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  have hwrs_eq : worldRoleSlots post = worldRoleSlots s :=
    R10Shards.P26_P28.worldRoleSlots_eq_of_unhit hAs.2 hT hF hcore
      (fun _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (fun _ _ _ _ _ _ => rfl) ⟨rfl, rfl⟩
  have hjr_part :=
    R10Shards.P26_P28.journalRoleSlots_eq_of_unhit hAs.1 hAp.1 hAs.2 hag
      (fun _ hx => hx) hJ hF hcore (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
  have hT_post : TablesTyped post S := by
    obtain ⟨hndS, hTt, hTp, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, hboT, hroles⟩ := hT
    refine ⟨hndS, ?_, hTp, ?_, ?_, ?_, ?_, ?_, ?_, hbalT, ?_, ?_⟩
    · intro t ht
      refine ⟨R10Shards.P26_P28.htabWF_congr_unhit hAs.1 hAp.1 (hTt t ht).1 (fun _ _ _ _ _ => rfl),
        fun i hi => ⟨hag.allocated ((hTt t ht).2 i hi).1, fun j hj => ?_⟩⟩
      rcases hfix_sub j hj with hold | rfl
      · exact ((hTt t ht).2 i hi).2 j hold
      · exact (hw_ow (w.toNat, 120) (List.mem_singleton.2 rfl) i
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨t, ht, hi⟩)))).flip
    · intro k hk hnz
      rw [hlu "ws" (by decide)] at hnz ⊢
      exact hwsR k hk hnz
    · intro k hk hnz
      rw [hlu "bs" (by decide)] at hnz ⊢
      exact hbsR k hk hnz
    · intro k hk hnz
      rw [hlu "ts" (by decide)] at hnz ⊢
      exact htsR k hk hnz
    · intro g hg
      have hne : ofString g ≠ ofString "be" := by
        simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl <;> decide
      rw [hlu g hne]
      exact hgR g hg
    · intro hnz hm
      rw [hlu "bs" (by decide)] at hnz hm ⊢
      exact hbsN hnz hm
    · intro hnz hm
      rw [hlu "ts" (by decide)] at hnz hm ⊢
      exact htsN hnz hm
    · intro hnz k hk hknz
      rw [hlu "bo" (by decide)] at hnz hknz ⊢
      exact hboT hnz k hk hknz
    · unfold RolesOK at hroles ⊢
      rw [hwrs_eq, hjr_part.1]
      exact hroles
  have hTr_post : TriesTypedWith post S Nd := by
    refine ⟨?_, ?_, ?_⟩
    · exact (R10Shards.P26_P28.nodeHeap_congr_bytes hAs.1 hAp.1 hag hTr.1
        (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl)).1
    · intro o ho
      have ho_s : o ∈ nodeExtents s Nd := ho
      refine ⟨(hTr.2.1 o ho_s).1, fun j hj => ?_⟩
      rcases hfix_sub j hj with hold | rfl
      · exact (hTr.2.1 o ho_s).2 j hold
      · exact (hw_ow (w.toNat, 120) (List.mem_singleton.2 rfl) o
          (List.mem_append_right _ ho_s)).flip
    · intro hnz
      rw [hlu "ws" (by decide)] at hnz ⊢
      exact hTr.2.2 hnz
  have hWT_post : WorldTypedWith post S Nd := ⟨hT_post, hjr_part.2, hF_post, hTr_post⟩
  have how_sub : ∀ o ∈ worldOwned post S Nd, o ∈ worldOwned s S Nd ∨ o = (w.toNat, 120) := by
    intro o ho
    unfold worldOwned at ho
    rcases List.mem_append.1 ho with h12 | hnd
    · rcases List.mem_append.1 h12 with htab | hfix
      · left
        exact List.mem_append_left _ (List.mem_append_left _ htab)
      · rcases hfix_sub o hfix with hold | rfl
        · left
          exact List.mem_append_left _ (List.mem_append_right _ hold)
        · exact Or.inr rfl
    · left
      exact List.mem_append_right _ hnd
  have hic_eq : inputCells post si = inputCells s si := rfl
  have hrc_eq : runAttemptCells post si = runAttemptCells s si := rfl
  have hrc_disj_post : IvlsDisj (runAttemptCells post si) (worldOwned post S Nd) := by
    rw [hrc_eq]
    intro c hc o ho
    rcases how_sub o ho with hold | rfl
    · exact h.2.2.1 c hc o hold
    · exact hw_rc c hc (w.toNat, 120) (List.mem_singleton.2 rfl)
  refine ⟨⟨⟨hAp, hWT_post, ?_, inputCells_disj_of_runAttemptCells hrc_disj_post,
    h.1.2.2.2.2.1, h.1.2.2.2.2.2.1, h.1.2.2.2.2.2.2⟩, ?_, hrc_disj_post, h.2.2.2.1, h.2.2.2.2⟩,
    ?_, hjc_eq, hbe_lu, hw_nz⟩
  · rw [hic_eq, hhp_eq]; exact h.1.2.2.1
  · rw [hrc_eq, hhp_eq]; exact h.2.1
  · intro b hb
    obtain ⟨b1, b2, bin, bw, bow⟩ := hbs b hb
    refine ⟨b1, b2, by rw [hhp_eq]; exact bin, bw, ?_⟩
    intro b' hb' o ho
    rw [List.mem_singleton.1 hb']
    rcases how_sub o ho with hold | rfl
    · exact bow b (List.mem_singleton.2 rfl) o hold
    · exact hw_bs b hb (w.toNat, 120) (List.mem_singleton.2 rfl)

theorem store_in_be_preserves_nullAndBlocks {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si off : Nat} {bs : List Ivl}
    {x : BitVec 64} {v : ValueHOL 64} {mem' : BitVec 64 → HolWordLab 64}
    (h : (InputAtNullWith Z) s S Nd si)
    (hbs : AllBlocksGood s S Nd bs)
    (hbe_nz : globN s "be" ≠ 0)
    (hoff8 : off % 8 = 0)
    (hoff_fit : off + 8 * (flattenHOL v).length ≤ 120)
    (hdst : evalAt s (.op .add [.var .global (ofString "be"), .const (BitVec.ofNat 64 off)]) =
      some (.val (.word x)))
    (hst : @panMemStoresHOL 64 _ x (flattenHOL v) s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem') :
    let post := { s with memory := mem' }
    (InputAtNullWith Z) post S Nd si ∧
      AllBlocksGood post S Nd bs ∧
      globN post "journal_cap" = globN s "journal_cap" ∧
      globN post "be" = globN s "be" ∧
      (∀ b : Ivl, (b.2 = 0 → b.1 % 8 = 0) → Disj b (globN s "be", 120) →
        R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post b) := by
  intro post
  have hAs : ArenaReady s := h.1.1
  have hWT : WorldTypedWith s S Nd := h.1.2.1
  have hbe_gb : ("be", 120) ∈ globalBuffers := by decide
  have hbe_untr : "be" ∉ typedRecords.map Prod.fst := by decide
  have hbuf_eq : bufferRegion s ("be", 120) = (globN s "be", 120) := by
    simp [bufferRegion, hbe_nz]
  have hmem_fix : (globN s "be", 120) ∈ fixedObjects s := by
    unfold fixedObjects
    rw [List.append_assoc, List.append_assoc]
    apply List.mem_append_left
    exact List.mem_map.2 ⟨("be", 120), hbe_gb, hbuf_eq⟩
  have hbe_alloc : Allocated s (globN s "be", 120) ∧ WordsOK s (globN s "be", 120) := by
    rcases hWT.2.2.1.1 _ hmem_fix with h0 | hh
    · simp at h0
    · exact hh
  have hbe_hi : globN s "be" + 120 ≤ 2 ^ 64 := by
    have := (R10Shards.Fast_GbodyC17ToC21.ivl_allocated_bound hAs.2 hbe_alloc.1).2
    dsimp at this; exact this
  have hbe_lo : sourceBase ≤ globN s "be" := by
    rcases hbe_alloc.1 with ⟨hlo, _⟩ | ⟨hlo, _⟩
    · exact hlo
    · have : sourceBase ≤ heapLimit := hAs.2.1.trans hAs.2.2.1
      have : heapLimit ≤ globN s "frame_mem_ptr" := hAs.2.2.2.1
      have : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hAs.2.2.2.2.1
      dsimp at hlo; omega
  have hbe8 : (globN s "be") % 8 = 0 := hbe_alloc.2.1
  obtain ⟨w_be, hbe_g⟩ := hAs.2.2.2.2.2.2.2.2.2 "be" (by decide)
  have hbe_g' : s.globals.lookup (ofString "be") = some (.val (.word w_be)) := hbe_g
  have hw_be_nat : w_be.toNat = globN s "be" := by simp [globN, hbe_g']
  have hx_eq : x = w_be + BitVec.ofNat 64 off := by
    simp only [evalAt, evalHOLExact, evalListHOLExact] at hdst
    rw [hbe_g'] at hdst
    simp only [List.all_cons, List.all_nil, Bool.and_self, valueIsWord, ↓reduceIte,
      List.map, valueWord, wordOpHOL, wordOp, List.foldr, add_zero, Option.map, Option.some.injEq,
      ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst
    exact hdst.symm
  have hx_nat : x.toNat = globN s "be" + off := by
    rw [hx_eq, BitVec.toNat_add, hw_be_nat, BitVec.toNat_ofNat]
    have hoff_lt : off < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hoff_lt]
    exact Nat.mod_eq_of_lt (show globN s "be" + off < 2 ^ 64 by
      have : globN s "be" + 120 < 2 ^ 64 :=
        lt_of_le_of_lt (R10Shards.Fast_GbodyC17ToC21.ivl_allocated_bound hAs.2 hbe_alloc.1).1
          (by decide : heapEnd < 2 ^ 64)
      omega)
  have hframe : FrameOutside s post [(globN s "be", 120)] (0, 0) := by
    intro a hkeep _
    apply panMemStoresHOL_frame (flattenHOL v) x s.memory mem' hst a
    intro k hk h_eq
    apply hkeep (globN s "be", 120) (by simp)
    have ha_nat : a.toNat = globN s "be" + off + 8 * k := by
      rw [h_eq, BitVec.toNat_add, hx_nat, BitVec.toNat_ofNat]
      have hk_lt : 8 * k < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hk_lt]
      simpa [Nat.add_assoc] using Nat.mod_eq_of_lt (show globN s "be" + off + 8 * k < 2 ^ 64 by
        have : globN s "be" + 120 < 2 ^ 64 :=
          lt_of_le_of_lt (R10Shards.Fast_GbodyC17ToC21.ivl_allocated_bound hAs.2 hbe_alloc.1).1
            (by decide : heapEnd < 2 ^ 64)
        omega)
    unfold CellHits
    rw [ha_nat]
    exact ⟨by omega, by omega⟩
  have hcond := nullAndBlocks_bufferRegion_conditions h hbs ("be", 120) hbe_gb hbe_untr (by decide)
  rw [hbuf_eq] at hcond
  have hWT_res := R10Shards.Fast_GbodyC17ToC21.worldTypedWith_store_range_disj (post := post)
    hAs hbe8 (by decide) hbe_lo
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, hframe⟩ hWT
    (fun j hj => (hcond.2.1 (globN s "be", 120) (by simp) j hj).flip)
  have hdisj_unhit : ∀ b : Ivl, (b.2 = 0 → b.1 % 8 = 0) → Disj b (globN s "be", 120) →
      R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post b := by
    intro b hbz hdb
    exact R10Shards.Fast_GbodyC17ToC21.ivlUnhit_of_frameOutside_aligned hframe hbz
      (fun j hj => by rw [List.mem_singleton.1 hj]; exact ⟨hbe8, show 120 % 8 = 0 by decide⟩)
      ⟨by decide, by decide⟩
      (fun j hj => by rw [List.mem_singleton.1 hj]; exact hdb)
      (R10Shards.Fast_GbodyC17ToC21.disj_zero_right b)
  have hu_rc : ∀ c ∈ runAttemptCells s si, R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post c :=
    fun c hc => hdisj_unhit c (fun _ => (h.2.1 c hc).1)
      (hcond.2.2.1 c hc (globN s "be", 120) (by simp))
  have h_in_surv : ∀ c ∈ inputCells s si, R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post c :=
    fun c hc => hdisj_unhit c (fun _ => (h.1.2.2.1 c hc).2.1)
      ((inputCells_disj_of_runAttemptCells hcond.2.2.1) c hc (globN s "be", 120) (by simp))
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
  have hcells := h.1.2.2.1
  have hsi_mem : (si, 40) ∈ inputCells s si := by simp [inputCells]
  obtain ⟨hsi_in_s, hsi_w_s⟩ := hcells (si, 40) hsi_mem
  have hsi_u := h_in_surv (si, 40) hsi_mem
  have hsi_eq0 : memW post si = memW s si :=
    R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit hsi_u hsi_w_s.1
      (by unfold Inside at hsi_in_s; omega) ⟨le_rfl, by omega⟩
  have hsi_eq32 : memW post (si + 32) = memW s (si + 32) :=
    R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit hsi_u (by have := hsi_w_s.1; omega)
      (by unfold Inside at hsi_in_s; omega) ⟨by omega, by omega⟩
  set pl := memW s si
  set rq := memW s (si + 32)
  have hpl_mem : (pl, 136) ∈ inputCells s si := by simp [inputCells, pl]
  obtain ⟨hpl_in_s, hpl_w_s⟩ := hcells (pl, 136) hpl_mem
  have hpl_u := h_in_surv (pl, 136) hpl_mem
  have hpl_word : ∀ off', off' % 8 = 0 → off' + 8 ≤ 136 → memW post (pl + off') = memW s (pl + off') :=
    fun off' hoff8' hoff_hi =>
      R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit hpl_u (by have := hpl_w_s.1; omega)
        (by unfold Inside at hpl_in_s; omega) ⟨by omega, by omega⟩
  have hpl24 : memW post (pl + 24) = memW s (pl + 24) := hpl_word 24 (by omega) (by omega)
  have hpl32 : memW post (pl + 32) = memW s (pl + 32) := hpl_word 32 (by omega) (by omega)
  have hpl40 : memW post (pl + 40) = memW s (pl + 40) := hpl_word 40 (by omega) (by omega)
  have hic_eq : inputCells post si = inputCells s si := by
    simp only [inputCells, hsi_eq0, hsi_eq32]
    change [(si, 40), (pl, 136), (rq, 80), (memW post (pl + 32), 16 * memW post (pl + 40))] =
           [(si, 40), (pl, 136), (rq, 80), (memW s (pl + 32), 16 * memW s (pl + 40))]
    rw [hpl32, hpl40]
  have hrq_mem : (rq, 80) ∈ inputCells s si := by simp [inputCells, rq]
  obtain ⟨hrq_in_s, hrq_w_s⟩ := hcells (rq, 80) hrq_mem
  have hrq_u := h_in_surv (rq, 80) hrq_mem
  have hptxs_mem : (memW s (pl + 32), 16 * memW s (pl + 40)) ∈ inputCells s si := by
    simp [inputCells, pl]
  obtain ⟨hptxs_in_s, hptxs_w_s⟩ := hcells _ hptxs_mem
  have hptxs_u := h_in_surv _ hptxs_mem
  have hIA' : (InputAtWithZ Z) post S Nd si := by
    refine ⟨hWT_res.1, hWT_res.2.1, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hic_eq]
      exact fun i hi => ⟨(hcells i hi).1,
        R10Shards.Fast_GbodyC17ToC21.wordsOK_transfer hAs.1 hWT_res.1.1 (hcells i hi).2⟩
    · rw [hic_eq, hWT_res.2.2.1]; exact h.1.2.2.2.1
    · rw [hsi_eq0, hpl40]; exact h.1.2.2.2.2.1
    · rw [hsi_eq0]
      refine ⟨R10Shards.Fast_GbodyC17ToC21.wordsOK_transfer hAs.1 hWT_res.1.1 h.1.2.2.2.2.2.1.1,
        by rw [hpl24]; exact h.1.2.2.2.2.2.1.2.1,
        by rw [hpl40]; exact h.1.2.2.2.2.2.1.2.2.1, ?_⟩
      rw [hpl32, hpl40]
      intro idx hidx
      have hcell_eq : memW post (memW s (pl + 32) + 16 * idx + 8) =
          memW s (memW s (pl + 32) + 16 * idx + 8) :=
        R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit hptxs_u
          (by have := hptxs_w_s.1; omega) (by unfold Inside at hptxs_in_s; omega)
          ⟨by dsimp; omega, by dsimp; omega⟩
      rw [hcell_eq]; exact h.1.2.2.2.2.2.1.2.2.2 idx hidx
    · rw [hsi_eq32]
      refine ⟨R10Shards.Fast_GbodyC17ToC21.wordsOK_transfer hAs.1 hWT_res.1.1 h.1.2.2.2.2.2.2.1,
        fun idx hidx => ?_⟩
      have hcell_eq : memW post (rq + 16 * idx + 8) = memW s (rq + 16 * idx + 8) :=
        R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit hrq_u
          (by have := hrq_w_s.1; omega) (by unfold Inside at hrq_in_s; omega) ⟨by omega, by omega⟩
      rw [hcell_eq]; exact h.1.2.2.2.2.2.2.2 idx hidx
  have hrc_eq : runAttemptCells post si = runAttemptCells s si :=
    runAttemptCells_eq_of_unhit (inputAtNullWith_strong h) hu_rc
  have hrc_disj : IvlsDisj (runAttemptCells post si) (worldOwned post S Nd) := by
    rw [hrc_eq, hWT_res.2.2.1]; exact h.2.2.1
  have hsi_eq16 : memW post (si + 16) = memW s (si + 16) :=
    R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit hsi_u (by have := hsi_w_s.1; omega)
      (by unfold Inside at hsi_in_s; omega) ⟨by omega, by omega⟩
  have hpl56 : memW post (pl + 56) = memW s (pl + 56) := hpl_word 56 (by omega) (by omega)
  refine ⟨⟨hIA', ?_, hrc_disj, ?_, ?_⟩, ?_, rfl, rfl, hdisj_unhit⟩
  · rw [hrc_eq]
    exact fun c hc => ⟨(h.2.1 c hc).1, (h.2.1 c hc).2.1,
      R10Shards.Fast_GbodyC17ToC21.wordsOK_transfer hAs.1 hWT_res.1.1 (h.2.1 c hc).2.2⟩
  · rw [hsi_eq16]; exact h.2.2.2.1
  · rw [hsi_eq0, hpl56]; exact h.2.2.2.2
  · intro b hb
    obtain ⟨b1, b2, bin, bw, bow⟩ := hbs b hb
    refine ⟨b1, b2, bin, R10Shards.Fast_GbodyC17ToC21.wordsOK_transfer hAs.1 hWT_res.1.1 bw, ?_⟩
    rw [hWT_res.2.2.1]; exact bow

private theorem evalAt_load_one_word {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hg : GuestInv s) {addr : ExpHOL 64} {v : ValueHOL 64}
    (hev : evalAt s (.load .one addr) = some v) :
    ∃ a w : BitVec 64, evalAt s addr = some (.val (.word a)) ∧
      v = .val (.word w) ∧ w.toNat = memW s a.toNat ∧
      a.toNat % 8 = 0 ∧ sourceBase ≤ a.toNat ∧ a.toNat < heapEnd := by
  simp only [evalAt, evalHOLExact] at hev
  rcases ha : @evalHOLExact 64 F _ s.toExact
      (fun address => Classical.propDecidable (s.memaddrs address)) addr with _ | va
  · rw [ha] at hev; simp at hev
  · rw [ha] at hev
    cases va with
    | val wl =>
      cases wl with
      | word a =>
        simp only [memLoadHOLExact] at hev
        split_ifs at hev with _ hdom
        simp only [Option.some.injEq] at hev
        rw [hg.memaddrs, ordinaryDomain_iff] at hdom
        cases hmem : s.memory a with
        | word w =>
          rw [hmem] at hev
          have hmemW : memW s a.toNat = w.toNat := by
            unfold memW; simp [BitVec.ofNat_toNat, hmem]
          exact ⟨a, w, ha, hev.symm, hmemW.symm, hdom.1, hdom.2.1, hdom.2.2⟩
    | rStruct _ => simp at hev
    | nStruct _ => simp at hev

private theorem evalAt_add2_words {F : Type} {s : PanSemStateFiniteExact 64 F}
    {e1 e2 : ExpHOL 64} {x : BitVec 64}
    (hev : evalAt s (.op .add [e1, e2]) = some (.val (.word x))) :
    ∃ w1 w2 : BitVec 64, evalAt s e1 = some (.val (.word w1)) ∧
      evalAt s e2 = some (.val (.word w2)) ∧ x = w1 + w2 := by
  simp only [evalAt, evalHOLExact, evalListHOLExact] at hev
  rcases h1 : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
  · rw [h1] at hev; simp at hev
  · rw [h1] at hev
    rcases h2 : @evalHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | v2
    · rw [h2] at hev; simp at hev
    · rw [h2] at hev; dsimp only at hev
      rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> try simp [valueIsWord] at hev
      rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;> try simp at hev
      simp only [valueWord, wordOpHOL, wordOp, List.foldr, add_zero, Option.some.injEq] at hev
      exact ⟨w1, w2, h1, h2, hev.symm⟩

theorem callEntryOn_blockReadyExecAttemptNull :
    CallEntryOn (BlockReadyExecAttemptNull Z) (BlockReadyExecAttemptNull Z) (ofString "execute_block")
      [.var .local (ofString "si"), .var .local (ofString "hdr")] := by
  intro F s values body callee ret hcode hP hargs hl
  cases hsi : s.locals.lookup (ofString "si") with
  | none =>
    rw [evalListHOLFinite_eq_toExact] at hargs
    simp [evalListHOLExact, evalHOLExact, hsi] at hargs
  | some vsi =>
    cases hhdr : s.locals.lookup (ofString "hdr") with
    | none =>
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp [evalListHOLExact, evalHOLExact, hsi, hhdr] at hargs
    | some vhdr =>
      have hp := callee_param_two s (ofString "execute_block")
        (ofString "si") (ofString "hdr") .one .one _ _
        (by rw [hcode]; exact GuestTrapAndLookup.lookup_execute_block)
        (.var .local (ofString "si")) (.var .local (ofString "hdr"))
        vsi vhdr values body callee ret
        (by simpa [evalAt, evalHOLExact] using hsi)
        (by simpa [evalAt, evalHOLExact] using hhdr) hargs hl
      exact localsOnly_blockReadyExecAttemptNull s callee (s.clock - 1)
        (fun n hn => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
          rcases hn with rfl | rfl
          · exact hp.2.1.trans hsi.symm
          · exact hp.2.2.trans hhdr.symm) hP

private def AnyState {F : Type} (_ : PanSemStateFiniteExact 64 F) : Prop := True

theorem runAttemptExecuteTail_bounded
    (he : TerminatingFunBoundedOn (BlockReadyExecAttemptNull Z)
      (ofString "execute_block") K.«execute_block») :
    TerminatingProgBoundedOn (BlockReadyExecAttemptNull Z) runAttemptExecuteTail
      (K.«execute_block» + 1) := by
  have hret : TerminatingProgBoundedOn AnyState
      (.seq .skip (.return (.const 0#64))) (0 + 0) :=
    TerminatingProgBoundedOn.seq_hoare (P := AnyState)
      (TerminatingProgBoundedOn.of_clock (P := AnyState) clock_skip)
      (Hoare.skip (P := AnyState) (fun _ _ _ => True.intro))
      (TerminatingProgBoundedOn.of_clock (P := AnyState)
        (fun s => clock_return s (.const 0#64)))
  have hcall : TerminatingProgBoundedOn (BlockReadyExecAttemptNull Z)
      (.seq (.call (some (none, none)) (ofString "execute_block")
        [.var .local (ofString "si"), .var .local (ofString "hdr")])
        (.seq .skip (.return (.const 0#64))))
      ((K.«execute_block» + 1) + (0 + 0)) :=
    TerminatingProgBoundedOn.seq_hoare_trans
      (P := (BlockReadyExecAttemptNull Z)) (Q := AnyState)
      (TerminatingProgBoundedOn.call_on he none _ callEntryOn_blockReadyExecAttemptNull)
      ⟨fun _ _ _ _ _ => True.intro⟩
      hret
  unfold runAttemptExecuteTail
  intro F s hc hp
  exact TerminatingProgBoundedOn.mono_bound (P := (BlockReadyExecAttemptNull Z))
    (a := 0 + ((K.«execute_block» + 1) + (0 + 0)))
    (b := K.«execute_block» + 1)
    (TerminatingProgBoundedOn.seq_hoare (P := (BlockReadyExecAttemptNull Z))
      (TerminatingProgBoundedOn.of_clock (P := (BlockReadyExecAttemptNull Z)) clock_skip)
      (Hoare.skip (P := (BlockReadyExecAttemptNull Z)) (fun _ h _ => h)) hcall)
    (by omega) s hc hp

def RunAttemptPreBe (Z : Prop) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ w_si w_hdr : BitVec 64, ∃ S Nd : List Nat,
    (InputAtNullWith Z) s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_hdr.toNat, 248)] ∧
    HeaderAt s w_hdr.toNat ∧
    globN s "journal_cap" ≠ 0 ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr))

def RunAttemptHasBe (Z : Prop) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ w_si w_hdr : BitVec 64, ∃ S Nd : List Nat,
    (InputAtNullWith Z) s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_hdr.toNat, 248)] ∧
    HeaderAt s w_hdr.toNat ∧
    globN s "journal_cap" ≠ 0 ∧
    globN s "be" ≠ 0 ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr))

theorem localsOnly_runAttemptPreBe : LocalsOnly ["si", "hdr"] (RunAttemptPreBe Z) := by
  intro F s locals k hl hP
  obtain ⟨w_si, w_hdr, S, Nd, hIA, hBs, hHdr, hjc, hsi, hhdr⟩ := hP
  exact ⟨w_si, w_hdr, S, Nd,
    (inputAtNullWith_with_locals s locals k S Nd w_si.toNat).2 hIA,
    (allBlocksGood_with_locals s locals k S Nd [(w_hdr.toNat, 248)]).2 hBs,
    hHdr, hjc,
    (hl "si" (by simp)).trans hsi,
    (hl "hdr" (by simp)).trans hhdr⟩

theorem localsOnly_runAttemptHasBe : LocalsOnly ["si", "hdr"] (RunAttemptHasBe Z) := by
  intro F s locals k hl hP
  obtain ⟨w_si, w_hdr, S, Nd, hIA, hBs, hHdr, hjc, hbe, hsi, hhdr⟩ := hP
  exact ⟨w_si, w_hdr, S, Nd,
    (inputAtNullWith_with_locals s locals k S Nd w_si.toNat).2 hIA,
    (allBlocksGood_with_locals s locals k S Nd [(w_hdr.toNat, 248)]).2 hBs,
    hHdr, hjc, hbe,
    (hl "si" (by simp)).trans hsi,
    (hl "hdr" (by simp)).trans hhdr⟩

theorem runAttemptPreBe_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : (RunAttemptPreBe Z) s) : GuestInv s := by
  obtain ⟨_, _, _, _, hIA, _⟩ := h
  exact hIA.1.1.1

theorem runAttemptPreBe_inputReadyNull {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : (RunAttemptPreBe Z) s) : (InputReadyNull Z) s := by
  obtain ⟨w_si, _, S, Nd, hIA, _, _, _, hsi, _⟩ := h
  have heq : locN s "si" = w_si.toNat := by simp [locN, hsi]
  unfold InputReadyNull
  rw [heq]
  exact inputAtNullWith_strong hIA

theorem runAttemptPreBe_worldOK {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : (RunAttemptPreBe Z) s) : WorldOK s :=
  inputReadyNull_worldOK s (runAttemptPreBe_inputReadyNull h)

theorem runAttemptPreBe_blockReadyExecNull {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : (RunAttemptPreBe Z) s) : (BlockReadyExecAttemptNull Z) s := by
  have hIR := runAttemptPreBe_inputReadyNull h
  obtain ⟨_, w_hdr, _, _, _, _, hHdr, hjc, _, hhdr⟩ := h
  exact blockReadyExecNull_of s hIR (by simpa [locN, hhdr] using hHdr) hjc

theorem runAttemptHasBe_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : (RunAttemptHasBe Z) s) : GuestInv s := by
  obtain ⟨_, _, _, _, hIA, _⟩ := h
  exact hIA.1.1.1

theorem runAttemptHasBe_blockReadyExecNull {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : (RunAttemptHasBe Z) s) : (BlockReadyExecAttemptNull Z) s := by
  obtain ⟨w_si, w_hdr, S, Nd, hIA, _, hHdr, hjc, _, hlsi, hlhdr⟩ := h
  have hsi_eq : locN s "si" = w_si.toNat := by simp [locN, hlsi]
  have hhdr_eq : locN s "hdr" = w_hdr.toNat := by simp [locN, hlhdr]
  have hIRS : (InputReadyNull Z) s := by
    unfold InputReadyNull
    rw [hsi_eq]
    exact inputAtNullWith_strong hIA
  exact blockReadyExecNull_of s hIRS (by rwa [hhdr_eq]) hjc

theorem runAttemptPreBe_worldStep
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hP : (RunAttemptPreBe Z) s) (hw : WorldStep R gw keep Q s r post)
    (hz : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (ht : ∀ S Nd si, (InputAtNullWith Z) s S Nd si →
      IvlsDisj (R s) (worldTypedIvls s S Nd))
    (hc : ∀ si, (InputAtNull Z) s si → IvlsDisj (runAttemptCells s si) (R s))
    (hb : ∀ h, HeaderAt s h →
      Inside (h, 248) sourceBase (globN s "heap_ptr") →
      IvlsDisj [(h, 248)] (R s))
    (hj : ofString "journal_cap" ∉ gw.map ofString) :
    (RunAttemptPreBe Z) { post with locals := s.locals } := by
  obtain ⟨w_si, w_hdr, S, Nd, hIA, hBs, hHdr, hjc, hsi, hhdr⟩ := hP
  have hgood := hBs (w_hdr.toNat, 248) (by simp)
  obtain ⟨S', Nd', hIA', hBs', _, _, hub, _⟩ :=
    worldStep_preserves_nullAndBlocks hIA hBs hw hz (ht S Nd w_si.toNat hIA)
      (hc w_si.toNat (inputAtNullWith_strong hIA)) (hb w_hdr.toNat hHdr hgood.2.2.1)
  have hlim : heapLimit ≤ 2 ^ 64 := by decide
  have hhp : globN s "heap_ptr" ≤ heapLimit := hIA.1.1.2.2.1
  have hHdr' : HeaderAt post w_hdr.toNat :=
    headerAt_of_unhit hIA.1.1.1 hIA'.1.1.1
      (by have hi := hgood.2.2.1; unfold Inside at hi; omega)
      (hub (w_hdr.toNat, 248) (by simp)) hHdr
  have hjc' : globN post "journal_cap" = globN s "journal_cap" :=
    globN_eq_of_lookup (hw.2.2.1 (ofString "journal_cap") hj)
  refine ⟨w_si, w_hdr, S', Nd',
    (inputAtNullWith_with_locals post s.locals post.clock S' Nd' w_si.toNat).2 hIA',
    (allBlocksGood_with_locals post s.locals post.clock S' Nd' [(w_hdr.toNat, 248)]).2 hBs',
    hHdr', ?_, hsi, hhdr⟩
  change globN post "journal_cap" ≠ 0
  rwa [hjc']

theorem hoare_alloc_be_120
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    Hoare (RunAttemptPreBe Z)
      (.call (some (some (.global, ofString "be"), none)) (ofString "alloc") [.const 120#64])
      (fun r t => r = none → (RunAttemptHasBe Z) t) := by
  refine ⟨fun {F} state hcode hPre _ hr => ?_⟩
  rcases hcall : evaluateHOLFiniteState state
      (.call (some (some (.global, ofString "be"), none)) (ofString "alloc") [.const 120#64]) with
    ⟨cres, cpost⟩
  have hr' : cres = none := by rw [hcall] at hr; exact hr
  subst hr'
  obtain ⟨w_si, w_hdr, S, Nd, hIA, hBs, hHdr, hjc, hlsi, hlhdr⟩ := hPre
  have hAs : ArenaReady state := hIA.1.1
  have hW_state : WorldOK state := ⟨hAs, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.1.2.1⟩⟩
  rw [evaluateHOLFiniteState_call] at hcall
  have hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.const 120#64] = some [.val (.word 120#64)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, evalHOLExact]
  rw [hargs] at hcall; dsimp only at hcall
  rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "alloc")
      [.val (.word 120#64)] with _ | ⟨body, callee, ret⟩
  · rw [hl] at hcall; simp at hcall
  · rw [hl] at hcall; dsimp only at hcall
    split_ifs at hcall with hz
    · simp at hcall
    · rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨bres, post⟩
      rw [hrun] at hcall
      cases bres with
      | none => simp at hcall
      | some br =>
        cases br with
        | returned v =>
          dsimp only at hcall
          split_ifs at hcall with hsh hvalid
          · obtain ⟨_, hpost_eq⟩ := Prod.mk.inj hcall
            have hpc := callee_param_one_exp state (ofString "alloc") (ofString "n") .one _ _
              (by rw [hcode]; exact lookup_alloc_fn) (.const 120#64) (.val (.word 120#64))
              [.val (.word 120#64)] body callee ret rfl hargs hl
            set entry := callEntryStateHOLFinite state callee
            have hn_loc : locN entry "n" = 120 := by
              simp [entry, locN, callEntryStateHOLFinite, hpc.2]
            have hstep := FunSpec.at_lookup wal state hcode _ body callee ret hl
              (localsFree_worldOK state callee (state.clock - 1) hW_state) (by rw [hrun]; simp)
            rw [hrun] at hstep; dsimp only at hstep
            have hws := hstep (Or.inl ⟨v, rfl⟩)
            have hrt := FunSpec.at_lookup rtal state hcode _ body callee ret hl
              (localsFree_arenaReady state callee (state.clock - 1) hAs) (by rw [hrun]; simp)
            rw [hrun] at hrt; dsimp only at hrt
            obtain ⟨w_be, rfl, _, _, hfb⟩ := hrt v rfl
            rw [hn_loc] at hfb
            have hfb_in : Inside (w_be.toNat, 120) (globN state "heap_ptr") (globN post "heap_ptr") :=
              hfb.2.1
            have hIA_entry : (InputAtNullWith Z) entry S Nd w_si.toNat :=
              (inputAtNullWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
            have hBs_entry : AllBlocksGood entry S Nd [(w_hdr.toNat, 248)] :=
              (allBlocksGood_with_locals state callee (state.clock - 1) S Nd [(w_hdr.toNat, 248)]).2 hBs
            obtain ⟨S', Nd', hIA_post, hBs_post, _, hu_rc, hu_bs, _, _, hQ⟩ :=
              worldStep_preserves_nullAndBlocks hIA_entry hBs_entry hws
                (fun _ hj => by simp at hj) (fun _ hj => by simp at hj)
                (fun _ _ _ hj => by simp at hj) (fun _ _ _ hj => by simp at hj)
            obtain ⟨w_be', hw_eq, hav⟩ := hQ (.val (.word w_be)) rfl
            injection hw_eq with hw_eq'; injection hw_eq' with hw_eq''; subst hw_eq''
            dsimp only at hav; rw [hn_loc] at hav
            have hjc_post : globN post "journal_cap" = globN state "journal_cap" := by
              exact globN_eq_of_lookup (s := state) (post := post)
                (hws.2.2.1 (ofString "journal_cap") (by decide))
            have hrc_eq : runAttemptCells post w_si.toNat = runAttemptCells state w_si.toNat :=
              runAttemptCells_eq_of_unhit (inputAtNullWith_strong hIA) hu_rc
            have h264 : heapLimit ≤ 2 ^ 64 := by decide
            have hhp_lim : globN state "heap_ptr" ≤ heapLimit := hAs.2.2.1
            have hhdr_in := (hBs (w_hdr.toNat, 248) (by simp)).2.2.1
            have hHdr_post : HeaderAt post w_hdr.toNat :=
              headerAt_of_unhit hAs.1 hIA_post.1.1.1 (by unfold Inside at hhdr_in; omega)
                (hu_bs (w_hdr.toNat, 248) (by simp)) hHdr
            have hw_rc : IvlsDisj (runAttemptCells post w_si.toNat) [(w_be.toNat, 120)] := by
              rw [hrc_eq]
              intro c hc b hb
              rw [List.mem_singleton.1 hb]
              have hc_in := (hIA.2.1 c hc).2.1
              unfold Inside at hc_in hfb_in
              unfold Disj; dsimp only at hc_in hfb_in ⊢; omega
            have hw_bs : IvlsDisj [(w_hdr.toNat, 248)] [(w_be.toNat, 120)] := by
              intro b1 hb1 b2 hb2
              rw [List.mem_singleton.1 hb1, List.mem_singleton.1 hb2]
              unfold Inside at hhdr_in hfb_in
              unfold Disj; dsimp only at hhdr_in hfb_in ⊢; omega
            set resumed0 := { post with locals := state.locals }
            have hIA_res0 : (InputAtNullWith Z) resumed0 S' Nd' w_si.toNat :=
              (inputAtNullWith_with_locals post state.locals post.clock S' Nd' w_si.toNat).2 hIA_post
            have hBs_res0 : AllBlocksGood resumed0 S' Nd' [(w_hdr.toNat, 248)] :=
              (allBlocksGood_with_locals post state.locals post.clock S' Nd' [(w_hdr.toNat, 248)]).2 hBs_post
            have hbe_step := nullAndBlocks_setGlobal_be (w := w_be) hIA_res0 hBs_res0 hfb.1
              ⟨Nat.le_trans hAs.2.1 hfb_in.1, hfb_in.2⟩ hav hw_rc hw_bs
            set resumed := setGlobalHOLFinite (ofString "be") (.val (.word w_be)) resumed0
            have hRes : (RunAttemptHasBe Z) resumed := by
              refine ⟨w_si, w_hdr, S', Nd', hbe_step.1, hbe_step.2.1, hHdr_post, ?_, ?_, hlsi, hlhdr⟩
              · rw [hbe_step.2.2.1]; change globN post "journal_cap" ≠ 0; rwa [hjc_post]
              · rw [hbe_step.2.2.2.1]; exact hbe_step.2.2.2.2
            simpa [resumed, resumed0, setKvarHOLFinite] using hpost_eq ▸ hRes
          · simp at hcall
          · simp at hcall
        | _ => simp [emptyLocalsHOLFinite] at hcall

theorem hoare_memzero_be_120
    (wmz : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")]) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memzero")) :
    Hoare (RunAttemptHasBe Z)
      (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "be"), .const 120#64])
      (fun r t => r = none → (RunAttemptHasBe Z) t) := by
  refine ⟨fun {F} state hcode hHas _ hr => ?_⟩
  rcases hcall : evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "be"), .const 120#64]) with
    ⟨cres, cpost⟩
  have hr' : cres = none := by rw [hcall] at hr; exact hr
  subst hr'
  obtain ⟨w_si, w_hdr, S, Nd, hIA, hBs, hHdr, hjc, hbe_nz, hlsi, hlhdr⟩ := hHas
  have hAs : ArenaReady state := hIA.1.1
  have hW_state : WorldOK state := ⟨hAs, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.1.2.1⟩⟩
  obtain ⟨w_be, hbe_g⟩ := hAs.2.2.2.2.2.2.2.2.2 "be" (by decide)
  have hbe_g' : state.globals.lookup (ofString "be") = some (.val (.word w_be)) := hbe_g
  have hw_be_nat : w_be.toNat = globN state "be" := by simp [globN, hbe_g']
  rw [evaluateHOLFiniteState_call] at hcall
  have hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .global (ofString "be"), .const 120#64] = some [.val (.word w_be), .val (.word 120#64)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, evalHOLExact, hbe_g']
  rw [hargs] at hcall; dsimp only at hcall
  rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "memzero")
      [.val (.word w_be), .val (.word 120#64)] with _ | ⟨body, callee, ret⟩
  · rw [hl] at hcall; simp at hcall
  · rw [hl] at hcall; dsimp only at hcall
    split_ifs at hcall with hz
    · simp at hcall
    · rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨bres, post⟩
      rw [hrun] at hcall
      cases bres with
      | none => simp at hcall
      | some br =>
        cases br with
        | returned v =>
          dsimp only at hcall
          split_ifs at hcall with hsh
          · obtain ⟨_, hpost_eq⟩ := Prod.mk.inj hcall
            have hpc := callee_param_two state (ofString "memzero") (ofString "dst") (ofString "n")
              .one .one _ _ (by rw [hcode]; exact lookup_memzero_fn)
              (.var .global (ofString "be")) (.const 120#64)
              (.val (.word w_be)) (.val (.word 120#64))
              [.val (.word w_be), .val (.word 120#64)] body callee ret
              (by simpa [evalAt, evalHOLExact] using hbe_g') rfl hargs hl
            set entry := callEntryStateHOLFinite state callee
            have hdst : locN entry "dst" = globN state "be" := by
              simp [entry, locN, callEntryStateHOLFinite, hpc.2.1, hw_be_nat]
            have hn_loc : locN entry "n" = 120 := by
              simp [entry, locN, callEntryStateHOLFinite, hpc.2.2]
            have hstep := FunSpec.at_lookup wmz state hcode _ body callee ret hl
              (localsFree_worldOK state callee (state.clock - 1) hW_state) (by rw [hrun]; simp)
            rw [hrun] at hstep; dsimp only at hstep
            have hws := hstep (Or.inl ⟨v, rfl⟩)
            have hIA_entry : (InputAtNullWith Z) entry S Nd w_si.toNat :=
              (inputAtNullWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
            have hBs_entry : AllBlocksGood entry S Nd [(w_hdr.toNat, 248)] :=
              (allBlocksGood_with_locals state callee (state.clock - 1) S Nd [(w_hdr.toNat, 248)]).2 hBs
            have hcond := nullAndBlocks_bufferRegion_conditions hIA_entry hBs_entry
              ("be", 120) (by decide) (by decide) (by decide)
            have hbuf_eq : bufferRegion entry ("be", 120) = (locN entry "dst", locN entry "n") := by
              change bufferRegion state ("be", 120) = _
              rw [hdst, hn_loc]; simp [bufferRegion, hbe_nz]
            rw [hbuf_eq] at hcond
            obtain ⟨S', Nd', hIA_post, hBs_post, _, hu_rc, hu_bs, _, _, _⟩ :=
              worldStep_preserves_nullAndBlocks hIA_entry hBs_entry hws
                (fun j hj => by rw [List.mem_singleton.1 hj]; exact hcond.1)
                hcond.2.1 hcond.2.2.1 hcond.2.2.2
            have hjc_post : globN post "journal_cap" = globN state "journal_cap" := by
              exact globN_eq_of_lookup (s := state) (post := post)
                (hws.2.2.1 (ofString "journal_cap") (by decide))
            have hbe_post : globN post "be" = globN state "be" := by
              exact globN_eq_of_lookup (s := state) (post := post)
                (hws.2.2.1 (ofString "be") (by decide))
            have hrc_eq : runAttemptCells post w_si.toNat = runAttemptCells state w_si.toNat :=
              runAttemptCells_eq_of_unhit (inputAtNullWith_strong hIA) hu_rc
            have h264 : heapLimit ≤ 2 ^ 64 := by decide
            have hhp_lim : globN state "heap_ptr" ≤ heapLimit := hAs.2.2.1
            have hhdr_in := (hBs (w_hdr.toNat, 248) (by simp)).2.2.1
            have hHdr_post : HeaderAt post w_hdr.toNat :=
              headerAt_of_unhit hAs.1 hIA_post.1.1.1 (by unfold Inside at hhdr_in; omega)
                (hu_bs (w_hdr.toNat, 248) (by simp)) hHdr
            set resumed := { post with locals := state.locals }
            have hRes : (RunAttemptHasBe Z) resumed := by
              refine ⟨w_si, w_hdr, S', Nd',
                (inputAtNullWith_with_locals post state.locals post.clock S' Nd' w_si.toNat).2 hIA_post,
                (allBlocksGood_with_locals post state.locals post.clock S' Nd' [(w_hdr.toNat, 248)]).2 hBs_post,
                hHdr_post, ?_, ?_, hlsi, hlhdr⟩
              · change globN post "journal_cap" ≠ 0; rwa [hjc_post]
              · change globN post "be" ≠ 0; rwa [hbe_post]
            rwa [hpost_eq] at hRes
          · simp at hcall
        | _ => simp [emptyLocalsHOLFinite] at hcall

theorem hoare_store_be_preserve {off : Nat} {src : ExpHOL 64}
    (hoff8 : off % 8 = 0)
    (hfit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      (RunAttemptHasBe Z) s → evalAt s src = some v → off + 8 * (flattenHOL v).length ≤ 120) :
    Hoare (RunAttemptHasBe Z)
      (.store (.op .add [.var .global (ofString "be"), .const (BitVec.ofNat 64 off)]) src)
      (fun r t => r = none → (RunAttemptHasBe Z) t) := by
  refine Hoare_store_fall (fun s x v mem' hHas hx hv hst => ?_)
  have hf := hfit s v hHas hv
  obtain ⟨w_si, w_hdr, S, Nd, hIA, hBs, hHdr, hjc, hbe_nz, hlsi, hlhdr⟩ := hHas
  have htr := store_in_be_preserves_nullAndBlocks (off := off) hIA hBs hbe_nz hoff8 hf hx hst
  have hcond := nullAndBlocks_bufferRegion_conditions hIA hBs ("be", 120) (by decide) (by decide) (by decide)
  have hbuf_eq : bufferRegion s ("be", 120) = (globN s "be", 120) := by simp [bufferRegion, hbe_nz]
  rw [hbuf_eq] at hcond
  have hu_hdr : IvlUnhit s { s with memory := mem' } (w_hdr.toNat, 248) :=
    htr.2.2.2.2 (w_hdr.toNat, 248) (by simp)
      (hcond.2.2.2 (w_hdr.toNat, 248) (by simp) (globN s "be", 120) (by simp))
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hIA.1.1.2.2.1
  have hhdr_in := (hBs (w_hdr.toNat, 248) (by simp)).2.2.1
  have hHdr' : HeaderAt { s with memory := mem' } w_hdr.toNat :=
    headerAt_of_unhit hIA.1.1.1 htr.1.1.1.1 (by unfold Inside at hhdr_in; omega) hu_hdr hHdr
  exact ⟨w_si, w_hdr, S, Nd, htr.1, htr.2.1, hHdr',
    by rw [htr.2.2.1]; exact hjc,
    by rw [htr.2.2.2.1]; exact hbe_nz,
    hlsi, hlhdr⟩

private theorem hoare_store_be_load_one (off : Nat) (addr : ExpHOL 64)
    (hoff8 : off % 8 = 0) (hoff_le : off + 8 ≤ 120) :
    Hoare (RunAttemptHasBe Z)
      (.store (.op .add [.var .global (ofString "be"), .const (BitVec.ofNat 64 off)])
        (.load .one addr))
      (fun r t => r = none → (RunAttemptHasBe Z) t) :=
  hoare_store_be_preserve hoff8 (fun s v hHas hv => by
    obtain ⟨_, w, _, rfl, _⟩ := evalAt_load_one_ordinary (runAttemptHasBe_guestInv hHas) hv
    simp only [flattenHOL, List.length_singleton]
    omega)

private theorem hoare_store_be_global_word (off : Nat) (gname : String)
    (hmem : gname ∈ guestGlobalNames)
    (hoff8 : off % 8 = 0) (hoff_le : off + 8 ≤ 120) :
    Hoare (RunAttemptHasBe Z)
      (.store (.op .add [.var .global (ofString "be"), .const (BitVec.ofNat 64 off)])
        (.var .global (ofString gname)))
      (fun r t => r = none → (RunAttemptHasBe Z) t) :=
  hoare_store_be_preserve hoff8 (fun s v hHas hv => by
    obtain ⟨_, _, _, _, hIA, _⟩ := hHas
    have hAs : ArenaReady s := hIA.1.1
    obtain ⟨wg, hwg⟩ := hAs.2.2.2.2.2.2.2.2.2 gname hmem
    have hwg' : s.globals.lookup (ofString gname) = some (.val (.word wg)) := hwg
    simp only [evalAt, evalHOLExact, hwg', Option.some.injEq] at hv
    subst hv
    simp only [flattenHOL, List.length_singleton]
    omega)

theorem runAttemptPhaseC2_bounded
    (hal : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hmz : TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero»)
    (hexec : TerminatingFunBoundedOn (BlockReadyExecAttemptNull Z)
      (ofString "execute_block") K.«execute_block»)
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc"))
    (wmz : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")]) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memzero")) :
    TerminatingProgBoundedOn (RunAttemptPreBe Z) runAttemptPhaseC2Prog
      ((K.«alloc» + 1) + (K.«memzero» + 1) + (K.«execute_block» + 1)) := by
  have htail_has : TerminatingProgBoundedOn (RunAttemptHasBe Z) runAttemptExecuteTail
      (K.«execute_block» + 1) := by
    intro F s hc hp
    exact (runAttemptExecuteTail_bounded hexec) s hc (runAttemptHasBe_blockReadyExecNull hp)
  have hstores : TerminatingProgBoundedOn (RunAttemptHasBe Z) runAttemptBeStoresProg
      (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (K.«execute_block» + 1))))))))))))) :=
    TerminatingProgBoundedOn.seq_hoare (P := (RunAttemptHasBe Z))
      (TerminatingProgBoundedOn.of_clock (P := (RunAttemptHasBe Z)) (fun s => clock_store s _ _))
      (hoare_store_be_load_one 0 _ (by decide) (by omega))
      (TerminatingProgBoundedOn.seq_hoare (P := (RunAttemptHasBe Z))
        (TerminatingProgBoundedOn.of_clock (P := (RunAttemptHasBe Z)) (fun s => clock_store s _ _))
        (hoare_store_be_load_one 8 _ (by decide) (by omega))
        (TerminatingProgBoundedOn.seq_hoare (P := (RunAttemptHasBe Z))
          (TerminatingProgBoundedOn.of_clock (P := (RunAttemptHasBe Z)) (fun s => clock_store s _ _))
          (hoare_store_be_global_word 16 "block_hashes" (by decide) (by decide) (by omega))
          (TerminatingProgBoundedOn.seq_hoare (P := (RunAttemptHasBe Z))
            (TerminatingProgBoundedOn.of_clock (P := (RunAttemptHasBe Z)) (fun s => clock_store s _ _))
            (hoare_store_be_global_word 24 "block_hashes_n" (by decide) (by decide) (by omega))
            (TerminatingProgBoundedOn.seq_hoare (P := (RunAttemptHasBe Z))
              (TerminatingProgBoundedOn.of_clock (P := (RunAttemptHasBe Z)) (fun s => clock_store s _ _))
              (hoare_store_be_load_one 32 _ (by decide) (by omega))
              (TerminatingProgBoundedOn.seq_hoare (P := (RunAttemptHasBe Z))
                (TerminatingProgBoundedOn.of_clock (P := (RunAttemptHasBe Z)) (fun s => clock_store s _ _))
                (hoare_store_be_load_one 40 _ (by decide) (by omega))
                (TerminatingProgBoundedOn.seq_hoare (P := (RunAttemptHasBe Z))
                  (TerminatingProgBoundedOn.of_clock (P := (RunAttemptHasBe Z)) (fun s => clock_store s _ _))
                  (hoare_store_be_preserve (off := 48) (by decide) (fun s v _ hv => by
                    rw [evalAt_load_comb4_len hv]; omega))
                  (TerminatingProgBoundedOn.seq_hoare (P := (RunAttemptHasBe Z))
                    (TerminatingProgBoundedOn.of_clock (P := (RunAttemptHasBe Z)) (fun s => clock_store s _ _))
                    (hoare_store_be_load_one 80 _ (by decide) (by omega))
                    (TerminatingProgBoundedOn.seq_hoare (P := (RunAttemptHasBe Z))
                      (TerminatingProgBoundedOn.of_clock (P := (RunAttemptHasBe Z)) (fun s => clock_store s _ _))
                      (hoare_store_be_load_one 88 _ (by decide) (by omega))
                      (TerminatingProgBoundedOn.seq_hoare (P := (RunAttemptHasBe Z))
                        (TerminatingProgBoundedOn.of_clock (P := (RunAttemptHasBe Z)) (fun s => clock_store s _ _))
                        (hoare_store_be_load_one 96 _ (by decide) (by omega))
                        (TerminatingProgBoundedOn.seq_hoare (P := (RunAttemptHasBe Z))
                          (TerminatingProgBoundedOn.of_clock (P := (RunAttemptHasBe Z)) (fun s => clock_store s _ _))
                          (hoare_store_be_load_one 104 _ (by decide) (by omega))
                          (TerminatingProgBoundedOn.seq_hoare (P := (RunAttemptHasBe Z))
                            (TerminatingProgBoundedOn.of_clock (P := (RunAttemptHasBe Z)) (fun s => clock_store s _ _))
                            (hoare_store_be_load_one 112 _ (by decide) (by omega))
                            htail_has)))))))))))
  have hmzc : TerminatingProgBoundedOn (RunAttemptHasBe Z)
      (.seq (.call (some (none, none)) (ofString "memzero")
          [.var .global (ofString "be"), .const 120#64])
        runAttemptBeStoresProg)
      ((K.«memzero» + 1) +
        (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (K.«execute_block» + 1)))))))))))))) :=
    TerminatingProgBoundedOn.seq_hoare (P := (RunAttemptHasBe Z))
      (TerminatingProgBoundedOn.call_on hmz none _
        (callEntryOn_of_imp localsFree_guestInv (fun _ h => runAttemptHasBe_guestInv h) _ _))
      (hoare_memzero_be_120 wmz)
      hstores
  have hall : TerminatingProgBoundedOn (RunAttemptPreBe Z) runAttemptPhaseC2Prog
      ((K.«alloc» + 1) +
        ((K.«memzero» + 1) +
          (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (K.«execute_block» + 1))))))))))))))) :=
    TerminatingProgBoundedOn.seq_hoare_trans (P := (RunAttemptPreBe Z)) (Q := (RunAttemptHasBe Z))
      (TerminatingProgBoundedOn.call_on hal (some (.global, ofString "be")) _
        (callEntryOn_of_imp localsFree_guestInv (fun _ h => runAttemptPreBe_guestInv h) _ _))
      (hoare_alloc_be_120 wal rtal)
      hmzc
  intro F s hc hp
  exact TerminatingProgBoundedOn.mono_bound (P := (RunAttemptPreBe Z))
    (a := (K.«alloc» + 1) +
      ((K.«memzero» + 1) +
        (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (0 + (K.«execute_block» + 1)))))))))))))))
    (b := (K.«alloc» + 1) + (K.«memzero» + 1) + (K.«execute_block» + 1))
    hall (by omega) s hc hp

def RunAttemptPostScan (Z : Prop) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ w_si w_pl w_parent : BitVec 64, ∃ S Nd : List Nat,
    (InputAtNullWith Z) s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_parent.toNat, 248)] ∧
    HeaderAt s w_parent.toNat ∧
    globN s "journal_cap" ≠ 0 ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "parent") = some (.val (.word w_parent))

def RunAttemptPostHdr (Z : Prop) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ w_si w_pl w_parent w_hdr : BitVec 64, ∃ S Nd : List Nat,
    (InputAtNullWith Z) s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_parent.toNat, 248), (w_hdr.toNat, 248)] ∧
    HeaderAt s w_parent.toNat ∧
    HeaderAt s w_hdr.toNat ∧
    globN s "journal_cap" ≠ 0 ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "parent") = some (.val (.word w_parent)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr))

def RunAttemptPostBh (Z : Prop) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ w_si w_pl w_parent w_hdr w_bh : BitVec 64, ∃ S Nd : List Nat,
    (InputAtNullWith Z) s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_parent.toNat, 248), (w_hdr.toNat, 248), (w_bh.toNat, 32)] ∧
    HeaderAt s w_parent.toNat ∧
    HeaderAt s w_hdr.toNat ∧
    IvlsDisj (runAttemptCells s w_si.toNat) [(w_bh.toNat, 32)] ∧
    Disj (w_parent.toNat, 248) (w_bh.toNat, 32) ∧
    Disj (w_hdr.toNat, 248) (w_bh.toNat, 32) ∧
    globN s "journal_cap" ≠ 0 ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "parent") = some (.val (.word w_parent)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)) ∧
    s.locals.lookup (ofString "bh") = some (.val (.word w_bh))

theorem localsOnly_runAttemptPostScan : LocalsOnly ["si", "pl", "parent"] (RunAttemptPostScan Z) := by
  intro F s locals k hl hP
  obtain ⟨w_si, w_pl, w_parent, S, Nd, hIA, hBs, hPar, hjc, hsi, hpl, hpar⟩ := hP
  exact ⟨w_si, w_pl, w_parent, S, Nd,
    (inputAtNullWith_with_locals s locals k S Nd w_si.toNat).2 hIA,
    (allBlocksGood_with_locals s locals k S Nd [(w_parent.toNat, 248)]).2 hBs,
    hPar, hjc,
    (hl "si" (by simp)).trans hsi,
    (hl "pl" (by simp)).trans hpl,
    (hl "parent" (by simp)).trans hpar⟩

theorem localsOnly_runAttemptPostHdr : LocalsOnly ["si", "pl", "parent", "hdr"] (RunAttemptPostHdr Z) := by
  intro F s locals k hl hP
  obtain ⟨w_si, w_pl, w_parent, w_hdr, S, Nd, hIA, hBs, hPar, hHdr, hjc, hsi, hpl, hpar, hhdr⟩ := hP
  exact ⟨w_si, w_pl, w_parent, w_hdr, S, Nd,
    (inputAtNullWith_with_locals s locals k S Nd w_si.toNat).2 hIA,
    (allBlocksGood_with_locals s locals k S Nd [(w_parent.toNat, 248), (w_hdr.toNat, 248)]).2 hBs,
    hPar, hHdr, hjc,
    (hl "si" (by simp)).trans hsi,
    (hl "pl" (by simp)).trans hpl,
    (hl "parent" (by simp)).trans hpar,
    (hl "hdr" (by simp)).trans hhdr⟩

theorem runAttemptPostScan_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : (RunAttemptPostScan Z) s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, hIA, _⟩ := h
  exact hIA.1.1.1

theorem runAttemptPostScan_inputReadyNull {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : (RunAttemptPostScan Z) s) : (InputReadyNull Z) s := by
  obtain ⟨w_si, _, _, S, Nd, hIA, _, _, _, hsi, _, _⟩ := h
  have heq : locN s "si" = w_si.toNat := by simp [locN, hsi]
  unfold InputReadyNull
  rw [heq]
  exact inputAtNullWith_strong hIA

theorem runAttemptPostHdr_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : (RunAttemptPostHdr Z) s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, hIA, _⟩ := h
  exact hIA.1.1.1

theorem runAttemptPostHdr_preBe {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : (RunAttemptPostHdr Z) s) : (RunAttemptPreBe Z) s := by
  obtain ⟨w_si, _, _, w_hdr, S, Nd, hIA, hBs, _, hHdr, hjc, hsi, _, _, hhdr⟩ := h
  refine ⟨w_si, w_hdr, S, Nd, hIA, ?_, hHdr, hjc, hsi, hhdr⟩
  intro b hb
  simp only [List.mem_singleton] at hb; subst hb
  exact hBs (w_hdr.toNat, 248) (by simp)

theorem runAttemptPostBh_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : (RunAttemptPostBh Z) s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, hIA, _⟩ := h
  exact hIA.1.1.1

theorem decCallResumeOn_memeq_runAttemptPreBe
    (romeq : ReadOnlyFn (ofString "memeq"))
    (arguments : List (ExpHOL 64)) :
    DecCallResumeOn (RunAttemptPreBe Z) (RunAttemptPreBe Z)
      (ofString "eq") (ofString "memeq") arguments :=
  ReadOnlyFn.resumeOn localsOnly_runAttemptPreBe (fun _ h => runAttemptPreBe_guestInv h)
    romeq (ofString "eq") (by intro n hn; simp at hn; rcases hn with rfl | rfl <;> decide) arguments

theorem decCallResumeOn_memeq_runAttemptPostHdr
    (romeq : ReadOnlyFn (ofString "memeq"))
    (arguments : List (ExpHOL 64)) :
    DecCallResumeOn (RunAttemptPostHdr Z) (RunAttemptPostHdr Z)
      (ofString "eq") (ofString "memeq") arguments :=
  ReadOnlyFn.resumeOn localsOnly_runAttemptPostHdr (fun _ h => runAttemptPostHdr_guestInv h)
    romeq (ofString "eq")
    (by intro n hn; simp at hn; rcases hn with rfl | rfl | rfl | rfl <;> decide) arguments

theorem decCallResumeOn_payload_header
    (wph : WorldKeeps (InputReadyZ Z)
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
        (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16),
        (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
        (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr", "wd_rlp_slices"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetHeader (ofString "payload_header")) :
    DecCallResumeOn (RunAttemptPostScan Z) (RunAttemptPostHdr Z)
      (ofString "hdr") (ofString "payload_header") [.var .local (ofString "si")] := by
  intro F state values body callee ret value post hcode hP hargs hl hrun
  obtain ⟨w_si, w_pl, w_parent, S, Nd, hIA, hBs, hPar, hjc, hlsi, hlpl, hlpar⟩ := hP
  have hAs : ArenaReady state := hIA.1.1
  have hpc := callee_param_one state (ofString "payload_header") (ofString "si") .one _ _
    (by rw [hcode]; exact lookup_payload_header_fn) values body callee ret hargs hl
  set entry := callEntryStateHOLFinite state callee
  have hsi_loc : locN entry "si" = w_si.toNat := by
    have hev : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        [.var .local (ofString "si")] = some [.val (.word w_si)] := by
      rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, evalHOLExact, hlsi]
    rw [hev] at hargs
    have hv := Option.some.inj hargs; subst hv
    simp [entry, locN, callEntryStateHOLFinite, hpc, hlsi]
  have hIA_entry : (InputAtNullWith Z) entry S Nd w_si.toNat :=
    (inputAtNullWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
  have hBs_entry : AllBlocksGood entry S Nd [(w_parent.toNat, 248)] :=
    (allBlocksGood_with_locals state callee (state.clock - 1) S Nd [(w_parent.toNat, 248)]).2 hBs
  have hIR_entry : (InputReadyZ Z) entry := by
    unfold InputReadyZ
    rw [hsi_loc]
    exact (inputAtNullWith_strong hIA_entry).1
  have hstep := FunSpec.at_lookup wph state hcode values body callee ret hl hIR_entry
    (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  have hws := hstep (Or.inl ⟨value, rfl⟩)
  have hc1 := nullAndBlocks_bufferRegion_conditions hIA_entry hBs_entry ("keccak_pad", 136) (by decide) (by decide) (by decide)
  have hc2 := nullAndBlocks_bufferRegion_conditions hIA_entry hBs_entry ("keccak_st", 200) (by decide) (by decide) (by decide)
  have hc3 := nullAndBlocks_bufferRegion_conditions hIA_entry hBs_entry ("mpt_hash_scratch", 40) (by decide) (by decide) (by decide)
  have hc4 := nullAndBlocks_bufferRegion_conditions hIA_entry hBs_entry ("mpt_key_scratch", 16) (by decide) (by decide) (by decide)
  have hc5 := nullAndBlocks_bufferRegion_conditions hIA_entry hBs_entry ("sha_pad", 128) (by decide) (by decide) (by decide)
  have hc6 := nullAndBlocks_bufferRegion_conditions hIA_entry hBs_entry ("sha_st", 64) (by decide) (by decide) (by decide)
  obtain ⟨S', Nd', hIA_post, hBs_post, _, _, hu_bs, _, _, hQ⟩ :=
    worldStep_preserves_nullAndBlocks hIA_entry hBs_entry hws
      (fun j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hc1.1
        · exact hc2.1
        · exact hc3.1
        · exact hc4.1
        · exact hc5.1
        · exact hc6.1)
      (fun j hj k hk => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hc1.2.1 _ (by simp [bufferRegion]) k hk
        · exact hc2.2.1 _ (by simp [bufferRegion]) k hk
        · exact hc3.2.1 _ (by simp [bufferRegion]) k hk
        · exact hc4.2.1 _ (by simp [bufferRegion]) k hk
        · exact hc5.2.1 _ (by simp [bufferRegion]) k hk
        · exact hc6.2.1 _ (by simp [bufferRegion]) k hk)
      (fun c hc j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hc1.2.2.1 c hc _ (by simp [bufferRegion])
        · exact hc2.2.2.1 c hc _ (by simp [bufferRegion])
        · exact hc3.2.2.1 c hc _ (by simp [bufferRegion])
        · exact hc4.2.2.1 c hc _ (by simp [bufferRegion])
        · exact hc5.2.2.1 c hc _ (by simp [bufferRegion])
        · exact hc6.2.2.1 c hc _ (by simp [bufferRegion]))
      (fun b hb j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hc1.2.2.2 b hb _ (by simp [bufferRegion])
        · exact hc2.2.2.2 b hb _ (by simp [bufferRegion])
        · exact hc3.2.2.2 b hb _ (by simp [bufferRegion])
        · exact hc4.2.2.2 b hb _ (by simp [bufferRegion])
        · exact hc5.2.2.2 b hb _ (by simp [bufferRegion])
        · exact hc6.2.2.2 b hb _ (by simp [bufferRegion]))
  obtain ⟨w_hdr, rfl, hHdr_post, hhdr_in, hhdr_ow⟩ := hQ value rfl
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hhp_lim : globN state "heap_ptr" ≤ heapLimit := hAs.2.2.1
  have hpar_in := (hBs (w_parent.toNat, 248) (by simp)).2.2.1
  have hPar_post : HeaderAt post w_parent.toNat :=
    headerAt_of_unhit hAs.1 hIA_post.1.1.1 (by unfold Inside at hpar_in; omega)
      (hu_bs (w_parent.toNat, 248) (by simp)) hPar
  have hjc_post : globN post "journal_cap" = globN state "journal_cap" :=
    globN_eq_of_lookup (s := state) (post := post)
      (hws.2.2.1 (ofString "journal_cap") (by decide))
  have hBs_both : AllBlocksGood post S' Nd' [(w_parent.toNat, 248), (w_hdr.toNat, 248)] := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hBs_post (w_parent.toNat, 248) (by simp)
    · exact ⟨hHdr_post.1.1, show (248 : Nat) % 8 = 0 by decide, hhdr_in, hHdr_post.1, hhdr_ow⟩
  set resumed := setVarHOLFinite (ofString "hdr") (.val (.word w_hdr)) { post with locals := state.locals }
  refine ⟨w_si, w_pl, w_parent, w_hdr, S', Nd',
    (inputAtNullWith_with_locals post _ post.clock S' Nd' w_si.toNat).2 hIA_post,
    (allBlocksGood_with_locals post _ post.clock S' Nd' [(w_parent.toNat, 248), (w_hdr.toNat, 248)]).2 hBs_both,
    hPar_post, hHdr_post, ?_, ?_, ?_, ?_, ?_⟩
  · change globN post "journal_cap" ≠ 0; rwa [hjc_post]
  · simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "hdr" ≠ ofString "si" by decide, hlsi]
  · simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "hdr" ≠ ofString "pl" by decide, hlpl]
  · simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "hdr" ≠ ofString "parent" by decide, hlpar]
  · simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

theorem decCallResumeOn_alloc_bh_32
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    DecCallResumeOn (RunAttemptPostHdr Z) (RunAttemptPostBh Z)
      (ofString "bh") (ofString "alloc") [.const 32#64] := by
  intro F state values body callee ret value post hcode hP hargs hl hrun
  obtain ⟨w_si, w_pl, w_parent, w_hdr, S, Nd, hIA, hBs, hPar, hHdr, hjc, hlsi, hlpl, hlpar, hlhdr⟩ := hP
  have hAs : ArenaReady state := hIA.1.1
  have hW : WorldOK state := ⟨hAs, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.1.2.1⟩⟩
  have hpc := callee_param_one_exp state (ofString "alloc") (ofString "n") .one _ _
    (by rw [hcode]; exact lookup_alloc_fn) (.const 32#64) (.val (.word 32#64))
    values body callee ret rfl hargs hl
  set entry := callEntryStateHOLFinite state callee
  have hn : locN entry "n" = 32 := by
    simp [entry, locN, callEntryStateHOLFinite, hpc.2]
  have hstep := FunSpec.at_lookup wal state hcode values body callee ret hl
    (localsFree_worldOK state callee (state.clock - 1) hW) (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  have hws := hstep (Or.inl ⟨value, rfl⟩)
  have hrt := FunSpec.at_lookup rtal state hcode values body callee ret hl
    (localsFree_arenaReady state callee (state.clock - 1) hAs) (by rw [hrun]; simp)
  rw [hrun] at hrt; dsimp only at hrt
  obtain ⟨w_bh, rfl, _, _, hfb⟩ := hrt value rfl
  rw [hn] at hfb
  have hfb_in : Inside (w_bh.toNat, 32) (globN state "heap_ptr") (globN post "heap_ptr") := hfb.2.1
  have hIA_entry : (InputAtNullWith Z) entry S Nd w_si.toNat :=
    (inputAtNullWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
  have hBs_entry : AllBlocksGood entry S Nd [(w_parent.toNat, 248), (w_hdr.toNat, 248)] :=
    (allBlocksGood_with_locals state callee (state.clock - 1) S Nd _).2 hBs
  obtain ⟨S', Nd', hIA_post, hBs_post, _, hu_rc, hu_bs, _, _, hQ⟩ :=
    worldStep_preserves_nullAndBlocks hIA_entry hBs_entry hws
      (fun _ hj => by simp at hj) (fun _ hj => by simp at hj)
      (fun _ _ _ hj => by simp at hj) (fun _ _ _ hj => by simp at hj)
  obtain ⟨w_bh', hw_eq, hav⟩ := hQ (.val (.word w_bh)) rfl
  injection hw_eq with hw_eq'; injection hw_eq' with hw_eq''; subst hw_eq''
  dsimp only at hav; rw [hn] at hav
  have hrc_eq : runAttemptCells post w_si.toNat = runAttemptCells state w_si.toNat :=
    runAttemptCells_eq_of_unhit (inputAtNullWith_strong hIA) hu_rc
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hhp_lim : globN state "heap_ptr" ≤ heapLimit := hAs.2.2.1
  have hpar_in := (hBs (w_parent.toNat, 248) (by simp)).2.2.1
  have hhdr_in := (hBs (w_hdr.toNat, 248) (by simp)).2.2.1
  have hPar_post : HeaderAt post w_parent.toNat :=
    headerAt_of_unhit hAs.1 hIA_post.1.1.1 (by unfold Inside at hpar_in; omega)
      (hu_bs (w_parent.toNat, 248) (by simp)) hPar
  have hHdr_post : HeaderAt post w_hdr.toNat :=
    headerAt_of_unhit hAs.1 hIA_post.1.1.1 (by unfold Inside at hhdr_in; omega)
      (hu_bs (w_hdr.toNat, 248) (by simp)) hHdr
  have hBs_all : AllBlocksGood post S' Nd'
      [(w_parent.toNat, 248), (w_hdr.toNat, 248), (w_bh.toNat, 32)] := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hBs_post _ (by simp)
    · exact hBs_post _ (by simp)
    · exact ⟨hfb.1, show (32 : Nat) % 8 = 0 by decide,
        ⟨Nat.le_trans hAs.2.1 hfb_in.1, hfb_in.2⟩, hfb.2.2,
        fun i hi o ho => by rw [List.mem_singleton.1 hi]; exact hav (w_bh.toNat, 32) (by simp) o ho⟩
  have hd_rc : IvlsDisj (runAttemptCells post w_si.toNat) [(w_bh.toNat, 32)] := by
    rw [hrc_eq]
    intro c hc b hb
    rw [List.mem_singleton.1 hb]
    have hi := (hIA.2.1 c hc).2.1
    unfold Inside at hi hfb_in
    unfold Disj; dsimp only at hi hfb_in ⊢; omega
  have hd_bs : ∀ b ∈ [(w_parent.toNat, 248), (w_hdr.toNat, 248)], Disj b (w_bh.toNat, 32) := by
    intro b hb
    have hi := (hBs b hb).2.2.1
    unfold Inside at hi hfb_in
    unfold Disj; dsimp only at hi hfb_in ⊢; omega
  have hjc_post : globN post "journal_cap" = globN state "journal_cap" :=
    globN_eq_of_lookup (s := state) (post := post)
      (hws.2.2.1 (ofString "journal_cap") (by decide))
  refine ⟨w_si, w_pl, w_parent, w_hdr, w_bh, S', Nd',
    (inputAtNullWith_with_locals post _ post.clock S' Nd' w_si.toNat).2 hIA_post,
    (allBlocksGood_with_locals post _ post.clock S' Nd' _).2 hBs_all,
    hPar_post, hHdr_post, hd_rc, hd_bs _ (by simp), hd_bs _ (by simp), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change globN post "journal_cap" ≠ 0; rwa [hjc_post]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlsi,
      show ofString "bh" ≠ ofString "si" by decide]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlpl,
      show ofString "bh" ≠ ofString "pl" by decide]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlpar,
      show ofString "bh" ≠ ofString "parent" by decide]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlhdr,
      show ofString "bh" ≠ ofString "hdr" by decide]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

theorem hoare_header_hash_bh
    (whh : WorldKeeps (fun s => WorldOK s ∧ HeaderOKStrongLocal s)
      (fun s => [(locN s "out", 32),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "header_hash")) :
    Hoare (RunAttemptPostBh Z)
      (.call (some (none, none)) (ofString "header_hash")
        [.var .local (ofString "hdr"), .var .local (ofString "bh")])
      (fun r t => r = none → (RunAttemptPostHdr Z) t) := by
  refine ⟨fun {F} state hcode hP _ hr => ?_⟩
  rcases hcall : evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "header_hash")
        [.var .local (ofString "hdr"), .var .local (ofString "bh")]) with ⟨cres, cpost⟩
  have hr' : cres = none := by rw [hcall] at hr; exact hr
  subst hr'
  obtain ⟨w_si, w_pl, w_parent, w_hdr, w_bh, S, Nd,
    hIA, hBs, hPar, hHdr, hd_rc_bh, hd_par_bh, hd_hdr_bh,
    hjc, hlsi, hlpl, hlpar, hlhdr, hlbh⟩ := hP
  have hAs : ArenaReady state := hIA.1.1
  have hW : WorldOK state := ⟨hAs, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.1.2.1⟩⟩
  rw [evaluateHOLFiniteState_call] at hcall
  have hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "hdr"), .var .local (ofString "bh")] =
      some [.val (.word w_hdr), .val (.word w_bh)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact, evalHOLExact, hlhdr, hlbh]
  rw [hargs] at hcall; dsimp only at hcall
  rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "header_hash")
      [.val (.word w_hdr), .val (.word w_bh)] with _ | ⟨body, callee, ret⟩
  · rw [hl] at hcall; simp at hcall
  · rw [hl] at hcall; dsimp only at hcall
    split_ifs at hcall with hz
    · simp at hcall
    · rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨bres, post⟩
      rw [hrun] at hcall
      cases bres with
      | none => simp at hcall
      | some br =>
        cases br with
        | returned v =>
          dsimp only at hcall
          split_ifs at hcall with hsh
          · obtain ⟨_, hpost_eq⟩ := Prod.mk.inj hcall
            have hpc := callee_param_two state (ofString "header_hash") (ofString "h") (ofString "out")
              .one .one _ _ (by rw [hcode]; exact lookup_header_hash_fn)
              (.var .local (ofString "hdr")) (.var .local (ofString "bh"))
              (.val (.word w_hdr)) (.val (.word w_bh))
              [.val (.word w_hdr), .val (.word w_bh)] body callee ret
              (by simpa [evalAt, evalHOLExact] using hlhdr)
              (by simpa [evalAt, evalHOLExact] using hlbh) hargs hl
            set entry := callEntryStateHOLFinite state callee
            have hh_loc : locN entry "h" = w_hdr.toNat := by
              simp [entry, locN, callEntryStateHOLFinite, hpc.2.1]
            have hout_loc : locN entry "out" = w_bh.toNat := by
              simp [entry, locN, callEntryStateHOLFinite, hpc.2.2]
            have hhdr_good := hBs (w_hdr.toNat, 248) (by simp)
            have hbh_good := hBs (w_bh.toNat, 32) (by simp)
            have hHOK : HeaderOKStrongLocal entry := by
              unfold HeaderOKStrongLocal HeaderAtStrongLocal
              rw [hh_loc]
              exact ⟨hHdr, hhdr_good.2.2.1⟩
            have hstep := FunSpec.at_lookup whh state hcode _ body callee ret hl
              ⟨localsFree_worldOK state callee (state.clock - 1) hW, hHOK⟩ (by rw [hrun]; simp)
            rw [hrun] at hstep; dsimp only at hstep
            have hws := hstep (Or.inl ⟨v, rfl⟩)
            have hIA_entry : (InputAtNullWith Z) entry S Nd w_si.toNat :=
              (inputAtNullWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
            have hBs_two : AllBlocksGood state S Nd [(w_parent.toNat, 248), (w_hdr.toNat, 248)] := by
              intro b hb
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
              rcases hb with rfl | rfl
              · exact hBs _ (by simp)
              · exact hBs _ (by simp)
            have hBs_entry : AllBlocksGood entry S Nd [(w_parent.toNat, 248), (w_hdr.toNat, 248)] :=
              (allBlocksGood_with_locals state callee (state.clock - 1) S Nd _).2 hBs_two
            have hc1 := nullAndBlocks_bufferRegion_conditions hIA_entry hBs_entry
              ("keccak_pad", 136) (by decide) (by decide) (by decide)
            have hc2 := nullAndBlocks_bufferRegion_conditions hIA_entry hBs_entry
              ("keccak_st", 200) (by decide) (by decide) (by decide)
            obtain ⟨S', Nd', hIA_post, hBs_post, _, _, hu_bs, _, _, _⟩ :=
              worldStep_preserves_nullAndBlocks hIA_entry hBs_entry hws
                (fun j hj => by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
                  rcases hj with rfl | rfl | rfl
                  · rw [hout_loc]; exact fun _ => hbh_good.1
                  · exact hc1.1
                  · exact hc2.1)
                (fun j hj k hk => by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
                  rcases hj with rfl | rfl | rfl
                  · rw [hout_loc]
                    exact hbh_good.2.2.2.2 (w_bh.toNat, 32) (by simp) k
                      (R10Shards.Fast_GbodyC17ToC21.worldTypedIvls_sub_worldOwned _ _ _ k hk)
                  · exact hc1.2.1 _ (by simp [bufferRegion]) k hk
                  · exact hc2.2.1 _ (by simp [bufferRegion]) k hk)
                (fun c hc j hj => by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
                  rcases hj with rfl | rfl | rfl
                  · rw [hout_loc]; exact hd_rc_bh c hc _ (by simp)
                  · exact hc1.2.2.1 c hc _ (by simp [bufferRegion])
                  · exact hc2.2.2.1 c hc _ (by simp [bufferRegion]))
                (fun b hb j hj => by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
                  rcases hj with rfl | rfl | rfl
                  · rw [hout_loc]
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
                    rcases hb with rfl | rfl
                    · exact hd_par_bh
                    · exact hd_hdr_bh
                  · exact hc1.2.2.2 b hb _ (by simp [bufferRegion])
                  · exact hc2.2.2.2 b hb _ (by simp [bufferRegion]))
            have h264 : heapLimit ≤ 2 ^ 64 := by decide
            have hhp_lim : globN state "heap_ptr" ≤ heapLimit := hAs.2.2.1
            have hpar_in := (hBs (w_parent.toNat, 248) (by simp)).2.2.1
            have hhdr_in := hhdr_good.2.2.1
            have hPar_post : HeaderAt post w_parent.toNat :=
              headerAt_of_unhit hAs.1 hIA_post.1.1.1 (by unfold Inside at hpar_in; omega)
                (hu_bs (w_parent.toNat, 248) (by simp)) hPar
            have hHdr_post : HeaderAt post w_hdr.toNat :=
              headerAt_of_unhit hAs.1 hIA_post.1.1.1 (by unfold Inside at hhdr_in; omega)
                (hu_bs (w_hdr.toNat, 248) (by simp)) hHdr
            have hjc_post : globN post "journal_cap" = globN state "journal_cap" :=
              globN_eq_of_lookup (s := state) (post := post)
                (hws.2.2.1 (ofString "journal_cap") (by decide))
            have hRes : (RunAttemptPostHdr Z) { post with locals := state.locals } := by
              refine ⟨w_si, w_pl, w_parent, w_hdr, S', Nd',
                (inputAtNullWith_with_locals post state.locals post.clock S' Nd' w_si.toNat).2 hIA_post,
                (allBlocksGood_with_locals post state.locals post.clock S' Nd' _).2 hBs_post,
                hPar_post, hHdr_post, ?_, hlsi, hlpl, hlpar, hlhdr⟩
              change globN post "journal_cap" ≠ 0; rwa [hjc_post]
            exact hpost_eq ▸ hRes
          · simp at hcall
        | _ => simp [emptyLocalsHOLFinite] at hcall

theorem decCallResumeOn_is_valid_versioned_hashes
    (wvvh : WorldKeeps WorldOK (fun _ => []) ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "is_valid_versioned_hashes")) :
    DecCallResumeOn (RunAttemptPostHdr Z) (RunAttemptPostHdr Z)
      (ofString "vvh") (ofString "is_valid_versioned_hashes") [.var .local (ofString "si")] := by
  intro F state values body callee ret value post hcode hP hargs hl hrun
  obtain ⟨w_si, w_pl, w_parent, w_hdr, S, Nd, hIA, hBs, hPar, hHdr, hjc, hlsi, hlpl, hlpar, hlhdr⟩ := hP
  have hAs : ArenaReady state := hIA.1.1
  have hW : WorldOK state := ⟨hAs, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.1.2.1⟩⟩
  set entry := callEntryStateHOLFinite state callee
  have hstep := FunSpec.at_lookup wvvh state hcode values body callee ret hl
    (localsFree_worldOK state callee (state.clock - 1) hW) (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  have hws := hstep (Or.inl ⟨value, rfl⟩)
  have hIA_entry : (InputAtNullWith Z) entry S Nd w_si.toNat :=
    (inputAtNullWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
  have hBs_entry : AllBlocksGood entry S Nd [(w_parent.toNat, 248), (w_hdr.toNat, 248)] :=
    (allBlocksGood_with_locals state callee (state.clock - 1) S Nd _).2 hBs
  obtain ⟨S', Nd', hIA_post, hBs_post, _, _, hu_bs, _, _, _⟩ :=
    worldStep_preserves_nullAndBlocks hIA_entry hBs_entry hws
      (fun _ hj => by simp at hj) (fun _ hj => by simp at hj)
      (fun _ _ _ hj => by simp at hj) (fun _ _ _ hj => by simp at hj)
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hhp_lim : globN state "heap_ptr" ≤ heapLimit := hAs.2.2.1
  have hpar_in := (hBs (w_parent.toNat, 248) (by simp)).2.2.1
  have hhdr_in := (hBs (w_hdr.toNat, 248) (by simp)).2.2.1
  have hPar_post : HeaderAt post w_parent.toNat :=
    headerAt_of_unhit hAs.1 hIA_post.1.1.1 (by unfold Inside at hpar_in; omega)
      (hu_bs (w_parent.toNat, 248) (by simp)) hPar
  have hHdr_post : HeaderAt post w_hdr.toNat :=
    headerAt_of_unhit hAs.1 hIA_post.1.1.1 (by unfold Inside at hhdr_in; omega)
      (hu_bs (w_hdr.toNat, 248) (by simp)) hHdr
  have hjc_post : globN post "journal_cap" = globN state "journal_cap" :=
    globN_eq_of_lookup (s := state) (post := post)
      (hws.2.2.1 (ofString "journal_cap") (by decide))
  refine ⟨w_si, w_pl, w_parent, w_hdr, S', Nd',
    (inputAtNullWith_with_locals post _ post.clock S' Nd' w_si.toNat).2 hIA_post,
    (allBlocksGood_with_locals post _ post.clock S' Nd' _).2 hBs_post,
    hPar_post, hHdr_post, ?_, ?_, ?_, ?_, ?_⟩
  · change globN post "journal_cap" ≠ 0; rwa [hjc_post]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlsi,
      show ofString "vvh" ≠ ofString "si" by decide]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlpl,
      show ofString "vvh" ≠ ofString "pl" by decide]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlpar,
      show ofString "vvh" ≠ ofString "parent" by decide]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlhdr,
      show ofString "vvh" ≠ ofString "hdr" by decide]

theorem hoare_validate_header
    (wvh : WorldKeeps R16Shards.TopGbodyWk.ValidateHeaderReady
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "validate_header")) :
    Hoare (RunAttemptPostHdr Z)
      (.call (some (none, none)) (ofString "validate_header")
        [.var .local (ofString "parent"), .var .local (ofString "hdr")])
      (fun r t => r = none → (RunAttemptPreBe Z) t) := by
  refine ⟨fun {F} state hcode hP _ hr => ?_⟩
  rcases hcall : evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "validate_header")
        [.var .local (ofString "parent"), .var .local (ofString "hdr")]) with ⟨cres, cpost⟩
  have hr' : cres = none := by rw [hcall] at hr; exact hr
  subst hr'
  obtain ⟨w_si, w_pl, w_parent, w_hdr, S, Nd, hIA, hBs, hPar, hHdr, hjc, hlsi, hlpl, hlpar, hlhdr⟩ := hP
  have hAs : ArenaReady state := hIA.1.1
  have hW : WorldOK state := ⟨hAs, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.1.2.1⟩⟩
  rw [evaluateHOLFiniteState_call] at hcall
  have hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "parent"), .var .local (ofString "hdr")] =
      some [.val (.word w_parent), .val (.word w_hdr)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact, evalHOLExact, hlpar, hlhdr]
  rw [hargs] at hcall; dsimp only at hcall
  rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "validate_header")
      [.val (.word w_parent), .val (.word w_hdr)] with _ | ⟨body, callee, ret⟩
  · rw [hl] at hcall; simp at hcall
  · rw [hl] at hcall; dsimp only at hcall
    split_ifs at hcall with hz
    · simp at hcall
    · rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨bres, post⟩
      rw [hrun] at hcall
      cases bres with
      | none => simp at hcall
      | some br =>
        cases br with
        | returned v =>
          dsimp only at hcall
          split_ifs at hcall with hsh
          · obtain ⟨_, hpost_eq⟩ := Prod.mk.inj hcall
            have hpc := callee_param_two state (ofString "validate_header") (ofString "parent") (ofString "h")
              .one .one _ _ (by rw [hcode]; exact lookup_validate_header_fn)
              (.var .local (ofString "parent")) (.var .local (ofString "hdr"))
              (.val (.word w_parent)) (.val (.word w_hdr))
              [.val (.word w_parent), .val (.word w_hdr)] body callee ret
              (by simpa [evalAt, evalHOLExact] using hlpar)
              (by simpa [evalAt, evalHOLExact] using hlhdr) hargs hl
            set entry := callEntryStateHOLFinite state callee
            have hpar_loc : locN entry "parent" = w_parent.toNat := by
              simp [entry, locN, callEntryStateHOLFinite, hpc.2.1]
            have hh_loc : locN entry "h" = w_hdr.toNat := by
              simp [entry, locN, callEntryStateHOLFinite, hpc.2.2]
            have hpar_in := (hBs (w_parent.toNat, 248) (by simp)).2.2.1
            have hIA_entry : (InputAtNullWith Z) entry S Nd w_si.toNat :=
              (inputAtNullWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
            have hBs_entry : AllBlocksGood entry S Nd [(w_parent.toNat, 248), (w_hdr.toNat, 248)] :=
              (allBlocksGood_with_locals state callee (state.clock - 1) S Nd _).2 hBs
            have hHOK : HeaderOK entry := by
              show HeaderAt entry (locN entry "h")
              rw [hh_loc]; exact hHdr
            have hPar_entry : R16Shards.HeaderHashRecover.HeaderAtStrong entry (locN entry "parent") := by
              unfold R16Shards.HeaderHashRecover.HeaderAtStrong; rw [hpar_loc]; exact ⟨hPar, hpar_in⟩
            have hPar_disj : ∀ iv ∈ R14Shards.OpHandlersA.untypedGlobalBufIvls entry,
                Disj (locN entry "parent", 248) iv := by
              rw [hpar_loc]
              have how := (hBs_entry (w_parent.toNat, 248) (by simp)).2.2.2.2 (w_parent.toNat, 248) (by simp)
              intro iv hiv
              simp only [R14Shards.OpHandlersA.untypedGlobalBufIvls, List.map_cons, List.map_nil,
                List.mem_cons, List.not_mem_nil, or_false] at hiv
              rcases hiv with rfl | rfl | rfl | rfl | rfl
              · exact how (bufferRegion entry ("u256_ws", 640)) (bufferRegion_mem_worldOwned entry S Nd (by decide))
              · exact how (bufferRegion entry ("sk_buf", 64)) (bufferRegion_mem_worldOwned entry S Nd (by decide))
              · exact how (bufferRegion entry ("keccak_pad", 136)) (bufferRegion_mem_worldOwned entry S Nd (by decide))
              · exact how (bufferRegion entry ("keccak_st", 200)) (bufferRegion_mem_worldOwned entry S Nd (by decide))
              · exact how (bufferRegion entry ("mpt_nib_scratch", 64)) (bufferRegion_mem_worldOwned entry S Nd (by decide))
            have hstep := FunSpec.at_lookup wvh state hcode _ body callee ret hl
              ⟨localsFree_worldOK state callee (state.clock - 1) hW, hHOK, hPar_entry, hPar_disj⟩
              (by rw [hrun]; simp)
            rw [hrun] at hstep; dsimp only at hstep
            have hws := hstep (Or.inl ⟨v, rfl⟩)
            have hc1 := nullAndBlocks_bufferRegion_conditions hIA_entry hBs_entry
              ("keccak_pad", 136) (by decide) (by decide) (by decide)
            have hc2 := nullAndBlocks_bufferRegion_conditions hIA_entry hBs_entry
              ("keccak_st", 200) (by decide) (by decide) (by decide)
            have hc3 := nullAndBlocks_bufferRegion_conditions hIA_entry hBs_entry
              ("u256_ws", 640) (by decide) (by decide) (by decide)
            obtain ⟨S', Nd', hIA_post, hBs_post, _, _, hu_bs, _, _, _⟩ :=
              worldStep_preserves_nullAndBlocks hIA_entry hBs_entry hws
                (fun j hj => by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
                  rcases hj with rfl | rfl | rfl
                  · exact hc1.1
                  · exact hc2.1
                  · exact hc3.1)
                (fun j hj k hk => by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
                  rcases hj with rfl | rfl | rfl
                  · exact hc1.2.1 _ (by simp [bufferRegion]) k hk
                  · exact hc2.2.1 _ (by simp [bufferRegion]) k hk
                  · exact hc3.2.1 _ (by simp [bufferRegion]) k hk)
                (fun c hc j hj => by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
                  rcases hj with rfl | rfl | rfl
                  · exact hc1.2.2.1 c hc _ (by simp [bufferRegion])
                  · exact hc2.2.2.1 c hc _ (by simp [bufferRegion])
                  · exact hc3.2.2.1 c hc _ (by simp [bufferRegion]))
                (fun b hb j hj => by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
                  rcases hj with rfl | rfl | rfl
                  · exact hc1.2.2.2 b hb _ (by simp [bufferRegion])
                  · exact hc2.2.2.2 b hb _ (by simp [bufferRegion])
                  · exact hc3.2.2.2 b hb _ (by simp [bufferRegion]))
            have h264 : heapLimit ≤ 2 ^ 64 := by decide
            have hhp_lim : globN state "heap_ptr" ≤ heapLimit := hAs.2.2.1
            have hhdr_in := (hBs (w_hdr.toNat, 248) (by simp)).2.2.1
            have hHdr_post : HeaderAt post w_hdr.toNat :=
              headerAt_of_unhit hAs.1 hIA_post.1.1.1 (by unfold Inside at hhdr_in; omega)
                (hu_bs (w_hdr.toNat, 248) (by simp)) hHdr
            have hjc_post : globN post "journal_cap" = globN state "journal_cap" :=
              globN_eq_of_lookup (s := state) (post := post)
                (hws.2.2.1 (ofString "journal_cap") (by decide))
            have hBs_one : AllBlocksGood post S' Nd' [(w_hdr.toNat, 248)] := by
              intro b hb
              rw [List.mem_singleton.1 hb]
              exact hBs_post (w_hdr.toNat, 248) (by simp)
            have hRes : (RunAttemptPreBe Z) { post with locals := state.locals } := by
              refine ⟨w_si, w_hdr, S', Nd',
                (inputAtNullWith_with_locals post state.locals post.clock S' Nd' w_si.toNat).2 hIA_post,
                (allBlocksGood_with_locals post state.locals post.clock S' Nd' [(w_hdr.toNat, 248)]).2 hBs_one,
                hHdr_post, ?_, hlsi, hlhdr⟩
              change globN post "journal_cap" ≠ 0; rwa [hjc_post]
            exact hpost_eq ▸ hRes
          · simp at hcall
        | _ => simp [emptyLocalsHOLFinite] at hcall

theorem runAttemptPhaseC1_bounded
    (hal : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hexec : TerminatingFunBoundedOn (BlockReadyExecAttemptNull Z)
      (ofString "execute_block") K.«execute_block»)
    (hhh : TerminatingFunBoundedOn GuestInv (ofString "header_hash") K.«header_hash»)
    (hvvh : TerminatingFunBoundedOn GuestInv
      (ofString "is_valid_versioned_hashes") K.«is_valid_versioned_hashes»)
    (hmeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (hmz : TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero»)
    (hph : TerminatingFunBoundedOn (InputReadyNwdZ Z) (ofString "payload_header") K.«payload_header»)
    (hvh : TerminatingFunBoundedOn GuestInv (ofString "validate_header") K.«validate_header»)
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc"))
    (whh : WorldKeeps (fun s => WorldOK s ∧ HeaderOKStrongLocal s)
      (fun s => [(locN s "out", 32),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "header_hash"))
    (wvvh : WorldKeeps WorldOK (fun _ => []) ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "is_valid_versioned_hashes"))
    (romeq : ReadOnlyFn (ofString "memeq"))
    (wmz : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")]) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memzero"))
    (wph : WorldKeeps (InputReadyZ Z)
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
        (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16),
        (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
        (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr", "wd_rlp_slices"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetHeader (ofString "payload_header"))
    (wvh : WorldKeeps
      R16Shards.TopGbodyWk.ValidateHeaderReady
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "validate_header")) :
    TerminatingProgBoundedOn (RunAttemptPostScan Z) runAttemptPhaseC1Prog
      ((K.«payload_header» + 1) + (K.«alloc» + 1) + (K.«header_hash» + 1) +
        (K.«memeq» + 1) + (K.«is_valid_versioned_hashes» + 1) + (K.«validate_header» + 1) +
        (K.«alloc» + 1) + (K.«memzero» + 1) + (K.«execute_block» + 1)) := by
  have hentry_ph : CallEntryOn (RunAttemptPostScan Z) (InputReadyNwdZ Z)
      (ofString "payload_header") [.var .local (ofString "si")] := by
    have hentry_strong : CallEntryOn (InputReadyNull Z) (InputReadyNull Z)
        (ofString "payload_header") [.var .local (ofString "si")] :=
      callEntryOn_inputReadyNull lookup_payload_header_fn rfl
    intro F state values body' callee ret' hcode hP hargs hl
    exact inputReadyNull_inputReadyNwd _
      (hentry_strong state values body' callee ret' hcode
        (runAttemptPostScan_inputReadyNull hP) hargs hl)
  have hc2 : TerminatingProgBoundedOn (RunAttemptPreBe Z) runAttemptPhaseC2Prog
      ((K.«alloc» + 1) + (K.«memzero» + 1) + (K.«execute_block» + 1)) :=
    runAttemptPhaseC2_bounded hal hmz hexec wal rtal wmz
  have hskip_c2 : TerminatingProgBoundedOn (RunAttemptPreBe Z)
      (.seq .skip runAttemptPhaseC2Prog)
      (0 + ((K.«alloc» + 1) + (K.«memzero» + 1) + (K.«execute_block» + 1))) :=
    TerminatingProgBoundedOn.seq_hoare (P := (RunAttemptPreBe Z))
      (TerminatingProgBoundedOn.of_clock (P := (RunAttemptPreBe Z)) (fun s => clock_skip s))
      (Hoare.skip fun _ h _ => h)
      hc2
  have hvld : TerminatingProgBoundedOn (RunAttemptPostHdr Z) _ _ :=
    TerminatingProgBoundedOn.seq_hoare_trans (P := (RunAttemptPostHdr Z)) (Q := (RunAttemptPreBe Z))
      (TerminatingProgBoundedOn.call_on hvh none _
        (callEntryOn_of_imp localsFree_guestInv (fun _ h => runAttemptPostHdr_guestInv h) _ _))
      (hoare_validate_header wvh)
      hskip_c2
  have hskip_vld : TerminatingProgBoundedOn (RunAttemptPostHdr Z) _ _ :=
    TerminatingProgBoundedOn.seq_hoare (P := (RunAttemptPostHdr Z))
      (TerminatingProgBoundedOn.of_clock (P := (RunAttemptPostHdr Z)) (fun s => clock_skip s))
      (Hoare.skip fun _ h _ => h)
      hvld
  have hite_vvh : TerminatingProgBoundedOn (RunAttemptPostHdr Z)
      (.ite (.cmp .equal (.var .local (ofString "vvh")) (.const 0#64))
        (.raise (ofString "BlockErr") (.const 6#64))
        .skip)
      (max 0 0) :=
    TerminatingProgBoundedOn.ite_on
      (TerminatingProgBoundedOn.of_clock (P := (RunAttemptPostHdr Z)) (fun s => clock_raise s _ _))
      (TerminatingProgBoundedOn.of_clock (P := (RunAttemptPostHdr Z)) (fun s => clock_skip s))
  have hafter_vvh : TerminatingProgBoundedOn (RunAttemptPostHdr Z) _ _ :=
    TerminatingProgBoundedOn.seq_hoare (P := (RunAttemptPostHdr Z))
      (TerminatingProgBoundedOn.of_clock (P := (RunAttemptPostHdr Z)) (fun s => clock_skip s))
      (Hoare.skip fun _ h _ => h)
      (TerminatingProgBoundedOn.seq_hoare (P := (RunAttemptPostHdr Z))
        hite_vvh (Hoare.ite_raise_skip _ _ _) hskip_vld)
  have hvvh_call : TerminatingProgBoundedOn (RunAttemptPostHdr Z) _ _ :=
    TerminatingProgBoundedOn.decCall_on hvvh (ofString "vvh") .one _
      (callEntryOn_of_imp localsFree_guestInv (fun _ h => runAttemptPostHdr_guestInv h) _ _)
      (decCallResumeOn_is_valid_versioned_hashes wvvh)
      hafter_vvh
  have hskip_vvh : TerminatingProgBoundedOn (RunAttemptPostHdr Z) _ _ :=
    TerminatingProgBoundedOn.seq_hoare (P := (RunAttemptPostHdr Z))
      (TerminatingProgBoundedOn.of_clock (P := (RunAttemptPostHdr Z)) (fun s => clock_skip s))
      (Hoare.skip fun _ h _ => h)
      hvvh_call
  have hite_eq : TerminatingProgBoundedOn (RunAttemptPostHdr Z)
      (.ite (.cmp .equal (.var .local (ofString "eq")) (.const 0#64))
        (.raise (ofString "BlockErr") (.const 5#64))
        .skip)
      (max 0 0) :=
    TerminatingProgBoundedOn.ite_on
      (TerminatingProgBoundedOn.of_clock (P := (RunAttemptPostHdr Z)) (fun s => clock_raise s _ _))
      (TerminatingProgBoundedOn.of_clock (P := (RunAttemptPostHdr Z)) (fun s => clock_skip s))
  have hafter_eq : TerminatingProgBoundedOn (RunAttemptPostHdr Z) _ _ :=
    TerminatingProgBoundedOn.seq_hoare (P := (RunAttemptPostHdr Z))
      hite_eq (Hoare.ite_raise_skip _ _ _) hskip_vvh
  set meqArgs : List (ExpHOL 64) :=
    [.var .local (ofString "bh"),
     .op .add [.load .one (.op .add [.var .local (ofString "pl"), .const 0#64]), .const 472#64],
     .const 32#64]
  have hmeq_call : TerminatingProgBoundedOn (RunAttemptPostHdr Z) _ _ :=
    TerminatingProgBoundedOn.decCall_on hmeq (ofString "eq") .one meqArgs
      (callEntryOn_of_imp localsFree_guestInv (fun _ h => runAttemptPostHdr_guestInv h) _ meqArgs)
      (decCallResumeOn_memeq_runAttemptPostHdr romeq meqArgs)
      hafter_eq
  have hhh_seq : TerminatingProgBoundedOn (RunAttemptPostBh Z) _ _ :=
    TerminatingProgBoundedOn.seq_hoare_trans (P := (RunAttemptPostBh Z)) (Q := (RunAttemptPostHdr Z))
      (TerminatingProgBoundedOn.call_on hhh none _
        (callEntryOn_of_imp localsFree_guestInv (fun _ h => runAttemptPostBh_guestInv h) _ _))
      (hoare_header_hash_bh whh)
      hmeq_call
  have hbh_call : TerminatingProgBoundedOn (RunAttemptPostHdr Z) _ _ :=
    TerminatingProgBoundedOn.decCall_on hal (ofString "bh") .one _
      (callEntryOn_of_imp localsFree_guestInv (fun _ h => runAttemptPostHdr_guestInv h) _ _)
      (decCallResumeOn_alloc_bh_32 wal rtal)
      hhh_seq
  have hskip_bh : TerminatingProgBoundedOn (RunAttemptPostHdr Z) _ _ :=
    TerminatingProgBoundedOn.seq_hoare (P := (RunAttemptPostHdr Z))
      (TerminatingProgBoundedOn.of_clock (P := (RunAttemptPostHdr Z)) (fun s => clock_skip s))
      (Hoare.skip fun _ h _ => h)
      hbh_call
  have hph_call : TerminatingProgBoundedOn (RunAttemptPostScan Z) _ _ :=
    TerminatingProgBoundedOn.decCall_on hph (ofString "hdr") .one _
      hentry_ph
      (decCallResumeOn_payload_header wph)
      hskip_bh
  have hall : TerminatingProgBoundedOn (RunAttemptPostScan Z) runAttemptPhaseC1Prog _ :=
    TerminatingProgBoundedOn.seq_hoare (P := (RunAttemptPostScan Z))
      (TerminatingProgBoundedOn.of_clock (P := (RunAttemptPostScan Z)) (fun s => clock_skip s))
      (Hoare.skip fun _ h _ => h)
      hph_call
  intro F s hc hp
  exact TerminatingRunBounded.weaken (hall s hc hp) (by omega)

def RA_Pl (Z : Prop) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ w_si w_pl : BitVec 64, ∃ S Nd : List Nat,
    (InputAtNullWith Z) s S Nd w_si.toNat ∧
    w_pl.toNat = memW s w_si.toNat ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl))

def RA_Vh (Z : Prop) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ w_si w_pl a b : BitVec 64, ∃ S Nd : List Nat,
    (InputAtNullWith Z) s S Nd w_si.toNat ∧
    w_pl.toNat = memW s w_si.toNat ∧
    a.toNat % 8 = 0 ∧
    WordsOK s (a.toNat, 8 * memW s (w_si.toNat + 80)) ∧
    Inside (a.toNat, 8 * memW s (w_si.toNat + 80)) sourceBase (globN s "heap_ptr") ∧
    (∀ i, i < memW s (w_si.toNat + 80) →
      let h := memW s (a.toNat + 8 * i)
      HeaderAt s h ∧ Inside (h, 248) sourceBase (globN s "heap_ptr") ∧
        IvlsDisj [(h, 248)] (worldOwned s S Nd)) ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "vh") = some (.rStruct [.val (.word a), .val (.word b)])

def RA_Nh (Z : Prop) (pos : Bool) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ w_si w_pl a b w_nh : BitVec 64, ∃ S Nd : List Nat,
    (InputAtNullWith Z) s S Nd w_si.toNat ∧
    w_pl.toNat = memW s w_si.toNat ∧
    w_nh.toNat = memW s (w_si.toNat + 80) ∧
    (pos = true → 0 < w_nh.toNat) ∧
    a.toNat % 8 = 0 ∧
    WordsOK s (a.toNat, 8 * w_nh.toNat) ∧
    Inside (a.toNat, 8 * w_nh.toNat) sourceBase (globN s "heap_ptr") ∧
    (∀ i, i < w_nh.toNat →
      let h := memW s (a.toNat + 8 * i)
      HeaderAt s h ∧ Inside (h, 248) sourceBase (globN s "heap_ptr") ∧
        IvlsDisj [(h, 248)] (worldOwned s S Nd)) ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "vh") = some (.rStruct [.val (.word a), .val (.word b)]) ∧
    s.locals.lookup (ofString "nh") = some (.val (.word w_nh))

def RA_ParentPre (Z : Prop) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ w_si w_pl w_parent a b w_nh : BitVec 64, ∃ S Nd : List Nat,
    (InputAtNullWith Z) s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_parent.toNat, 248)] ∧
    HeaderAt s w_parent.toNat ∧
    w_pl.toNat = memW s w_si.toNat ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "parent") = some (.val (.word w_parent)) ∧
    s.locals.lookup (ofString "vh") = some (.rStruct [.val (.word a), .val (.word b)]) ∧
    s.locals.lookup (ofString "nh") = some (.val (.word w_nh))

def RA_Parent (Z : Prop) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ w_si w_pl w_parent : BitVec 64, ∃ S Nd : List Nat,
    (InputAtNullWith Z) s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_parent.toNat, 248)] ∧
    HeaderAt s w_parent.toNat ∧
    w_pl.toNat = memW s w_si.toNat ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "parent") = some (.val (.word w_parent))

theorem ra_pl_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F} (h : (RA_Pl Z) s) : GuestInv s := by
  obtain ⟨_, _, _, _, hIA, _⟩ := h; exact hIA.1.1.1

theorem ra_parent_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F} (h : (RA_Parent Z) s) :
    GuestInv s := by
  obtain ⟨_, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1.1

theorem localsOnly_ra_parent : LocalsOnly ["si", "pl", "parent"] (RA_Parent Z) := by
  intro F s locals k hl hP
  obtain ⟨w_si, w_pl, w_parent, S, Nd, hIA, hBs, hPar, hpl_mem, hsi, hpl, hpar⟩ := hP
  exact ⟨w_si, w_pl, w_parent, S, Nd,
    (inputAtNullWith_with_locals s locals k S Nd w_si.toNat).2 hIA,
    (allBlocksGood_with_locals s locals k S Nd [(w_parent.toNat, 248)]).2 hBs,
    hPar, hpl_mem,
    (hl "si" (by simp)).trans hsi,
    (hl "pl" (by simp)).trans hpl,
    (hl "parent" (by simp)).trans hpar⟩

theorem ra_entry_dec_pl {K : Nat} {body : ProgHOL 64}
    (hbody : TerminatingProgBoundedOn (RA_Pl Z) body K) :
    TerminatingProgBoundedOn (InputReadyNull Z)
      (.dec (ofString "pl") .one
        (.load .one (.op .add [.var .local (ofString "si"), .const 0#64])) body) K := by
  refine dec_eval_on (P := (InputReadyNull Z)) (Q := (RA_Pl Z)) (ofString "pl") .one
    (.load .one (.op .add [.var .local (ofString "si"), .const 0#64])) ?_ hbody
  intro F s v hIR hev
  obtain ⟨S, Nd, hIA⟩ := (inputAtNull_iff_with s (locN s "si")).1 hIR
  obtain ⟨a, w_pl, ha, rfl, hpl_mem, _⟩ := evalAt_load_one_word hIA.1.1.1 hev
  obtain ⟨w_si, w0, hsi_ev, hw0_ev, ha_eq⟩ := evalAt_add2_words ha
  have hlsi : s.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    simpa [evalAt, evalHOLExact] using hsi_ev
  have hw0 : w0 = 0#64 := by
    simp only [evalAt, evalHOLExact, Option.some.injEq, ValueHOL.val.injEq,
      HolWordLab.word.injEq] at hw0_ev
    exact hw0_ev.symm
  subst hw0
  have ha_si : a = w_si := by rw [ha_eq, BitVec.add_zero]
  have hloc_si : locN s "si" = w_si.toNat := by simp [locN, hlsi]
  rw [hloc_si] at hIA
  rw [ha_si] at hpl_mem
  set s1 := setVarHOLFinite (ofString "pl") (.val (.word w_pl)) s
  exact ⟨w_si, w_pl, S, Nd,
    (inputAtNullWith_with_locals s _ s.clock S Nd w_si.toNat).2 hIA,
    hpl_mem,
    by simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
         show ofString "pl" ≠ ofString "si" by decide, hlsi],
    by simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]⟩

theorem decCallResumeOn_validate_headers
    (wvh : WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetHeadersStrong (ofString "validate_headers")) :
    DecCallResumeOn (RA_Pl Z) (RA_Vh Z) (ofString "vh") (ofString "validate_headers")
      [.load .one (.op .add [.var .local (ofString "si"), .const 72#64]),
       .load .one (.op .add [.var .local (ofString "si"), .const 80#64])] := by
  intro F state values body callee ret value post hcode hP hargs hl hrun
  obtain ⟨w_si, w_pl, S, Nd, hIA, hpl_mem, hlsi, hlpl⟩ := hP
  have hAs : ArenaReady state := hIA.1.1
  have hW : WorldOK state := ⟨hAs, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.1.2.1⟩⟩
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hhp_lim : globN state "heap_ptr" ≤ heapLimit := hAs.2.2.1
  have hsi_rc := hIA.2.1 (w_si.toNat, 96) (by simp [runAttemptCells])
  have hsi_in : Inside (w_si.toNat, 96) sourceBase (globN state "heap_ptr") :=
    inside_of_nullOrInside (by simp) hsi_rc.2.1
  have hsi_lt : w_si.toNat + 96 ≤ 2 ^ 64 := by unfold Inside at hsi_in; omega
  have hargs_ex := hargs
  rw [evalListHOLFinite_eq_toExact] at hargs_ex
  simp only [evalListHOLExact] at hargs_ex
  rcases he1 : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "si"), .const 72#64])) with _ | v1
  · rw [he1] at hargs_ex; simp at hargs_ex
  · rw [he1] at hargs_ex
    rcases he2 : @evalHOLExact 64 F _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "si"), .const 80#64])) with _ | v2
    · rw [he2] at hargs_ex; simp at hargs_ex
    · rw [he2] at hargs_ex
      simp only [Option.some.injEq] at hargs_ex
      subst values
      obtain ⟨a2, w_n, ha2, rfl, hn_mem, _⟩ := evalAt_load_one_word hAs.1 he2
      obtain ⟨w1, w80, hw1, hw80, ha2_eq⟩ := evalAt_add2_words ha2
      have hw1_eq : w1 = w_si := by
        have hl1 : state.locals.lookup (ofString "si") = some (.val (.word w1)) := by
          simpa [evalAt, evalHOLExact] using hw1
        exact (by simpa [hlsi] using hl1 : w_si = w1).symm
      have hw80_eq : w80 = 80#64 := by
        simp only [evalAt, evalHOLExact, Option.some.injEq, ValueHOL.val.injEq,
          HolWordLab.word.injEq] at hw80
        exact hw80.symm
      subst w1; subst w80
      have ha2_nat : a2.toNat = w_si.toNat + 80 := by
        rw [ha2_eq, BitVec.toNat_add]
        change (w_si.toNat + 80) % 2 ^ 64 = w_si.toNat + 80
        exact Nat.mod_eq_of_lt (by omega)
      rw [ha2_nat] at hn_mem
      have hpc := callee_param_two state (ofString "validate_headers")
        (ofString "arr") (ofString "n") .one .one _ _
        (by rw [hcode]; exact lookup_validate_headers_fn)
        (.load .one (.op .add [.var .local (ofString "si"), .const 72#64]))
        (.load .one (.op .add [.var .local (ofString "si"), .const 80#64]))
        v1 (.val (.word w_n)) [v1, .val (.word w_n)] body callee ret he1 he2 hargs hl
      set entry := callEntryStateHOLFinite state callee
      have hloc_n : locN entry "n" = w_n.toNat := by
        simp [entry, locN, callEntryStateHOLFinite, hpc.2]
      have hstep := FunSpec.at_lookup wvh state hcode [v1, .val (.word w_n)] body callee ret hl
        (localsFree_worldOK state callee (state.clock - 1) hW) (by rw [hrun]; simp)
      rw [hrun] at hstep; dsimp only at hstep
      have hws := hstep (Or.inl ⟨value, rfl⟩)
      have hIA_entry : (InputAtNullWith Z) entry S Nd w_si.toNat :=
        (inputAtNullWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
      have hc1 := nullAndBlocks_bufferRegion_conditions hIA_entry (allBlocksGood_nil entry S Nd) ("keccak_pad", 136) (by decide) (by decide) (by decide)
      have hc2 := nullAndBlocks_bufferRegion_conditions hIA_entry (allBlocksGood_nil entry S Nd) ("keccak_st", 200) (by decide) (by decide) (by decide)
      obtain ⟨S', Nd', hIA_post, _, _, hu_rc, _, _, _, hQ⟩ :=
        worldStep_preserves_nullAndBlocks hIA_entry (allBlocksGood_nil entry S Nd) hws
          (fun j hj => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
            rcases hj with rfl | rfl
            · exact hc1.1
            · exact hc2.1)
          (fun j hj k hk => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
            rcases hj with rfl | rfl
            · exact hc1.2.1 _ (by simp [bufferRegion]) k hk
            · exact hc2.2.1 _ (by simp [bufferRegion]) k hk)
          (fun c hc j hj => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
            rcases hj with rfl | rfl
            · exact hc1.2.2.1 c hc _ (by simp [bufferRegion])
            · exact hc2.2.2.1 c hc _ (by simp [bufferRegion]))
          (fun b hb _ _ => nomatch hb)
      obtain ⟨a, b, rfl, ha8, hWok, hIn, _, hh⟩ := hQ value rfl
      rw [hloc_n] at hWok hIn hh
      have hsi_unhit := hu_rc (w_si.toNat, 96) (by simp [runAttemptCells])
      have hmem_si0 : memW post w_si.toNat = memW state w_si.toNat :=
        R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit hsi_unhit hsi_rc.1
          hsi_lt ⟨by omega, by omega⟩
      have hmem_si80 : memW post (w_si.toNat + 80) = memW state (w_si.toNat + 80) :=
        R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit hsi_unhit (by have := hsi_rc.1; omega)
          hsi_lt ⟨by omega, by omega⟩
      have hn_post : w_n.toNat = memW post (w_si.toNat + 80) := by omega
      rw [hn_post] at hWok hIn hh
      set res := setVarHOLFinite (ofString "vh") (.rStruct [.val (.word a), .val (.word b)])
        { post with locals := state.locals }
      refine ⟨w_si, w_pl, a, b, S', Nd',
        (inputAtNullWith_with_locals post res.locals post.clock S' Nd' w_si.toNat).2 hIA_post,
        by change w_pl.toNat = memW post w_si.toNat; omega,
        ha8, hWok, hIn, hh, ?_, ?_, ?_⟩
      · simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlsi,
          show ofString "vh" ≠ ofString "si" by decide]
      · simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlpl,
          show ofString "vh" ≠ ofString "pl" by decide]
      · simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

theorem ra_dec_nh {K : Nat} {body : ProgHOL 64}
    (hbody : TerminatingProgBoundedOn ((RA_Nh Z) false) body K) :
    TerminatingProgBoundedOn (RA_Vh Z)
      (.dec (ofString "nh") .one
        (.load .one (.op .add [.var .local (ofString "si"), .const 80#64])) body) K := by
  refine dec_eval_on (P := (RA_Vh Z)) (Q := (RA_Nh Z) false) (ofString "nh") .one
    (.load .one (.op .add [.var .local (ofString "si"), .const 80#64])) ?_ hbody
  intro F s v hP hev
  obtain ⟨w_si, w_pl, a, b, S, Nd, hIA, hpl_mem, ha8, hWok, hIn, hh, hlsi, hlpl, hlvh⟩ := hP
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hIA.1.1.2.2.1
  have hsi_in := (hIA.2.1 (w_si.toNat, 96) (by simp [runAttemptCells])).2.1
  obtain ⟨addr, w_nh, ha, rfl, hnh_mem, _⟩ := evalAt_load_one_word hIA.1.1.1 hev
  obtain ⟨w1, w80, hw1, hw80, ha_eq⟩ := evalAt_add2_words ha
  have hw1_eq : w1 = w_si := by
    have hl1 : s.locals.lookup (ofString "si") = some (.val (.word w1)) := by
      simpa [evalAt, evalHOLExact] using hw1
    exact (by simpa [hlsi] using hl1 : w_si = w1).symm
  have hw80_eq : w80 = 80#64 := by
    simp only [evalAt, evalHOLExact, Option.some.injEq, ValueHOL.val.injEq,
      HolWordLab.word.injEq] at hw80
    exact hw80.symm
  subst w1; subst w80
  have ha_nat : addr.toNat = w_si.toNat + 80 := by
    rw [ha_eq, BitVec.toNat_add]
    change (w_si.toNat + 80) % 2 ^ 64 = w_si.toNat + 80
    exact Nat.mod_eq_of_lt (by unfold Inside at hsi_in; omega)
  rw [ha_nat] at hnh_mem
  rw [← hnh_mem] at hWok hIn hh
  set s1 := setVarHOLFinite (ofString "nh") (.val (.word w_nh)) s
  exact ⟨w_si, w_pl, a, b, w_nh, S, Nd,
    (inputAtNullWith_with_locals s _ s.clock S Nd w_si.toNat).2 hIA,
    hpl_mem, hnh_mem, (fun h => by cases h), ha8, hWok, hIn, hh,
    by simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
         show ofString "nh" ≠ ofString "si" by decide, hlsi],
    by simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
         show ofString "nh" ≠ ofString "pl" by decide, hlpl],
    by simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
         show ofString "nh" ≠ ofString "vh" by decide, hlvh],
    by simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]⟩

theorem hoare_ite_nh_zero :
    Hoare ((RA_Nh Z) false)
      (.ite (.cmp .equal (.var .local (ofString "nh")) (.const 0#64))
        (.raise (ofString "BlockErr") (.const 3#64))
        .skip)
      (fun r t => r = none → (RA_Nh Z) true t) := by
  apply Hoare.ite_fall
  · exact ⟨fun s _ _ _ hr => absurd hr (raise_ne_none s _ _)⟩
  · refine Hoare.skip fun s ⟨hP, hcond⟩ _ => ?_
    obtain ⟨w_si, w_pl, a, b, w_nh, S, Nd, hIA, hpl_mem, hnh_mem, _, ha8, hWok, hIn, hh,
      hlsi, hlpl, hlvh, hlnh⟩ := hP
    have hpos : 0 < w_nh.toNat := by
      obtain ⟨w1, w2, hw1, hw2, hcw⟩ := evalAt_cmp s .equal
        (.var .local (ofString "nh")) (.const 0#64) 0#64 hcond
      have hw1_eq : w1 = w_nh := by
        have hl1 : s.locals.lookup (ofString "nh") = some (.val (.word w1)) := by
          simpa [evalAt, evalHOLExact] using hw1
        exact (by simpa [hlnh] using hl1 : w_nh = w1).symm
      have hw2_eq : w2 = 0#64 := by
        simp only [evalAt, evalHOLExact, Option.some.injEq, ValueHOL.val.injEq,
          HolWordLab.word.injEq] at hw2
        exact hw2.symm
      subst w1; subst w2
      have hne : w_nh ≠ 0#64 := by
        intro heq; subst heq
        simp [wordCmpHOL] at hcw
      have hne_nat : w_nh.toNat ≠ 0 := fun hz => hne (BitVec.eq_of_toNat_eq hz)
      omega
    exact ⟨w_si, w_pl, a, b, w_nh, S, Nd, hIA, hpl_mem, hnh_mem, fun _ => hpos,
      ha8, hWok, hIn, hh, hlsi, hlpl, hlvh, hlnh⟩

theorem ra_dec_parent {K : Nat} {body : ProgHOL 64}
    (hbody : TerminatingProgBoundedOn (RA_ParentPre Z) body K) :
    TerminatingProgBoundedOn ((RA_Nh Z) true)
      (.dec (ofString "parent") .one
        (.load .one
          (.op .add
            [.rfield 0 (.var .local (ofString "vh")),
             .panop .mul
               [.op .sub [.var .local (ofString "nh"), .const 1#64],
                .const 8#64]])) body) K := by
  refine dec_eval_on (P := (RA_Nh Z) true) (Q := (RA_ParentPre Z)) (ofString "parent") .one
    (.load .one
      (.op .add
        [.rfield 0 (.var .local (ofString "vh")),
         .panop .mul
           [.op .sub [.var .local (ofString "nh"), .const 1#64],
            .const 8#64]])) ?_ hbody
  intro F s v hP hev
  obtain ⟨w_si, w_pl, a, b, w_nh, S, Nd, hIA, hpl_mem, hnh_mem, hpos_f,
    ha8, hWok, hIn, hh, hlsi, hlpl, hlvh, hlnh⟩ := hP
  have hpos : 0 < w_nh.toNat := hpos_f rfl
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hIA.1.1.2.2.1
  obtain ⟨addr, w_parent, haddr, rfl, hpar_mem, _⟩ := evalAt_load_one_word hIA.1.1.1 hev
  have hsub_nat : (w_nh - 1#64).toNat = w_nh.toNat - 1 := by
    have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_sub_of_le]
    · omega
    · rw [BitVec.le_def]; omega
  have hbound : a.toNat + 8 * w_nh.toNat ≤ 2 ^ 64 := by
    unfold Inside at hIn; omega
  have hmul_nat : ((w_nh - 1#64) * 8#64).toNat = 8 * (w_nh.toNat - 1) := by
    have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
    rw [BitVec.toNat_mul, hsub_nat, h8]
    change ((w_nh.toNat - 1) * 8) % 2 ^ 64 = 8 * (w_nh.toNat - 1)
    rw [Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]
  have haddr_expected : evalAt s
      (.op .add
        [.rfield 0 (.var .local (ofString "vh")),
         .panop .mul
           [.op .sub [.var .local (ofString "nh"), .const 1#64],
            .const 8#64]]) =
      some (.val (.word (a + (w_nh - 1#64) * 8#64))) := by
    simp [evalAt, evalHOLExact, evalListHOLExact, hlvh, hlnh,
      valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp, BitVec.add_zero]
  rw [haddr_expected] at haddr
  injection haddr with haddr'; injection haddr' with haddr''; injection haddr'' with haddr_eq
  subst addr
  have haddr_nat : (a + (w_nh - 1#64) * 8#64).toNat = a.toNat + 8 * (w_nh.toNat - 1) := by
    rw [BitVec.toNat_add, hmul_nat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [haddr_nat] at hpar_mem
  obtain ⟨hPar_h, hIn_h, hDisj_h⟩ := hh (w_nh.toNat - 1) (by omega)
  rw [← hpar_mem] at hPar_h hIn_h hDisj_h
  have hBs : AllBlocksGood s S Nd [(w_parent.toNat, 248)] := by
    intro blk hblk
    rw [List.mem_singleton.1 hblk]
    exact ⟨hPar_h.1.1, show 248 % 8 = 0 by decide, hIn_h, hPar_h.1, hDisj_h⟩
  set s1 := setVarHOLFinite (ofString "parent") (.val (.word w_parent)) s
  exact ⟨w_si, w_pl, w_parent, a, b, w_nh, S, Nd,
    (inputAtNullWith_with_locals s _ s.clock S Nd w_si.toNat).2 hIA,
    (allBlocksGood_with_locals s _ s.clock S Nd [(w_parent.toNat, 248)]).2 hBs,
    hPar_h, hpl_mem,
    by simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
         show ofString "parent" ≠ ofString "si" by decide, hlsi],
    by simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
         show ofString "parent" ≠ ofString "pl" by decide, hlpl],
    by simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    by simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
         show ofString "parent" ≠ ofString "vh" by decide, hlvh],
    by simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
         show ofString "parent" ≠ ofString "nh" by decide, hlnh]⟩

theorem hoare_assign_block_hashes :
    Hoare (RA_ParentPre Z)
      (.assign .global (ofString "block_hashes") (.rfield 1 (.var .local (ofString "vh"))))
      (fun r t => r = none → (RA_ParentPre Z) t) := by
  apply Hoare.assign_fall
  intro F s v hP hev
  obtain ⟨w_si, w_pl, w_parent, a, b, w_nh, S, Nd, hIA, hBs, hPar, hpl_mem,
    hlsi, hlpl, hlpar, hlvh, hlnh⟩ := hP
  have hv : v = .val (.word b) := by
    have hexp : evalAt s (.rfield 1 (.var .local (ofString "vh"))) = some (.val (.word b)) := by
      simp [evalAt, evalHOLExact, hlvh]
    rw [hexp] at hev; exact Option.some.inj hev |>.symm
  subst hv
  obtain ⟨hIA', hBs', _⟩ := nullAndBlocks_setGlobal_untracked (gname := ofString "block_hashes")
    (w := b) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hIA hBs
  exact ⟨w_si, w_pl, w_parent, a, b, w_nh, S, Nd, hIA', hBs', hPar, hpl_mem,
    hlsi, hlpl, hlpar, hlvh, hlnh⟩

theorem hoare_assign_block_hashes_n :
    Hoare (RA_ParentPre Z)
      (.assign .global (ofString "block_hashes_n") (.var .local (ofString "nh")))
      (fun r t => r = none → (RA_Parent Z) t) := by
  apply Hoare.assign_fall
  intro F s v hP hev
  obtain ⟨w_si, w_pl, w_parent, a, b, w_nh, S, Nd, hIA, hBs, hPar, hpl_mem,
    hlsi, hlpl, hlpar, _, hlnh⟩ := hP
  have hv : v = .val (.word w_nh) := by
    have hexp : evalAt s (.var .local (ofString "nh")) = some (.val (.word w_nh)) := by
      simp [evalAt, evalHOLExact, hlnh]
    rw [hexp] at hev; exact Option.some.inj hev |>.symm
  subst hv
  obtain ⟨hIA', hBs', _⟩ := nullAndBlocks_setGlobal_untracked (gname := ofString "block_hashes_n")
    (w := w_nh) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hIA hBs
  exact ⟨w_si, w_pl, w_parent, S, Nd, hIA', hBs', hPar, hpl_mem, hlsi, hlpl, hlpar⟩

theorem decCallResumeOn_check_gas_limit
    (rocgl : ReadOnlyFn (ofString "check_gas_limit"))
    (arguments : List (ExpHOL 64)) :
    DecCallResumeOn (RA_Parent Z) (RA_Parent Z)
      (ofString "gas_ok") (ofString "check_gas_limit") arguments :=
  ReadOnlyFn.resumeOn localsOnly_ra_parent (fun _ h => ra_parent_guestInv h)
    rocgl (ofString "gas_ok")
    (by intro n hn; simp at hn; rcases hn with rfl | rfl | rfl <;> decide) arguments

def RA_Nodedb (Z : Prop) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ w_si w_pl w_parent w_nodedb : BitVec 64, ∃ S Nd : List Nat,
    (InputAtNullWith Z) s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_parent.toNat, 248)] ∧
    HeaderAt s w_parent.toNat ∧
    w_pl.toNat = memW s w_si.toNat ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "parent") = some (.val (.word w_parent)) ∧
    s.locals.lookup (ofString "nodedb") = some (.val (.word w_nodedb))

def RA_Codedb (Z : Prop) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ w_si w_pl w_parent w_nodedb w_codedb : BitVec 64, ∃ S Nd : List Nat,
    (InputAtNullWith Z) s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_parent.toNat, 248)] ∧
    HeaderAt s w_parent.toNat ∧
    w_pl.toNat = memW s w_si.toNat ∧
    HtabWF s w_codedb.toNat ∧
    hdr s w_codedb.toNat 0 = 32 ∧
    (∀ i ∈ htabFootprint s w_codedb.toNat, Inside i sourceBase (globN s "heap_ptr")) ∧
    IvlsDisj (htabFootprint s w_codedb.toNat) (worldOwned s S Nd) ∧
    IvlsDisj (runAttemptCells s w_si.toNat) (htabFootprint s w_codedb.toNat) ∧
    IvlsDisj [(w_parent.toNat, 248)] (htabFootprint s w_codedb.toNat) ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "parent") = some (.val (.word w_parent)) ∧
    s.locals.lookup (ofString "nodedb") = some (.val (.word w_nodedb)) ∧
    s.locals.lookup (ofString "codedb") = some (.val (.word w_codedb))

def RunAttemptPreScan (Z : Prop) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ w_si w_pl w_parent : BitVec 64, ∃ S Nd : List Nat,
    (InputAtNullWith Z) s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_parent.toNat, 248)] ∧
    HeaderAt s w_parent.toNat ∧
    w_pl.toNat = memW s w_si.toNat ∧
    globN s "journal_cap" ≠ 0 ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "parent") = some (.val (.word w_parent))

theorem ra_nodedb_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F} (h : (RA_Nodedb Z) s) :
    GuestInv s := by
  obtain ⟨_, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1.1

theorem ra_codedb_worldOK {F : Type} {s : PanSemStateFiniteExact 64 F} (h : (RA_Codedb Z) s) :
    WorldOK s := by
  obtain ⟨_, _, _, _, _, S, Nd, hIA, _⟩ := h
  exact ⟨hIA.1.1, S, (worldTyped_iff_with s S).2 ⟨Nd, hIA.1.2.1⟩⟩

theorem runAttemptPreScan_postScan {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : (RunAttemptPreScan Z) s) : (RunAttemptPostScan Z) s := by
  obtain ⟨w_si, w_pl, w_parent, S, Nd, hIA, hBs, hPar, _, hjc, hsi, hpl, hpar⟩ := h
  exact ⟨w_si, w_pl, w_parent, S, Nd, hIA, hBs, hPar, hjc, hsi, hpl, hpar⟩

theorem localsOnly_runAttemptPreScan : LocalsOnly ["si", "pl", "parent"] (RunAttemptPreScan Z) := by
  intro F s locals k hl hP
  obtain ⟨w_si, w_pl, w_parent, S, Nd, hIA, hBs, hPar, hpl_mem, hjc, hsi, hpl, hpar⟩ := hP
  exact ⟨w_si, w_pl, w_parent, S, Nd,
    (inputAtNullWith_with_locals s locals k S Nd w_si.toNat).2 hIA,
    (allBlocksGood_with_locals s locals k S Nd [(w_parent.toNat, 248)]).2 hBs,
    hPar, hpl_mem, hjc,
    (hl "si" (by simp)).trans hsi,
    (hl "pl" (by simp)).trans hpl,
    (hl "parent" (by simp)).trans hpar⟩

theorem decCallResumeOn_nodedb_first
    (wnb : WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetNodeDb (ofString "nodedb_build"))
    (arguments : List (ExpHOL 64)) :
    DecCallResumeOn (RA_Parent Z) (RA_Nodedb Z)
      (ofString "nodedb") (ofString "nodedb_build") arguments := by
  intro F state values body callee ret value post hcode hP _ hl hrun
  obtain ⟨w_si, w_pl, w_parent, S, Nd, hIA, hBs, hPar, hpl_mem, hlsi, hlpl, hlpar⟩ := hP
  have hAs : ArenaReady state := hIA.1.1
  have hW : WorldOK state := ⟨hAs, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.1.2.1⟩⟩
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hhp_lim : globN state "heap_ptr" ≤ heapLimit := hAs.2.2.1
  have hsi_rc := hIA.2.1 (w_si.toNat, 96) (by simp [runAttemptCells])
  have hsi_in := hsi_rc.2.1
  have hpar_in := (hBs (w_parent.toNat, 248) (by simp)).2.2.1
  set entry := callEntryStateHOLFinite state callee
  have hstep := FunSpec.at_lookup wnb state hcode values body callee ret hl
    (localsFree_worldOK state callee (state.clock - 1) hW) (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  have hws := hstep (Or.inl ⟨value, rfl⟩)
  have hIA_entry : (InputAtNullWith Z) entry S Nd w_si.toNat :=
    (inputAtNullWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
  have hBs_entry : AllBlocksGood entry S Nd [(w_parent.toNat, 248)] :=
    (allBlocksGood_with_locals state callee (state.clock - 1) S Nd [(w_parent.toNat, 248)]).2 hBs
  have hc1 := nullAndBlocks_bufferRegion_conditions hIA_entry hBs_entry ("keccak_pad", 136) (by decide) (by decide) (by decide)
  have hc2 := nullAndBlocks_bufferRegion_conditions hIA_entry hBs_entry ("keccak_st", 200) (by decide) (by decide) (by decide)
  have hc3 := nullAndBlocks_bufferRegion_conditions hIA_entry hBs_entry ("mpt_hash_scratch", 40) (by decide) (by decide) (by decide)
  obtain ⟨S', Nd', hIA_post, hBs_post, _, hu_rc, hu_bs, _, _, hQ⟩ :=
    worldStep_preserves_nullAndBlocks hIA_entry hBs_entry hws
      (fun j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · exact hc1.1
        · exact hc2.1
        · exact hc3.1)
      (fun j hj k hk => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · exact hc1.2.1 _ (by simp [bufferRegion]) k hk
        · exact hc2.2.1 _ (by simp [bufferRegion]) k hk
        · exact hc3.2.1 _ (by simp [bufferRegion]) k hk)
      (fun c hc j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · exact hc1.2.2.1 c hc _ (by simp [bufferRegion])
        · exact hc2.2.2.1 c hc _ (by simp [bufferRegion])
        · exact hc3.2.2.1 c hc _ (by simp [bufferRegion]))
      (fun b hb j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · exact hc1.2.2.2 b hb _ (by simp [bufferRegion])
        · exact hc2.2.2.2 b hb _ (by simp [bufferRegion])
        · exact hc3.2.2.2 b hb _ (by simp [bufferRegion]))
  obtain ⟨w_nodedb, rfl, _⟩ := hQ value rfl
  have hPar_post : HeaderAt post w_parent.toNat :=
    headerAt_of_unhit hAs.1 hIA_post.1.1.1 (by unfold Inside at hpar_in; omega)
      (hu_bs (w_parent.toNat, 248) (by simp)) hPar
  have hmem_si0 : memW post w_si.toNat = memW state w_si.toNat :=
    R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit
      (hu_rc (w_si.toNat, 96) (by simp [runAttemptCells])) hsi_rc.1
      (by unfold Inside at hsi_in; omega) ⟨by omega, by omega⟩
  set res := setVarHOLFinite (ofString "nodedb") (.val (.word w_nodedb))
    { post with locals := state.locals }
  refine ⟨w_si, w_pl, w_parent, w_nodedb, S', Nd',
    (inputAtNullWith_with_locals post res.locals post.clock S' Nd' w_si.toNat).2 hIA_post,
    (allBlocksGood_with_locals post res.locals post.clock S' Nd' [(w_parent.toNat, 248)]).2 hBs_post,
    hPar_post,
    by change w_pl.toNat = memW post w_si.toNat; omega,
    ?_, ?_, ?_, ?_⟩
  · simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlsi,
      show ofString "nodedb" ≠ ofString "si" by decide]
  · simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlpl,
      show ofString "nodedb" ≠ ofString "pl" by decide]
  · simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlpar,
      show ofString "nodedb" ≠ ofString "parent" by decide]
  · simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

theorem decCallResumeOn_nodedb_codedb
    (wnb : WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetNodeDb (ofString "nodedb_build"))
    (arguments : List (ExpHOL 64)) :
    DecCallResumeOn (RA_Nodedb Z) (RA_Codedb Z)
      (ofString "codedb") (ofString "nodedb_build") arguments := by
  intro F state values body callee ret value post hcode hP _ hl hrun
  obtain ⟨w_si, w_pl, w_parent, w_nodedb, S, Nd, hIA, hBs, hPar, hpl_mem,
    hlsi, hlpl, hlpar, hlnb⟩ := hP
  have hAs : ArenaReady state := hIA.1.1
  have hW : WorldOK state := ⟨hAs, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.1.2.1⟩⟩
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hhp_lim : globN state "heap_ptr" ≤ heapLimit := hAs.2.2.1
  have hsi_rc := hIA.2.1 (w_si.toNat, 96) (by simp [runAttemptCells])
  have hsi_in := hsi_rc.2.1
  have hpar_in := (hBs (w_parent.toNat, 248) (by simp)).2.2.1
  set entry := callEntryStateHOLFinite state callee
  have hstep := FunSpec.at_lookup wnb state hcode values body callee ret hl
    (localsFree_worldOK state callee (state.clock - 1) hW) (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  have hws := hstep (Or.inl ⟨value, rfl⟩)
  have hIA_entry : (InputAtNullWith Z) entry S Nd w_si.toNat :=
    (inputAtNullWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
  have hBs_entry : AllBlocksGood entry S Nd [(w_parent.toNat, 248)] :=
    (allBlocksGood_with_locals state callee (state.clock - 1) S Nd [(w_parent.toNat, 248)]).2 hBs
  have hc1 := nullAndBlocks_bufferRegion_conditions hIA_entry hBs_entry ("keccak_pad", 136) (by decide) (by decide) (by decide)
  have hc2 := nullAndBlocks_bufferRegion_conditions hIA_entry hBs_entry ("keccak_st", 200) (by decide) (by decide) (by decide)
  have hc3 := nullAndBlocks_bufferRegion_conditions hIA_entry hBs_entry ("mpt_hash_scratch", 40) (by decide) (by decide) (by decide)
  obtain ⟨S', Nd', hIA_post, hBs_post, _, hu_rc, hu_bs, _, _, hQ⟩ :=
    worldStep_preserves_nullAndBlocks hIA_entry hBs_entry hws
      (fun j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · exact hc1.1
        · exact hc2.1
        · exact hc3.1)
      (fun j hj k hk => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · exact hc1.2.1 _ (by simp [bufferRegion]) k hk
        · exact hc2.2.1 _ (by simp [bufferRegion]) k hk
        · exact hc3.2.1 _ (by simp [bufferRegion]) k hk)
      (fun c hc j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · exact hc1.2.2.1 c hc _ (by simp [bufferRegion])
        · exact hc2.2.2.1 c hc _ (by simp [bufferRegion])
        · exact hc3.2.2.1 c hc _ (by simp [bufferRegion]))
      (fun b hb j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · exact hc1.2.2.2 b hb _ (by simp [bufferRegion])
        · exact hc2.2.2.2 b hb _ (by simp [bufferRegion])
        · exact hc3.2.2.2 b hb _ (by simp [bufferRegion]))
  obtain ⟨w_codedb, rfl, hWF, hhdr32, hfp_in, hfp_ow⟩ := hQ value rfl
  have hrc_eq : runAttemptCells post w_si.toNat = runAttemptCells entry w_si.toNat :=
    runAttemptCells_eq_of_unhit (inputAtNullWith_strong hIA_entry) hu_rc
  have hsb_le : sourceBase ≤ globN entry "heap_ptr" := hAs.2.1
  have hfp_sb : ∀ i ∈ htabFootprint post w_codedb.toNat, Inside i sourceBase (globN post "heap_ptr") :=
    fun i hi => ⟨le_trans hsb_le (hfp_in i hi).1, (hfp_in i hi).2⟩
  have hrc_fp : IvlsDisj (runAttemptCells post w_si.toNat) (htabFootprint post w_codedb.toNat) := by
    rw [hrc_eq]
    intro c hc i hi
    rcases (hIA.2.1 c hc).2.1 with hc0 | hc_in'
    · exact Or.inl hc0.2
    have hc_in : Inside c sourceBase (globN entry "heap_ptr") := hc_in'
    have hi_in := hfp_in i hi
    unfold Inside at hc_in hi_in
    unfold Disj; omega
  have hpar_fp : IvlsDisj [(w_parent.toNat, 248)] (htabFootprint post w_codedb.toNat) := by
    intro b hb i hi
    rw [List.mem_singleton.1 hb]
    have hb_in : Inside (w_parent.toNat, 248) sourceBase (globN entry "heap_ptr") := hpar_in
    have hi_in := hfp_in i hi
    unfold Inside at hb_in hi_in
    unfold Disj; omega
  have hPar_post : HeaderAt post w_parent.toNat :=
    headerAt_of_unhit hAs.1 hIA_post.1.1.1 (by unfold Inside at hpar_in; omega)
      (hu_bs (w_parent.toNat, 248) (by simp)) hPar
  have hmem_si0 : memW post w_si.toNat = memW state w_si.toNat :=
    R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit
      (hu_rc (w_si.toNat, 96) (by simp [runAttemptCells])) hsi_rc.1
      (by unfold Inside at hsi_in; omega) ⟨by omega, by omega⟩
  set res := setVarHOLFinite (ofString "codedb") (.val (.word w_codedb))
    { post with locals := state.locals }
  refine ⟨w_si, w_pl, w_parent, w_nodedb, w_codedb, S', Nd',
    (inputAtNullWith_with_locals post res.locals post.clock S' Nd' w_si.toNat).2 hIA_post,
    (allBlocksGood_with_locals post res.locals post.clock S' Nd' [(w_parent.toNat, 248)]).2 hBs_post,
    hPar_post,
    by change w_pl.toNat = memW post w_si.toNat; omega,
    (htabWF_with_locals post res.locals post.clock w_codedb.toNat).2 hWF,
    hhdr32, hfp_sb, hfp_ow, hrc_fp, hpar_fp,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlsi,
      show ofString "codedb" ≠ ofString "si" by decide]
  · simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlpl,
      show ofString "codedb" ≠ ofString "pl" by decide]
  · simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlpar,
      show ofString "codedb" ≠ ofString "parent" by decide]
  · simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlnb,
      show ofString "codedb" ≠ ofString "nodedb" by decide]
  · simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

theorem hoare_state_init
    (wsi : WorldReturnsIn StateInitReady
      (fun s => if locN s "codedb" = 0 then [] else [locN s "codedb"]) (fun _ => [])
      ["bs", "heap_ptr", "journal", "journal_cap", "journal_n", "scratch_ptr", "sk_buf", "ts", "ws"]
      [("ws", []), ("bs", []), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetStateInit (ofString "state_init")) :
    Hoare (RA_Codedb Z)
      (.call (some (none, none)) (ofString "state_init")
        [.var .local (ofString "nodedb"),
         .load .one (.op .add [.var .local (ofString "parent"), .const 32#64]),
         .var .local (ofString "codedb")])
      (fun r t => r = none → (RunAttemptPreScan Z) t) := by
  refine ⟨fun {F} state hcode hP _ hr => ?_⟩
  rcases hcall : evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "state_init")
        [.var .local (ofString "nodedb"),
         .load .one (.op .add [.var .local (ofString "parent"), .const 32#64]),
         .var .local (ofString "codedb")]) with ⟨cres, cpost⟩
  have hr' : cres = none := by rw [hcall] at hr; exact hr
  subst hr'
  obtain ⟨w_si, w_pl, w_parent, w_nodedb, w_codedb, S, Nd, hIA, hBs, hPar, hpl_mem,
    hWF, hhdr32, hfp_sb, hfp_ow, hrc_fp, hpar_fp, hlsi, hlpl, hlpar, hlnb, hlcb⟩ := hP
  have hAs : ArenaReady state := hIA.1.1
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hhp_lim : globN state "heap_ptr" ≤ heapLimit := hAs.2.2.1
  have hsi_rc := hIA.2.1 (w_si.toNat, 96) (by simp [runAttemptCells])
  have hsi_in := hsi_rc.2.1
  have hpar_in := (hBs (w_parent.toNat, 248) (by simp)).2.2.1
  rw [evaluateHOLFiniteState_call] at hcall
  rcases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "nodedb"),
       .load .one (.op .add [.var .local (ofString "parent"), .const 32#64]),
       .var .local (ofString "codedb")] with _ | values
  · rw [hargs] at hcall; simp at hcall
  · rw [hargs] at hcall; dsimp only at hcall
    rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "state_init") values
      with _ | ⟨body, callee, ret⟩
    · rw [hl] at hcall; simp at hcall
    · rw [hl] at hcall; dsimp only at hcall
      split_ifs at hcall with hz
      · simp at hcall
      · rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨bres, post⟩
        rw [hrun] at hcall
        cases bres with
        | none => simp at hcall
        | some br =>
          cases br with
          | returned v =>
            dsimp only at hcall
            split_ifs at hcall with hsh
            · obtain ⟨_, hpost_eq⟩ := Prod.mk.inj hcall
              have hargs_ex := hargs
              rw [evalListHOLFinite_eq_toExact] at hargs_ex
              simp only [evalListHOLExact] at hargs_ex
              have he1 : evalAt state (.var .local (ofString "nodedb")) =
                  some (.val (.word w_nodedb)) := by
                simpa [evalAt, evalHOLExact] using hlnb
              have he3 : evalAt state (.var .local (ofString "codedb")) =
                  some (.val (.word w_codedb)) := by
                simpa [evalAt, evalHOLExact] using hlcb
              rw [show @evalHOLExact 64 F _ state.toExact
                    (fun a => Classical.propDecidable (state.memaddrs a))
                    (.var .local (ofString "nodedb")) = some (.val (.word w_nodedb)) from he1] at hargs_ex
              rcases he2 : @evalHOLExact 64 F _ state.toExact
                  (fun a => Classical.propDecidable (state.memaddrs a))
                  (.load .one (.op .add [.var .local (ofString "parent"), .const 32#64]))
                with _ | v2
              · rw [he2] at hargs_ex; simp at hargs_ex
              · have hpc := callee_param_three state (ofString "state_init")
                  (ofString "nodedb") (ofString "state_root") (ofString "codedb")
                  .one .one .one _ _ (by rw [hcode]; exact lookup_state_init_fn)
                  (.var .local (ofString "nodedb"))
                  (.load .one (.op .add [.var .local (ofString "parent"), .const 32#64]))
                  (.var .local (ofString "codedb"))
                  (.val (.word w_nodedb)) v2 (.val (.word w_codedb))
                  values body callee ret he1 he2 he3 hargs hl
                set entry := callEntryStateHOLFinite state callee
                have hloc_cb : locN entry "codedb" = w_codedb.toNat := by
                  simp [entry, locN, callEntryStateHOLFinite, hpc.2.2]
                have hWF_entry : HtabWF entry w_codedb.toNat :=
                  (htabWF_with_locals state callee (state.clock - 1) w_codedb.toNat).2 hWF
                have hSIR : StateInitReady entry := by
                  refine ⟨localsFree_arenaReady state callee (state.clock - 1) hAs, S, Nd,
                    (worldTypedWith_with_locals state callee (state.clock - 1) S Nd).2 hIA.1.2.1,
                    Or.inr ?_⟩
                  rw [hloc_cb]
                  exact ⟨hWF_entry, hhdr32, hfp_sb, hfp_ow⟩
                have hstep := FunSpec.at_lookup wsi state hcode values body callee ret hl
                  hSIR (by rw [hrun]; simp)
                rw [hrun] at hstep; dsimp only at hstep
                have hws := hstep ⟨v, rfl⟩
                have hIA_entry : (InputAtNullWith Z) entry S Nd w_si.toNat :=
                  (inputAtNullWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
                have hBs_entry : AllBlocksGood entry S Nd [(w_parent.toNat, 248)] :=
                  (allBlocksGood_with_locals state callee (state.clock - 1) S Nd [(w_parent.toNat, 248)]).2 hBs
                have hIA_cons : (InputAtNullWith Z) entry (w_codedb.toNat :: S) Nd w_si.toNat :=
                  inputAtNullWith_cons_fresh hIA_entry hWF_entry hfp_sb hfp_ow hrc_fp
                have hBs_cons : AllBlocksGood entry (w_codedb.toNat :: S) Nd [(w_parent.toNat, 248)] :=
                  allBlocksGood_cons_fresh hBs_entry hpar_fp
                obtain ⟨S', Nd', hIA_post, hBs_post, _, hu_rc, hu_bs, _, _, hQ⟩ :=
                  worldStepIn_preserves_nullAndBlocks hIA_cons hBs_cons hws
                    (fun t ht => by
                      split_ifs at ht with hz_cb
                      · nomatch ht
                      · rw [List.mem_singleton.1 ht, hloc_cb]
                        exact List.mem_cons_self)
                    (fun _ hj => nomatch hj)
                    (fun _ hj => nomatch hj)
                    (fun _ _ _ hj => nomatch hj)
                    (fun _ _ _ hj => nomatch hj)
                have hjc_post : globN post "journal_cap" ≠ 0 := hQ v rfl
                have hPar_post : HeaderAt post w_parent.toNat :=
                  headerAt_of_unhit hAs.1 hIA_post.1.1.1 (by unfold Inside at hpar_in; omega)
                    (hu_bs (w_parent.toNat, 248) (by simp)) hPar
                have hmem_si0 : memW post w_si.toNat = memW state w_si.toNat :=
                  R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit
                    (hu_rc (w_si.toNat, 96) (by simp [runAttemptCells])) hsi_rc.1
                    (by unfold Inside at hsi_in; omega) ⟨by omega, by omega⟩
                have hRes : (RunAttemptPreScan Z) { post with locals := state.locals } :=
                  ⟨w_si, w_pl, w_parent, S', Nd',
                    (inputAtNullWith_with_locals post state.locals post.clock S' Nd' w_si.toNat).2 hIA_post,
                    (allBlocksGood_with_locals post state.locals post.clock S' Nd' [(w_parent.toNat, 248)]).2 hBs_post,
                    hPar_post,
                    by change w_pl.toNat = memW post w_si.toNat; omega,
                    hjc_post, hlsi, hlpl, hlpar⟩
                exact hpost_eq ▸ hRes
            · simp at hcall
          | _ => simp [emptyLocalsHOLFinite] at hcall

theorem runAttemptScanBlock_bounded
    (hal : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hexec : TerminatingFunBoundedOn (BlockReadyExecAttemptNull Z)
      (ofString "execute_block") K.«execute_block»)
    (hhh : TerminatingFunBoundedOn GuestInv (ofString "header_hash") K.«header_hash»)
    (hvvh : TerminatingFunBoundedOn GuestInv
      (ofString "is_valid_versioned_hashes") K.«is_valid_versioned_hashes»)
    (hmeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (hmz : TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero»)
    (hph : TerminatingFunBoundedOn (InputReadyNwdZ Z) (ofString "payload_header") K.«payload_header»)
    (hvh : TerminatingFunBoundedOn GuestInv (ofString "validate_header") K.«validate_header»)
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc"))
    (whh : WorldKeeps (fun s => WorldOK s ∧ HeaderOKStrongLocal s)
      (fun s => [(locN s "out", 32),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "header_hash"))
    (wvvh : WorldKeeps WorldOK (fun _ => []) ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "is_valid_versioned_hashes"))
    (romeq : ReadOnlyFn (ofString "memeq"))
    (wmz : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")]) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memzero"))
    (wph : WorldKeeps (InputReadyZ Z)
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
        (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16),
        (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
        (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr", "wd_rlp_slices"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetHeader (ofString "payload_header"))
    (wvh : WorldKeeps
      R16Shards.TopGbodyWk.ValidateHeaderReady
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "validate_header")) :
    TerminatingProgBoundedOn (RunAttemptPreScan Z) runAttemptScanBlockProg
      ((31104957952 + 1) * (0 + 1) +
        ((K.«payload_header» + 1) + (K.«alloc» + 1) + (K.«header_hash» + 1) +
          (K.«memeq» + 1) + (K.«is_valid_versioned_hashes» + 1) + (K.«validate_header» + 1) +
          (K.«alloc» + 1) + (K.«memzero» + 1) + (K.«execute_block» + 1))) := by
  have hc1 : TerminatingProgBoundedOn (RunAttemptPreScan Z) runAttemptPhaseC1Prog
      ((K.«payload_header» + 1) + (K.«alloc» + 1) + (K.«header_hash» + 1) +
        (K.«memeq» + 1) + (K.«is_valid_versioned_hashes» + 1) + (K.«validate_header» + 1) +
        (K.«alloc» + 1) + (K.«memzero» + 1) + (K.«execute_block» + 1)) := by
    intro F s hc hp
    exact runAttemptPhaseC1_bounded hal hexec hhh hvvh hmeq hmz hph hvh
      wal rtal whh wvvh romeq wmz wph wvh s hc (runAttemptPreScan_postScan hp)
  unfold runAttemptScanBlockProg
  intro F s hc hp
  refine runAttemptScan_init_bounded (W := (RunAttemptPreScan Z))
    (fun s h => localsOnly_runAttemptPreScan s s.locals (s.clock - 1) (fun _ _ => rfl) h)
    (fun s v h => localsOnly_runAttemptPreScan s _ s.clock
      (fun n hn => by
        rcases List.mem_cons.1 hn with rfl | hn
        · simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "txs" ≠ ofString "si" by decide]
        · rcases List.mem_cons.1 hn with rfl | hn
          · simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "txs" ≠ ofString "pl" by decide]
          · rcases List.mem_singleton.1 hn with rfl
            simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "txs" ≠ ofString "parent" by decide]) h)
    (fun s v h => localsOnly_runAttemptPreScan s _ s.clock
      (fun n hn => by
        rcases List.mem_cons.1 hn with rfl | hn
        · simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "ntx" ≠ ofString "si" by decide]
        · rcases List.mem_cons.1 hn with rfl | hn
          · simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "ntx" ≠ ofString "pl" by decide]
          · rcases List.mem_singleton.1 hn with rfl
            simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "ntx" ≠ ofString "parent" by decide]) h)
    (fun s v h => localsOnly_runAttemptPreScan s _ s.clock
      (fun n hn => by
        rcases List.mem_cons.1 hn with rfl | hn
        · simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "i" ≠ ofString "si" by decide]
        · rcases List.mem_cons.1 hn with rfl | hn
          · simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "i" ≠ ofString "pl" by decide]
          · rcases List.mem_singleton.1 hn with rfl
            simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "i" ≠ ofString "parent" by decide]) h)
    ?_ hc1 s hc hp
  intro F s hP
  obtain ⟨w_si, w_pl, _, S, Nd, hIA, _, _, hpl_mem, _, _, hlpl, _⟩ := hP
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hIA.1.1.2.2.1
  have hpl_in : Inside (memW s w_si.toNat, 136) sourceBase (globN s "heap_ptr") :=
    inputAtNullWith_pl_inside hIA
  have hntx_lt : memW s (memW s w_si.toNat + 40) < 2 ^ 32 :=
    hIA.1.2.2.2.2.2.1.2.2.1
  refine ⟨hIA.1.1.1, w_pl, hlpl, ?_, ?_⟩
  · unfold Inside at hpl_in; omega
  · rw [hpl_mem]; exact hntx_lt

theorem runAttemptFullProg_bounded
    (hal : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hcgl : TerminatingFunBoundedOn GuestInv (ofString "check_gas_limit") K.«check_gas_limit»)
    (hexec : TerminatingFunBoundedOn (BlockReadyExecAttemptNull Z)
      (ofString "execute_block") K.«execute_block»)
    (hhh : TerminatingFunBoundedOn GuestInv (ofString "header_hash") K.«header_hash»)
    (hvvh : TerminatingFunBoundedOn GuestInv
      (ofString "is_valid_versioned_hashes") K.«is_valid_versioned_hashes»)
    (hmeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (hmz : TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero»)
    (hnb : TerminatingFunBoundedOn GuestInv (ofString "nodedb_build") K.«nodedb_build»)
    (hph : TerminatingFunBoundedOn (InputReadyNwdZ Z) (ofString "payload_header") K.«payload_header»)
    (hsi : TerminatingFunBoundedOn WorldOK (ofString "state_init") K.«state_init»)
    (hvh : TerminatingFunBoundedOn GuestInv (ofString "validate_header") K.«validate_header»)
    (hvhs : TerminatingFunBoundedOn GuestInv (ofString "validate_headers") K.«validate_headers»)
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc"))
    (rocgl : ReadOnlyFn (ofString "check_gas_limit"))
    (whh : WorldKeeps (fun s => WorldOK s ∧ HeaderOKStrongLocal s)
      (fun s => [(locN s "out", 32),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "header_hash"))
    (wvvh : WorldKeeps WorldOK (fun _ => []) ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "is_valid_versioned_hashes"))
    (romeq : ReadOnlyFn (ofString "memeq"))
    (wmz : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")]) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memzero"))
    (_zvmz : ZeroFills (ofString "memzero"))
    (wnb : WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetNodeDb (ofString "nodedb_build"))
    (wph : WorldKeeps (InputReadyZ Z)
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
        (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16),
        (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
        (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr", "wd_rlp_slices"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetHeader (ofString "payload_header"))
    (wsi : WorldReturnsIn StateInitReady
      (fun s => if locN s "codedb" = 0 then [] else [locN s "codedb"]) (fun _ => [])
      ["bs", "heap_ptr", "journal", "journal_cap", "journal_n", "scratch_ptr", "sk_buf", "ts", "ws"]
      [("ws", []), ("bs", []), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetStateInit (ofString "state_init"))
    (wvh : WorldKeeps
      R16Shards.TopGbodyWk.ValidateHeaderReady
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "validate_header"))
    (wvhs : WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetHeadersStrong (ofString "validate_headers")) :
    TerminatingProgBoundedOn (InputReadyNull Z) runAttemptFullProg K.«run_attempt» := by
  have hscan : TerminatingProgBoundedOn (RunAttemptPreScan Z) runAttemptScanBlockProg _ :=
    runAttemptScanBlock_bounded hal hexec hhh hvvh hmeq hmz hph hvh
      wal rtal whh wvvh romeq wmz wph wvh
  have hskip_scan : TerminatingProgBoundedOn (RunAttemptPreScan Z)
      (.seq .skip runAttemptScanBlockProg) _ :=
    TerminatingProgBoundedOn.seq_hoare (P := (RunAttemptPreScan Z))
      (TerminatingProgBoundedOn.of_clock (P := (RunAttemptPreScan Z)) (fun s => clock_skip s))
      (Hoare.skip fun _ h _ => h)
      hscan
  set siArgs : List (ExpHOL 64) :=
    [.var .local (ofString "nodedb"),
     .load .one (.op .add [.var .local (ofString "parent"), .const 32#64]),
     .var .local (ofString "codedb")]
  have hsi_seq : TerminatingProgBoundedOn (RA_Codedb Z) _ _ :=
    TerminatingProgBoundedOn.seq_hoare_trans (P := (RA_Codedb Z)) (Q := (RunAttemptPreScan Z))
      (TerminatingProgBoundedOn.call_on hsi none siArgs
        (callEntryOn_of_imp localsFree_worldOK (fun _ h => ra_codedb_worldOK h) _ siArgs))
      (hoare_state_init wsi)
      hskip_scan
  set cbArgs : List (ExpHOL 64) :=
    [.load .one (.op .add [.var .local (ofString "si"), .const 56#64]),
     .load .one (.op .add [.var .local (ofString "si"), .const 64#64])]
  have hcb_call : TerminatingProgBoundedOn (RA_Nodedb Z) _ _ :=
    TerminatingProgBoundedOn.decCall_on hnb (ofString "codedb") .one cbArgs
      (callEntryOn_of_imp localsFree_guestInv (fun _ h => ra_nodedb_guestInv h) _ cbArgs)
      (decCallResumeOn_nodedb_codedb wnb cbArgs)
      hsi_seq
  set nbArgs : List (ExpHOL 64) :=
    [.load .one (.op .add [.var .local (ofString "si"), .const 40#64]),
     .load .one (.op .add [.var .local (ofString "si"), .const 48#64])]
  have hnb_call : TerminatingProgBoundedOn (RA_Parent Z) _ _ :=
    TerminatingProgBoundedOn.decCall_on hnb (ofString "nodedb") .one nbArgs
      (callEntryOn_of_imp localsFree_guestInv (fun _ h => ra_parent_guestInv h) _ nbArgs)
      (decCallResumeOn_nodedb_first wnb nbArgs)
      hcb_call
  have hite_gok : TerminatingProgBoundedOn (RA_Parent Z)
      (.ite (.cmp .equal (.var .local (ofString "gas_ok")) (.const 0#64))
        (.raise (ofString "BlockErr") (.const 10#64))
        .skip)
      (max 0 0) :=
    TerminatingProgBoundedOn.ite_on
      (TerminatingProgBoundedOn.of_clock (P := (RA_Parent Z)) (fun s => clock_raise s _ _))
      (TerminatingProgBoundedOn.of_clock (P := (RA_Parent Z)) (fun s => clock_skip s))
  have hafter_cgl : TerminatingProgBoundedOn (RA_Parent Z) _ _ :=
    TerminatingProgBoundedOn.seq_hoare (P := (RA_Parent Z))
      hite_gok (Hoare.ite_raise_skip _ _ _) hnb_call
  set cglArgs : List (ExpHOL 64) :=
    [.load .one (.op .add [.var .local (ofString "pl"), .const 88#64]),
     .load .one (.op .add [.var .local (ofString "parent"), .const 104#64])]
  have hcgl_call : TerminatingProgBoundedOn (RA_Parent Z) _ _ :=
    TerminatingProgBoundedOn.decCall_on hcgl (ofString "gas_ok") .one cglArgs
      (callEntryOn_of_imp localsFree_guestInv (fun _ h => ra_parent_guestInv h) _ cglArgs)
      (decCallResumeOn_check_gas_limit rocgl cglArgs)
      hafter_cgl
  have hite_gas22 : TerminatingProgBoundedOn (RA_Parent Z)
      (.ite
        (.cmp .lower
          (.load .one (.op .add [.var .local (ofString "pl"), .const 88#64]))
          (.load .one (.op .add [.var .local (ofString "pl"), .const 96#64])))
        (.raise (ofString "BlockErr") (.const 22#64))
        .skip)
      (max 0 0) :=
    TerminatingProgBoundedOn.ite_on
      (TerminatingProgBoundedOn.of_clock (P := (RA_Parent Z)) (fun s => clock_raise s _ _))
      (TerminatingProgBoundedOn.of_clock (P := (RA_Parent Z)) (fun s => clock_skip s))
  have hgas22_seq : TerminatingProgBoundedOn (RA_Parent Z) _ _ :=
    TerminatingProgBoundedOn.seq_hoare (P := (RA_Parent Z))
      hite_gas22 (Hoare.ite_raise_skip _ _ _) hcgl_call
  have hskip_gas : TerminatingProgBoundedOn (RA_Parent Z) _ _ :=
    TerminatingProgBoundedOn.seq_hoare (P := (RA_Parent Z))
      (TerminatingProgBoundedOn.of_clock (P := (RA_Parent Z)) (fun s => clock_skip s))
      (Hoare.skip fun _ h _ => h)
      hgas22_seq
  have hbhn_seq : TerminatingProgBoundedOn (RA_ParentPre Z) _ _ :=
    TerminatingProgBoundedOn.seq_hoare_trans (P := (RA_ParentPre Z)) (Q := (RA_Parent Z))
      (TerminatingProgBoundedOn.of_clock (P := (RA_ParentPre Z)) (fun s => clock_assign s _ _ _))
      hoare_assign_block_hashes_n
      hskip_gas
  have hbh_seq : TerminatingProgBoundedOn (RA_ParentPre Z) _ _ :=
    TerminatingProgBoundedOn.seq_hoare (P := (RA_ParentPre Z))
      (TerminatingProgBoundedOn.of_clock (P := (RA_ParentPre Z)) (fun s => clock_assign s _ _ _))
      hoare_assign_block_hashes
      hbhn_seq
  have hpar_dec : TerminatingProgBoundedOn ((RA_Nh Z) true) _ _ :=
    ra_dec_parent hbh_seq
  have hite_nh0 : TerminatingProgBoundedOn ((RA_Nh Z) false)
      (.ite (.cmp .equal (.var .local (ofString "nh")) (.const 0#64))
        (.raise (ofString "BlockErr") (.const 3#64))
        .skip)
      (max 0 0) :=
    TerminatingProgBoundedOn.ite_on
      (TerminatingProgBoundedOn.of_clock (P := (RA_Nh Z) false) (fun s => clock_raise s _ _))
      (TerminatingProgBoundedOn.of_clock (P := (RA_Nh Z) false) (fun s => clock_skip s))
  have hnh0_seq : TerminatingProgBoundedOn ((RA_Nh Z) false) _ _ :=
    TerminatingProgBoundedOn.seq_hoare_trans (P := (RA_Nh Z) false) (Q := (RA_Nh Z) true)
      hite_nh0 hoare_ite_nh_zero hpar_dec
  have hnh_dec : TerminatingProgBoundedOn (RA_Vh Z) _ _ :=
    ra_dec_nh hnh0_seq
  set vhsArgs : List (ExpHOL 64) :=
    [.load .one (.op .add [.var .local (ofString "si"), .const 72#64]),
     .load .one (.op .add [.var .local (ofString "si"), .const 80#64])]
  have hvhs_call : TerminatingProgBoundedOn (RA_Pl Z) _ _ :=
    TerminatingProgBoundedOn.decCall_on hvhs (ofString "vh") (.comb [.one, .one]) vhsArgs
      (callEntryOn_of_imp localsFree_guestInv (fun _ h => ra_pl_guestInv h) _ vhsArgs)
      (decCallResumeOn_validate_headers wvhs)
      hnh_dec
  have hskip_vhs : TerminatingProgBoundedOn (RA_Pl Z) _ _ :=
    TerminatingProgBoundedOn.seq_hoare (P := (RA_Pl Z))
      (TerminatingProgBoundedOn.of_clock (P := (RA_Pl Z)) (fun s => clock_skip s))
      (Hoare.skip fun _ h _ => h)
      hvhs_call
  have hall : TerminatingProgBoundedOn (InputReadyNull Z) runAttemptFullProg _ :=
    ra_entry_dec_pl hskip_vhs
  intro F s hc hp
  exact TerminatingRunBounded.weaken (hall s hc hp) (by unfold K.«run_attempt»; omega)

theorem gbody_run_attempt_null_of
    (hal : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hcgl : TerminatingFunBoundedOn GuestInv (ofString "check_gas_limit") K.«check_gas_limit»)
    (hexec : TerminatingFunBoundedOn (BlockReadyExecAttemptNull Z)
      (ofString "execute_block") K.«execute_block»)
    (hhh : TerminatingFunBoundedOn GuestInv (ofString "header_hash") K.«header_hash»)
    (hvvh : TerminatingFunBoundedOn GuestInv
      (ofString "is_valid_versioned_hashes") K.«is_valid_versioned_hashes»)
    (hmeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (hmz : TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero»)
    (hnb : TerminatingFunBoundedOn GuestInv (ofString "nodedb_build") K.«nodedb_build»)
    (hph : TerminatingFunBoundedOn (InputReadyNwdZ Z) (ofString "payload_header") K.«payload_header»)
    (hsi : TerminatingFunBoundedOn WorldOK (ofString "state_init") K.«state_init»)
    (hvh : TerminatingFunBoundedOn GuestInv (ofString "validate_header") K.«validate_header»)
    (hvhs : TerminatingFunBoundedOn GuestInv (ofString "validate_headers") K.«validate_headers»)
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc"))
    (rocgl : ReadOnlyFn (ofString "check_gas_limit"))
    (whh : WorldKeeps (fun s => WorldOK s ∧ HeaderOKStrongLocal s)
      (fun s => [(locN s "out", 32),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "header_hash"))
    (wvvh : WorldKeeps WorldOK (fun _ => []) ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "is_valid_versioned_hashes"))
    (romeq : ReadOnlyFn (ofString "memeq"))
    (wmz : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")]) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memzero"))
    (zvmz : ZeroFills (ofString "memzero"))
    (wnb : WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetNodeDb (ofString "nodedb_build"))
    (wph : WorldKeeps (InputReadyZ Z)
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
        (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16),
        (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
        (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr", "wd_rlp_slices"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetHeader (ofString "payload_header"))
    (wsi : WorldReturnsIn StateInitReady
      (fun s => if locN s "codedb" = 0 then [] else [locN s "codedb"]) (fun _ => [])
      ["bs", "heap_ptr", "journal", "journal_cap", "journal_n", "scratch_ptr", "sk_buf", "ts", "ws"]
      [("ws", []), ("bs", []), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetStateInit (ofString "state_init"))
    (wvh : WorldKeeps
      R16Shards.TopGbodyWk.ValidateHeaderReady
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "validate_header"))
    (wvhs : WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetHeadersStrong (ofString "validate_headers")) :
    TerminatingFunBoundedOn (InputReadyNull Z) (ofString "run_attempt") K.«run_attempt» := by
  refine ⟨(sourceFunctionEntry Guest.Software.guestFn_run_attempt).2.1,
    (sourceFunctionEntry Guest.Software.guestFn_run_attempt).2.2.1,
    (sourceFunctionEntry Guest.Software.guestFn_run_attempt).2.2.2,
    R10Shards.Fast_GbodyC17ToC21.lookup_run_attempt_fn, ?_⟩
  rw [sourceFnBody_run_attempt_eq]
  exact runAttemptFullProg_bounded
    hal hcgl hexec hhh hvvh hmeq hmz hnb hph hsi hvh hvhs
    wal rtal rocgl whh wvvh romeq wmz zvmz wnb wph wsi wvh wvhs

end InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNullR32
