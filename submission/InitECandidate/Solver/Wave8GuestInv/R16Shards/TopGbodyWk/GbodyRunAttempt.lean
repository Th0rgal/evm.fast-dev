import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28_Core
import InitECandidate.Solver.Wave8GuestInv.ContractParts.C19

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

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

 def runAttemptCells {F : Type} (s : PanSemStateFiniteExact 64 F) (si : Nat) : List Ivl :=
  [(si, 96), (memW s si, 136), (memW s (si + 32), 80),
   (memW s (memW s si + 32), 16 * memW s (memW s si + 40)),
   (memW s (si + 40), 16 * memW s (si + 48)),
   (memW s (si + 56), 16 * memW s (si + 64)),
   (memW s (si + 72), 16 * memW s (si + 80))]

def InputAtStrong {F : Type} (s : PanSemStateFiniteExact 64 F) (si : Nat) : Prop :=
  InputAt s si ∧ ∃ S Nd, WorldTypedWith s S Nd ∧
    (∀ i ∈ runAttemptCells s si,
      i.1 % 8 = 0 ∧ Inside i sourceBase (globN s "heap_ptr") ∧ WordsOK s i) ∧
    IvlsDisj (runAttemptCells s si) (worldOwned s S Nd)

def InputReadyStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => InputAtStrong s (locN s "si")

theorem inputAtStrong_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k si : Nat) :
    InputAtStrong { s with locals := locals, clock := k } si ↔ InputAtStrong s si := by
  simp only [InputAtStrong, inputAt_with_locals, WorldTypedWith,
    tablesTyped_with_locals]
  exact Iff.rfl

theorem localsOnly_inputReadyStrong : LocalsOnly ["si"] InputReadyStrong := by
  intro F s locals k hl hP
  have hsi := locN_congr s locals k "si" (hl "si" (by simp))
  show InputAtStrong _ _
  rw [hsi]
  exact (inputAtStrong_with_locals s locals k _).2 hP

theorem inputReadyStrong_inputReady {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : InputReadyStrong s) : InputReady s := h.1

theorem inputReadyStrong_worldOK {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : InputReadyStrong s) : WorldOK s := inputReady_worldOK s h.1

theorem inputReadyStrong_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : InputReadyStrong s) : GuestInv s := inputReady_guestInv s h.1

def RetHeadersStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F →
    List Nat → List Nat → Prop :=
  fun s r post S Nd => ∀ v, r = some (.returned v) → ∃ a b : BitVec 64,
    v = .rStruct [.val (.word a), .val (.word b)] ∧
    a.toNat % 8 = 0 ∧ WordsOK post (a.toNat, 8 * locN s "n") ∧
    Inside (a.toNat, 8 * locN s "n") sourceBase (globN post "heap_ptr") ∧
    IvlsDisj [(a.toNat, 8 * locN s "n")] (worldOwned post S Nd) ∧
    ∀ i, i < locN s "n" →
      let h := memW post (a.toNat + 8 * i)
      HeaderAt post h ∧ Inside (h, 248) sourceBase (globN post "heap_ptr") ∧
        IvlsDisj [(h, 248)] (worldOwned post S Nd)

theorem retHeadersStrong_retHeaders {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (r : Option (PanSemResultExact 64)) (S Nd : List Nat)
    (h : RetHeadersStrong s r post S Nd) : RetHeaders s r post S Nd := by
  intro v hv
  obtain ⟨a, b, heq, _, _, _, _, hh⟩ := h v hv
  exact ⟨a, b, heq, fun i hi => (hh i hi).1⟩

def BlockReadyExecStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => BlockReadyStrong s ∧ InputReadyStrong s ∧ globN s "journal_cap" ≠ 0

theorem localsOnly_blockReadyExecStrong : LocalsOnly ["si", "hdr"] BlockReadyExecStrong := by
  intro F s locals k hl hP
  refine ⟨localsOnly_blockReadyStrong s locals k hl hP.1, ?_, hP.2.2⟩
  exact localsOnly_inputReadyStrong s locals k (fun n hn => hl n (by simp_all)) hP.2.1

theorem inputReadyStrong_tx_count {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : InputReadyStrong s) : memW s (memW s (locN s "si") + 40) < 2 ^ 32 := by
  obtain ⟨_, _, _, _, _, _, _, hPay, _⟩ := h.1
  exact hPay.2.2.1

theorem inputReadyStrong_blockReady {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : InputReadyStrong s) : BlockReady s := by
  refine ⟨inputReadyStrong_worldOK s h, ?_⟩
  have hn := inputReadyStrong_tx_count s h
  omega

theorem blockReadyExecStrong_of {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : InputReadyStrong s) (hh : HeaderAt s (locN s "hdr"))
    (hj : globN s "journal_cap" ≠ 0) : BlockReadyExecStrong s :=
  ⟨⟨inputReadyStrong_blockReady s h, h.1, hh⟩, h, hj⟩

theorem callEntryOn_inputReadyStrong
    {fname : MlS} {e : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL}
    (hl : originalRuntimeCode.lookup fname = some e)
    (hp : e.1 = [(ofString "si", .one)]) :
    CallEntryOn InputReadyStrong InputReadyStrong fname [.var .local (ofString "si")] := by
  obtain ⟨ps, b, r⟩ := e
  dsimp only at hp
  subst hp
  intro F state values body' callee ret' hcode hP hargs hlook
  have hc := callee_param_one state fname (ofString "si") .one b r
    (by rw [hcode]; exact hl) values body' callee ret' hargs hlook
  have hsi : locN (callEntryStateHOLFinite state callee) "si" = locN state "si" := by
    simp only [locN, callEntryStateHOLFinite, hc]
  show InputAtStrong (callEntryStateHOLFinite state callee)
    (locN (callEntryStateHOLFinite state callee) "si")
  rw [hsi]
  exact (inputAtStrong_with_locals state callee (state.clock - 1) _).2 hP

theorem runAttemptCells_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {si : Nat} (h : InputAtStrong s si)
    (hu : ∀ c ∈ runAttemptCells s si,
      R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post c) :
    runAttemptCells post si = runAttemptCells s si := by
  obtain ⟨hIA, S, Nd, _, hc, _⟩ := h
  have hs := hc (si, 96) (by simp [runAttemptCells])
  have hp := hc (memW s si, 136) (by simp [runAttemptCells])
  have hlim : globN s "heap_ptr" ≤ 2 ^ 64 := by
    have ha := hIA.1.2.2.1
    have hb : heapLimit ≤ 2 ^ 64 := by decide
    omega
  have hsi : ∀ off, off % 8 = 0 → off + 8 ≤ 96 →
      memW post (si + off) = memW s (si + off) := by
    intro off ho hb
    exact R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit
      (hu (si, 96) (by simp [runAttemptCells]))
      (by omega) (by have := hs.2.1.2; omega) ⟨by omega, by omega⟩
  have h0 : memW post si = memW s si := by
    simpa using hsi 0 (by decide) (by decide)
  have hpl : ∀ off, off % 8 = 0 → off + 8 ≤ 136 →
      memW post (memW s si + off) = memW s (memW s si + off) := by
    intro off ho hb
    exact R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit
      (hu (memW s si, 136) (by simp [runAttemptCells]))
      (by have := hp.1; omega) (by have := hp.2.1.2; omega) ⟨by omega, by omega⟩
  simp only [runAttemptCells, h0, hsi 32 (by decide) (by decide),
    hsi 40 (by decide) (by decide), hsi 48 (by decide) (by decide),
    hsi 56 (by decide) (by decide), hsi 64 (by decide) (by decide),
    hsi 72 (by decide) (by decide), hsi 80 (by decide) (by decide),
    hpl 32 (by decide) (by decide), hpl 40 (by decide) (by decide)]

def InputAtStrongWith {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) (si : Nat) : Prop :=
  R10Shards.Fast_GbodyC17ToC21.InputAtWith s S Nd si ∧
    (∀ i ∈ runAttemptCells s si,
      i.1 % 8 = 0 ∧ Inside i sourceBase (globN s "heap_ptr") ∧ WordsOK s i) ∧
    IvlsDisj (runAttemptCells s si) (worldOwned s S Nd)

theorem inputAtStrongWith_strong {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si : Nat} (h : InputAtStrongWith s S Nd si) :
    InputAtStrong s si :=
  ⟨(R10Shards.Fast_GbodyC17ToC21.inputAt_iff_with s si).2 ⟨S, Nd, h.1⟩,
    S, Nd, h.1.2.1, h.2⟩

theorem inputAtStrong_iff_with {F : Type} (s : PanSemStateFiniteExact 64 F) (si : Nat) :
    InputAtStrong s si ↔ ∃ S Nd, InputAtStrongWith s S Nd si := by
  constructor
  · rintro ⟨hIA, S, Nd, hWT, hcs, hd⟩
    obtain ⟨hA, _, _, _, hsmall, _, hn, hp, hr⟩ := hIA
    refine ⟨S, Nd, ⟨hA, hWT, hsmall, ?_, hn, hp, hr⟩, hcs, hd⟩
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
    exact inputAtStrongWith_strong h

theorem inputAtStrongWith_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S Nd : List Nat) (si : Nat) :
    InputAtStrongWith { s with locals := locals, clock := k } S Nd si ↔
      InputAtStrongWith s S Nd si := by
  rw [InputAtStrongWith, R10Shards.Fast_GbodyC17ToC21.inputAtWith_with_locals]
  exact Iff.rfl

theorem worldStep_preserves_inputAtStrongWith
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {S Nd : List Nat} {si : Nat}
    (h : InputAtStrongWith s S Nd si) (hw : WorldStep R gw keep Q s r post)
    (hz : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (ht : IvlsDisj (R s) (worldTypedIvls s S Nd))
    (hi : IvlsDisj (inputCells s si) (R s))
    (hc : IvlsDisj (runAttemptCells s si) (R s)) :
    ∃ S' Nd', InputAtStrongWith post S' Nd' si ∧
      (∀ t ∈ S, t ∈ S') ∧
      (∀ c ∈ runAttemptCells s si, R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post c) ∧
      Q s r post S' Nd' := by
  obtain ⟨S', Nd', hsub, hIA, hog, hfr, hQ⟩ :=
    R10Shards.Fast_GbodyC17ToC21.WorldStep.preserves_inputAtWith h.1 hw hz ht hi
  have hs : ∀ c ∈ runAttemptCells s si,
      Inside c sourceBase (globN post "heap_ptr") ∧
      (∀ o ∈ worldOwned post S' Nd', Disj c o) ∧
      R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post c := by
    intro c hcm
    obtain ⟨ha, hin, hword⟩ := h.2.1 c hcm
    exact R10Shards.Fast_GbodyC17ToC21.heap_ivl_survives_step
      h.1.1.2 hw.2.1 hog hfr
      (R10Shards.Fast_GbodyC17ToC21.worldOwned_zero_aligned h.1.2.1)
      hz ha hword.2.1 hin (h.2.2 c hcm) (hc c hcm)
  have heq := runAttemptCells_eq_of_unhit (inputAtStrongWith_strong h)
    (fun c hcm => (hs c hcm).2.2)
  refine ⟨S', Nd', ⟨hIA, ?_, ?_⟩, hsub, (fun c hcm => (hs c hcm).2.2), hQ⟩
  · rw [heq]
    intro c hcm
    exact ⟨(h.2.1 c hcm).1, (hs c hcm).1,
      R10Shards.Fast_GbodyC17ToC21.wordsOK_transfer h.1.1.1 hw.1.1 (h.2.1 c hcm).2.2⟩
  · rw [heq]
    exact fun c hcm => (hs c hcm).2.1

theorem inputCells_disj_of_runAttemptCells {F : Type}
    {s : PanSemStateFiniteExact 64 F} {si : Nat} {js : List Ivl}
    (hd : IvlsDisj (runAttemptCells s si) js) :
    IvlsDisj (inputCells s si) js := by
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

def AllBlocksGood {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) (bs : List Ivl) : Prop :=
  ∀ b ∈ bs, b.1 % 8 = 0 ∧ b.2 % 8 = 0 ∧
    Inside b sourceBase (globN s "heap_ptr") ∧
    WordsOK s b ∧
    IvlsDisj [b] (worldOwned s S Nd)

theorem allBlocksGood_nil {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat) :
    AllBlocksGood s S Nd [] :=
  fun _ h => nomatch h

theorem allBlocksGood_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S Nd : List Nat) (bs : List Ivl) :
    AllBlocksGood { s with locals := locals, clock := k } S Nd bs ↔ AllBlocksGood s S Nd bs :=
  Iff.rfl

theorem worldStepIn_preserves_strongAndBlocks
    {T : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {S Nd : List Nat} {si : Nat} {bs : List Ivl}
    (h : InputAtStrongWith s S Nd si)
    (hbs : AllBlocksGood s S Nd bs)
    (hw : WorldStepIn T R gw keep Q s r post)
    (hT : ∀ t ∈ T s, t ∈ S)
    (hz : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (ht : IvlsDisj (R s) (worldTypedIvls s S Nd))
    (hc : IvlsDisj (runAttemptCells s si) (R s))
    (hb : IvlsDisj bs (R s)) :
    ∃ S' Nd', InputAtStrongWith post S' Nd' si ∧
      AllBlocksGood post S' Nd' bs ∧
      (∀ t ∈ S, t ∈ S') ∧
      (∀ c ∈ runAttemptCells s si, R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post c) ∧
      (∀ b ∈ bs, R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post b) ∧
      OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd') ∧
      FrameOutside s post (worldOwned s S Nd ++ R s ++ [freeGap s]) (heapFree s) ∧
      Q s r post S' Nd' := by
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  obtain ⟨⟨hAs, hWT, hcells, hdisj_in, hntx63, hPay, hReq⟩, hrc, hrc_disj⟩ := h
  obtain ⟨hAp, hhp, _, _, hStep⟩ := hw
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
  obtain ⟨S', Nd', hsub, hWT', hog, hfr, hQ⟩ := hStep S Nd hWT hT ht
  have hold_z := R10Shards.Fast_GbodyC17ToC21.worldOwned_zero_aligned hWT
  have hR_in := inputCells_disj_of_runAttemptCells hc
  have h_in_surv : ∀ b ∈ inputCells s si,
      Inside b sourceBase (globN post "heap_ptr") ∧
      (∀ o ∈ worldOwned post S' Nd', Disj b o) ∧
      R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post b := by
    intro b hbm
    obtain ⟨hb_in, hb_w⟩ := hcells b hbm
    exact R10Shards.Fast_GbodyC17ToC21.heap_ivl_survives_step
      hAs.2 hhp hog hfr hold_z hz hb_w.1 hb_w.2.1 hb_in
      (fun j hj => hdisj_in b hbm j hj) (fun j hj => hR_in b hbm j hj)
  have h_rc_surv : ∀ c ∈ runAttemptCells s si,
      Inside c sourceBase (globN post "heap_ptr") ∧
      (∀ o ∈ worldOwned post S' Nd', Disj c o) ∧
      R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post c := by
    intro c hcm
    obtain ⟨ha, hin, hword⟩ := hrc c hcm
    exact R10Shards.Fast_GbodyC17ToC21.heap_ivl_survives_step
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
  obtain ⟨hsi_in_s, hsi_w_s⟩ := hcells (si, 40) hsi_mem
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
  obtain ⟨hpl_in_s, hpl_w_s⟩ := hcells (pl, 136) hpl_mem
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
  obtain ⟨hrq_in_s, hrq_w_s⟩ := hcells (rq, 80) hrq_mem
  obtain ⟨_, _, hrq_u⟩ := h_in_surv (rq, 80) hrq_mem
  have hptxs_mem : (memW s (pl + 32), 16 * memW s (pl + 40)) ∈ inputCells s si := by
    simp [inputCells, pl]
  obtain ⟨hptxs_in_s, hptxs_w_s⟩ := hcells _ hptxs_mem
  obtain ⟨_, _, hptxs_u⟩ := h_in_surv _ hptxs_mem
  have hIA' : R10Shards.Fast_GbodyC17ToC21.InputAtWith post S' Nd' si := by
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
        have hcell_eq : memW post (memW s (pl + 32) + 16 * idx + 8) =
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
  have heq := runAttemptCells_eq_of_unhit (inputAtStrongWith_strong ⟨⟨hAs, hWT, hcells, hdisj_in, hntx63, hPay, hReq⟩, hrc, hrc_disj⟩)
    (fun c hcm => (h_rc_surv c hcm).2.2)
  refine ⟨S', Nd', ⟨hIA', ?_, ?_⟩, ?_, hsub, (fun c hcm => (h_rc_surv c hcm).2.2),
    (fun b hbm => (h_bs_surv b hbm).2.2), hog, hfr, hQ⟩
  · rw [heq]
    exact fun c hcm => ⟨(hrc c hcm).1, (h_rc_surv c hcm).1,
      R10Shards.Fast_GbodyC17ToC21.wordsOK_transfer hAs.1 hAp.1 (hrc c hcm).2.2⟩
  · rw [heq]
    exact fun c hcm => (h_rc_surv c hcm).2.1
  · intro b hbm
    obtain ⟨hb8, hbl8, _, hbw, _⟩ := hbs b hbm
    exact ⟨hb8, hbl8, (h_bs_surv b hbm).1,
      R10Shards.Fast_GbodyC17ToC21.wordsOK_transfer hAs.1 hAp.1 hbw,
      fun b' hb' o ho => by rw [List.mem_singleton.1 hb']; exact (h_bs_surv b hbm).2.1 o ho⟩

theorem worldStep_preserves_strongAndBlocks
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {S Nd : List Nat} {si : Nat} {bs : List Ivl}
    (h : InputAtStrongWith s S Nd si)
    (hbs : AllBlocksGood s S Nd bs)
    (hw : WorldStep R gw keep Q s r post)
    (hz : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (ht : IvlsDisj (R s) (worldTypedIvls s S Nd))
    (hc : IvlsDisj (runAttemptCells s si) (R s))
    (hb : IvlsDisj bs (R s)) :
    ∃ S' Nd', InputAtStrongWith post S' Nd' si ∧
      AllBlocksGood post S' Nd' bs ∧
      (∀ t ∈ S, t ∈ S') ∧
      (∀ c ∈ runAttemptCells s si, R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post c) ∧
      (∀ b ∈ bs, R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post b) ∧
      OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd') ∧
      FrameOutside s post (worldOwned s S Nd ++ R s ++ [freeGap s]) (heapFree s) ∧
      Q s r post S' Nd' :=
  worldStepIn_preserves_strongAndBlocks h hbs (hw.stepIn (T := fun _ => []))
    (fun _ hx => nomatch hx) hz ht hc hb

theorem headerAt_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post) {h : Nat}
    (hh_bound : h + 248 ≤ 2 ^ 64)
    (hu : R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post (h, 248))
    (hH : HeaderAt s h) : HeaderAt post h := by
  obtain ⟨hw, h136⟩ := hH
  refine ⟨R10Shards.Fast_GbodyC17ToC21.wordsOK_transfer hgS hgP hw, ?_⟩
  have hm := R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit (a := h + 136) hu
    (by have := hw.1; omega) hh_bound ⟨by omega, by omega⟩
  rw [hm]; exact h136

theorem worldTypedWith_cons_fresh {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {t : Nat}
    (hW : WorldTypedWith s S Nd)
    (hWF : HtabWF s t)
    (hin : ∀ i ∈ htabFootprint s t, Inside i sourceBase (globN s "heap_ptr"))
    (hdisj : IvlsDisj (htabFootprint s t) (worldOwned s S Nd)) :
    WorldTypedWith s (t :: S) Nd := by
  have hsb : 0 < sourceBase := by decide
  have ht_mem : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
  have ht_in := hin (t, 88) ht_mem
  have ht_ne0 : t ≠ 0 := by unfold Inside at ht_in; omega
  have ht_not_S : t ∉ S := by
    intro htS
    have hu : (t, 88) ∈ worldOwned s S Nd := by
      unfold worldOwned
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨t, htS, ht_mem⟩))
    have hd := hdisj (t, 88) ht_mem (t, 88) hu
    unfold Disj at hd; dsimp only at hd; omega
  have hroot : ∀ x, RootIn S x → RootIn (t :: S) x := by
    rintro x (rfl | hx)
    · exact Or.inl rfl
    · exact Or.inr (List.mem_cons_of_mem t hx)
  have hval_in : ∀ r, HtabValuesIn s r S → HtabValuesIn s r (t :: S) :=
    fun _ hv i hi => List.mem_cons_of_mem t (hv i hi)
  obtain ⟨⟨hnd, htab, hpair, hws, hbs, hts, hg, hbsv, htsv, hbal, hbo, hroles⟩, hJ, hF, hTr⟩ := hW
  refine ⟨⟨List.nodup_cons.2 ⟨ht_not_S, hnd⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo, ?_⟩, ?_, hF, ?_⟩
  · intro u hu
    rcases List.mem_cons.1 hu with rfl | huS
    · refine ⟨hWF, fun i hi => ⟨Or.inl (hin i hi), fun j hj => hdisj i hi j ?_⟩⟩
      unfold worldOwned
      exact List.mem_append_left _ (List.mem_append_right _ hj)
    · exact htab u huS
  · intro u1 hu1 u2 hu2 hne i hi j hj
    rcases List.mem_cons.1 hu1 with rfl | hu1S
    · rcases List.mem_cons.1 hu2 with rfl | hu2S
      · exact absurd rfl hne
      · exact hdisj i hi j (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨u2, hu2S, hj⟩)))
    · rcases List.mem_cons.1 hu2 with rfl | hu2S
      · exact (hdisj j hj i (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨u1, hu1S, hi⟩)))).flip
      · exact hpair u1 hu1S u2 hu2S hne i hi j hj
  · exact fun k hk hg0 => hroot _ (hws k hk hg0)
  · exact fun k hk hg0 => hroot _ (hbs k hk hg0)
  · exact fun k hk hg0 => hroot _ (hts k hk hg0)
  · exact fun g hg0 => hroot _ (hg g hg0)
  · intro hbs0 hmem
    rcases hbs 32 (by decide) hbs0 with h0 | hS32
    · rw [h0] at hmem
      rcases List.mem_cons.1 hmem with h0t | h0S
      · exact absurd h0t.symm ht_ne0
      · exact hval_in _ (hbsv hbs0 (by rw [h0]; exact h0S))
    · exact hval_in _ (hbsv hbs0 hS32)
  · intro hts0 hmem
    rcases hts 32 (by decide) hts0 with h0 | hS32
    · rw [h0] at hmem
      rcases List.mem_cons.1 hmem with h0t | h0S
      · exact absurd h0t.symm ht_ne0
      · exact hval_in _ (htsv hts0 (by rw [h0]; exact h0S))
    · exact hval_in _ (htsv hts0 hS32)
  · exact fun ad had => ⟨List.mem_cons_of_mem t (hbal ad had).1,
      List.mem_cons_of_mem t (hbal ad had).2.1, (hbal ad had).2.2⟩
  · exact ⟨fun a ha => ⟨List.mem_cons_of_mem t (hroles.1 a ha).1, (hroles.1 a ha).2⟩, hroles.2⟩
  · exact ⟨hJ.1, hJ.2.1, hJ.2.2.1, fun i hi => List.mem_cons_of_mem t (hJ.2.2.2 i hi)⟩
  · refine ⟨hTr.1, fun o ho => ⟨?_, (hTr.2.1 o ho).2⟩, fun hws0 => ⟨(hTr.2.2 hws0).1, ?_⟩⟩
    · intro u hu i hi
      rcases List.mem_cons.1 hu with rfl | huS
      · exact (hdisj i hi o (List.mem_append_right _ ho)).flip
      · exact (hTr.2.1 o ho).1 u huS i hi
    · intro hmem
      rcases hws 32 (by decide) hws0 with h0 | hS32
      · rw [h0] at hmem
        rcases List.mem_cons.1 hmem with h0t | h0S
        · exact absurd h0t.symm ht_ne0
        · exact (hTr.2.2 hws0).2 (by rw [h0]; exact h0S)
      · exact (hTr.2.2 hws0).2 hS32

theorem worldOwned_cons {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) (t : Nat) :
    worldOwned s (t :: S) Nd = htabFootprint s t ++ worldOwned s S Nd := by
  simp only [worldOwned, List.flatMap_cons, List.append_assoc]

theorem inputAtStrongWith_cons_fresh {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si t : Nat}
    (h : InputAtStrongWith s S Nd si)
    (hWF : HtabWF s t)
    (hin : ∀ i ∈ htabFootprint s t, Inside i sourceBase (globN s "heap_ptr"))
    (hd : IvlsDisj (htabFootprint s t) (worldOwned s S Nd))
    (hc : IvlsDisj (runAttemptCells s si) (htabFootprint s t)) :
    InputAtStrongWith s (t :: S) Nd si := by
  have hWT := worldTypedWith_cons_fresh h.1.2.1 hWF hin hd
  have hdisj : IvlsDisj (runAttemptCells s si) (worldOwned s (t :: S) Nd) := by
    rw [worldOwned_cons]
    intro c hcm o ho
    rcases List.mem_append.1 ho with ho | ho
    · exact hc c hcm o ho
    · exact h.2.2 c hcm o ho
  exact ⟨⟨h.1.1, hWT, h.1.2.2.1,
    inputCells_disj_of_runAttemptCells hdisj, h.1.2.2.2.2⟩, h.2.1, hdisj⟩

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

theorem strongAndBlocks_bufferRegion_conditions {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {si : Nat} {bs : List Ivl}
    (h : InputAtStrongWith s S Nd si) (hb : AllBlocksGood s S Nd bs)
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
    exact h.2.2 c hc _ hm
  · intro b hbm i hi
    rw [List.mem_singleton.1 hi]
    exact (hb b hbm).2.2.2.2 b (by simp) _ hm

def boundedCounterRank (counter : MlS) (M : Nat) {F : Type}
    (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup counter with
  | some (.val (.word w)) => M - w.toNat
  | _ => 0

theorem while_signed_up_bounded_on
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (c b : MlS) (M : Nat) (hM : M < 2 ^ 63) {body : ProgHOL 64} {B : Nat}
    (hdec : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → P (decClockHOLFinite s))
    (hsmall : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s →
      ∀ wc wb : BitVec 64,
        s.locals.lookup c = some (.val (.word wc)) →
        s.locals.lookup b = some (.val (.word wb)) →
        wc.toNat < 2 ^ 63 ∧ wb.toNat ≤ M)
    (hbody : TerminatingProgBoundedOn P body B)
    (hpres : Hoare (fun s => P s ∧ CondTrue (.cmp .less (.var .local c) (.var .local b)) s)
      body (fun r t => r = none → P t))
    (hncb : noContBreak body = true)
    (hstepC : R10Shards.Fast_GbodyC17ToC21.StepsCounter c body) :
    TerminatingProgBoundedOn P (.while (.cmp .less (.var .local c) (.var .local b)) body)
      ((M + 1) * (B + 1)) := by
  refine TerminatingProgBoundedOn.while_rank (boundedCounterRank c M) hdec hbody ?_ ?_
  · intro F s _ _ _
    unfold boundedCounterRank
    split <;> omega
  · intro F s hcode hPs hact hflow
    have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none := by
      rcases hflow with h | h
      · exact h
      · exact absurd h (noContBreak_sound body hncb (decClockHOLFinite s)).1
    have hct : CondTrue (.cmp .less (.var .local c) (.var .local b)) (decClockHOLFinite s) := by
      obtain ⟨w, hw, hwnz⟩ := loopActive_decClock hact
      refine ⟨w, ?_, hwnz⟩
      rw [← evalHOLFinite_eq_toExact]
      exact hw
    have hPpost := hpres.run (decClockHOLFinite s) hcode ⟨hdec s hPs, hct⟩
      (by rw [hnone]; simp) hnone
    obtain ⟨wc, wb, hlc, hlb, hslt⟩ :=
      R10Shards.Fast_GbodyC17ToC21.loopActive_cmp_less_locals hact
    obtain ⟨hcsmall, hbsmall⟩ := hsmall s hPs wc wb hlc hlb
    have hlt : wc.toNat < wb.toNat := by
      simp only [BitVec.toInt_eq_msb_cond, BitVec.msb_eq_decide] at hslt
      simp only [show ¬ wc.toNat ≥ 2 ^ (64 - 1) by omega,
        show ¬ wb.toNat ≥ 2 ^ (64 - 1) by omega, decide_false, Bool.false_eq_true,
        ↓reduceIte] at hslt
      omega
    have hnext : (wc + 1#64).toNat = wc.toNat + 1 := by
      rw [BitVec.toNat_add]
      exact Nat.mod_eq_of_lt (by change wc.toNat + 1 < 2 ^ 64; omega)
    have hlu := hstepC (decClockHOLFinite s) wc hlc hnone
    refine ⟨hPpost, ?_⟩
    simp only [boundedCounterRank, hlu, hlc, hnext]
    omega

theorem worldTypedWith_setGlobal_untracked {F : Type} {s : PanSemStateFiniteExact 64 F}
    {gname : MlS} {w : BitVec 64} {S Nd : List Nat}
    (hgb : ∀ gn ∈ globalBuffers, ofString gn.1 ≠ gname)
    (hgtr : ∀ g ∈ globalTableRoots, ofString g ≠ gname)
    (hj : ofString "journal" ≠ gname)
    (hjc : ofString "journal_cap" ≠ gname)
    (hjn : ofString "journal_n" ≠ gname)
    (hhp : ofString "heap_ptr" ≠ gname)
    (hfm : ofString "frame_mem_ptr" ≠ gname)
    (hsc : ofString "scratch_ptr" ≠ gname)
    (hAs : ArenaReady s) (hW : WorldTypedWith s S Nd) :
    let post := setGlobalHOLFinite gname (.val (.word w)) s
    ArenaReady post ∧ WorldTypedWith post S Nd ∧
      worldOwned post S Nd = worldOwned s S Nd := by
  intro post
  have hlu : ∀ n : String, ofString n ≠ gname → globN post n = globN s n :=
    fun n hne => globN_setGlobal_ne s gname (.val (.word w)) n hne
  have hAp : ArenaReady post := arenaReady_setGlobal_ne hAs gname w hhp hfm hsc
  have hag : AllocatorGrows s post := by
    unfold AllocatorGrows
    rw [hlu "heap_ptr" hhp, hlu "scratch_ptr" hsc]
    exact ⟨le_rfl, le_rfl⟩
  have hgs : WorldGlobalsSame s post :=
    ⟨fun gn hgn => hlu gn.1 (hgb gn hgn),
      fun g hg => hlu g (hgtr g hg),
      hlu "journal" hj, hlu "journal_cap" hjc, hlu "journal_n" hjn⟩
  have hunhit : ∀ i : Ivl, IvlUnhit s post i := fun _ _ _ _ => rfl
  have hres := worldTypedWith_congr_bo hAs hAp rfl hag hgs hW
    (fun _ _ i _ => hunhit i)
    (fun _ => hunhit _) (fun _ => hunhit _) (fun _ => hunhit _) (fun _ => hunhit _)
    (fun i _ _ => hunhit i) (fun i _ => hunhit i) (fun o _ => hunhit o)
    (fun _ _ _ => rfl) ⟨rfl, rfl⟩
  exact ⟨hAp, hres.1, hres.2.1⟩

theorem strongAndBlocks_setGlobal_untracked {F : Type} {s : PanSemStateFiniteExact 64 F}
    {gname : MlS} {w : BitVec 64} {S Nd : List Nat} {si : Nat} {bs : List Ivl}
    (hgb : ∀ gn ∈ globalBuffers, ofString gn.1 ≠ gname)
    (hgtr : ∀ g ∈ globalTableRoots, ofString g ≠ gname)
    (hj : ofString "journal" ≠ gname)
    (hjc : ofString "journal_cap" ≠ gname)
    (hjn : ofString "journal_n" ≠ gname)
    (hhp : ofString "heap_ptr" ≠ gname)
    (hfm : ofString "frame_mem_ptr" ≠ gname)
    (hsc : ofString "scratch_ptr" ≠ gname)
    (h : InputAtStrongWith s S Nd si)
    (hbs : AllBlocksGood s S Nd bs) :
    let post := setGlobalHOLFinite gname (.val (.word w)) s
    InputAtStrongWith post S Nd si ∧ AllBlocksGood post S Nd bs ∧
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
    ?_, ?_⟩, ?_, hjc_eq⟩
  · rw [hic_eq, hhp_eq]; exact h.1.2.2.1
  · rw [hic_eq, hu.2.2]; exact h.1.2.2.2.1
  · rw [hrc_eq, hhp_eq]; exact h.2.1
  · rw [hrc_eq, hu.2.2]; exact h.2.2
  · intro b hb
    obtain ⟨b1, b2, bin, bw, bow⟩ := hbs b hb
    refine ⟨b1, b2, ?_, bw, ?_⟩
    · rw [hhp_eq]; exact bin
    · rw [hu.2.2]; exact bow

theorem strongAndBlocks_setGlobal_be {F : Type} {s : PanSemStateFiniteExact 64 F}
    {w : BitVec 64} {S Nd : List Nat} {si : Nat} {bs : List Ivl}
    (h : InputAtStrongWith s S Nd si)
    (hbs : AllBlocksGood s S Nd bs)
    (hw8 : w.toNat % 8 = 0)
    (hwin : Inside (w.toNat, 120) sourceBase (globN s "heap_ptr"))
    (hw_ow : IvlsDisj [(w.toNat, 120)] (worldOwned s S Nd))
    (hw_rc : IvlsDisj (runAttemptCells s si) [(w.toNat, 120)])
    (hw_bs : IvlsDisj bs [(w.toNat, 120)]) :
    let post := setGlobalHOLFinite (ofString "be") (.val (.word w)) s
    InputAtStrongWith post S Nd si ∧ AllBlocksGood post S Nd bs ∧
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
    · exact h.2.2 c hc o hold
    · exact hw_rc c hc (w.toNat, 120) (List.mem_singleton.2 rfl)
  refine ⟨⟨⟨hAp, hWT_post, ?_, inputCells_disj_of_runAttemptCells hrc_disj_post,
    h.1.2.2.2.2.1, h.1.2.2.2.2.2.1, h.1.2.2.2.2.2.2⟩, ?_, hrc_disj_post⟩,
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

theorem Hoare_store_fall {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {dst src : ExpHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64) (v : ValueHOL 64)
      (mem' : BitVec 64 → HolWordLab 64),
      P s → evalAt s dst = some (.val (.word x)) → evalAt s src = some v →
      @panMemStoresHOL 64 _ x (flattenHOL v) s.memaddrs
        (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem' →
      Q { s with memory := mem' }) :
    Hoare P (.store dst src) (fun r t => r = none → Q t) := by
  refine ⟨fun {F} s _ hP _ hr => ?_⟩
  rw [evaluateHOLFiniteState_store] at hr ⊢
  revert hr
  split
  · rename_i x hx
    split
    · rename_i v hv
      rcases hm : @panMemStoresHOL 64 _ x (flattenHOL v) s.memaddrs
          (fun a => Classical.propDecidable (s.memaddrs a)) s.memory with _ | mem'
      · simp
      · intro _
        exact h s x v mem' hP hx hv hm
    · simp
  · simp

theorem store_in_be_preserves_strongAndBlocks {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si off : Nat} {bs : List Ivl}
    {x : BitVec 64} {v : ValueHOL 64} {mem' : BitVec 64 → HolWordLab 64}
    (h : InputAtStrongWith s S Nd si)
    (hbs : AllBlocksGood s S Nd bs)
    (hbe_nz : globN s "be" ≠ 0)
    (hoff8 : off % 8 = 0)
    (hoff_fit : off + 8 * (flattenHOL v).length ≤ 120)
    (hdst : evalAt s (.op .add [.var .global (ofString "be"), .const (BitVec.ofNat 64 off)]) =
      some (.val (.word x)))
    (hst : @panMemStoresHOL 64 _ x (flattenHOL v) s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem') :
    let post := { s with memory := mem' }
    InputAtStrongWith post S Nd si ∧
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
  have hcond := strongAndBlocks_bufferRegion_conditions h hbs ("be", 120) hbe_gb hbe_untr (by decide)
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
  have hIA' : R10Shards.Fast_GbodyC17ToC21.InputAtWith post S Nd si := by
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
    runAttemptCells_eq_of_unhit (inputAtStrongWith_strong h) hu_rc
  have hrc_disj : IvlsDisj (runAttemptCells post si) (worldOwned post S Nd) := by
    rw [hrc_eq, hWT_res.2.2.1]; exact h.2.2
  refine ⟨⟨hIA', ?_, hrc_disj⟩, ?_, rfl, rfl, hdisj_unhit⟩
  · rw [hrc_eq]
    exact fun c hc => ⟨(h.2.1 c hc).1, (h.2.1 c hc).2.1,
      R10Shards.Fast_GbodyC17ToC21.wordsOK_transfer hAs.1 hWT_res.1.1 (h.2.1 c hc).2.2⟩
  · intro b hb
    obtain ⟨b1, b2, bin, bw, bow⟩ := hbs b hb
    refine ⟨b1, b2, bin, R10Shards.Fast_GbodyC17ToC21.wordsOK_transfer hAs.1 hWT_res.1.1 bw, ?_⟩
    rw [hWT_res.2.2.1]; exact bow

def RunAttemptScanReady (M : Nat) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ wi wn : BitVec 64,
    s.locals.lookup (ofString "i") = some (.val (.word wi)) ∧
    s.locals.lookup (ofString "ntx") = some (.val (.word wn)) ∧
    wi.toNat ≤ wn.toNat ∧ wn.toNat ≤ M

theorem runAttemptScan_bounded
    {W : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hW : LocalsFree W) (M : Nat) (hM : M < 2 ^ 63) (test : ExpHOL 64) :
    TerminatingProgBoundedOn (fun s => W s ∧ RunAttemptScanReady M s)
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntx")))
        (.seq (.ite test (.raise (ofString "BlockErr") (.const 4#64)) .skip)
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const 1#64]))))
      ((M + 1) * (0 + 1)) := by
  have hdec : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      W s ∧ RunAttemptScanReady M s → W (decClockHOLFinite s) ∧
        RunAttemptScanReady M (decClockHOLFinite s) := by
    intro F s h
    exact ⟨hW s s.locals (s.clock - 1) h.1, h.2⟩
  apply while_signed_up_bounded_on (ofString "i") (ofString "ntx") M hM hdec
  · intro F s h wi wn hi hn
    obtain ⟨wi', wn', hi', hn', hle, hbound⟩ := h.2
    have heqi : wi = wi' := by simpa [hi] using hi'
    have heqn : wn = wn' := by simpa [hn] using hn'
    subst wi'; subst wn'
    exact ⟨by omega, hbound⟩
  · intro F s hcode _
    exact TerminatingProgBounded.straight _ rfl s hcode
  · apply Hoare.seq_fall (Hoare.ite_raise_skip _ _ _)
    apply Hoare.assign_fall
    intro F s v h hev
    obtain ⟨wi, wn, hi, hn, hle, hbound⟩ := h.1.2
    have hact : LoopActive
        (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntx"))) s := by
      obtain ⟨w, hw, hwne⟩ := h.2
      exact ⟨w, by rwa [evalHOLFinite_eq_toExact], hwne⟩
    obtain ⟨wi', wn', hi', hn', hlt⟩ := loopActive_cmp_less_locals hact
    have heqi : wi = wi' := by simpa [hi] using hi'
    have heqn : wn = wn' := by simpa [hn] using hn'
    subst wi'; subst wn'
    have hnat : wi.toNat < wn.toNat := by
      simp only [BitVec.toInt_eq_msb_cond, BitVec.msb_eq_decide] at hlt
      simp only [show ¬ wi.toNat ≥ 2 ^ (64 - 1) by omega,
        show ¬ wn.toNat ≥ 2 ^ (64 - 1) by omega, decide_false,
        Bool.false_eq_true, ↓reduceIte] at hlt
      omega
    have hv : v = .val (.word (wi + 1#64)) := by
      simpa [evalAt, evalHOLExact, evalListHOLExact, hi, valueIsWord, valueWord,
        wordOpHOL, wordOp, BitVec.add_zero] using hev.symm
    subst v
    have hnext : (wi + 1#64).toNat = wi.toNat + 1 := by
      rw [BitVec.toNat_add]
      exact Nat.mod_eq_of_lt (by change wi.toNat + 1 < 2 ^ 64; omega)
    refine ⟨hW s _ s.clock h.1.1, wi + 1#64, wn, ?_, ?_, ?_, hbound⟩
    · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
    · simpa [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "i" ≠ ofString "ntx" by decide] using hn
    · rw [hnext]; omega
  · rfl
  · exact StepsCounter.seq_keep (PreservesCounter.ite_raise_skip _ _ _ _)
      (StepsCounter.assign_inc _)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
