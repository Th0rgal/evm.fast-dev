import InitECandidate.Solver.Wave8GuestInv.FrameGlue
import InitECandidate.Solver.Wave8GuestInv.Shards.S06.StateRestore
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M08.Base
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M19.htab_truncate_spec
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M23.EvmLemmas

/-! `IvlUnhit`, `Hoare` fallthrough combinators, and `StateRestoreLoopInv` (`< 350` LOC). -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R11Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.S06
open InitECandidate.Solver.Wave8Contracts.M08 (disj_of_inside_left disj_of_inside_right
  globN_eq_of_lookup ivl_allocated_bound htabFootprint_eq_of_hdr_unhit htabWF_congr_unhit)
open InitECandidate.Solver.Wave8M19.Htab (call0_flow)
open InitECandidate.Solver.Wave8Contracts.M23 (EvmInvAt)

def IvlUnhit {F : Type} (s post : PanSemStateFiniteExact 64 F) (i : Ivl) : Prop :=
  ∀ a : BitVec 64, a.toNat % 8 = 0 → CellHits a.toNat i → post.memory a = s.memory a

theorem memW_eq_of_ivlUnhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {i : Ivl} (hu : IvlUnhit s post i) {a : Nat}
    (ha8 : a % 8 = 0) (hhi : i.1 + i.2 ≤ 2 ^ 64) (hin : i.1 ≤ a ∧ a + 8 ≤ i.1 + i.2) :
    memW post a = memW s a := by
  have ha_lt : a < 2 ^ 64 := by omega
  have hmem := hu (BitVec.ofNat 64 a)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; exact ha8)
    (by unfold CellHits; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; omega)
  unfold memW; rw [hmem]

theorem ivlUnhit_to_m08 {F : Type} {s post : PanSemStateFiniteExact 64 F} {i : Ivl}
    (hu : IvlUnhit s post i) : InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post i :=
  fun a ha8 h1 h2 => hu a ha8 ⟨by omega, by omega⟩

theorem ivlUnhit_of_frameOutside {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {keep : List Ivl} {fresh i : Ivl}
    (hi_al : i.1 % 8 = 0 ∧ i.2 % 8 = 0)
    (hfr : FrameOutside s post keep fresh)
    (hk_al : ∀ j ∈ keep, j.1 % 8 = 0 ∧ j.2 % 8 = 0)
    (hf_al : fresh.1 % 8 = 0 ∧ fresh.2 % 8 = 0)
    (hk : ∀ j ∈ keep, Disj i j) (hf : Disj i fresh) :
    IvlUnhit s post i := by
  obtain ⟨hia1, hia2⟩ := hi_al
  intro a ha8 ⟨hh1, hh2⟩
  apply hfr a
  · intro j hj ⟨hc1, hc2⟩
    obtain ⟨hja1, hja2⟩ := hk_al j hj
    rcases hk j hj with hd | hd | hd | hd <;> omega
  · intro ⟨hcf1, hcf2⟩
    rcases hf with hd | hd | hd | hd <;> omega

theorem disj_fresh_of_allocated {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {j : Ivl} (hj : Allocated s j) :
    Disj j (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨_, hs_hp, hs_fm, hs_sc, _⟩ := hAs
  obtain ⟨_, hp_hp, _, _, _⟩ := hAp
  rcases hj with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
  · exact Or.inr (Or.inr (Or.inr (by dsimp; omega)))

theorem evmInv_iff_at {F : Type} (s : PanSemStateFiniteExact 64 F) :
    EvmInv s ↔ ArenaReady s ∧ ∃ S, EvmInvAt s S := Iff.rfl

theorem Hoare.dec_fall {P P' Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} {name : MlS} {shape : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (hname : ∀ n ∈ names, ofString n ≠ name)
    (hQ : LocalsOnly names Q)
    (hinit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      evalAt s init = some v → P' (setVarHOLFinite name v s))
    (hbody : Hoare P' body (fun r t => r = none → Q t)) :
    Hoare P (.dec name shape init body) (fun r t => r = none → Q t) :=
  Hoare.dec hname hinit hbody
    (fun _ t locals hl h hr => hQ t locals t.clock hl (h hr))
    (fun _ _ hr => absurd hr (by simp))

theorem Hoare.ite_fall {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {cond : ExpHOL 64} {yes no : ProgHOL 64}
    (hyes : Hoare (fun s => P s ∧ CondTrue cond s) yes (fun r t => r = none → Q t))
    (hno : Hoare (fun s => P s ∧ CondFalse cond s) no (fun r t => r = none → Q t)) :
    Hoare P (.ite cond yes no) (fun r t => r = none → Q t) :=
  Hoare.ite hyes hno (fun _ _ hr => absurd hr (by simp))

theorem Hoare.while_preserve {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {cond : ExpHOL 64} {body : ProgHOL 64}
    (hdec : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → P (decClockHOLFinite s))
    (hbody : Hoare (fun s => P s ∧ CondTrue cond s) body
      (fun r t => (r = none ∨ r = some .continue ∨ r = some .break) → P t)) :
    Hoare P (.while cond body) (fun r t => r = none → P t) := by
  refine ⟨fun {F} s hcode hP _ hr => ?_⟩
  rcases hrun : evaluateHOLFiniteState s (.while cond body) with ⟨r, post⟩
  rw [hrun] at hr; dsimp only at hr; subst hr
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F),
      st.clock = k → st.code = originalRuntimeCode → P st →
      evaluateHOLFiniteState st (.while cond body) = (none, post) → P post from
    this s.clock s rfl hcode hP hrun
  intro k; induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk st_code hPst hst_run
    rw [evaluateHOLFiniteState_while_total] at hst_run
    split at hst_run
    · rename_i w hw
      split at hst_run
      · rename_i hwnz
        split at hst_run
        · simp at hst_run
        · dsimp only at hst_run
          rw [fixClockHOLFinite_evaluateState] at hst_run
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite st) body).1
          have hct : CondTrue cond (decClockHOLFinite st) := by
            obtain ⟨_, hw', hwnz'⟩ := loopActive_decClock (s := st) ⟨w, hw, hwnz⟩
            exact ⟨_, hw', hwnz'⟩
          rcases bRun : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r1, mid⟩
          rw [bRun] at hst_run hrem hmeta
          have hclk_lt : mid.clock < k := by change mid.clock ≤ st.clock - 1 at hrem; omega
          have hb_nt : (evaluateHOLFiniteState (decClockHOLFinite st) body).1 ≠ some .timeOut := by
            intro hto; rw [bRun] at hto; dsimp only at hto; subst hto; simp at hst_run
          have hb_post := hbody.run (decClockHOLFinite st) st_code ⟨hdec st hPst, hct⟩ hb_nt
          rw [bRun] at hb_post; dsimp only at hb_post
          cases r1 with
          | none =>
            exact ih mid.clock hclk_lt mid rfl (hmeta.trans st_code) (hb_post (Or.inl rfl)) hst_run
          | some r1' =>
            cases r1' with
            | «continue» =>
              exact ih mid.clock hclk_lt mid rfl (hmeta.trans st_code) (hb_post (Or.inr (Or.inl rfl))) hst_run
            | «break» =>
              injection hst_run with _ hp; subst hp; exact hb_post (Or.inr (Or.inr rfl))
            | _ => simp at hst_run
      · injection hst_run with _ hp; subst hp; exact hPst
    · simp at hst_run

theorem call0_returned_inv {F : Type} {s post_call : PanSemStateFiniteExact 64 F}
    {fname : MlS} {args : List (ExpHOL 64)}
    (hcall : evaluateHOLFiniteState s (.call (some (none, none)) fname args) = (none, post_call)) :
    ∃ values body callee ret v cpost,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), cpost) ∧
      post_call = { cpost with locals := s.locals } := by
  obtain ⟨values, body, callee, ret, v, cpost, hargs, hl, hrun, heq⟩ :=
    call0_flow s fname args (Or.inl (by rw [hcall]))
  rw [hcall] at heq; injection heq with _ hp
  exact ⟨values, body, callee, ret, v, cpost, hargs, hl, hrun, hp⟩

theorem seq_returned_inv {F : Type} {s : PanSemStateFiniteExact 64 F} {p1 p2 : ProgHOL 64}
    {v : ValueHOL 64}
    (h : (evaluateHOLFiniteState s (.seq p1 p2)).1 = some (.returned v))
    (hn1 : ∀ u, (evaluateHOLFiniteState s p1).1 ≠ some (.returned u)) :
    ∃ m, evaluateHOLFiniteState s p1 = (none, m) ∧
      evaluateHOLFiniteState m p2 = evaluateHOLFiniteState s (.seq p1 p2) := by
  have hseq := evaluateHOLFiniteState_seq_line780 s p1 p2
  rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, m⟩
  rw [hr1] at hseq
  cases r1 with
  | none => exact ⟨m, rfl, hseq.symm⟩
  | some r =>
    rw [hseq] at h; dsimp only at h; injection h with hr; subst hr
    exact absurd hr1 (fun h' => hn1 v (by rw [h']))

theorem call0_ne_returned {F : Type} (s : PanSemStateFiniteExact 64 F) (fn : MlS)
    (args : List (ExpHOL 64)) (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).1 ≠ some (.returned u) := by
  rw [evaluateHOLFiniteState_call]
  rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | _
  · simp
  · dsimp only; rcases lookupCodeHOLFinite s.code.lookup fn _ with _ | ⟨_, _, _⟩
    · simp
    · dsimp only; split
      · simp
      · rcases evaluateHOLFiniteState _ _ with ⟨res, _⟩
        rcases res with _ | r
        · simp
        · cases r with
          | returned _ => dsimp only; split <;> simp
          | _ => simp

theorem ite_ne_returned {F : Type} {s : PanSemStateFiniteExact 64 F}
    {c : ExpHOL 64} {y n : ProgHOL 64}
    (hy : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t y).1 ≠ some (.returned u))
    (hn : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t n).1 ≠ some (.returned u))
    (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.ite c y n)).1 ≠ some (.returned u) := by
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact hn s u
    · exact hy s u
  · simp

theorem evmChain_congr_lc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    evmChain { s with locals := L, clock := k } = evmChain s :=
  evmChain_with_locals s L k

theorem evmR_congr_lc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    evmR { s with locals := L, clock := k } = evmR s :=
  (evm_congr (s := s) (t := { s with locals := L, clock := k }) rfl rfl).2.1

theorem evmInv_congr_lc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (h : EvmInv s) :
    EvmInv { s with locals := L, clock := k } :=
  localsFree_evmInv s L k h

theorem lookup_state_restore :
    originalRuntimeCode.lookup (ofString "state_restore") =
      some ([(ofString "snap", .one)], sourceFnBody Guest.Software.guestFn_state_restore, .one) :=
  lookup_of_guestAst_getElem 359 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_state_restore) rfl

theorem lookup_frame_epilogue :
    originalRuntimeCode.lookup (ofString "frame_epilogue") =
      some ([], sourceFnBody Guest.Software.guestFn_frame_epilogue, .one) :=
  lookup_of_guestAst_getElem 582 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_frame_epilogue) rfl

/-- Loop invariant for `while (snap < journal_n)` in `state_restore` parameterized by pure values:
initial memory `m0`, table list `S`, frame-object list `FO`, and initial globals `j0, jc0, jn0`. -/
def StateRestoreLoopInv (m0 : BitVec 64 → HolWordLab 64) (S : List Nat) (FO : List Ivl)
    (j0 jc0 jn0 : Nat) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ArenaReady s ∧
  (∀ o ∈ FO, Allocated s o) ∧
  (jc0 ≠ 0 → Allocated s (j0, 32 * jc0)) ∧
  (∀ u ∈ S, HtabWF s u ∧ ∀ i ∈ htabFootprint s u, Allocated s i ∧
    (∀ o ∈ FO, Disj i o) ∧ (jc0 ≠ 0 → Disj i (j0, 32 * jc0))) ∧
  (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ∀ i ∈ htabFootprint s u, ∀ j ∈ htabFootprint s v, Disj i j) ∧
  globN s "journal" = j0 ∧
  globN s "journal_cap" = jc0 ∧
  globN s "journal_n" ≤ jn0 ∧
  (∀ k < jn0, memW s (j0 + 32 * k) ∈ S) ∧
  (∀ a : BitVec 64, a.toNat % 8 = 0 → (∃ o ∈ FO, CellHits a.toNat o) → s.memory a = m0 a)

theorem stateRestoreLoopInv_localsFree (m0 : BitVec 64 → HolWordLab 64) (S : List Nat) (FO : List Ivl)
    (j0 jc0 jn0 : Nat) :
    LocalsFree (StateRestoreLoopInv m0 S FO j0 jc0 jn0) := by
  intro F s L k ⟨hA, hFOA, hjrA, hT, hPW, hj, hjc, hjn, hje, hmem⟩
  refine ⟨localsFree_arenaReady s L k hA, hFOA, hjrA,
    fun u hu => ⟨(htabWF_with_locals s L k u).2 (hT u hu).1, (hT u hu).2⟩,
    hPW, hj, hjc, hjn, hje, hmem⟩

/-- Preserving `StateRestoreLoopInv` across an `HtabExit` step on `t0 ∈ S`. -/
theorem stateRestoreLoopInv_of_htabExit (m0 : BitVec 64 → HolWordLab 64) (S : List Nat) (FO : List Ivl)
    (j0 jc0 jn0 : Nat)
    (hjn_le_cap : jn0 ≤ jc0)
    (halign : (∀ o ∈ FO, o.1 % 8 = 0 ∧ o.2 % 8 = 0) ∧ (jc0 ≠ 0 → j0 % 8 = 0 ∧ j0 + 32 * jc0 ≤ 2 ^ 64))
    {F : Type} {s post : PanSemStateFiniteExact 64 F} {t0 : Nat}
    (hInv : StateRestoreLoopInv m0 S FO j0 jc0 jn0 s) (ht0_S : t0 ∈ S)
    (hexit :
      let fresh : Ivl := (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")
      ArenaReady post ∧ HtabWF post t0 ∧
      hdr post t0 0 = hdr s t0 0 ∧ hdr post t0 1 = hdr s t0 1 ∧
      globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
      (∀ i ∈ htabFootprint post t0, Allocated post i ∧
        ((∃ j ∈ htabFootprint s t0, Inside i j.1 (j.1 + j.2)) ∨ Inside i fresh.1 (fresh.1 + fresh.2))) ∧
      FrameOutside s post (htabFootprint s t0) fresh ∧
      (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
        s.globals.lookup k = post.globals.lookup k)) :
    StateRestoreLoopInv m0 S FO j0 jc0 jn0 post := by
  obtain ⟨hAs, hFOA, hjrA, hT, hPW, hj, hjc, hjn, hje, hmem⟩ := hInv
  obtain ⟨hAp, hwf_t0, _, _, hhp, hfp_t0, hfr, hg_kept⟩ := hexit
  have hag : AllocatorGrows s post := by
    refine ⟨hhp, ?_⟩
    rw [globN_eq_of_lookup (hg_kept (ofString "scratch_ptr") (by decide))]
  have hf_al : (globN s "heap_ptr") % 8 = 0 ∧ (globN post "heap_ptr" - globN s "heap_ptr") % 8 = 0 :=
    ⟨hAs.2.2.2.2.2.2.1, by have := hAs.2.2.2.2.2.2.1; have := hAp.2.2.2.2.2.2.1; omega⟩
  have ht0_al : ∀ j ∈ htabFootprint s t0, j.1 % 8 = 0 ∧ j.2 % 8 = 0 := fun j hj => by
    have hw := ((hT t0 ht0_S).1.1 j hj).2
    exact ⟨hw.1, hw.2.1⟩
  have hunhit : ∀ i : Ivl, i.1 % 8 = 0 ∧ i.2 % 8 = 0 →
      (∀ j ∈ htabFootprint s t0, Disj i j) → Allocated s i → IvlUnhit s post i := fun i hial hdi hal =>
    ivlUnhit_of_frameOutside hial hfr ht0_al hf_al hdi (disj_fresh_of_allocated hAs.2 hAp.2 hhp hal)
  have hu_other : ∀ u ∈ S, u ≠ t0 → ∀ i ∈ htabFootprint s u, IvlUnhit s post i := fun u hu hne i hi => by
    have hw := ((hT u hu).1.1 i hi).2
    exact hunhit i ⟨hw.1, hw.2.1⟩ (fun j hj => hPW u hu t0 ht0_S hne i hi j hj) ((hT u hu).2 i hi).1
  have hother_fp : ∀ u ∈ S, u ≠ t0 → htabFootprint post u = htabFootprint s u := fun u hu hne => by
    have hfp := (hT u hu).1.1
    have ht_fp : (u, 88) ∈ htabFootprint s u := by simp [htabFootprint]
    have h264 : heapEnd ≤ 2 ^ 64 := by decide
    exact (htabFootprint_eq_of_hdr_unhit ((hfp _ ht_fp).2.1)
      (by have := (hfp _ ht_fp).1.2; omega) (ivlUnhit_to_m08 (hu_other u hu hne _ ht_fp))).2
  have hu_fo : ∀ o ∈ FO, IvlUnhit s post o := fun o ho =>
    hunhit o (halign.1 o ho) (fun j hj => (((hT t0 ht0_S).2 j hj).2.1 o ho).flip) (hFOA o ho)
  have hu_jr : jc0 ≠ 0 → IvlUnhit s post (j0, 32 * jc0) := fun hnz =>
    hunhit _ ⟨(halign.2 hnz).1, by omega⟩
      (fun j hj => (((hT t0 ht0_S).2 j hj).2.2 hnz).flip) (hjrA hnz)
  have ht0_disj : ∀ i ∈ htabFootprint post t0,
      (∀ u ∈ S, u ≠ t0 → ∀ j ∈ htabFootprint s u, Disj i j) ∧
      (∀ o ∈ FO, Disj i o) ∧ (jc0 ≠ 0 → Disj i (j0, 32 * jc0)) := by
    intro i hi
    rcases (hfp_t0 i hi).2 with ⟨k, hk, hin⟩ | hfresh
    · refine ⟨fun u hu hne j hj => disj_of_inside_left hin (hPW t0 ht0_S u hu hne.symm k hk j hj),
        fun o ho => disj_of_inside_left hin (((hT t0 ht0_S).2 k hk).2.1 o ho),
        fun hnz => disj_of_inside_left hin (((hT t0 ht0_S).2 k hk).2.2 hnz)⟩
    · have hin' : Inside i (globN s "heap_ptr") (globN s "heap_ptr" + (globN post "heap_ptr" - globN s "heap_ptr")) := by
        unfold Inside at hfresh ⊢; omega
      refine ⟨fun u hu _ j hj => (disj_of_inside_right hin'
          (disj_fresh_of_allocated hAs.2 hAp.2 hhp ((hT u hu).2 j hj).1)).flip,
        fun o ho => (disj_of_inside_right hin' (disj_fresh_of_allocated hAs.2 hAp.2 hhp (hFOA o ho))).flip,
        fun hnz => (disj_of_inside_right hin' (disj_fresh_of_allocated hAs.2 hAp.2 hhp (hjrA hnz))).flip⟩
  have hj_post : globN post "journal" = j0 :=
    (globN_eq_of_lookup (hg_kept (ofString "journal") (by decide))).trans hj
  have hjc_post : globN post "journal_cap" = jc0 :=
    (globN_eq_of_lookup (hg_kept (ofString "journal_cap") (by decide))).trans hjc
  have hjn_eq : globN post "journal_n" = globN s "journal_n" :=
    globN_eq_of_lookup (hg_kept (ofString "journal_n") (by decide))
  refine ⟨hAp, fun o ho => hag.allocated (hFOA o ho), fun hnz => hag.allocated (hjrA hnz),
    ?_, ?_, hj_post, hjc_post, by rw [hjn_eq]; exact hjn, ?_,
    fun a ha8 ⟨o, ho, hc⟩ => (hu_fo o ho a ha8 hc).trans (hmem a ha8 ⟨o, ho, hc⟩)⟩
  · intro u hu
    by_cases heq : u = t0
    · subst heq
      exact ⟨hwf_t0, fun i hi => ⟨(hfp_t0 i hi).1, (ht0_disj i hi).2.1, (ht0_disj i hi).2.2⟩⟩
    · rw [hother_fp u hu heq]
      exact ⟨htabWF_congr_unhit hAs.1 hAp.1 (hT u hu).1 (fun i hi => ivlUnhit_to_m08 (hu_other u hu heq i hi)),
        fun i hi => ⟨hag.allocated ((hT u hu).2 i hi).1, ((hT u hu).2 i hi).2⟩⟩
  · intro u hu v hv hne i hi j hj
    by_cases hu0 : u = t0
    · subst hu0; rw [hother_fp v hv hne.symm] at hj; exact (ht0_disj i hi).1 v hv hne.symm j hj
    · by_cases hv0 : v = t0
      · subst hv0; rw [hother_fp u hu hu0] at hi; exact ((ht0_disj j hj).1 u hu hu0 i hi).flip
      · rw [hother_fp u hu hu0] at hi; rw [hother_fp v hv hv0] at hj
        exact hPW u hu v hv hne i hi j hj
  · intro k hk
    have hjc_nz : jc0 ≠ 0 := by omega
    have hk_cap : k < jc0 := lt_of_lt_of_le hk hjn_le_cap
    obtain ⟨hj8, hj_hi⟩ := halign.2 hjc_nz
    rw [memW_eq_of_ivlUnhit (hu_jr hjc_nz) (by omega) hj_hi ⟨by omega, by omega⟩]
    exact hje k hk

end InitECandidate.Solver.Wave8GuestInv.R11Shards
