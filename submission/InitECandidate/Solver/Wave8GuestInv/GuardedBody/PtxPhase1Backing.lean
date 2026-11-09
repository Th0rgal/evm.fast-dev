import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2StrongTail4
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase1
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkEncodeTxBounded

/-!
# Wave 8 / R16k: the Phase 1 backing cut (`PtxPhase1BackingCut`)

This module closes the Phase 1 integration obligation documented in the
header of `GuardedBody/PtxPhase2StrongTail4.lean` (the "TxBacking threading
wall"). The seventeen Phase 1 callee steps could not be framed by
`WorldKeeps`-level contracts alone, because `FrameOutside` makes the
world-owned region (which contains the block-out list data objects)
writable. The `R16Shards.TopGbodyWk` ScBo calculus (`WorldKeepsScBo`,
compiled over the pre-cutover tree) supplies exactly the missing
block-out-unhit side condition: `WorldStepScBo = WorldStepSc ∧
(NonExResult r → PtxBlockOutUnhit s post)`.

## Architecture

* `txBacking_of_step_facts` is the generic bridge: bo pointer stability plus
  bo header-word preservation plus `PtxBlockOutUnhit` implies `TxBacking post`
  (`txBacking_of_header_words` over the 24-byte list header objects, which
  are members of `blockOutObjects` whenever the pointers are nonzero).
* `txBacking_of_scbo_returned` packages the three facts out of a
  `WorldStepScBo` step with a `returned` result.
* `decCallResume_bk_of_scbo` turns any `WorldKeepsScBo WorldOK` spec into a
  backing-strengthened `DecCallResumeOn`: the non-backing resume carries the
  callee run equation, `FunSpec.at_lookup` instantiates the ScBo spec at
  that run, and the bridge closes the `TxBacking` conjunct. The resumed
  state differs from the callee post-state only in locals, which `TxBacking`
  does not read.
-/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R13Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8Contracts.M12

/-! ## The generic `TxBacking` bridge -/

/-- The words a `TxBacking` proof needs: the two header words of the `bo`
record and the data words they point at. The pointed words sit at offset 0 of
the 24-byte list header objects `obj l 24`, which are members of
`blockOutObjects` whenever `bo` and the pointers are nonzero, so
`PtxBlockOutUnhit` preserves them. -/
theorem txBacking_of_step_facts {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hW : WorldOK s) (hbonz : globN s "bo" ≠ 0)
    (h40 : memW s (globN s "bo" + 40) ≠ 0) (h72 : memW s (globN s "bo" + 72) ≠ 0)
    (htx : TxBacking s)
    (hbo : globN post "bo" = globN s "bo")
    (hfields : ∀ k ∈ ([40, 72] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k))
    (hu : R16Shards.TopGbodyWk.PtxBlockOutUnhit s post) :
    TxBacking post := by
  obtain ⟨hA, S, hWT0⟩ := hW
  obtain ⟨Nd, hWT⟩ := (worldTyped_iff_with s S).1 hWT0
  have hmem : ∀ k ∈ ([40, 72] : List Nat),
      memW post (memW s (globN s "bo" + k)) = memW s (memW s (globN s "bo" + k)) := by
    intro k hk
    have hk' : k = 40 ∨ k = 72 := by simpa using hk
    have hi : (memW s (globN s "bo" + k), 24) ∈ blockOutObjects s := by
      rcases hk' with rfl | rfl
      · simp [blockOutObjects, hbonz, h40]
      · simp [blockOutObjects, hbonz, h72]
    exact R16Shards.TopGbodyWk.memW_eq_of_ptxBlockOutUnhit hA hWT hu hi
      (off := 0) (by decide) (by norm_num)
  exact R16Shards.txBacking_of_header_words htx hbo
    (fun k hk => hfields k hk) (fun k hk => hmem k hk)

/-- Core transport: `TxBacking` from bo-pointer stability, the two bo header
words, and the block-out unhit. -/
theorem txBacking_of_scbo_step {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hW : WorldOK s) (hbonz : globN s "bo" ≠ 0)
    (h40 : memW s (globN s "bo" + 40) ≠ 0) (h72 : memW s (globN s "bo" + 72) ≠ 0)
    (htx : TxBacking s) (hbo : globN post "bo" = globN s "bo")
    (hf40 : memW post (globN s "bo" + 40) = memW s (globN s "bo" + 40))
    (hf72 : memW post (globN s "bo" + 72) = memW s (globN s "bo" + 72))
    (hu : R16Shards.TopGbodyWk.PtxBlockOutUnhit s post) :
    TxBacking post := by
  refine txBacking_of_step_facts hW hbonz h40 h72 htx hbo ?_ hu
  intro k hk
  have hk' : k = 40 ∨ k = 72 := by simpa using hk
  rcases hk' with rfl | rfl
  · exact hf40
  · exact hf72

/-- A `WorldStepScBo` step over `bufRegions B` whose keep list carries the `bo`
record preserves `TxBacking` on a normal return: the `bo` global is kept, the
bo header words by `RecordsKept` (the write regions are disjoint from the
fixed records), and the pointed list-header words by the ScBo unhit side
condition. -/
theorem txBacking_of_scbo_returned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {B : BufList} {gw : List String} {keep : List (String × List Nat)} {v : ValueHOL 64}
    (hW : WorldOK s) (hbonz : globN s "bo" ≠ 0)
    (h40 : memW s (globN s "bo" + 40) ≠ 0) (h72 : memW s (globN s "bo" + 72) ≠ 0)
    (htx : TxBacking s) (hB : ValidBufList B)
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hbo_keep : ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) ∈ keep)
    (hstep : WorldStepScBo (bufRegions B) gw keep NoExtra s (some (.returned v)) post) :
    TxBacking post := by
  obtain ⟨hA, S, hWT0⟩ := id hW
  obtain ⟨Nd, hWT⟩ := (worldTyped_iff_with s S).1 hWT0
  exact txBacking_of_scbo_step hW hbonz h40 h72 htx
    (globN_eq_of_lookup (hstep.1.1.2.2.1 (ofString "bo") hbo_gw))
    (ptx_bo_field_eq_of_step hB hWT hstep.1.1.2.2.2.1 hbo_keep hbonz
      (off := 40) (by simp) (by decide) (by decide))
    (ptx_bo_field_eq_of_step hB hWT hstep.1.1.2.2.2.1 hbo_keep hbonz
      (off := 72) (by simp) (by decide) (by decide))
    (hstep.2 (Or.inr (Or.inr (Or.inr ⟨v, rfl⟩))))

/-! ## The resumed state -/

/-- `TxBacking` does not read locals, so it is stable under the
`decCall`-resume state surgery. -/
theorem txBacking_setVarResume {F : Type} {post : PanSemStateFiniteExact 64 F}
    {locals : HolFiniteMapExact MlS (ValueHOL 64)} {name : MlS} {v : ValueHOL 64}
    (htx : TxBacking post) :
    TxBacking (setVarHOLFinite name v { post with locals := locals }) := by
  unfold TxBacking
  exact htx

/-! ## The generic ScBo-backed `DecCallResumeOn` adapter -/

/-- Backing-strengthened `DecCallResumeOn` from a ScBo callee spec. The
non-backing resume re-establishes `Q`; `FunSpec.at_lookup` instantiates the
`WorldKeepsScBo` spec at the callee's run equation (the caller-side code
lookup is part of the resume hypothesis), the ScBo step preserves `TxBacking`
across the callee, and the resume surgery only touches locals. The guard
side-condition `hPw` extracts the world/bo facts the bridge needs; for the
Phase 1 replay these come from `TxReadyStrong` (`TxReady` supplies `WorldOK`
and `bo ≠ 0`, the strong conjuncts supply the two pointer words). -/
theorem decCallResumeBk_scbo {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {name fname : MlS} {args : List (ExpHOL 64)} {B : BufList} {gw : List String}
    {keep : List (String × List Nat)}
    (hr : DecCallResumeOn P Q name fname args)
    (hPw : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s →
      WorldOK s ∧ globN s "bo" ≠ 0 ∧
        memW s (globN s "bo" + 40) ≠ 0 ∧ memW s (globN s "bo" + 72) ≠ 0)
    (spec : WorldKeepsScBo WorldOK (bufRegions B) gw keep NoExtra fname)
    (hB : ValidBufList B) (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hbo_keep : ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) ∈ keep) :
    DecCallResumeOn (fun s => P s ∧ TxBacking s) (fun s => Q s ∧ TxBacking s)
      name fname args := by
  intro F state values body callee ret v post hc hp ha hl hb
  refine ⟨hr state values body callee ret v post hc hp.1 ha hl hb, ?_⟩
  obtain ⟨hW, hbonz, h40, h72⟩ := hPw state hp.1
  have hentW : WorldOK (callEntryStateHOLFinite state callee) :=
    localsFree_worldOK state callee (state.clock - 1) hW
  have hspec := FunSpec.at_lookup spec state hc values body callee ret hl hentW
    (by rw [hb]; simp)
  rw [hb] at hspec
  simp only at hspec
  have hq := hspec (Or.inl ⟨v, rfl⟩)
  have htxEnt : TxBacking (callEntryStateHOLFinite state callee) :=
    (R16Shards.txBacking_with_locals state callee (state.clock - 1)).2 hp.2
  have hentBo : globN (callEntryStateHOLFinite state callee) "bo" ≠ 0 := hbonz
  have hent40 : memW (callEntryStateHOLFinite state callee)
      (globN (callEntryStateHOLFinite state callee) "bo" + 40) ≠ 0 := h40
  have hent72 : memW (callEntryStateHOLFinite state callee)
      (globN (callEntryStateHOLFinite state callee) "bo" + 72) ≠ 0 := h72
  exact txBacking_setVarResume
    (txBacking_of_scbo_returned (s := callEntryStateHOLFinite state callee)
      (post := post) (v := v) hentW hentBo hent40 hent72 htxEnt hB hbo_gw hbo_keep hq)

/-! ## Stage 4: state congruence and the read-only adapter -/

/-- `TxBacking` only reads the two header words through the `bo` global, so
equal memory plus an equal `bo` global transport it. -/
theorem txBacking_state_congr {F : Type} {s s' : PanSemStateFiniteExact 64 F}
    (hmem : ∀ x, memW s' x = memW s x) (hg : globN s' "bo" = globN s "bo")
    (h : TxBacking s) : TxBacking s' := by
  refine ⟨?_, ?_⟩
  · rw [hg, hmem, hmem]; exact h.1
  · rw [hg, hmem, hmem]; exact h.2

/-- Backing-and-recover-validity strengthening of any `DecCallResumeOn` whose
callee is read-only. A read-only callee returns the entry state with only
locals and clock replaced, so both `TxBacking` (memory/global transport) and
`TxValidRecoverReady` (locals/clock transport via `with_locals`) survive. -/
theorem decCallResumeBk_ro {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {name fname : MlS} {args : List (ExpHOL 64)}
    (hr : DecCallResumeOn P Q name fname args)
    (hro : ReadOnlyFn fname)
    (hne : ofString "tx" ≠ name)
    (hPg : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s) :
    DecCallResumeOn (fun s => P s ∧ TxBacking s ∧ TxValidRecoverReady s)
      (fun s => Q s ∧ TxBacking s ∧ TxValidRecoverReady s) name fname args := by
  intro F state values body callee ret v post hc hp ha hl hb
  have hspec := FunSpec.at_lookup hro state hc values body callee ret hl
    (guestInv_callEntry state callee (hPg state hp.1)) (by rw [hb]; simp)
  rw [hb] at hspec
  have hro_eq : post = { callEntryStateHOLFinite state callee with
      locals := post.locals, clock := post.clock } := by
    have h1 := hspec (Or.inl ⟨v, rfl⟩)
    simpa using h1
  -- memory and bo transport
  have hmem : ∀ x, memW post x = memW state x := by
    intro x
    rw [hro_eq]
    simp [memW, callEntryStateHOLFinite]
  have hgb : globN post "bo" = globN state "bo" := by
    rw [hro_eq]
    simp [globN, callEntryStateHOLFinite]
  have hset_mem : ∀ x, memW (setVarHOLFinite name v { post with locals := state.locals }) x =
      memW state x := by
    intro x
    have h0 : memW (setVarHOLFinite name v { post with locals := state.locals }) x =
        memW post x := by simp [setVarHOLFinite, memW]
    rw [h0, hmem x]
  have hset_gb : globN (setVarHOLFinite name v { post with locals := state.locals }) "bo" =
      globN state "bo" := by
    have h0 : globN (setVarHOLFinite name v { post with locals := state.locals }) "bo" =
        globN post "bo" := by simp [setVarHOLFinite, globN]
    rw [h0, hgb]
  have hbk' : TxBacking (setVarHOLFinite name v { post with locals := state.locals }) :=
    txBacking_state_congr hset_mem hset_gb hp.2.1
  have hVR' : TxValidRecoverReady (setVarHOLFinite name v { post with locals := state.locals }) := by
    have hVRent : TxValidRecoverReadyAt (callEntryStateHOLFinite state callee) (locN state "tx") :=
      txValidRecoverReadyAt_with_locals state callee (state.clock - 1) hp.2.2
    have hVRpost : TxValidRecoverReadyAt post (locN state "tx") := by
      rw [hro_eq]
      exact txValidRecoverReadyAt_with_locals (callEntryStateHOLFinite state callee)
        post.locals post.clock hVRent
    have hloc : locN (setVarHOLFinite name v { post with locals := state.locals }) "tx" =
        locN state "tx" := by
      simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne.symm]
    unfold TxValidRecoverReady
    rw [hloc]
    exact txValidRecoverReadyAt_with_locals post (state.locals.update (name, v)) post.clock
      hVRpost
  exact ⟨hr state values body callee ret v post hc hp.1 ha hl hb, hbk', hVR'⟩

/-! ## Stage 5: the encode step -/

/-- Backing-strengthened `resume_encode`. The bounded encode spec supplies the
block-out unhit for `TxBacking` (via `txBacking_of_step_facts`), its
`("bo", [0..80])` record-keep entry preserves the two header words, and
`encode_tx_heap_unhit` transports `TxValidRecoverReady` across the callee.
`TxValidEncodeReady` is consumed here (the envelope shrinks). -/
theorem resume_encode_bk :
    R16Shards.PtxP1.DecCallResumeShapeOn
      (fun s => TxReadyStrong s ∧ TxBacking s ∧ TxValidEncodeReady s ∧ TxValidRecoverReady s)
      (fun s => R16Shards.PtxP1.EncReady s ∧ TxBacking s ∧ TxValidRecoverReady s)
      (ofString "enc") (.comb [.one, .one]) (ofString "encode_transaction")
      [.var .local (ofString "tx")] := by
  intro F s vs body callee ret v post hc hp ha hl hb hsh
  obtain ⟨hrdy, hbk, hVE, hVR⟩ := hp
  obtain ⟨tv, he, ht⟩ := R16Shards.PtxP1.params_one_value s (ofString "encode_transaction")
    (ofString "tx") .one _ (.comb [.one, .one])
    (by rw [hc]; exact R16Shards.PtxP1.lookup_encode_transaction)
    (.var .local (ofString "tx")) vs body callee ret ha hl
  have htx : callee.lookup (ofString "tx") = s.locals.lookup (ofString "tx") := ht.trans he.symm
  set entry := callEntryStateHOLFinite s callee with hentry
  have htxN : locN entry "tx" = locN s "tx" := by
    simp only [locN, hentry, callEntryStateHOLFinite, htx]
  have hWent : WorldOK entry := R16Shards.PtxP1.worldOK_callEntry hrdy.1.1 callee
  have hVEent : TxValidEncodeReady entry := by
    unfold TxValidEncodeReady
    rw [htxN]
    exact txValidEncodeAt_with_locals s callee (s.clock - 1) hVE
  have hs := R16Shards.PtxP1.funSpec_at_lookup «wk_encode_transaction_bounded» s hc vs body callee
    ret hl ⟨hWent, hVEent⟩ (by rw [hb]; simp)
  rw [hb] at hs
  have hstep : WorldStep (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetTxSliceBounded entry (some (.returned v)) post := hs (Or.inl ⟨v, rfl⟩)
  refine ⟨?_, ?_, ?_⟩
  · -- `EncReady` at the resumed state
    have hstage := R16Shards.PtxP1.stage_after_scratchStep hstep (R16Shards.PtxP1.stage0 hrdy)
      (gs := []) (by simp [R16Shards.PtxP1.ScratchSpec]) rfl (by decide) (by decide)
      (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) (by decide)
    have hready := R16Shards.PtxP1.txReadyStrong_with_locals { post with locals := s.locals }
      (s.locals.update (ofString "enc", v)) post.clock
      (by simp [HolFiniteMapExact.update, FUPDATE,
        show ofString "enc" ≠ ofString "tx" from by decide])
      (by simp [HolFiniteMapExact.update, FUPDATE,
        show ofString "enc" ≠ ofString "index" from by decide]) hstage.1
    obtain ⟨a, b, rfl⟩ := R16Shards.PtxP1.shape_pair_words hsh
    exact ⟨hready, a, b, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]⟩
  · -- `TxBacking` at the resumed state
    have hbonz : globN entry "bo" ≠ 0 := hrdy.1.2.1
    have hbo : globN post "bo" = globN entry "bo" :=
      globN_eq_of_lookup (hstep.2.2.1 _ (by decide))
    have hfields : ∀ k ∈ ([40, 72] : List Nat),
        memW post (globN entry "bo" + k) = memW entry (globN entry "bo" + k) := by
      intro k hk
      have hk' : k = 40 ∨ k = 72 := by simpa using hk
      rcases hk' with rfl | rfl
      · exact hstep.2.2.2.1 ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by decide) hbonz 40
          (by decide) (by intro i hi; cases hi)
      · exact hstep.2.2.2.1 ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by decide) hbonz 72
          (by decide) (by intro i hi; cases hi)
    have hWcopy : WorldOK entry := hWent
    obtain ⟨hA, S, hWT0⟩ := hWcopy
    obtain ⟨Nd, hWT⟩ := (worldTyped_iff_with entry S).1 hWT0
    obtain ⟨S', Nd', _, _, _, _, hQ⟩ := hstep.2.2.2.2 S Nd hWT (by intro i hi; cases hi)
    have hu : R16Shards.TopGbodyWk.PtxBlockOutUnhit entry post := hQ.1
    have htxE : TxBacking entry := (R16Shards.txBacking_with_locals s callee (s.clock - 1)).2 hbk
    exact txBacking_setVarResume
      (txBacking_of_step_facts hWent hbonz hrdy.2.2.1 hrdy.2.2.2.1 htxE hbo hfields hu)
  · -- `TxValidRecoverReady` at the resumed state
    have hu_heap := encode_tx_heap_unhit hc hrdy.1.1 hVE ha hl hb
    have hVRpost : TxValidRecoverReadyAt post (locN s "tx") :=
      txValidRecoverReadyAt_step_heap_unhit hrdy.1.1.1 hstep.1.1 hstep.2.1 hu_heap hVR
    have hloc : locN (setVarHOLFinite (ofString "enc") v { post with locals := s.locals }) "tx" =
        locN s "tx" := by
      simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "enc" ≠ ofString "tx" by decide]
    unfold TxValidRecoverReady
    rw [hloc]
    have hset_eq : setVarHOLFinite (ofString "enc") v { post with locals := s.locals } =
        { post with locals := s.locals.update (ofString "enc", v), clock := post.clock } := by
      simp [setVarHOLFinite]
    rw [hset_eq]
    exact txValidRecoverReadyAt_with_locals post _ post.clock hVRpost

/-! ## Stage 6: the `state_fresh_tx` entry call -/

/-- The phase-1 entry call `state_fresh_tx` preserves backing,
encode-validity, and recover-validity: the callee allocates its records above
`heap_ptr` (so every word below `heap_ptr` — the tx record, the bo record's
fields, and the block-out list headers — is unchanged), the `bo` global and
the bo record words are kept by the ScBo step's globals/records conditions,
and the pointed list-header words by the ScBo unhit side condition. -/
theorem hoare_state_fresh_tx_bk :
    Hoare (fun s => R16Shards.PtxP1.StageP 0 s ∧ TxBacking s ∧
        TxValidEncodeReady s ∧ TxValidRecoverReady s)
      (.call (some (none, none)) (ofString "state_fresh_tx") [])
      (fun r t => r = none → R16Shards.PtxP1.StageP 0 t ∧ TxBacking t ∧
        TxValidEncodeReady t ∧ TxValidRecoverReady t) := by
  refine Hoare.call0_resume ?_
  intro F s vs body callee ret v post hc hP ha hl hb
  have hspec := R16Shards.PtxP1.funSpec_at_lookup wkScBo_state_fresh_tx
    s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hP.1.1.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hspec
  have hscbo := hspec (Or.inl ⟨v, rfl⟩)
  have hstep := hscbo.1.1
  have hst1 : R16Shards.PtxP1.StageP 0 { post with locals := s.locals } :=
    R16Shards.PtxP1.stage_after_scratchStep hstep (R16Shards.PtxP1.stage0 hP.1.1)
      (gs := []) (by simp [R16Shards.PtxP1.ScratchSpec]) rfl (by decide) (by decide)
      (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) (by decide)
  have hu_heap := state_fresh_tx_heap_unhit hc hP.1.1.1.1 hl hb
  have hVEp : TxValidEncodeAt post (locN s "tx") :=
    txValidEncodeAt_step_heap_unhit hP.1.1.1.1.1 hstep.1 hstep.2.1 hu_heap hP.2.2.1
  have hVRp : TxValidRecoverReadyAt post (locN s "tx") :=
    txValidRecoverReadyAt_step_heap_unhit hP.1.1.1.1.1 hstep.1.1 hstep.2.1 hu_heap hP.2.2.2
  have hbonz : globN (callEntryStateHOLFinite s callee) "bo" ≠ 0 := hP.1.1.1.2.1
  have hbkp : TxBacking post :=
    txBacking_of_scbo_step (s := callEntryStateHOLFinite s callee) (post := post)
      (R16Shards.PtxP1.worldOK_callEntry hP.1.1.1.1 callee) hbonz hP.1.1.2.2.1 hP.1.1.2.2.2.1
      ((R16Shards.txBacking_with_locals s callee (s.clock - 1)).2 hP.2.1)
      (globN_eq_of_lookup (hstep.2.2.1 (ofString "bo") (by decide)))
      (hstep.2.2.2.1 ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp)
        hbonz 40 (by simp) (by intro i hi; cases hi))
      (hstep.2.2.2.1 ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp)
        hbonz 72 (by simp) (by intro i hi; cases hi))
      (hscbo.2 (Or.inr (Or.inr (Or.inr ⟨v, rfl⟩))))
  refine ⟨hst1, ?_, ?_, ?_⟩
  · exact (R16Shards.txBacking_with_locals post s.locals post.clock).2 hbkp
  · exact txValidEncodeAt_with_locals post s.locals post.clock hVEp
  · exact txValidRecoverReadyAt_with_locals post s.locals post.clock hVRp

/-! ## Stage 7: the `encSlot` stores -/

/-- A single store anywhere inside the encoding array preserves `TxBacking`:
the `bo` record is a global buffer disjoint from the encoding array (via
`fixedObjects_disj_parts`), and the two 24-byte list headers hanging off
`bo+40`/`bo+72` are members of `blockOutObjects` (whose concrete 7-element
shape `blockOutObjects_eq_list` exposes, with the encoding array at index 0),
so the block-out pairwise disjointness keeps them apart from the stored word. -/
theorem txBacking_store_encArray {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hRs : TxReadyStrong s) (htx : TxBacking s) {x : BitVec 64}
    (hin : Inside (x.toNat, 8) (R16Shards.PtxP1.encArray s).1
      ((R16Shards.PtxP1.encArray s).1 + (R16Shards.PtxP1.encArray s).2))
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    TxBacking {s with memory := mem'} := by
  have hEs := R16Shards.PtxP1.txEnv_of_ready hRs
  obtain ⟨_, _, hW, -⟩ := hRs.2.2.2.2
  have hArenaOK := hRs.1.1.1.2
  have hm_ne_ivl : ∀ iv : Ivl, Disj iv (R16Shards.PtxP1.encArray s) → Allocated s iv →
      ∀ off, off + 8 ≤ iv.2 →
      memW {s with memory := mem'} (iv.1 + off) = memW s (iv.1 + off) := by
    intro iv hd hal off hoff
    have hhi_iv := (ivl_allocated_bound hArenaOK hal).2
    have hlt64 : iv.1 + off < 2 ^ 64 := by omega
    have hne : BitVec.ofNat 64 (iv.1 + off) ≠ x := by
      intro heq
      have htonat := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64] at htonat
      have hd_x := disj_of_inside_right hin hd
      rcases hd_x with h0 | h0 | hd1 | hd2 <;> ((try dsimp only at *); omega)
    unfold memW; dsimp only; rw [hm _ hne]
  obtain ⟨_, hbo_pw, hgb_rest, _, _⟩ := fixedObjects_disj_parts hW.2.2.1
  obtain ⟨_, _, hbo_eq⟩ := blockOutObjects_eq_list hEs hW.1
  have hbo_len : (blockOutObjects s).length = 7 := by rw [hbo_eq]; rfl
  have h0_eq : (blockOutObjects s)[0] = R16Shards.PtxP1.encArray s := by
    simp [hbo_eq, R16Shards.PtxP1.encArray, hEs.bo_nz, hEs.bo24]
  have hbo_idx_disj : ∀ (j : Nat) (hj : j < (blockOutObjects s).length), 0 < j →
      Disj (blockOutObjects s)[j] (R16Shards.PtxP1.encArray s) := by
    intro j hj hgt
    have hget := List.pairwise_iff_getElem.1 hbo_pw
    exact disj_symm (h0_eq ▸ hget 0 j (by omega) hj hgt)
  have hbo_disj_arr : Disj (globN s "bo", 88) (R16Shards.PtxP1.encArray s) :=
    hgb_rest _ (List.mem_map.2 ⟨("bo", 88), by decide, by simp [hEs.bo_nz]⟩) _
      (List.mem_append_left _ (List.mem_append_right _
        (R16Shards.PtxP1.encArray_mem_block hEs)))
  have hbo_al : Allocated s (globN s "bo", 88) := (bo_words hW.2.2.1 hEs.bo_nz).1
  have hbo_mem : ∀ off, off + 8 ≤ 88 →
      memW {s with memory := mem'} (globN s "bo" + off) = memW s (globN s "bo" + off) :=
    hm_ne_ivl (globN s "bo", 88) hbo_disj_arr hbo_al
  have h40_disj : Disj (memW s (globN s "bo" + 40), 24) (R16Shards.PtxP1.encArray s) := by
    have h3 : (blockOutObjects s)[3] = (memW s (globN s "bo" + 40), 24) := by simp [hbo_eq]
    exact h3 ▸ hbo_idx_disj 3 (by omega) (by omega)
  have h72_disj : Disj (memW s (globN s "bo" + 72), 24) (R16Shards.PtxP1.encArray s) := by
    have h5 : (blockOutObjects s)[5] = (memW s (globN s "bo" + 72), 24) := by simp [hbo_eq]
    exact h5 ▸ hbo_idx_disj 5 (by omega) (by omega)
  have h40_mem : (memW s (globN s "bo" + 40), 24) ∈ fixedObjects s :=
    List.mem_append_left _ (List.mem_append_right _
      (by simp [blockOutObjects, hEs.bo_nz, hEs.bo40]))
  have h72_mem : (memW s (globN s "bo" + 72), 24) ∈ fixedObjects s :=
    List.mem_append_left _ (List.mem_append_right _
      (by simp [blockOutObjects, hEs.bo_nz, hEs.bo72]))
  have h40_al : Allocated s (memW s (globN s "bo" + 40), 24) :=
    ((hW.2.2.1.1 _ h40_mem).resolve_left (by simp)).1
  have h72_al : Allocated s (memW s (globN s "bo" + 72), 24) :=
    ((hW.2.2.1.1 _ h72_mem).resolve_left (by simp)).1
  refine R16Shards.txBacking_of_header_words htx rfl ?_ ?_
  · intro k hk
    have hk' : k = 40 ∨ k = 72 := by simpa using hk
    rcases hk' with rfl | rfl
    · exact hbo_mem 40 (by omega)
    · exact hbo_mem 72 (by omega)
  · intro k hk
    have hk' : k = 40 ∨ k = 72 := by simpa using hk
    rcases hk' with rfl | rfl
    · simpa using hm_ne_ivl _ h40_disj h40_al 0 (by omega)
    · simpa using hm_ne_ivl _ h72_disj h72_al 0 (by omega)

/-- The backing- and recover-validity-strengthened version of
`R16Shards.PtxP1.store_encSlot`: the stored word lands inside the encoding
array, so `txBacking_store_encArray` keeps the block-output slots and list
headers intact, and `txValidRecoverReadyAt_store_encArray` keeps the recover
source valid. -/
theorem store_encSlot_bk (off : Bool) :
    Hoare (fun s => R16Shards.PtxP1.EncReady s ∧ TxBacking s ∧ TxValidRecoverReady s)
      (.store (R16Shards.PtxP1.encDst off)
        (.rfield (if off then 1 else 0) (.var .local (ofString "enc"))))
      (fun r t => r = none → R16Shards.PtxP1.EncReady t ∧ TxBacking t ∧
        TxValidRecoverReady t) := by
  refine Hoare.store_fall fun s x v mem' h hx hv hst => ?_
  obtain ⟨a, b, he⟩ := h.1.2
  have hvw : ∃ w : HolWordLab 64, v = .val w := by
    cases off <;> simp [evalAt, evalHOLExact, he] at hv <;> subst v
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  obtain ⟨w, rfl⟩ := hvw
  obtain ⟨hdom, _, hmem⟩ := panMemStoresHOL_word_spec (by simpa only [flattenHOL] using hst)
  have hin : Inside (x.toNat, 8) (R16Shards.PtxP1.encArray s).1
      ((R16Shards.PtxP1.encArray s).1 + (R16Shards.PtxP1.encArray s).2) := by
    cases off
    · exact R16Shards.PtxP1.encDst0_inside h.1.1 hx
    · exact R16Shards.PtxP1.encDst8_inside h.1.1 hx
  refine ⟨⟨R16Shards.PtxP1.txReadyStrong_store_encArray h.1.1 hdom hin hmem, a, b, he⟩,
    txBacking_store_encArray h.1.1 h.2.1 hin hmem, ?_⟩
  exact txValidRecoverReadyAt_store_encArray h.1.1 hin hmem h.2.2

/-! ## Stage 8: the `alloc` call site -/

/-- Backing- and recover-validity-strengthened version of
`R16Shards.PtxP1.resume_alloc_sender` for the `alloc` call that binds
`sender`. The `SenderAllocated` conjunct is the R11 proof verbatim (with the
stage predicate shifted under the new conjunction); the new `TxBacking` and
`TxValidRecoverReady` conjuncts come from the raw allocator body analysis
(`alloc_body_resumes_props`): the allocator leaves memory and every global
except `heap_ptr` untouched, so the block-out header words and the recover
source words survive verbatim, and the grown `heap_ptr` satisfies the
recover-validity step lemma's monotonicity side condition. -/
theorem resume_alloc_sender_bk (h : PtxCallees) :
    R16Shards.PtxP1.DecCallResumeShapeOn
      (fun s => R16Shards.PtxP1.StageP 0 s ∧ TxBacking s ∧ TxValidRecoverReady s)
      (fun s => R16Shards.PtxP1.SenderAllocated s ∧ TxBacking s ∧ TxValidRecoverReady s)
      (ofString "sender") .one (ofString "alloc") [.const 24] := by
  intro F s vs body callee ret v post hc hP ha hl hb hsh
  obtain ⟨nv, he, hn⟩ := R16Shards.PtxP1.params_one_value s (ofString "alloc") (ofString "n")
    .one _ .one (by rw [hc]; exact R16Shards.PtxP1.lookup_alloc) (.const 24) vs body callee ret ha hl
  have hnv : nv = .val (.word (24#64)) := by simpa [evalAt, evalHOLExact] using he.symm
  subst nv
  have hcn : locN (callEntryStateHOLFinite s callee) "n" = 24 := by
    simp [locN, callEntryStateHOLFinite, hn]
  have hrt := R16Shards.PtxP1.funSpec_at_lookup h.rt_alloc s hc vs body callee ret hl
    ((arenaReady_with_locals s callee (s.clock - 1)).mpr hP.1.1.1.1.1) (by rw [hb]; simp)
  rw [hb] at hrt
  obtain ⟨w, hv, _, _, hfb⟩ := hrt v rfl
  subst v
  rw [hcn] at hfb
  change FreshBlock (callEntryStateHOLFinite s callee) post w.toNat 24 at hfb
  have hpFresh : globN s "heap_ptr" ≤ w.toNat := hfb.2.1.1
  have hs := R16Shards.PtxP1.funSpec_at_lookup h.wk_alloc s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hP.1.1.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hs
  have hstep := hs (Or.inl ⟨.val (.word w), rfl⟩)
  have hsready := R16Shards.PtxP1.stage_after_scratchStep hstep hP.1
    (gs := []) (by simp [R16Shards.PtxP1.ScratchSpec]) rfl
    (by decide) (by decide) (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) (by decide)
  obtain ⟨S, Nd, hW, hT⟩ := hP.1.1.2.2.2.2
  obtain ⟨S', Nd', _, hW', hog, hfr, hret⟩ := hstep.2.2.2.2 S Nd
    ((R13Shards.worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hW) (by simp [IvlsDisj])
  obtain ⟨w', heq, hav⟩ := hret (.val (.word w)) rfl
  have hww : w' = w := by cases heq; rfl
  subst w'
  dsimp only at hav
  rw [hcn] at hav
  change IvlsDisj [(w.toNat, 24)] (worldOwned post S' Nd') at hav
  have hT' := R16Shards.PtxP1.txAccessListOK_survives_step hP.1.1.1.1.1 hstep.1.1 hstep.2.1 hW
    (R := []) (by simp) hog hfr hT (by simp) (by simp) (locals := s.locals) rfl
  obtain ⟨_, _, hu⟩ := R13Shards.heap_ivl_survives_step hP.1.1.1.1.1.2 hstep.2.1
    (R13Shards.worldOwned_zero_aligned hW) (R := []) (by simp) hog hfr hT.1.1.1 (by simp)
    hT.1.2.1 (fun j hj => hT.2.1 _ (by simp) j hj) (by simp)
  have hhi := (R13Shards.ivl_allocated_bound hP.1.1.1.1.1.2 (Or.inl hT.1.2.1)).2
  have hm208 : memW post (locN s "tx" + 208) = memW s (locN s "tx" + 208) :=
    R13Shards.memW_eq_of_ivlUnhit hu (by have := hT.1.1.1; omega) hhi ⟨by omega, by omega⟩
  have hm216 : memW post (locN s "tx" + 216) = memW s (locN s "tx" + 216) :=
    R13Shards.memW_eq_of_ivlUnhit hu (by have := hT.1.1.1; omega) hhi ⟨by omega, by omega⟩
  let resumed := setVarHOLFinite (ofString "sender") (.val (.word w)) { post with locals := s.locals }
  have htx : resumed.locals.lookup (ofString "tx") = s.locals.lookup (ofString "tx") := by
    simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "sender" ≠ ofString "tx" from by decide]
  have hidx : resumed.locals.lookup (ofString "index") = s.locals.lookup (ofString "index") := by
    simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "sender" ≠ ofString "index" from by decide]
  have hsender : locN resumed "sender" = w.toNat := by
    simp [resumed, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have htxN : locN resumed "tx" = locN s "tx" := locN_congr s resumed.locals post.clock "tx" htx
  have hrdy : TxReadyStrong resumed := R16Shards.PtxP1.txReadyStrong_with_locals
    { post with locals := s.locals } resumed.locals post.clock htx hidx hsready.1
  -- raw allocator analysis: memory and all globals but `heap_ptr` are untouched
  have hbody_eq : body = GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_alloc :=
    PanRunBounded.lookupCodeHOLFinite_installed_body s.code.lookup (ofString "alloc")
      [(ofString "n", .one)] (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_alloc) body .one ret vs callee
      (by rw [hc]; exact lookup_alloc_r13) hl
  have hab := alloc_body_resumes_props (callEntryStateHOLFinite s callee) hc
    ((arenaReady_with_locals s callee (s.clock - 1)).mpr hP.1.1.1.1.1)
    (by rw [← hbody_eq, hb]; exact Or.inl ⟨.val (.word w), rfl⟩)
  dsimp only at hab
  rw [← hbody_eq, hb] at hab
  obtain ⟨p, q, hrv, hp_eq, hq_eq, hq_lim, hq_8, hp_le_q, hgp, hmem, hbe, hma, hApost, hhp_eq,
    hsp_eq⟩ := hab
  have hpost_mem : post.memory = s.memory := hmem
  have hpost_glob : post.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) := hgp
  have hhp : globN s "heap_ptr" ≤ globN post "heap_ptr" := by
    have h1 : globN s "heap_ptr" = p.toNat := hp_eq.symm
    rw [hhp_eq]
    omega
  have hbo_eq : globN post "bo" = globN s "bo" :=
    globN_eq_of_lookup (by rw [hpost_glob]; simp [HolFiniteMapExact.update, FUPDATE,
      show ofString "heap_ptr" ≠ ofString "bo" from by decide])
  have hmw : ∀ a : Nat, memW post a = memW s a := by
    intro a
    unfold memW
    rw [hpost_mem]
  have hbkpost : TxBacking post := by
    obtain ⟨hbk1, hbk2⟩ := hP.2.1
    refine ⟨?_, ?_⟩
    · have e1 : memW post (globN s "bo" + 40) = memW s (globN s "bo" + 40) := hmw _
      have e2 : memW post (memW s (globN s "bo" + 40)) = memW s (memW s (globN s "bo" + 40)) :=
        hmw _
      rw [hbo_eq, e1, e2]
      exact hbk1
    · have e1 : memW post (globN s "bo" + 72) = memW s (globN s "bo" + 72) := hmw _
      have e2 : memW post (memW s (globN s "bo" + 72)) = memW s (memW s (globN s "bo" + 72)) :=
        hmw _
      rw [hbo_eq, e1, e2]
      exact hbk2
  have hVRpost : TxValidRecoverReadyAt post (locN s "tx") :=
    txValidRecoverReadyAt_step_heap_unhit hP.1.1.1.1.1 hApost.1 hhp
      (fun a _ _ => congrFun hpost_mem a) hP.2.2
  refine ⟨⟨hrdy, ?_, S', Nd', ?_, ?_, ?_, ?_, ?_⟩, hbkpost, ?_⟩
  · unfold R16Shards.PtxP1.SenderOK
    rw [hsender]
    exact ⟨⟨hP.1.1.1.1.1.2.1.trans hpFresh, hfb.2.1.2⟩, hfb.2.2⟩
  · exact (R13Shards.worldTypedWith_with_locals post resumed.locals post.clock S' Nd').mpr hW'
  · exact R16Shards.PtxP1.txAccessListOK_with_locals { post with locals := s.locals }
      resumed.locals post.clock htx hT'
  · rw [hsender]
    intro j hj
    exact hav _ (by simp) j (R13Shards.worldTypedIvls_sub_worldOwned hj)
  · rw [htxN, hsender]
    exact Or.inr (Or.inr (Or.inl (hT.1.2.1.2.trans hpFresh)))
  · rw [htxN, hsender]
    change 0 < memW post (locN s "tx" + 216) →
      Disj (memW post (locN s "tx" + 208), 24 * memW post (locN s "tx" + 216)) (w.toNat, 24)
    rw [hm208, hm216]
    intro hn
    exact Or.inr (Or.inr (Or.inl ((hT.2.2 hn).1.2.trans hpFresh)))
  · -- `TxValidRecoverReady` at the resumed state: the predicate reads only
    -- memory and globals, which `setVarHOLFinite` does not touch.
    unfold TxValidRecoverReady
    have hloc : locN (setVarHOLFinite (ofString "sender") (.val (.word w))
        { post with locals := s.locals }) "tx" = locN s "tx" := by
      simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "sender" ≠ ofString "tx" from by decide]
    rw [hloc]
    exact hVRpost

/-! ## Stage 9: the `recover_sender_with_chain_id` call -/

/-- Backing- and recover-validity-strengthened version of
`R16Shards.PtxP1.hoare_recover_sender` for the `recover_sender_with_chain_id`
call that closes Phase 1. The R11 proof is replayed against the ScBo spec
`wk_recover_sender_with_chain_id_bo`: its `PtxBlockOutUnhit` Q-slot plus the
`stdKeep` record-keep preserves the block-out header words, so `TxBacking`
survives the call; the consumed `TxValidRecoverReady` is exactly the spec's
entry precondition. -/
theorem hoare_recover_sender_bk (_h : PtxCallees) :
    Hoare (fun s => R16Shards.PtxP1.SenderAllocated s ∧ TxValidRecoverReady s ∧ TxBacking s)
      (.call (some (none, none)) (ofString "recover_sender_with_chain_id") R16Shards.PtxP1.recoverArgs)
      (fun r t => r = none → R16Shards.PtxP1.StageP 1 t ∧ TxBacking t) := by
  apply R13Shards.Hoare.call0_resume
  intro F s vs body callee ret v post hc hP ha hl hb
  obtain ⟨v1, _, v3, he1, _, he3, hp, _, hr⟩ := R16Shards.PtxP1.params_three_values s
    (ofString "recover_sender_with_chain_id") (ofString "tx") (ofString "chain_id") (ofString "out20")
    .one .one .one _ .one (by rw [hc]; exact R16Shards.PtxP1.lookup_recover_sender_with_chain_id)
    (.var .local (ofString "tx"))
    (.load .one (.op .add [.var .global (ofString "be"), .const 0])) (.var .local (ofString "sender"))
    vs body callee ret ha hl
  have htx_cal : callee.lookup (ofString "tx") = s.locals.lookup (ofString "tx") := hp.trans he1.symm
  have hout : locN (callEntryStateHOLFinite s callee) "out20" = locN s "sender" := by
    simp only [locN, callEntryStateHOLFinite, hr,
      show s.locals.lookup (ofString "sender") = some v3 from he3]
  have hVR := hP.2.1
  have hVR_cal : TxValidRecoverReady (callEntryStateHOLFinite s callee) := by
    unfold TxValidRecoverReady at hVR ⊢
    have hloc : locN (callEntryStateHOLFinite s callee) "tx" = locN s "tx" := by
      simp [callEntryStateHOLFinite, locN, htx_cal]
    rw [hloc]
    exact txValidRecoverReadyAt_with_locals s callee (s.clock - 1) hVR
  obtain ⟨S, Nd, hW, hT, hTyped, hTx, hRecs⟩ := hP.1.2.2
  have hin : Inside (locN s "sender", 20) (locN s "sender") (locN s "sender" + 24) :=
    ⟨le_rfl, by omega⟩
  have hout_bo : ∀ i ∈ blockOutObjects (callEntryStateHOLFinite s callee),
      Disj i (locN (callEntryStateHOLFinite s callee) "out20", 20) := by
    rw [hout]
    intro i hi
    have hi_s : i ∈ blockOutObjects s := hi
    have hi_wti : i ∈ worldTypedIvls s S Nd := by
      simp only [worldTypedIvls, List.mem_append]
      exact Or.inl (Or.inl (Or.inr hi_s))
    exact disj_symm (disj_of_inside_left hin (hTyped i hi_wti))
  have hspec := FunSpec.at_lookup «wk_recover_sender_with_chain_id_bo» s hc
    vs body callee ret hl
    ⟨R16Shards.PtxP1.worldOK_callEntry hP.1.1.1.1 callee, hVR_cal, hout_bo⟩
    (by rw [hb]; simp)
  rw [hb] at hspec
  have hstep := hspec (Or.inl ⟨v, rfl⟩)
  have hs0 : WorldStep
      (fun _ => [(locN (callEntryStateHOLFinite s callee) "out20", 20),
        bufferRegion s ("keccak_pad", 136), bufferRegion s ("keccak_st", 200),
        bufferRegion s ("u256_ws", 640)])
      ["heap_ptr"] stdKeep
      (fun s0 _ post0 _ _ => R16Shards.TopGbodyWk.PtxBlockOutUnhit s0 post0)
      s (some (.returned v)) post :=
    ⟨hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2.1, fun Sx Ndx hWx hDx =>
      hstep.2.2.2.2 Sx Ndx ((R13Shards.worldTypedWith_with_locals s callee (s.clock - 1) Sx Ndx).2 hWx) hDx⟩
  rw [hout] at hs0
  have hA := hP.1.1.1.1.1
  have hRT : IvlsDisj [(locN s "sender", 20), bufferRegion s ("keccak_pad", 136),
      bufferRegion s ("keccak_st", 200), bufferRegion s ("u256_ws", 640)]
      (worldTypedIvls s S Nd) := by
    intro i hi j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact R13Shards.disj_of_inside_left hin (hTyped j hj)
    · exact bufferRegion_disj_le hW ("keccak_pad", 136) (by decide) (by decide) 136 le_rfl j hj
    · exact bufferRegion_disj_le hW ("keccak_st", 200) (by decide) (by decide) 200 le_rfl j hj
    · exact bufferRegion_disj_le hW ("u256_ws", 640) (by decide) (by decide) 640 le_rfl j hj
  have hR0 : ∀ i ∈ [(locN s "sender", 20), bufferRegion s ("keccak_pad", 136),
      bufferRegion s ("keccak_st", 200), bufferRegion s ("u256_ws", 640)], i.2 = 0 → i.1 % 8 = 0 := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · simp
    · exact R16Shards.PtxP1.bufferRegion_zero_aligned s "keccak_pad" 136 (by decide)
    · exact R16Shards.PtxP1.bufferRegion_zero_aligned s "keccak_st" 200 (by decide)
    · exact R16Shards.PtxP1.bufferRegion_zero_aligned s "u256_ws" 640 (by decide)
  have hReady : TxReadyStrong { post with locals := s.locals } := by
    apply R16Shards.PtxP1.txReadyStrong_worldStep hs0 hA (R16Shards.PtxP1.txEnv_of_ready hP.1.1) hW hT
      (by decide) (by decide) (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp [stdKeep])
      (by decide) hR0 hRT
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact R13Shards.disj_of_inside_right hin hTx
      · exact R16Shards.PtxP1.heap_ivl_disj_bufferRegion_le (fun j hj => hT.2.1 _ (by simp) j hj)
          ("keccak_pad", 136) (by decide) 136 le_rfl
      · exact R16Shards.PtxP1.heap_ivl_disj_bufferRegion_le (fun j hj => hT.2.1 _ (by simp) j hj)
          ("keccak_st", 200) (by decide) 200 le_rfl
      · exact R16Shards.PtxP1.heap_ivl_disj_bufferRegion_le (fun j hj => hT.2.1 _ (by simp) j hj)
          ("u256_ws", 640) (by decide) 640 le_rfl
    · intro hn i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact R13Shards.disj_of_inside_right hin (hRecs hn)
      · exact R16Shards.PtxP1.heap_ivl_disj_bufferRegion_le (fun j hj => (hT.2.2 hn).2 _ (by simp) j hj)
          ("keccak_pad", 136) (by decide) 136 le_rfl
      · exact R16Shards.PtxP1.heap_ivl_disj_bufferRegion_le (fun j hj => (hT.2.2 hn).2 _ (by simp) j hj)
          ("keccak_st", 200) (by decide) 200 le_rfl
      · exact R16Shards.PtxP1.heap_ivl_disj_bufferRegion_le (fun j hj => (hT.2.2 hn).2 _ (by simp) j hj)
          ("u256_ws", 640) (by decide) 640 le_rfl
  -- TxBacking: bo pointer kept, header words kept, block-out objects unhit
  have hbo_eq : globN post "bo" = globN s "bo" :=
    globN_eq_of_lookup (hs0.2.2.1 (ofString "bo") (by decide))
  have hB : ValidBufList [("keccak_pad", 136), ("keccak_st", 200), ("u256_ws", 640)] := by
    intro p hp0
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp0
    rcases hp0 with rfl | rfl | rfl
    · exact ⟨136, by decide, by decide, le_rfl⟩
    · exact ⟨200, by decide, by decide, le_rfl⟩
    · exact ⟨640, by decide, by decide, le_rfl⟩
  have hrec_buf : RecordsKept (bufRegions [("keccak_pad", 136), ("keccak_st", 200), ("u256_ws", 640)])
      stdKeep s post := by
    intro rec hrec hnz off hoff hno
    apply hs0.2.2.2.1 rec hrec hnz off hoff
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · intro hch
      have hrec_sz : ∃ sz, (rec.1, sz) ∈ typedRecords ∧ off + 8 ≤ sz ∧ 0 < sz := by
        simp only [stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
        rcases hrec with rfl | rfl | rfl | rfl
        · refine ⟨40, by decide, ?_, by decide⟩; simp at hoff; omega
        · refine ⟨80, by decide, ?_, by decide⟩; simp at hoff; omega
        · refine ⟨72, by decide, ?_, by decide⟩; simp at hoff; omega
        · refine ⟨88, by decide, ?_, by decide⟩; simp at hoff; omega
      obtain ⟨sz, htr, hoff_sz, hsz_pos⟩ := hrec_sz
      have hrec_wti : (globN s rec.1, sz) ∈ worldTypedIvls s S Nd := by
        simp only [worldTypedIvls, List.mem_append]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
          (List.mem_map.2 ⟨(rec.1, sz), htr, by simp [hnz]⟩)))))
      have hd_rec := hTyped _ hrec_wti
      rcases hd_rec with h0 | h0 | hd1 | hd2
      · simp at h0
      · dsimp only at h0; omega
      · dsimp only [CellHits] at hd1 hch; omega
      · dsimp only [CellHits] at hd2 hch; omega
    · exact hno _ (by simp [bufRegions])
    · exact hno _ (by simp [bufRegions])
    · exact hno _ (by simp [bufRegions])
  have hf40 : memW post (globN s "bo" + 40) = memW s (globN s "bo" + 40) :=
    R16Shards.TopGbodyWk.ptx_bo_field_eq_of_step hB hW hrec_buf
      (by simp [stdKeep] :
        ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) ∈ stdKeep) hP.1.1.1.2.1
      (off := 40) (by decide) (by decide) (by decide)
  have hf72 : memW post (globN s "bo" + 72) = memW s (globN s "bo" + 72) :=
    R16Shards.TopGbodyWk.ptx_bo_field_eq_of_step hB hW hrec_buf
      (by simp [stdKeep] :
        ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) ∈ stdKeep) hP.1.1.1.2.1
      (off := 72) (by decide) (by decide) (by decide)
  obtain ⟨_, _, _, _, _, _, hu⟩ := hs0.2.2.2.2 S Nd hW hRT
  have hbk : TxBacking { post with locals := s.locals } :=
    txBacking_of_step_facts hP.1.1.1.1 hP.1.1.1.2.1 hP.1.1.2.2.1 hP.1.1.2.2.2.1 hP.2.2 hbo_eq
      (fun k hk => by
        have hk' : k = 40 ∨ k = 72 := by simpa using hk
        rcases hk' with rfl | rfl
        · exact hf40
        · exact hf72) hu
  have hSender := R16Shards.PtxP1.senderOK_grows hA.1 hReady.1.1.1.1 hs0.2.1 rfl hP.1.2.1
  exact ⟨⟨hReady, fun _ => hSender, by omega, by omega, by omega⟩, hbk⟩

end InitECandidate.Solver.Wave8GuestInv.R13Shards

