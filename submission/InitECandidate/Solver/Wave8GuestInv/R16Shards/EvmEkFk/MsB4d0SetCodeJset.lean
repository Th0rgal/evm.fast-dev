import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB4c2dEvmBridge

/-!
# Scratch Rung B4d (sections 1-3): `EvmMbStep` calculus & the bounded `jset` step

Shared front half of the B4d rung: the `EvmMbStep`/`EvmStepCC` calculus around
`EvmMsgReadyMsgBounded`, the `set_code` step-global and call0 effect lemmas,
and the bounded `jset(ts+48, h, sl)` step. The bounded `set_code` body itself
lives in `MsB4dSetCodeBounded`.
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
open InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21
  (IvlUnhit not_cellHits_of_disj memW_eq_of_ivlUnhit)
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

/-! ## 1. Lookup & Local Step Combinators -/

theorem lookup_set_code :
    originalRuntimeCode.lookup (ofString "set_code") =
      some ([(ofString "addr", .one), (ofString "code", .one), (ofString "code_len", .one)],
        sourceFnBody Guest.Software.guestFn_set_code, .one) :=
  lookup_of_guestAst_getElem 399 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_set_code) rfl

private theorem lookup_jset_b4d :
    originalRuntimeCode.lookup (ofString "jset") =
      some ([(ofString "t", .one), (ofString "key", .one), (ofString "value", .one)],
        sourceFnBody Guest.Software.guestFn_jset, .one) :=
  lookup_jset

def setCodeGw : List String := ["heap_ptr", "journal_n", "scratch_ptr"]

theorem safeStepGlobals_setCode : SafeStepGlobals setCodeGw := by
  intro g hg; simp [setCodeGw] at hg; rcases hg with rfl | rfl | rfl <;> simp

private theorem chainCellsAgree_refl_b4d {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ChainCellsAgree s s :=
  fun _ _ => ⟨rfl, rfl, rfl, rfl⟩

private theorem chainCellsAgree_trans_b4d {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F}
    (h1 : ChainCellsAgree s mid) (hch : evmChain mid = evmChain s)
    (h2 : ChainCellsAgree mid post) :
    ChainCellsAgree s post := by
  intro ec hec
  obtain ⟨a1, b1, c1, d1⟩ := h1 ec hec
  obtain ⟨a2, b2, c2, d2⟩ := h2 ec (hch.symm ▸ hec)
  exact ⟨a2.trans a1, b2.trans b1, c2.trans c1, d2.trans d1⟩

private theorem evmStepCC_refl_b4d {gw : List String} {F : Type}
    {s : PanSemStateFiniteExact 64 F} (hInv : EvmInv s) :
    EvmStepCC gw s s :=
  ⟨⟨hInv, le_rfl, fun _ _ => rfl, rfl⟩, chainCellsAgree_refl_b4d s⟩

private theorem evmStepCC_trans_b4d {gw : List String} {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F}
    (h1 : EvmStepCC gw s mid) (h2 : EvmStepCC gw mid post) :
    EvmStepCC gw s post :=
  ⟨⟨h2.1.1, le_trans h1.1.2.1 h2.1.2.1,
    fun k hk => (h1.1.2.2.1 k hk).trans (h2.1.2.2.1 k hk),
    h2.1.2.2.2.trans h1.1.2.2.2⟩,
   chainCellsAgree_trans_b4d h1.2 h1.1.2.2.2 h2.2⟩

theorem evmStepCC_mono_gw_b4d {gw1 gw2 : List String} {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hsub : ∀ g ∈ gw1, g ∈ gw2) (h : EvmStepCC gw1 s post) :
    EvmStepCC gw2 s post := by
  refine ⟨⟨h.1.1, h.1.2.1, fun k hk => h.1.2.2.1 k ?_, h.1.2.2.2⟩, h.2⟩
  intro hmem
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hmem
  exact hk (List.mem_map.2 ⟨g, hsub g hg, rfl⟩)

private theorem evmStepCC_with_locals_right_b4d {gw : List String} {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (h : EvmStepCC gw s post) :
    EvmStepCC gw s { post with locals := locals, clock := clock } :=
  ⟨⟨localsFree_evmInv post locals clock h.1.1, h.1.2.1, h.1.2.2.1,
    (evmChain_with_locals post locals clock).trans h.1.2.2.2⟩, h.2⟩

private theorem evmStepCC_of_pre_locals_clock_b4d {gw : List String} {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {L : HolFiniteMapExact MlS (ValueHOL 64)} {k : Nat}
    (h : EvmStepCC gw { s with locals := L, clock := k } post) :
    EvmStepCC gw s post := by
  refine ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.trans (evmChain_with_locals s L k)⟩, ?_⟩
  intro ec hec
  exact h.2 ec ((evmChain_with_locals s L k).symm ▸ hec)

def EvmMbStep (gw : List String) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) : Prop :=
  EvmMsgReadyMsgBounded post ∧ EvmStepCC gw s post ∧
    memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112)

theorem evmMbStep_refl {gw : List String} {F : Type}
    {s : PanSemStateFiniteExact 64 F} (h : EvmMsgReadyMsgBounded s) :
    EvmMbStep gw s s :=
  ⟨h, evmStepCC_refl_b4d (evmInv_of_msgBounded h), rfl⟩

theorem evmMbStep_with_locals_right {gw : List String} {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (h : EvmMbStep gw s post) :
    EvmMbStep gw s { post with locals := locals, clock := clock } :=
  ⟨localsFree_evmMsgReadyMsgBounded post locals clock h.1,
   evmStepCC_with_locals_right_b4d locals clock h.2.1, h.2.2⟩

theorem evmMbStep_of_pre_locals_clock {gw : List String} {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {L : HolFiniteMapExact MlS (ValueHOL 64)} {k : Nat}
    (h : EvmMbStep gw { s with locals := L, clock := k } post) :
    EvmMbStep gw s post :=
  ⟨h.1, evmStepCC_of_pre_locals_clock_b4d h.2.1, h.2.2⟩

theorem evmMbStep_trans {gw : List String} {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F}
    (hev_out : ofString "ev" ∉ gw.map ofString)
    (h1 : EvmMbStep gw s mid) (h2 : EvmMbStep gw mid post) :
    EvmMbStep gw s post := by
  have hev_mid : globN mid "ev" = globN s "ev" :=
    globN_eq_of_lookup (h1.2.1.1.2.2.1 (ofString "ev") hev_out)
  refine ⟨h2.1, evmStepCC_trans_b4d h1.2.1 h2.2.1, ?_⟩
  have h2_112 := h2.2.2
  rw [hev_mid] at h2_112
  exact h2_112.trans h1.2.2

theorem contOrRes_of_flowingOrResumes_b4d {r : Option (PanSemResultExact 64)}
    (hfr : FlowingOrResumes r) : ContOrRes r := by
  rcases hfr with h | h | h | hr
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr hr))

private theorem call0_or_resumes_b4d {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fname : MlS) (args : List (ExpHOL 64))
    (hcr : ContOrRes (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = none ∨
    Resumes (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 := by
  rcases hcr with h | h | h | hr
  · exact Or.inl h
  · exfalso
    rw [evaluateHOLFiniteState_call] at h
    revert h; split <;> [simp; (split <;> [simp; (split <;> [simp; skip])])]
    rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨rc, _⟩
    rcases rc with _ | (_ | _ | _ | _ | _ | _ | _) <;> dsimp only <;> (repeat' split) <;> simp
  · exfalso
    rw [evaluateHOLFiniteState_call] at h
    revert h; split <;> [simp; (split <;> [simp; (split <;> [simp; skip])])]
    rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨rc, _⟩
    rcases rc with _ | (_ | _ | _ | _ | _ | _ | _) <;> dsimp only <;> (repeat' split) <;> simp
  · exact Or.inr hr

theorem call0_none_locals_b4d {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fn : MlS) (args : List (ExpHOL 64))
    (hnone : (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).1 = none) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).2.locals = s.locals := by
  rw [evaluateHOLFiniteState_call] at hnone ⊢
  unfold evalListHOLFinite at hnone ⊢
  rcases h1 : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [h1] at hnone
  · simp only [h1] at hnone ⊢
    rcases h2 : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fn vs with _ | ⟨b, c, r⟩
    · simp [h2] at hnone
    · simp only [h2] at hnone ⊢
      split at hnone
      · simp at hnone
      · rename_i hcz; rw [if_neg hcz]
        rcases h3 : evaluateHOLFiniteState (callEntryStateHOLFinite s c) b with ⟨rb, sb⟩
        simp only [h3] at hnone ⊢
        rcases rb with _ | rb'
        · simp at hnone
        · cases rb' with
          | returned rv =>
            dsimp only at hnone ⊢
            split at hnone
            · rename_i hsh; rw [if_pos hsh]
            · simp at hnone
          | _ => simp at hnone

theorem worldEff_call0_funByteEff_b4d {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    {fname : MlS} {argR : List (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64) → List Ivl}
    (hf : Fast_C08WkShard03.FunByteEff fname argR)
    (args : List (ExpHOL 64)) (Sub : List Ivl)
    (hsub_args : ∀ vals,
      evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args = some vals →
      ∀ i ∈ argR vals cur.globals, 0 < i.2 → ∃ j ∈ Sub, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2)
    (hsub_world : ∀ iv ∈ Sub, 0 < iv.2 →
      (∃ j ∈ Rl, j.1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ j.1 + j.2) ∨
      (∃ gs ∈ B, (bufferRegion s gs).1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ (bufferRegion s gs).1 + (bufferRegion s gs).2) ∨
      (globN s "frame_mem_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ heapLimit))
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).1) :
    WorldEff s (evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).2 Rl B gw :=
  h.of_byteEff
    (Fast_C08WkShard03.call0_byteEff hf cur args Sub h.code h.arena.1 hsub_args hnt
      (call0_or_resumes_b4d cur fname args hcr))
    hsub_world

/-! ## 2. Role & Table Slot Helpers for `ts+48` -/

private theorem nonValueSlot_ts48_b4d {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (hT : TablesTyped s S) (hts_nz : globN s "ts" ≠ 0)
    (ht0_nz : memW s (globN s "ts" + 48) ≠ 0) :
    let t0 := memW s (globN s "ts" + 48)
    t0 ∈ S ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∧
    globN s "bal_accounts" ≠ t0 ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) := by
  have ht0_S : memW s (globN s "ts" + 48) ∈ S := by
    rcases hT.2.2.2.2.2.1 48 (by simp [tsTableSlots]) hts_nz with h0 | hm
    · exact absurd h0 ht0_nz
    · exact hm
  have ht0_wrs : (memW s (globN s "ts" + 48), "ts+48") ∈ worldRoleSlots s := by
    apply mem_worldRoleSlots_recRole s "ts" 48 "ts+48" hts_nz ht0_nz
    apply List.mem_append.2; right
    unfold recRoles; simp [hts_nz]
  exact nonValueSlot_of_wrs s S _ "ts+48" hT ht0_nz ht0_S ht0_wrs
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem journalRole_ts48_b4d {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (hT : TablesTyped s S) (hts_nz : globN s "ts" ≠ 0)
    (ht0_nz : memW s (globN s "ts" + 48) ≠ 0) :
    journalRole s (memW s (globN s "ts" + 48)) = "ts+48" := by
  have hroles := hT.2.2.2.2.2.2.2.2.2.2.2
  have ht48_wrs : (memW s (globN s "ts" + 48), "ts+48") ∈ worldRoleSlots s := by
    apply mem_worldRoleSlots_recRole s "ts" 48 "ts+48" hts_nz ht0_nz
    apply List.mem_append.2; right
    unfold recRoles; simp [hts_nz]
  have hne16 : memW s (globN s "ts" + 48) ≠ memW s (globN s "ts" + 16) := by
    intro heq
    have h16_nz : memW s (globN s "ts" + 16) ≠ 0 := by rw [← heq]; exact ht0_nz
    have ht16_wrs : (memW s (globN s "ts" + 16), "ts+16") ∈ worldRoleSlots s := by
      apply mem_worldRoleSlots_recRole s "ts" 16 "ts+16" hts_nz h16_nz
      apply List.mem_append.2; right
      unfold recRoles; simp [hts_nz]
    exact slot_ne_of_diff_nonshared_role hroles ht48_wrs ht16_wrs (by decide) heq
  have hne32 : memW s (globN s "ts" + 48) ≠ memW s (globN s "ts" + 32) :=
    ((nonValueSlot_ts48_b4d s S hT hts_nz ht0_nz).2.2.1 hts_nz).symm
  unfold journalRole
  rw [if_neg (by rintro ⟨_, h⟩; exact hne16 h), if_neg (by rintro ⟨_, h⟩; exact hne32 h),
      if_pos ⟨hts_nz, rfl⟩]

private theorem ts48_ne_ws16_bs48_b4d {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (hT : TablesTyped s S) (hts_nz : globN s "ts" ≠ 0)
    (ht0_nz : memW s (globN s "ts" + 48) ≠ 0) :
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 16) ≠ memW s (globN s "ts" + 48)) ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 48) ≠ memW s (globN s "ts" + 48)) := by
  have hroles := hT.2.2.2.2.2.2.2.2.2.2.2
  have ht48_wrs : (memW s (globN s "ts" + 48), "ts+48") ∈ worldRoleSlots s := by
    apply mem_worldRoleSlots_recRole s "ts" 48 "ts+48" hts_nz ht0_nz
    apply List.mem_append.2; right
    unfold recRoles; simp [hts_nz]
  refine ⟨fun hws heq => ?_, fun hbs heq => ?_⟩
  · have hws_nz : memW s (globN s "ws" + 16) ≠ 0 := by rw [heq]; exact ht0_nz
    have hws_wrs : (memW s (globN s "ws" + 16), "ws+16") ∈ worldRoleSlots s := by
      apply mem_worldRoleSlots_recRole s "ws" 16 "ws+16" hws hws_nz
      apply List.mem_append.2; left; apply List.mem_append.2; left
      unfold recRoles; simp [hws]
    exact slot_ne_of_diff_nonshared_role hroles hws_wrs ht48_wrs (by decide) heq
  · have hbs_nz : memW s (globN s "bs" + 48) ≠ 0 := by rw [heq]; exact ht0_nz
    have hbs_wrs : (memW s (globN s "bs" + 48), "bs+48") ∈ worldRoleSlots s := by
      apply mem_worldRoleSlots_recRole s "bs" 48 "bs+48" hbs hbs_nz
      apply List.mem_append.2; left; apply List.mem_append.2; right
      unfold recRoles; simp [hbs]
    exact slot_ne_of_diff_nonshared_role hroles hbs_wrs ht48_wrs (by decide) heq

private theorem ts48_mem_worldTableRefs_b4d {F : Type}
    (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (hts_nz : globN s "ts" ≠ 0) :
    memW s (globN s "ts" + 48) ∈ worldTableRefs s S := by
  have hm : memW s (globN s "ts" + 48) ∈ recordSlots s "ts" tsTableSlots := by
    unfold recordSlots
    rw [if_neg hts_nz]
    exact List.mem_map.2 ⟨48, by simp [tsTableSlots], rfl⟩
  unfold worldTableRefs; dsimp only
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hm)))))

private theorem typed_code_root_after_htab_exit_b4d {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (g : String) (sz k : Nat)
    (htr : (g, sz) ∈ typedRecords) (hk_in : k + 8 ≤ sz) (hk8 : k % 8 = 0)
    (hAs : ArenaReady s) (hW : WorldTyped s S)
    (ht : locN s "t" ∈ S) (hgnz : globN s g ≠ 0)
    (hx : HtabExit s post) :
    memW post (globN s g + k) = memW s (globN s g + k) := by
  have hi : (globN s g, sz) ∈ fixedObjects s := by
    have hm := R10Shards.GbodyProcessMsg.typedRecord_mem_fixedObjects s htr
    simpa [hgnz] using hm
  have hpos : sz ≠ 0 := by omega
  have hw := ((hW.2.2.1.1 _ hi).resolve_left hpos).2
  have hal : globN s g % 8 = 0 := hw.1
  apply fixed_word_after_htab_exit _ (globN s g, sz) hAs hW ht hi
  · unfold Inside; dsimp; omega
  · omega
  · exact hx

/-! ## 3. Bounded `jset` on `ts+48` with Fresh 16-Byte Code Record -/

/-- Calling `jset(*(ts + 48), kExp, slExp)` when `slExp` evaluates to a 16-byte heap record `wsl`
with `Inside (wsl.toNat, 16) sourceBase (globN s "heap_ptr")`, `WordsOK s (wsl.toNat, 16)`,
`memW s (wsl.toNat + 8) < 2^40`, disjoint from every `nonTrieOwned s S` interval on every `(S, Nd)`
and from `(memW s (globN s "ev" + 112), 176)`, preserves `EvmMsgReadyMsgBounded`, establishes
`EvmStepCC ["heap_ptr", "journal_n"]`, and preserves `memW _ (globN s "ev" + 112)`. -/
theorem jset_ts48_bounded_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (S_ent : List Nat) (kExp slExp : ExpHOL 64) (wsl : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hA : ArenaReady s)
    (hM : MsgDisjCodeStrong s)
    (hInvAt_s : EvmInvAt s S_ent)
    (hMO_s : MsgOwned s S_ent (memW s (globN s "ev" + 112)))
    (hC_s : CodeDbPayloadBoundedNz s S_ent)
    (hsl_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) slExp =
      some (.val (.word wsl)))
    (hwsl_in : Inside (wsl.toNat, 16) sourceBase (globN s "heap_ptr"))
    (hwsl_words : WordsOK s (wsl.toNat, 16))
    (hwsl_len : memW s (wsl.toNat + 8) < 2 ^ 40)
    (hwsl_disj_nt : ∀ j ∈ nonTrieOwned s S_ent, Disj (wsl.toNat, 16) j)
    (hwsl_disj_msg : Disj (memW s (globN s "ev" + 112), 176) (wsl.toNat, 16))
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "jset")
        [.load .one (.op .add [.var .global (ofString "ts"), .const 48#64]), kExp, slExp])).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "jset")
        [.load .one (.op .add [.var .global (ofString "ts"), .const 48#64]), kExp, slExp])).1) :
    EvmMbStep ["heap_ptr", "journal_n"] s
      (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "jset")
          [.load .one (.op .add [.var .global (ofString "ts"), .const 48#64]), kExp, slExp])).2 := by
  have hhl_264 : heapLimit < 2 ^ 64 := by decide
  have hMB : EvmMsgReadyMsgBounded s := ⟨hA, hM, S_ent, hInvAt_s, hMO_s, hC_s⟩
  have hW : WorldOK s := worldOK_of_msgBounded hMB
  have hwsl_64 : wsl.toNat + 16 ≤ 2 ^ 64 := by
    have := hW.1.2.2.1; unfold Inside at hwsl_in; dsimp at hwsl_in; omega
  set argsL : List (ExpHOL 64) :=
    [.load .one (.op .add [.var .global (ofString "ts"), .const 48#64]), kExp, slExp]
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) argsL with _ | values
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    have hargs_fin : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) argsL = some values := by
      rwa [evalListHOLFinite_eq_toExact]
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "jset") values with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        have hbody_eq := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "jset")
          _ _ body' _ ret' values callee lookup_jset_b4d (by rwa [← hcode])
        have hret_eq := lookupCodeHOLFinite_installed_return s (ofString "jset")
          _ _ _ _ ret' values callee (by rw [hcode]; exact lookup_jset_b4d) hl
        obtain ⟨v1, v2, v3, he1, _, he3, hc_t, hc_k, hc_v⟩ := callee_param_three s (ofString "jset")
          (ofString "t") (ofString "key") (ofString "value") .one .one .one _ _
          (by rw [hcode]; exact lookup_jset_b4d) _ _ _ values body' callee ret' hargs_fin hl
        obtain ⟨tw, rfl, htw_nat, hts_nz⟩ := evalAt_loadG_nz s hW.1.1 "ts" 48#64 (by decide) v1 he1
        have hlk_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "jset") values =
            some (sourceFnBody Guest.Software.guestFn_jset, callee, .one) := by
          rw [← hcode, hl, hbody_eq, hret_eq]
        obtain ⟨_, kw, vlw, _, _, hc_k', hc_v'⟩ := Fast_C08WkShard03.lookupCode_three_words
          (by decide) (by decide) (by decide) lookup_jset_b4d hlk_orig
        have hv23 : v2 = .val (.word kw) ∧ v3 = .val (.word vlw) := by
          rw [hc_k] at hc_k'; rw [hc_v] at hc_v'
          exact ⟨Option.some.inj hc_k', Option.some.inj hc_v'⟩
        rcases hv23 with ⟨rfl, rfl⟩
        have hvlw_eq : wsl = vlw := by
          change @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) slExp =
            some (.val (.word vlw)) at he3
          rw [hsl_ev] at he3
          injection he3 with h1; injection h1 with h2; cases h2; rfl
        subst hvlw_eq
        let ent := callEntryStateHOLFinite s callee
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, post⟩
        simp only [ent, hrun] at hnt hfr ⊢
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | exception eid ev =>
            exfalso
            have hne : eid ≠ ofString "TrapErr" := by
              rcases hfr with h | h | h | ⟨_, h⟩ | ⟨_, _, h, hne⟩ <;> try simp at h
              obtain ⟨rfl, _⟩ := h; exact hne
            have hbody_ok : noCatchableRaise trapOnlyCallees body' = true :=
              trapOnlyCallees_good (ofString "jset") (by decide) values body' callee ret' (by rwa [← hcode])
            have hno := evaluate_noCatchableRaise trapOnlyCallees trapOnlyCallees_good
              body' hbody_ok ent hcode eid ev hne
            dsimp only [ent] at hno; rw [hrun] at hno; exact hno rfl
          | returned rv =>
            dsimp only at hfr ⊢
            split
            · have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hW
              have hrun_jset : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_jset) =
                  (some (.returned rv), post) := by
                rw [← hbody_eq]; exact hrun
              clear hbody_eq hret_eq hl hlk_orig hnt hfr hc_k' hc_v' hrun
              have hbody_fold : sourceFnBody Guest.Software.guestFn_jset =
                  .decCall (ofString "old") (.comb [.one, .one]) (ofString "htab_get")
                    [.var .local (ofString "t"), .var .local (ofString "key")]
                    (journalAppendTailProg 4#64 (.rfield 0 (.var .local (ofString "old")))
                      (.seq
                        (.call (some (none, none)) (ofString "htab_set")
                          [.var .local (ofString "t"), .var .local (ofString "key"), .var .local (ofString "value")])
                        (.return (.const 0#64)))) := rfl
              rw [hbody_fold] at hrun_jset
              rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun_jset
              have hrun := hrun_jset
              have hent_t : ent.locals.lookup (ofString "t") = some (.val (.word tw)) := hc_t
              have hent_k : ent.locals.lookup (ofString "key") = some (.val (.word kw)) := hc_k
              have hent_v : ent.locals.lookup (ofString "value") = some (.val (.word wsl)) := hc_v
              have hargs_hg : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
                  [.var .local (ofString "t"), .var .local (ofString "key")] =
                  some [.val (.word tw), .val (.word kw)] := by
                simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, hent_t, hent_k]
              rw [hargs_hg] at hrun; dsimp only at hrun
              rcases hlk_hg : lookupCodeHOLFinite ent.code.lookup (ofString "htab_get")
                  [.val (.word tw), .val (.word kw)] with _ | ⟨bhg, chg, rhg⟩
              · rw [hlk_hg] at hrun; simp at hrun
              · rw [hlk_hg] at hrun; dsimp only at hrun
                by_cases hcz_ent : ent.clock = 0
                · simp [hcz_ent] at hrun
                rw [if_neg hcz_ent] at hrun
                have hbhg_eq := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "htab_get")
                  _ _ bhg _ rhg _ chg EvmFrameSpecs.lookup_htab_get
                  (by rwa [← show ent.code = originalRuntimeCode from hcode])
                subst hbhg_eq
                have hchg_t' : chg.lookup (ofString "t") = some (.val (.word tw)) := by
                  have ht_ev : evalAt ent (.var .local (ofString "t")) = some (.val (.word tw)) := by
                    simp [evalAt, evalHOLExact, toExact, hent_t]
                  have ⟨v1', _, he1', _, hc1', _⟩ := callee_param_two_r16_code ent (ofString "htab_get")
                    (ofString "t") (ofString "key") .one .one _ _
                    (by rw [show ent.code = originalRuntimeCode from hcode]; exact EvmFrameSpecs.lookup_htab_get)
                    (.var .local (ofString "t")) (.var .local (ofString "key"))
                    _ _ chg rhg hargs_hg hlk_hg
                  rw [ht_ev] at he1'; injection he1' with h'; subst h'; exact hc1'
                have hchg_k' : chg.lookup (ofString "key") = some (.val (.word kw)) := by
                  have hk_ev : evalAt ent (.var .local (ofString "key")) = some (.val (.word kw)) := by
                    simp [evalAt, evalHOLExact, toExact, hent_k]
                  have ⟨_, v2', _, he2', _, hc2'⟩ := callee_param_two_r16_code ent (ofString "htab_get")
                    (ofString "t") (ofString "key") .one .one _ _
                    (by rw [show ent.code = originalRuntimeCode from hcode]; exact EvmFrameSpecs.lookup_htab_get)
                    (.var .local (ofString "t")) (.var .local (ofString "key"))
                    _ _ chg rhg hargs_hg hlk_hg
                  rw [hk_ev] at he2'; injection he2' with h'; subst h'; exact hc2'
                let ent_hg := callEntryStateHOLFinite ent chg
                rcases hrun_hg : evaluateHOLFiniteState ent_hg (sourceFnBody Guest.Software.guestFn_htab_get) with
                  ⟨res_hg, p_hg⟩
                dsimp only [ent_hg] at hrun_hg
                rw [hrun_hg] at hrun
                cases res_hg with
                | none => simp at hrun
                | some cr_hg =>
                  cases cr_hg with
                  | exception eid_hg ev_hg =>
                    exfalso
                    dsimp only at hrun; injection hrun with hr_eq _
                    cases hr_eq
                  | timeOut | error | «break» | «continue» | finalFfi _ => simp at hrun
                  | returned v_old =>
                    dsimp only at hrun
                    split at hrun <;> try simp at hrun
                    have htw_nz : tw ≠ 0 := WkBal.htab_get_t_nonzero ent_hg tw kw
                      (guestInv_callEntry ent chg hWent.1.1) hchg_t' hchg_k' v_old
                      (by dsimp only [ent_hg]; rw [hrun_hg])
                    have ht0_nz : memW s (globN s "ts" + 48) ≠ 0 := by
                      intro h0; apply htw_nz; apply BitVec.eq_of_toNat_eq
                      change tw.toNat = 0; simpa [htw_nat] using h0
                    obtain ⟨_, S0, hWT0⟩ := hW
                    have htw_S0 : tw.toNat ∈ S0 := by
                      rw [htw_nat]; exact (nonValueSlot_ts48_b4d s S0 hWT0.1 hts_nz ht0_nz).1
                    have hwf_hg : HtabWF ent_hg tw.toNat :=
                      (htabWF_with_locals s chg (ent.clock - 1) tw.toNat).2 (hWT0.1.2.1 _ htw_S0).1
                    obtain ⟨f0, f1, rfl, _⟩ := WkBal.htab_get_ret_in_values ent_hg tw kw
                      hcode hchg_t' hchg_k' hwf_hg v_old
                      (by dsimp only [ent_hg]; rw [hrun_hg])
                    have hro_hg := FunSpec.at_lookup EvmFrameSpecs.ro_htab_get ent hcode
                      _ (sourceFnBody Guest.Software.guestFn_htab_get) chg rhg hlk_hg
                      (guestInv_callEntry ent chg hWent.1.1) (by rw [hrun_hg]; simp)
                    have hro_hg' : ((evaluateHOLFiniteState ent_hg
                        (sourceFnBody Guest.Software.guestFn_htab_get)).2) = _ :=
                      hro_hg (by rw [hrun_hg]; exact Or.inl ⟨_, rfl⟩)
                    dsimp only [ent_hg] at hro_hg'
                    rw [hrun_hg] at hro_hg'
                    dsimp only at hro_hg'
                    set s_old := setVarHOLFinite (ofString "old") (.rStruct [.val (.word f0), .val (.word f1)])
                      { p_hg with locals := ent.locals }
                    have heff_old : WorldEff ent s_old [] [] ["heap_ptr"] :=
                      ((WorldEff.refl ent [] [] ["heap_ptr"] hWent.1 hcode).of_readOnly hro_hg').locals_clock _ _
                    have hg_all_old : ∀ k : MlS, s_old.globals.lookup k = ent.globals.lookup k := by
                      intro k; dsimp only [s_old, setVarHOLFinite]; rw [hro_hg']; rfl
                    have hold_t : s_old.locals.lookup (ofString "t") = some (.val (.word tw)) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_t,
                        show ofString "old" ≠ ofString "t" by decide]
                    have hold_k : s_old.locals.lookup (ofString "key") = some (.val (.word kw)) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_k,
                        show ofString "old" ≠ ofString "key" by decide]
                    have hold_v : s_old.locals.lookup (ofString "value") = some (.val (.word wsl)) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_v,
                        show ofString "old" ≠ ofString "value" by decide]
                    have hold_old : s_old.locals.lookup (ofString "old") =
                        some (.rStruct [.val (.word f0), .val (.word f1)]) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                    rcases htail_old : evaluateHOLFiniteState s_old
                        (journalAppendTailProg 4#64 (.rfield 0 (.var .local (ofString "old")))
                          (.seq
                            (.call (some (none, none)) (ofString "htab_set")
                              [.var .local (ofString "t"), .var .local (ofString "key"), .var .local (ofString "value")])
                            (.return (.const 0#64)))) with ⟨rtail, ptail⟩
                    rw [htail_old] at hrun; dsimp only at hrun
                    have hrtail_eq : rtail = some (.returned rv) := hrun.1
                    have hpost_ptail : post = { ptail with locals := (HolFiniteMapExact.resVarEq ptail.locals
                        (ofString "old", ent.locals.lookup (ofString "old"))) } := hrun.2.symm
                    obtain ⟨mid, tailPost, hstep_j, hmid_t, hmid_k, hmid_v_eq, hmid_tail, hptail_tp⟩ :=
                      journal_append_block_step_code ent s_old
                        4#64 (.rfield 0 (.var .local (ofString "old"))) tw kw f0 f1 f0 hWent heff_old hg_all_old
                        hold_t hold_k hold_old
                        (fun st hst => by simp [evalHOLExact, toExact, hst])
                        (fun S hTS => by
                          have htw_nat' : tw.toNat = memW s (globN s "ts" + 48) := htw_nat
                          have hts_ent : globN ent "ts" = globN s "ts" := rfl
                          have hm48_ent : memW ent (globN ent "ts" + 48) = memW s (globN s "ts" + 48) := rfl
                          have ht0_ent_nz : memW ent (globN ent "ts" + 48) ≠ 0 := by rw [hm48_ent]; exact ht0_nz
                          have htw_S : tw.toNat ∈ S := by
                            rw [htw_nat']
                            exact (nonValueSlot_ts48_b4d ent S hTS (by rwa [hts_ent]) ht0_ent_nz).1
                          have hjr_48 : journalRole ent tw.toNat = "ts+48" := by
                            rw [htw_nat', ← hm48_ent]
                            exact journalRole_ts48_b4d ent S hTS (by rwa [hts_ent]) ht0_ent_nz
                          refine ⟨htw_S, ?_⟩
                          dsimp only
                          rw [hjr_48]
                          simp only [show ("ts+48" = "ts+32") ↔ False by decide, and_false, ↓reduceIte,
                            List.mem_singleton]
                          rintro p rfl
                          have hm48_wrs : (memW ent (globN ent "ts" + 48), "ts+48") ∈ worldRoleSlots ent := by
                            apply mem_worldRoleSlots_recRole ent "ts" 48 "ts+48" (by rwa [hts_ent]) ht0_ent_nz
                            apply List.mem_append.2; right
                            unfold recRoles; simp [hts_ent, hts_nz]
                          rwa [hm48_ent, ← htw_nat'] at hm48_wrs)
                        (by rw [htail_old, hrtail_eq])
                    have hmid_v : mid.locals.lookup (ofString "value") = some (.val (.word wsl)) :=
                      hmid_v_eq.trans hold_v
                    have hB_nil : PosBufList [] := posBufList_nil
                    have hgw_jn : SafeStepGlobals ["heap_ptr", "journal_n"] := by
                      intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp
                    have hA_ent : ArenaReady ent := localsFree_arenaReady s callee (s.clock - 1) hA
                    have hM_ent : MsgDisjCodeStrong ent :=
                      (msgDisjCodeStrong_with_locals_clock s callee (s.clock - 1)).2 hM
                    have hInvAt_ent : EvmInvAt ent S_ent :=
                      (evmInvAt_with_locals s callee (s.clock - 1) S_ent).2 hInvAt_s
                    have hMO_ent : MsgOwned ent S_ent (memW ent (globN ent "ev" + 112)) :=
                      (msgOwned_with_locals s callee (s.clock - 1) S_ent _).2 hMO_s
                    have hC_ent : CodeDbPayloadBoundedNz ent S_ent :=
                      (codeDbPayloadBoundedNz_with_locals_clock s S_ent callee (s.clock - 1)).2 hC_s
                    have hMB_ent' : EvmMsgReadyMsgBounded ent :=
                      ⟨hA_ent, hM_ent, S_ent, hInvAt_ent, hMO_ent, hC_ent⟩
                    obtain ⟨Sw, Frem, Sw', Nd_mid, Nd', hA_mid, hperm_S, hSw_sub, hWT_Sw, _,
                      hWT_Sw', hWT_S', hgrow_w, hfr_w, hFrem_fp, _, hInvAt_S', hMO_S',
                      hStepCC_mid0, h112_mid0, _⟩ :=
                      evmStepCC_full_of_worldStepSc hB_nil.1 hgw_jn (fun _ hg => hg)
                        hA_ent hInvAt_ent hMO_ent hstep_j.1
                    obtain ⟨hT_ent, hJ_ent, hF_ent, ⟨Nd_ent, hTr_ent⟩⟩ := hInvAt_ent.1
                    have hWT_ent : WorldTypedWith ent S_ent Nd_ent := ⟨hT_ent, hJ_ent, hF_ent, hTr_ent⟩
                    obtain ⟨⟨Nd_nt, hWT_nt⟩, hgrow_nt, hfr_nt⟩ := hstep_j.2 S_ent Nd_ent hWT_ent
                      (fun _ h => by cases h)
                    have hMB_step_mid0 := msgBounded_stepCC_of_worldStepCodeSc
                      hB_nil hgw_jn (fun _ hg => hg) hMB_ent' hstep_j
                    have hMB_step_mid : EvmMbStep ["heap_ptr", "journal_n"] s mid :=
                      evmMbStep_of_pre_locals_clock hMB_step_mid0
                    obtain ⟨hMB_mid, hStepCC_mid, h112_mid_s⟩ := hMB_step_mid
                    have hM_mid : MsgDisjCodeStrong mid := hMB_mid.2.1
                    have hW_mid : WorldOK mid := worldOK_of_msgBounded hMB_mid
                    have hmid_code : mid.code = originalRuntimeCode := hW_mid.1.1.code
                    have hts_mid : globN mid "ts" = globN s "ts" :=
                      globN_eq_of_lookup (hstep_j.1.1.2.2.1 (ofString "ts") (by decide))
                    have hev_mid : globN mid "ev" = globN s "ev" :=
                      globN_eq_of_lookup (hstep_j.1.1.2.2.1 (ofString "ev") (by decide))
                    have hm48_mid : memW mid (globN mid "ts" + 48) = tw.toNat := by
                      have hrk48 := hstep_j.1.1.2.2.2.1
                        ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64])
                        (by simp [R10Shards.P26_P28.stdKeep]) hts_nz
                        48 (by simp) (fun _ h => by cases h)
                      rw [hts_mid]; exact hrk48.trans htw_nat.symm
                    have hhp_ent_mid : globN s "heap_ptr" ≤ globN mid "heap_ptr" := hstep_j.1.1.2.1
                    have hwsl_in_mid : Inside (wsl.toNat, 16) sourceBase (globN mid "heap_ptr") :=
                      ⟨hwsl_in.1, le_trans hwsl_in.2 hhp_ent_mid⟩
                    have hwsl_words_mid : WordsOK mid (wsl.toNat, 16) :=
                      wordsOK_transfer_b4d hMB.1.1 hA_mid.1 hwsl_words
                    have hunhit_wsl_mid : IvlUnhit ent mid (wsl.toNat, 16) :=
                      ivlUnhit_of_worldStep_frameOutside_b4d hA_ent.2 hfr_nt
                        (nonTrieOwned_zero_aligned_b4d hT_ent hF_ent)
                        (fun _ h => by cases h)
                        hwsl_words.1 hwsl_words.2.1
                        (Or.inr (Or.inl hwsl_in))
                        hwsl_disj_nt
                        (fun _ h => by cases h)
                    have hwsl8_mid : memW mid (wsl.toNat + 8) = memW s (wsl.toNat + 8) :=
                      memW_eq_of_ivlUnhit hunhit_wsl_mid (by have := hwsl_words.1; dsimp at this; omega)
                        hwsl_64 ⟨by omega, by omega⟩
                    have hwsl_len_mid : memW mid (wsl.toNat + 8) < 2 ^ 40 := by
                      rw [hwsl8_mid]; exact hwsl_len
                    have hwsl_disj_mid : ∀ j ∈ nonTrieOwned mid S_ent, Disj (wsl.toNat, 16) j :=
                      allocatedEvm_disj_ownedGrows_b4d hA_ent.2 hA_mid.2 hhp_ent_mid
                        (Or.inr (Or.inl hwsl_in))
                        hwsl_disj_nt hgrow_nt
                    have hmsg_mid : memW mid (globN mid "ev" + 112) = memW s (globN s "ev" + 112) := by
                      rw [hev_mid]; exact h112_mid_s
                    have hwsl_disj_msg_mid : Disj (memW mid (globN mid "ev" + 112), 176) (wsl.toNat, 16) := by
                      rw [hmsg_mid]; exact hwsl_disj_msg
                    have hS_ent_join : ∀ t ∈ S_ent, t ∈ Sw' ++ Frem := by
                      intro t ht
                      rcases List.mem_append.1 (hperm_S.subset ht) with htw | htf
                      · exact List.mem_append_left _ (hSw_sub t htw)
                      · exact List.mem_append_right _ htf
                    obtain ⟨s_hs, hhs, hret_hs⟩ := seq_call0_ret_inv hmid_tail
                    rw [evaluateHOLFiniteState_return] at hret_hs
                    simp only [evalHOLExact, toExact, shapeOfHOLExact, sizeOfShapeWithContextHOL,
                      show (1 : Nat) ≤ 32 by decide, ↓reduceIte, emptyLocalsHOLFinite] at hret_hs
                    have htp_eq : tailPost = { s_hs with locals := HolFiniteMapExact.empty } :=
                      ((Prod.mk.inj hret_hs).2).symm
                    rw [evaluateHOLFiniteState_call] at hhs
                    have hargs_hs : evalListHOLFinite mid (h := fun a => Classical.propDecidable (mid.memaddrs a))
                        [.var .local (ofString "t"), .var .local (ofString "key"), .var .local (ofString "value")] =
                        some [.val (.word tw), .val (.word kw), .val (.word wsl)] := by
                      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, hmid_t, hmid_k, hmid_v]
                    rw [hargs_hs] at hhs; dsimp only at hhs
                    have hlook_hs := pan_three_word_lookup mid.code.lookup (ofString "htab_set")
                      (ofString "t") (ofString "key") (ofString "value")
                      (sourceFnBody Guest.Software.guestFn_htab_set) tw kw wsl
                      (by decide) (by decide) (by decide)
                      (by rw [hmid_code]; exact SoloHtabSet.lookup_htab_set)
                    rw [hlook_hs] at hhs; dsimp only at hhs
                    by_cases hcz_mid : mid.clock = 0
                    · rw [if_pos hcz_mid] at hhs; simp at hhs
                    · rw [if_neg hcz_mid] at hhs
                      let cmap_hs : HolFiniteMapExact MlS (ValueHOL 64) :=
                        (((HolFiniteMapExact.empty.update (ofString "t", ValueHOL.val (.word tw))).update
                          (ofString "key", ValueHOL.val (.word kw))).update
                          (ofString "value", ValueHOL.val (.word wsl)))
                      let ent_hs := callEntryStateHOLFinite mid cmap_hs
                      rcases hrun_hs : evaluateHOLFiniteState ent_hs (sourceFnBody Guest.Software.guestFn_htab_set) with
                        ⟨res_hs, p_hs⟩
                      have hrun_hs' : evaluateHOLFiniteState (callEntryStateHOLFinite mid cmap_hs)
                          (sourceFnBody Guest.Software.guestFn_htab_set) = (res_hs, p_hs) := hrun_hs
                      rw [hrun_hs'] at hhs
                      cases res_hs with
                      | none => simp at hhs
                      | some cr_hs =>
                        cases cr_hs with
                        | returned v_hs =>
                          dsimp only at hhs
                          split at hhs <;> try simp at hhs
                          have hs_hs_eq : s_hs = { p_hs with locals := mid.locals } := hhs.symm
                          have hcal_t : ent_hs.locals.lookup (ofString "t") = some (.val (.word tw)) := by
                            have h1 : ofString "value" ≠ ofString "t" := by decide
                            have h2 : ofString "key" ≠ ofString "t" := by decide
                            simp [ent_hs, cmap_hs, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update,
                              FUPDATE, h1, h2, Ne.symm h1, Ne.symm h2]
                          have hcal_k : ent_hs.locals.lookup (ofString "key") = some (.val (.word kw)) := by
                            have h1 : ofString "value" ≠ ofString "key" := by decide
                            simp [ent_hs, cmap_hs, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update,
                              FUPDATE, h1, Ne.symm h1]
                          have hcal_v : ent_hs.locals.lookup (ofString "value") = some (.val (.word wsl)) := by
                            simp [ent_hs, cmap_hs, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                          have hloc_t_hs : locN ent_hs "t" = tw.toNat := by simp [locN, hcal_t]
                          have hloc_v_hs : locN ent_hs "value" = wsl.toNat := by simp [locN, hcal_v]
                          have hAe_hs : ArenaReady ent_hs := localsFree_arenaReady mid _ _ hA_mid
                          have hWe_hs : WorldTyped ent_hs S_ent :=
                            (worldTyped_with_locals mid _ _ S_ent).2
                              ⟨hWT_nt.1, hWT_nt.2.1, hWT_nt.2.2.1, ⟨Nd_nt, hWT_nt.2.2.2⟩⟩
                          have hInv_mid_Sent : EvmInvAt mid S_ent := by
                            have hold_z : ∀ j ∈ nonTrieOwned ent S_ent, j.2 = 0 → j.1 % 8 = 0 :=
                              nonTrieOwned_zero_aligned_b4d hT_ent hF_ent
                            have hslots_mid : ∀ ec ∈ evmChain mid,
                                memW mid (ec.1 + 136) ∈ S_ent ∧ memW mid (ec.1 + 168) ∈ S_ent ∧
                                  memW mid (ec.1 + 176) ∈ S_ent := by
                              rw [hStepCC_mid0.1.2.2.2]
                              intro ec hec
                              have hFW_e := hInvAt_ent.2.2.2.2.1 ec hec
                              have hfo_disj_e := hInvAt_ent.2.2.2.2.2.2.2.2.1 ec hec (ec.1, 280)
                                (by simp [frameObjects])
                              have hscr_ec := hFW_e.1 (ec.1, 280) (by simp)
                              have hal_ec : (ec.1, 280).2 = 0 ∨ AllocatedEvmB4d ent (ec.1, 280) :=
                                Or.inr (Or.inr (Or.inr hscr_ec.1))
                              have hb_ec : ec.1 + 280 ≤ 2 ^ 64 :=
                                allocatedEvm_bound_b4d hA_ent.2 (Or.inr (Or.inr hscr_ec.1))
                              have hnt_disj : ∀ j ∈ nonTrieOwned ent S_ent, Disj (ec.1, 280) j := by
                                intro j hj
                                unfold nonTrieOwned at hj
                                rcases List.mem_append.1 hj with htab | hfix
                                · obtain ⟨t, ht, hit⟩ := List.mem_flatMap.1 htab
                                  exact hfo_disj_e.1 t ht j hit
                                · exact hfo_disj_e.2 j hfix
                              have hunhit : IvlUnhit ent mid (ec.1, 280) :=
                                ivlUnhit_of_worldStep_frameOutside_b4d hA_ent.2 hfr_nt hold_z
                                  (fun _ h => by cases h)
                                  hscr_ec.2.1 hscr_ec.2.2.1 hal_ec hnt_disj (fun _ h => by cases h)
                              have he1_8 : ec.1 % 8 = 0 := hscr_ec.2.1
                              rw [memW_eq_of_ivlUnhit hunhit (by omega) hb_ec ⟨by omega, by omega⟩,
                                memW_eq_of_ivlUnhit hunhit (by omega) hb_ec ⟨by omega, by omega⟩,
                                memW_eq_of_ivlUnhit hunhit (by omega) hb_ec ⟨by omega, by omega⟩]
                              exact ⟨hFW_e.2.2.2.2.2.2.2.1, hFW_e.2.2.2.2.2.2.2.2.1,
                                hFW_e.2.2.2.2.2.2.2.2.2.1⟩
                            obtain ⟨_, hne_m, hlen_m, hlast_m, hFW_m, hFR_m, hRW_m, hPW_m, hFO_m,
                              ⟨Nd_at, ⟨hNH_at, hDisj_at, hWs_at⟩, hd_at⟩, hMarks_m, hRoles_m, hGas_m⟩ := hInvAt_S'
                            have hW_mid_S : WorldTyped mid S_ent :=
                              ⟨hWT_nt.1, hWT_nt.2.1, hWT_nt.2.2.1, ⟨Nd_nt, hWT_nt.2.2.2⟩⟩
                            have hTr_sub : ∀ {os}, AvoidsTries mid (Sw' ++ Frem) os → AvoidsTries mid S_ent os := by
                              rintro os ⟨Nd_o, ⟨hNH_o, hDisj_o, hWs_o⟩, hd_o⟩
                              refine ⟨Nd_o, ⟨hNH_o, fun o ho => ⟨fun t ht => (hDisj_o o ho).1 t (hS_ent_join t ht),
                                (hDisj_o o ho).2⟩, fun hws => ?_⟩, hd_o⟩
                              obtain ⟨hR24, hR32⟩ := hWs_o hws
                              exact ⟨hR24, fun h32 => hR32 (hS_ent_join _ h32)⟩
                            refine ⟨hW_mid_S, hne_m, hlen_m, hlast_m, ?_, hFR_m, hRW_m, hPW_m, ?_,
                              hTr_sub ⟨Nd_at, ⟨hNH_at, hDisj_at, hWs_at⟩, hd_at⟩, ?_, ?_, hGas_m⟩
                            · intro ec hec
                              obtain ⟨hs1, hs2, hs3⟩ := hslots_mid ec hec
                              obtain ⟨f1, f2, f3, f4, f5, f6, f7, _, _, _, f11, f12, f13, f14, f15, f16,
                                ⟨m1, m2, m3, m4, m5, m6⟩⟩ := hFW_m ec hec
                              exact ⟨f1, f2, f3, f4, f5, f6, f7, hs1, hs2, hs3, f11, f12, f13, f14, f15, f16,
                                ⟨m1, m2, fun t ht => m3 t (hS_ent_join t ht), m4, m5, hTr_sub m6⟩⟩
                            · intro ec hec o ho
                              exact ⟨fun t ht => (hFO_m ec hec o ho).1 t (hS_ent_join t ht), (hFO_m ec hec o ho).2⟩
                            · intro i hi
                              obtain ⟨mk1, mk2, mk3, mk4, mk5, mk6, mk7, mk8, mk9⟩ := hMarks_m i hi
                              refine ⟨mk1, mk2, mk3, mk4, mk5, mk6, mk7, ?_, mk9⟩
                              intro t ht
                              rcases mk8 t (hS_ent_join t ht) with ⟨htake, hdel⟩ | hloc
                              · refine Or.inl ⟨htake, ⟨fun hm => hdel.1 ?_, hdel.2⟩⟩
                                unfold worldTableRefs at hm ⊢
                                dsimp only at hm ⊢
                                have hnest : ∀ g : String,
                                    t ∈ (if globN mid g ≠ 0 ∧ memW mid (globN mid g + 32) ∈ S_ent then
                                      htabValues mid (memW mid (globN mid g + 32)) else []) →
                                    t ∈ (if globN mid g ≠ 0 ∧ memW mid (globN mid g + 32) ∈ Sw' ++ Frem then
                                      htabValues mid (memW mid (globN mid g + 32)) else []) := by
                                  intro g hg; split at hg
                                  · rename_i hc; rw [if_pos ⟨hc.1, hS_ent_join _ hc.2⟩]; exact hg
                                  · cases hg
                                rcases List.mem_append.1 hm with h1 | hr
                                · rcases List.mem_append.1 h1 with h2 | hb
                                  · rcases List.mem_append.1 h2 with h3 | hts
                                    · rcases List.mem_append.1 h3 with h4 | hbs
                                      · exact List.mem_append_left _ (List.mem_append_left _
                                          (List.mem_append_left _ (List.mem_append_left _ h4)))
                                      · exact List.mem_append_left _ (List.mem_append_left _
                                          (List.mem_append_left _ (List.mem_append_right _ (hnest "bs" hbs))))
                                    · exact List.mem_append_left _ (List.mem_append_left _
                                        (List.mem_append_right _ (hnest "ts" hts)))
                                  · exact List.mem_append_left _ (List.mem_append_right _ hb)
                                · exact List.mem_append_right _ hr
                              · exact Or.inr hloc
                            · refine ⟨?_, hRoles_m.2.1, hRoles_m.2.2⟩
                              intro a ha
                              refine ⟨?_, (hRoles_m.1 a ha).2⟩
                              rcases List.mem_append.1 ha with hwf | hjr
                              · rcases List.mem_append.1 hwf with hw | hf
                                · exact (hW_mid_S.1.2.2.2.2.2.2.2.2.2.2.2.1 a (List.mem_append_left _ hw)).1
                                · obtain ⟨ec, hec, ha_ec⟩ := List.mem_flatMap.1 hf
                                  obtain ⟨h136, h168, h176⟩ := hslots_mid ec hec
                                  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha_ec
                                  rcases ha_ec with rfl | rfl | rfl
                                  · exact h136
                                  · exact h168
                                  · exact h176
                              · exact (hW_mid_S.1.2.2.2.2.2.2.2.2.2.2.2.1 a (List.mem_append_right _ hjr)).1
                          have hInv_hs : EvmInvAt ent_hs S_ent :=
                            (evmInvAt_with_locals mid _ _ S_ent).2 hInv_mid_Sent
                          have hts_mid_nz : globN mid "ts" ≠ 0 := by rwa [hts_mid]
                          have ht0_mid_nz : memW mid (globN mid "ts" + 48) ≠ 0 := by
                            rw [hm48_mid]; intro h0; exact htw_nz (BitVec.eq_of_toNat_eq h0)
                          have htw_Sent : tw.toNat ∈ S_ent := by
                            have hnvs0 := nonValueSlot_ts48_b4d mid S_ent hWT_nt.1 hts_mid_nz ht0_mid_nz
                            dsimp only at hnvs0; rw [hm48_mid] at hnvs0; exact hnvs0.1
                          have hArg_hs : HtabArgWF ent_hs := by
                            refine ⟨hAe_hs, ?_, ?_⟩
                            · rw [hloc_t_hs]; exact (hWe_hs.1.2.1 _ htw_Sent).1
                            · rw [hloc_t_hs]; intro i hi; exact ((hWe_hs.1.2.1 _ htw_Sent).2 i hi).1
                          have hhl_hs : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "htab_set")
                              [.val (.word tw), .val (.word kw), .val (.word wsl)] =
                              some (sourceFnBody Guest.Software.guestFn_htab_set, ent_hs.locals, .one) := by
                            rw [← hmid_code]; exact hlook_hs
                          have hvals_sub := htab_set_values_sub ent_hs tw kw wsl hcal_t hcal_k hcal_v hArg_hs
                            v_hs (by dsimp only [ent_hs]; rw [hrun_hs])
                          dsimp only at hvals_sub
                          have hp_hs_eq : (evaluateHOLFiniteState ent_hs (sourceFnBody Guest.Software.guestFn_htab_set)).2 = p_hs := by
                            rw [hrun_hs]
                          rw [hp_hs_eq] at hvals_sub
                          have hexit_hs : HtabExit ent_hs p_hs := hvals_sub.1
                          have hexit_hs_u : HtabExit ent_hs p_hs := hexit_hs
                          unfold HtabExit at hexit_hs_u; dsimp only at hexit_hs_u
                          rw [hloc_t_hs] at hexit_hs_u
                          obtain ⟨hAp_hs, hwf_hs, hhdr0_hs, _, hhp_hs, hfp_hs, hfr_hs, hg_hs⟩ := hexit_hs_u
                          have hbe_hs : p_hs.be = mid.be := hvals_sub.2.1
                          have hvals_hs := hvals_sub.2.2
                          rw [hloc_t_hs, hloc_v_hs] at hvals_hs
                          have htw_ndel : ∀ (i : Nat) (hi : i + 1 < (evmChain mid).length),
                              ¬ DelExclusive mid S_ent (evmChain mid) i tw.toNat := by
                            intro i hi hdel
                            have hmem := ts48_mem_worldTableRefs_b4d mid S_ent hts_mid_nz
                            rw [hm48_mid] at hmem
                            exact hdel.1 hmem
                          have hnvs_mid := nonValueSlot_ts48_b4d mid S_ent hWT_nt.1 hts_mid_nz ht0_mid_nz
                          dsimp only at hnvs_mid
                          rw [hm48_mid] at hnvs_mid
                          obtain ⟨ht0_S, ht0_nbs32, ht0_nts32, ht0_nba, ht0_nad, ht0_nws32⟩ := hnvs_mid
                          have hne_roots := ts48_ne_ws16_bs48_b4d mid S_ent hWT_nt.1 hts_mid_nz ht0_mid_nz
                          rw [hm48_mid] at hne_roots
                          obtain ⟨hInv_p, hch_p, _, hu_ec⟩ := evmInvAt_of_htab_step
                            hA_mid hInv_mid_Sent hAp_hs hbe_hs
                            hwf_hs hhdr0_hs hhp_hs hfp_hs hfr_hs
                            (fun k hk => hg_hs k (fun h => hk (by simp at h; simp [h])))
                            (by
                              have hjn : globN p_hs "journal_n" = globN ent_hs "journal_n" :=
                                globN_eq_of_lookup_eq (hg_hs (ofString "journal_n") (by decide)).symm
                              have hjn_ent : globN ent_hs "journal_n" = globN mid "journal_n" := rfl
                              omega)
                            ht0_S htw_ndel
                            ht0_nws32 ht0_nbs32
                            ht0_nba ht0_nad (Or.inl ht0_nts32)
                          have hgN : ∀ g : String, ofString g ≠ ofString "heap_ptr" → globN p_hs g = globN mid g := by
                            intro g hgne
                            have hlk := hg_hs (ofString g) (by simp [hgne])
                            unfold globN; rw [← hlk]; rfl
                          have hec_words : ∀ ec ∈ evmChain mid,
                              (∀ off, off + 8 ≤ 280 → off % 8 = 0 → memW p_hs (ec.1 + off) = memW mid (ec.1 + off)) ∧
                              (∀ off, off + 8 ≤ 104 → off % 8 = 0 → memW p_hs (ec.2 + off) = memW mid (ec.2 + off)) := by
                            intro ec hec
                            have hFW := hInv_mid_Sent.2.2.2.2.1 ec hec
                            obtain ⟨hb1, hb2, _, _⟩ := EvmStepLemmas.frameWF_bounds hA_mid.2 hFW
                            have he1_8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
                            have he2_8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
                            obtain ⟨hu1, hu2⟩ := hu_ec ec hec
                            refine ⟨fun off hoff hoff8 => ?_, fun off hoff hoff8 => ?_⟩
                            · exact memW_eq_of_ivlUnhit hu1 (by omega) hb1 ⟨by omega, by omega⟩
                            · exact memW_eq_of_ivlUnhit hu2 (by omega) hb2 ⟨by omega, by omega⟩
                          have hhead_mem : (globN mid "ev", globN mid "cur_cont") ∈ evmChain mid := by
                            have hcons : ∃ tl, evmChain mid = (globN mid "ev", globN mid "cur_cont") :: tl := ⟨_, rfl⟩
                            obtain ⟨tl, htl⟩ := hcons; rw [htl]; exact List.mem_cons_self
                          have h112_p : memW p_hs (globN mid "ev" + 112) = memW mid (globN mid "ev" + 112) :=
                            (hec_words _ hhead_mem).1 112 (by omega) (by omega)
                          have hm_p : MsgOwned p_hs S_ent (memW p_hs (globN p_hs "ev" + 112)) := by
                            have hhead_p : (globN mid "ev", globN mid "cur_cont") ∈ evmChain p_hs := by
                              rw [hch_p]; exact hhead_mem
                            have hFW_p := hInv_p.2.2.2.2.1 _ hhead_p
                            simpa [hgN "ev" (by decide)] using hFW_p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                          have ht_ent : locN ent_hs "t" ∈ S_ent := by rw [hloc_t_hs]; exact htw_Sent
                          have hroot_eq : ∀ g k, (g, k) ∈ ([("ws", 16), ("bs", 48), ("ts", 48)] : List (String × Nat)) →
                              globN mid g ≠ 0 → memW p_hs (globN mid g + k) = memW mid (globN mid g + k) := by
                            intro g k hgk hgnz
                            simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
                            rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                            · exact typed_code_root_after_htab_exit_b4d (s := ent_hs) (post := p_hs) "ws" 40 16
                                (by decide) (by omega) (by omega) hAe_hs hWe_hs ht_ent hgnz hexit_hs
                            · exact typed_code_root_after_htab_exit_b4d (s := ent_hs) (post := p_hs) "bs" 80 48
                                (by decide) (by omega) (by omega) hAe_hs hWe_hs ht_ent hgnz hexit_hs
                            · exact typed_code_root_after_htab_exit_b4d (s := ent_hs) (post := p_hs) "ts" 72 48
                                (by decide) (by omega) (by omega) hAe_hs hWe_hs ht_ent hgnz hexit_hs
                          have hroot_in_S : ∀ g k, (g, k) ∈ ([("ws", 16), ("bs", 48), ("ts", 48)] : List (String × Nat)) →
                              globN mid g ≠ 0 → memW mid (globN mid g + k) ≠ 0 → memW mid (globN mid g + k) ∈ S_ent := by
                            intro g k hgk hgnz hnz
                            have hrin : RootIn S_ent (memW mid (globN mid g + k)) := by
                              simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
                              rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                              · exact hWT_nt.1.2.2.2.1 16 (by decide) hgnz
                              · exact hWT_nt.1.2.2.2.2.1 48 (by decide) hgnz
                              · exact hWT_nt.1.2.2.2.2.2.1 48 (by decide) hgnz
                            exact hrin.resolve_left hnz
                          have hroots_mid := code_roots_kept_of_safeGlobals hWT_ent hB_nil hgw_jn hstep_j.1.1.2.2.2.1
                            (fun k hk => hstep_j.1.1.2.2.1 k hk)
                          obtain ⟨_, _, _, _, _, _, hv_nt⟩ :=
                            hstep_j.1.1.2.2.2.2 S_ent Nd_ent hWT_ent (fun _ h => by cases h)
                          have hC_ent_mid : CodeDbPayloadBoundedNz mid S_ent :=
                            codeDbPayloadBoundedNz_of_nonTrieStep hB_nil.1 hA_ent hA_mid hhp_ent_mid
                              hT_ent hF_ent hC_ent hv_nt
                              hgrow_nt hfr_nt
                              (fun g hg => by
                                simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
                                rcases hg with rfl | rfl | rfl
                                · exact (hroots_mid "ws" 16 (by decide)).1
                                · exact (hroots_mid "bs" 48 (by decide)).1
                                · exact (hroots_mid "ts" 48 (by decide)).1)
                              (fun g k hgk hgnz => by
                                have hk_in : (g, k) ∈ ([("ws", 16), ("ts", 40), ("ts", 48), ("bs", 48)] : List (String × Nat)) := by
                                  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk ⊢
                                  rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
                                obtain ⟨hg_eq, hr_eq⟩ := hroots_mid g k hk_in
                                have hhr := hr_eq hgnz
                                rwa [hg_eq] at hhr)
                          have hnba_ent : globN ent_hs "bal_accounts" ≠ locN ent_hs "t" := by
                            rw [hloc_t_hs]; exact ht0_nba
                          have hnad_ent : ∀ ad ∈ balRecords ent_hs, memW ent_hs ad ≠ locN ent_hs "t" := by
                            intro ad had; rw [hloc_t_hs]; exact ht0_nad ad had
                          have htw_ent : HtabWF ent_hs (locN ent_hs "t") := by
                            rw [hloc_t_hs]; exact (hWe_hs.1.2.1 _ htw_Sent).1
                          have hC_ts48 : CodeDbPayloadBounded p_hs S_ent tw.toNat := by
                            have he_ts : CodeDbPayloadBounded ent_hs S_ent tw.toNat := by
                              have h0 := hC_ent_mid "ts" 48 (by decide) hts_mid_nz ht0_mid_nz
                              rw [hm48_mid] at h0
                              exact (codeDbPayloadBounded_with_locals_clock mid S_ent _ _ (mid.clock - 1)).2 h0
                            have ht_fp_pos : ∀ i ∈ htabFootprint ent_hs (locN ent_hs "t"), 0 < i.2 :=
                              htabFootprint_pos ent_hs _ htw_ent.2.2.1 htw_ent.2.2.2.2.1
                            have hwsl_fp_disj : ∀ i ∈ htabFootprint ent_hs (locN ent_hs "t"),
                                Disj (wsl.toNat, 16) i := by
                              rw [hloc_t_hs]
                              intro i hi
                              exact hwsl_disj_mid i (List.mem_append_left _
                                (List.mem_flatMap.2 ⟨tw.toNat, htw_Sent, hi⟩))
                            have hwsl8_p : memW p_hs (wsl.toNat + 8) = memW ent_hs (wsl.toNat + 8) :=
                              (htab_frame_preserves_code_record (locN ent_hs "t") wsl.toNat
                                hwsl_in_mid.2 hwsl_64 ht_fp_pos hwsl_fp_disj hexit_hs.2.2.2.2.2.2.1).2
                            have hwords : NodeDbEntriesBounded p_hs tw.toNat := by
                              intro p hp
                              rcases hvals_hs p hp with rfl | hold
                              · refine ⟨wordsOK_transfer_b4d hA_mid.1 hexit_hs.1.1 hwsl_words_mid, ?_⟩
                                rw [hwsl8_p]; exact hwsl_len_mid
                              · obtain ⟨hw_old, hlt_old⟩ := he_ts.1 p hold
                                obtain ⟨hin_old, hb_old, hd_old, _⟩ := he_ts.2 p hold
                                have hp8_eq : memW p_hs (p + 8) = memW ent_hs (p + 8) :=
                                  (htab_frame_preserves_code_record (locN ent_hs "t") p
                                    hin_old.2 hb_old ht_fp_pos (hd_old _ ht_ent) hexit_hs.2.2.2.2.2.2.1).2
                                refine ⟨wordsOK_transfer_b4d hAe_hs.1 hexit_hs.1.1 hw_old, ?_⟩
                                rw [hp8_eq]; exact hlt_old
                            refine ⟨hwords, ?_⟩
                            intro p hp
                            rcases hvals_hs p hp with rfl | hold
                            · refine ⟨⟨hwsl_in_mid.1, le_trans hwsl_in_mid.2 hexit_hs.2.2.2.2.1⟩,
                                hwsl_64, ?_, ?_⟩
                              · intro t hm i hi
                                rcases table_coverage_of_htab_exit hAe_hs hWe_hs ht_ent hexit_hs t hm i hi with
                                  ⟨u, hu, j, hj, hin⟩ | hfr
                                · exact disj_of_inside_right hin (hwsl_disj_mid j
                                    (List.mem_append_left _ (List.mem_flatMap.2 ⟨u, hu, hj⟩)))
                                · exact allocatedEvm_disj_freshHeap_b4d (s := ent_hs) (post := p_hs)
                                    hAe_hs.2 hAp_hs.2 hhp_hs (Or.inr (Or.inl hwsl_in_mid)) hfr
                              · intro i hm
                                rw [fixedObjects_eq_of_nonbal_htab_exit hAe_hs hWe_hs ht_ent hexit_hs
                                  ⟨hnba_ent, hnad_ent⟩] at hm
                                exact hwsl_disj_mid i (List.mem_append_right _ hm)
                            · obtain ⟨hi_old, hb_old, _, hf_old⟩ := he_ts.2 p hold
                              refine ⟨⟨hi_old.1, le_trans hi_old.2 hexit_hs.2.2.2.2.1⟩, hb_old, ?_, ?_⟩
                              · intro t hm i hi
                                apply protected_payload_disj_of_growth_bounded he_ts hold
                                rcases table_coverage_of_htab_exit hAe_hs hWe_hs ht_ent hexit_hs t hm i hi with
                                  ⟨u, hu, j, hj, hin⟩ | hfr
                                · exact Or.inr (Or.inl ⟨j, Or.inl ⟨u, hu, hj⟩, hin⟩)
                                · exact Or.inr (Or.inr hfr)
                              · intro i hm
                                rw [fixedObjects_eq_of_nonbal_htab_exit hAe_hs hWe_hs ht_ent hexit_hs
                                  ⟨hnba_ent, hnad_ent⟩] at hm
                                exact hf_old i hm
                          have hC_p : CodeDbPayloadBoundedNz p_hs S_ent := by
                            intro g k hgk hgnz_p hdb_nz_p
                            have hg_eq : globN p_hs g = globN mid g := by
                              simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
                              rcases hgk with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact hgN _ (by decide)
                            rw [hg_eq] at hgnz_p hdb_nz_p ⊢
                            rw [hroot_eq g k hgk hgnz_p] at hdb_nz_p ⊢
                            have hdb_S := hroot_in_S g k hgk hgnz_p hdb_nz_p
                            have hgk' := hgk
                            simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk'
                            rcases hgk' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                            · have hne_ent : memW mid (globN mid "ws" + 16) ≠ locN ent_hs "t" := by
                                rw [hloc_t_hs]; exact hne_roots.1 hgnz_p
                              exact codeDbPayloadBounded_of_nonbal_htab_exit
                                (memW mid (globN mid "ws" + 16))
                                ((codeDbPayloadBounded_with_locals_clock mid S_ent _ _ (mid.clock - 1)).2
                                  (hC_ent_mid "ws" 16 hgk hgnz_p hdb_nz_p))
                                hAe_hs hWe_hs hdb_S ht_ent hne_ent hexit_hs ⟨hnba_ent, hnad_ent⟩
                            · have hne_ent : memW mid (globN mid "bs" + 48) ≠ locN ent_hs "t" := by
                                rw [hloc_t_hs]; exact hne_roots.2 hgnz_p
                              exact codeDbPayloadBounded_of_nonbal_htab_exit
                                (memW mid (globN mid "bs" + 48))
                                ((codeDbPayloadBounded_with_locals_clock mid S_ent _ _ (mid.clock - 1)).2
                                  (hC_ent_mid "bs" 48 hgk hgnz_p hdb_nz_p))
                                hAe_hs hWe_hs hdb_S ht_ent hne_ent hexit_hs ⟨hnba_ent, hnad_ent⟩
                            · rw [hm48_mid]
                              exact hC_ts48
                          have hM_p : MsgDisjCodeStrong p_hs := by
                            intro g k hgk hgnz_p hdb_nz_p p hp
                            have hg_eq : globN p_hs g = globN mid g := by
                              simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
                              rcases hgk with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact hgN _ (by decide)
                            rw [hg_eq] at hgnz_p hdb_nz_p hp
                            rw [hroot_eq g k hgk hgnz_p] at hdb_nz_p hp
                            rw [hgN "ev" (by decide), h112_p]
                            have hdb_S := hroot_in_S g k hgk hgnz_p hdb_nz_p
                            have hgk' := hgk
                            simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk'
                            rcases hgk' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                            · have hdj_ent : ∀ i ∈ htabFootprint ent_hs (memW mid (globN mid "ws" + 16)),
                                  ∀ j ∈ htabFootprint ent_hs (locN ent_hs "t"), Disj i j := by
                                rw [hloc_t_hs]; exact hWe_hs.1.2.2.1 _ hdb_S _ htw_Sent (hne_roots.1 hgnz_p)
                              have hv_eq : htabValues p_hs (memW mid (globN mid "ws" + 16)) =
                                  htabValues ent_hs (memW mid (globN mid "ws" + 16)) :=
                                htabValues_eq_of_htab_exit (memW mid (globN mid "ws" + 16))
                                  (hWe_hs.1.2.1 _ hdb_S).1 htw_ent
                                  (fun i hi => ((hWe_hs.1.2.1 _ hdb_S).2 i hi).1) hAe_hs hexit_hs hdj_ent
                              rw [hv_eq] at hp
                              exact hM_mid "ws" 16 hgk hgnz_p hdb_nz_p p hp
                            · have hdj_ent : ∀ i ∈ htabFootprint ent_hs (memW mid (globN mid "bs" + 48)),
                                  ∀ j ∈ htabFootprint ent_hs (locN ent_hs "t"), Disj i j := by
                                rw [hloc_t_hs]; exact hWe_hs.1.2.2.1 _ hdb_S _ htw_Sent (hne_roots.2 hgnz_p)
                              have hv_eq : htabValues p_hs (memW mid (globN mid "bs" + 48)) =
                                  htabValues ent_hs (memW mid (globN mid "bs" + 48)) :=
                                htabValues_eq_of_htab_exit (memW mid (globN mid "bs" + 48))
                                  (hWe_hs.1.2.1 _ hdb_S).1 htw_ent
                                  (fun i hi => ((hWe_hs.1.2.1 _ hdb_S).2 i hi).1) hAe_hs hexit_hs hdj_ent
                              rw [hv_eq] at hp
                              exact hM_mid "bs" 48 hgk hgnz_p hdb_nz_p p hp
                            · rw [hm48_mid] at hp
                              rcases hvals_hs p hp with rfl | hold
                              · exact hwsl_disj_msg_mid
                              · exact hM_mid "ts" 48 hgk hgnz_p hdb_nz_p p (by rwa [hm48_mid])
                          have hB_p : EvmMsgReadyMsgBounded p_hs := ⟨hexit_hs.1, hM_p, S_ent, hInv_p, hm_p, hC_p⟩
                          have hpost_eq : post = { p_hs with locals := post.locals, clock := p_hs.clock } := by
                            rw [hpost_ptail, hptail_tp, htp_eq, hs_hs_eq]
                          have hB_post : EvmMsgReadyMsgBounded post := by
                            rw [hpost_eq]; exact localsFree_evmMsgReadyMsgBounded p_hs _ _ hB_p
                          have hch_post : evmChain post = evmChain mid := by
                            rw [hpost_eq]; exact (evmChain_with_locals p_hs _ _).trans hch_p
                          have hstep_post : EvmStep ["heap_ptr"] mid post := by
                            refine ⟨evmInv_of_msgBounded hB_post, ?_, ?_, hch_post⟩
                            · rw [hpost_eq]; exact hhp_hs
                            · intro k hk; rw [hpost_eq]; exact hg_hs k (fun h => hk (by simp at h; simp [h]))
                          have hcc_post : ChainCellsAgree mid post := by
                            intro ec hec
                            obtain ⟨he_w, hc_w⟩ := hec_words ec hec
                            rw [hpost_eq]
                            exact ⟨he_w 24 (by omega) (by omega), he_w 32 (by omega) (by omega),
                              he_w 40 (by omega) (by omega), hc_w 56 (by omega) (by omega)⟩
                          have hStepCC_post : EvmStepCC ["heap_ptr", "journal_n"] mid post := by
                            refine ⟨⟨hstep_post.1, hstep_post.2.1, ?_, hstep_post.2.2.2⟩, hcc_post⟩
                            intro k hk
                            exact hstep_post.2.2.1 k (by
                              intro hmem
                              obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hmem
                              simp at hg; subst hg
                              exact hk (by simp))
                          have h112_post : memW post (globN mid "ev" + 112) = memW mid (globN mid "ev" + 112) := by
                            rw [hpost_eq]; exact h112_p
                          have hMB_mid_post : EvmMbStep ["heap_ptr", "journal_n"] mid post :=
                            ⟨hB_post, hStepCC_post, h112_post⟩
                          have hMB_post : EvmMbStep ["heap_ptr", "journal_n"] s post :=
                            evmMbStep_trans (s := s) (mid := mid) (post := post) (by decide)
                              ⟨hMB_mid, hStepCC_mid, h112_mid_s⟩ hMB_mid_post
                          exact evmMbStep_with_locals_right s.locals post.clock hMB_post
                        | _ => simp at hhs
            · rename_i hbad; simp only [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error

/-! ## 4. Bounded `set_code` Step & `D0PreB` Call Wrapper -/
