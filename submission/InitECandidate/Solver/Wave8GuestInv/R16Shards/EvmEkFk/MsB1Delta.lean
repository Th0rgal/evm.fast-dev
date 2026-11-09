import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.Depth0FrameOpen

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000
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

section MsgCodeStrongAndGetCodeUncond
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs

/-- Code payload records at nonzero code-DB roots are disjoint from a given 176-byte `msg` block. -/
def MsgDisjCodeStrongAt {F : Type} (s : PanSemStateFiniteExact 64 F) (msg : Nat) : Prop :=
  ∀ g k, (g, k) ∈ ([("ws", 16), ("bs", 48), ("ts", 48)] : List (String × Nat)) →
    globN s g ≠ 0 → memW s (globN s g + k) ≠ 0 →
    ∀ p ∈ htabValues s (memW s (globN s g + k)), Disj (msg, 176) (p, 16)

/-- Code payload records at nonzero code-DB roots are disjoint from the head frame's `ev+112` message block. -/
def MsgDisjCodeStrong {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  MsgDisjCodeStrongAt s (memW s (globN s "ev" + 112))

/-- Code-database payload typing restricted to nonzero code-DB roots (the zero address has no live table). -/
def CodeDbPayloadNonzero {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) : Prop :=
  ∀ g k, (g, k) ∈ ([("ws", 16), ("bs", 48), ("ts", 48)] : List (String × Nat)) →
    globN s g ≠ 0 → memW s (globN s g + k) ≠ 0 →
    CodeDbPayloadStrong s S (memW s (globN s g + k))

theorem codeDbPayloadNonzero_of_worldTypedCodeStrong {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (h : WorldTypedCodeStrong s S) : CodeDbPayloadNonzero s S :=
  fun g k hgk hg _ => h.2 g k hgk hg

theorem msgDisjCodeStrongAt_with_locals_clock {F : Type}
    (s : PanSemStateFiniteExact 64 F) (msg : Nat)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    MsgDisjCodeStrongAt {s with locals := L, clock := k} msg ↔ MsgDisjCodeStrongAt s msg :=
  Iff.rfl

theorem msgDisjCodeStrong_with_locals_clock {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    MsgDisjCodeStrong {s with locals := L, clock := k} ↔ MsgDisjCodeStrong s :=
  Iff.rfl

theorem codeDbPayloadNonzero_with_locals_clock {F : Type}
    (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    CodeDbPayloadNonzero {s with locals := L, clock := k} S ↔ CodeDbPayloadNonzero s S := by
  constructor
  · intro h g off hgk hg hdb
    have h0 := h g off hgk hg hdb
    refine ⟨h0.1, fun p hp => ?_⟩
    obtain ⟨hin, hp64, htd, hfd⟩ := h0.2 p hp
    exact ⟨hin, hp64, htd, hfd⟩
  · intro h g off hgk hg hdb
    have h0 := h g off hgk hg hdb
    refine ⟨h0.1, fun p hp => ?_⟩
    obtain ⟨hin, hp64, htd, hfd⟩ := h0.2 p hp
    exact ⟨hin, hp64, htd, hfd⟩

/-- Strengthened `MsgReady` carrying `CodeDbPayloadNonzero` and `MsgDisjCodeStrongAt` on `msg`. -/
def MsgReadyMsgCodeStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ memW s (locN s "msg" + 120) < 2 ^ 40 ∧
    MsgDisjCodeStrongAt s (locN s "msg") ∧
    ∃ S, WorldTyped s S ∧ CodeDbPayloadNonzero s S ∧
      memW s (locN s "msg" + 152) ∈ S ∧ memW s (locN s "msg" + 160) ∈ S ∧
      Inside (locN s "msg", 176) sourceBase (globN s "heap_ptr") ∧ WordsOK s (locN s "msg", 176) ∧
      (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj (locN s "msg", 176) i) ∧
      (∀ j ∈ fixedObjects s, Disj (locN s "msg", 176) j) ∧
      AvoidsTries s S [(locN s "msg", 176)] ∧
      memW s (locN s "msg" + 40) < 2 ^ 63 ∧
      RolesOK s S (worldRoleSlots s ++
        [(memW s (locN s "msg" + 152), "frame.addr"), (memW s (locN s "msg" + 160), "frame.key")])
        (journalRoleSlots s)

/-- Entry guard for `frame_open(msg, 0)` carrying code-DB payload typing and `msg` separation. -/
def FrameOpenReadyMsgCodeStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => MsgReadyMsgCodeStrong s ∧ locN s "kind" = 0

/-- Strengthened `EvmMsgReady` carrying `CodeDbPayloadNonzero` and `MsgDisjCodeStrong`. -/
def EvmMsgReadyMsgCodeStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ MsgDisjCodeStrong s ∧
    ∃ S, EvmInvAt s S ∧ MsgOwned s S (memW s (globN s "ev" + 112)) ∧ CodeDbPayloadNonzero s S

theorem evmMsgReadyCodeStrong_of_msgCodeStrong {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : EvmMsgReadyMsgCodeStrong s) : EvmMsgReadyCodeStrong s :=
  ⟨h.1, h.2.2⟩

theorem evmMsgReady_of_msgCodeStrong {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : EvmMsgReadyMsgCodeStrong s) : EvmMsgReady s :=
  evmMsgReady_of_codeStrong (evmMsgReadyCodeStrong_of_msgCodeStrong h)

theorem evmInv_of_msgCodeStrong {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : EvmMsgReadyMsgCodeStrong s) : EvmInv s :=
  evmInv_of_evmMsgReady s (evmMsgReady_of_msgCodeStrong h)

theorem evmInvAt_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S : List Nat) :
    EvmInvAt { s with locals := locals, clock := k } S ↔ EvmInvAt s S := by
  simp only [EvmInvAt, FrameWF, MsgOwned, worldTyped_with_locals, evmChain_with_locals]
  exact Iff.rfl

theorem msgOwned_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S : List Nat) (m : Nat) :
    MsgOwned { s with locals := locals, clock := k } S m ↔ MsgOwned s S m := by
  simp only [MsgOwned, evmChain_with_locals]
  exact Iff.rfl

theorem localsFree_evmMsgReadyMsgCodeStrong : LocalsFree EvmMsgReadyMsgCodeStrong := by
  intro F s locals k ⟨hA, hMD, S, hI, hMO, hCS⟩
  exact ⟨localsFree_arenaReady s locals k hA,
    (msgDisjCodeStrong_with_locals_clock s locals k).2 hMD,
    S, (evmInvAt_with_locals s locals k S).2 hI,
    (msgOwned_with_locals s locals k S _).2 hMO,
    (codeDbPayloadNonzero_with_locals_clock s S locals k).2 hCS⟩

theorem localsOnly_msgReadyMsgCodeStrong : LocalsOnly ["msg"] MsgReadyMsgCodeStrong := by
  intro F s locals k hl ⟨hA, hnb, hMD, S, hWT, hCS, ht152, ht160, hm_in, hm_wok, hm_tab, hm_fix, hm_at, hm_gas, hm_roles⟩
  have hm := locN_congr s locals k "msg" (hl "msg" (by simp))
  have hnb' : memW { s with locals := locals, clock := k } (locN { s with locals := locals, clock := k } "msg" + 120) < 2 ^ 40 := by
    change memW s (locN { s with locals := locals, clock := k } "msg" + 120) < 2 ^ 40
    rw [hm]; exact hnb
  have hMD' : MsgDisjCodeStrongAt { s with locals := locals, clock := k } (locN { s with locals := locals, clock := k } "msg") := by
    rw [hm]; exact (msgDisjCodeStrongAt_with_locals_clock s _ locals k).2 hMD
  have ht152' : memW { s with locals := locals, clock := k } (locN { s with locals := locals, clock := k } "msg" + 152) ∈ S := by
    change memW s (locN { s with locals := locals, clock := k } "msg" + 152) ∈ S
    rw [hm]; exact ht152
  have ht160' : memW { s with locals := locals, clock := k } (locN { s with locals := locals, clock := k } "msg" + 160) ∈ S := by
    change memW s (locN { s with locals := locals, clock := k } "msg" + 160) ∈ S
    rw [hm]; exact ht160
  have hm_in' : Inside (locN { s with locals := locals, clock := k } "msg", 176) sourceBase (globN { s with locals := locals, clock := k } "heap_ptr") := by
    change Inside (locN { s with locals := locals, clock := k } "msg", 176) sourceBase (globN s "heap_ptr")
    rw [hm]; exact hm_in
  have hm_wok' : WordsOK { s with locals := locals, clock := k } (locN { s with locals := locals, clock := k } "msg", 176) := by
    change WordsOK s (locN { s with locals := locals, clock := k } "msg", 176)
    rw [hm]; exact hm_wok
  have hm_tab' : ∀ t ∈ S, ∀ i ∈ htabFootprint { s with locals := locals, clock := k } t, Disj (locN { s with locals := locals, clock := k } "msg", 176) i := by
    change ∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj (locN { s with locals := locals, clock := k } "msg", 176) i
    rw [hm]; exact hm_tab
  have hm_fix' : ∀ j ∈ fixedObjects { s with locals := locals, clock := k }, Disj (locN { s with locals := locals, clock := k } "msg", 176) j := by
    change ∀ j ∈ fixedObjects s, Disj (locN { s with locals := locals, clock := k } "msg", 176) j
    rw [hm]; exact hm_fix
  have hm_at' : AvoidsTries { s with locals := locals, clock := k } S [(locN { s with locals := locals, clock := k } "msg", 176)] := by
    change AvoidsTries s S [(locN { s with locals := locals, clock := k } "msg", 176)]
    rw [hm]; exact hm_at
  have hm_gas' : memW { s with locals := locals, clock := k } (locN { s with locals := locals, clock := k } "msg" + 40) < 2 ^ 63 := by
    change memW s (locN { s with locals := locals, clock := k } "msg" + 40) < 2 ^ 63
    rw [hm]; exact hm_gas
  have hm_roles' : RolesOK { s with locals := locals, clock := k } S
      (worldRoleSlots { s with locals := locals, clock := k } ++
        [(memW { s with locals := locals, clock := k } (locN { s with locals := locals, clock := k } "msg" + 152), "frame.addr"),
         (memW { s with locals := locals, clock := k } (locN { s with locals := locals, clock := k } "msg" + 160), "frame.key")])
      (journalRoleSlots { s with locals := locals, clock := k }) := by
    change RolesOK s S
      (worldRoleSlots s ++
        [(memW s (locN { s with locals := locals, clock := k } "msg" + 152), "frame.addr"),
         (memW s (locN { s with locals := locals, clock := k } "msg" + 160), "frame.key")])
      (journalRoleSlots s)
    rw [hm]; exact hm_roles
  exact ⟨localsFree_arenaReady s locals k hA, hnb', hMD',
    S, (worldTyped_with_locals s locals k S).2 hWT,
    (codeDbPayloadNonzero_with_locals_clock s S locals k).2 hCS,
    ht152', ht160', hm_in', hm_wok', hm_tab', hm_fix', hm_at', hm_gas', hm_roles'⟩

theorem callEntryOn_frameOpenReadyMsgCodeStrong :
    CallEntryOn MsgReadyMsgCodeStrong FrameOpenReadyMsgCodeStrong (ofString "frame_open")
      [.var .local (ofString "msg"), .const 0] := by
  intro F state values body' callee ret' hcode hP hargs hlook
  obtain ⟨v1, v2, he1, he2, hc1, hc2⟩ := R10Shards.GbodyProcessMsg.callee_param_two state (ofString "frame_open")
    (ofString "msg") (ofString "kind") .one .one (sourceFnBody Guest.Software.guestFn_frame_open) .one
    (by rw [hcode]; exact lookup_frame_open)
    (.var .local (ofString "msg")) (.const 0) values body' callee ret' hargs hlook
  have hv1 : state.locals.lookup (ofString "msg") = some v1 := by
    simpa [evalAt, evalHOLExact] using he1
  have hv2 := evalAt_const state 0 v2 he2
  subst hv2
  refine ⟨?_, ?_⟩
  · exact localsOnly_msgReadyMsgCodeStrong state callee (state.clock - 1)
      (fun n hn => by simp at hn; subst hn; rw [hc1, hv1]) hP
  · simp [locN, callEntryStateHOLFinite, hc2]

/-- `frame_open(msg, 0)` transitions `FrameOpenReadyMsgCodeStrong` to `EvmMsgReadyMsgCodeStrong`. -/
theorem fk_frame_open_msgCodeStrong :
    KeepsOn FrameOpenReadyMsgCodeStrong EvmMsgReadyMsgCodeStrong (ofString "frame_open") := by
  refine ⟨_, _, _, lookup_frame_open, fun s hcode hP hex _hnt hr => ?_⟩
  obtain ⟨w1, hw1⟩ := hex
  obtain ⟨⟨m, hm⟩, ⟨k, hk⟩⟩ := fo_param_words_two s (p1 := "msg") (p2 := "kind") (by decide)
    lookup_frame_open ⟨w1, hw1⟩
  have hmloc : locN s "msg" = m.toNat := by unfold locN; rw [hm]
  have hlk : locN s "kind" = k.toNat := by unfold locN; rw [hk]
  obtain ⟨v, hv⟩ := frame_open_resumes_returned s hcode hw1 hr
  obtain ⟨⟨hAR, hnb, hMD, S, hWT, hCS, ht152, ht160, hm_in, hm_wok, hm_tab, hm_fix, hm_at, hm_gas, hm_roles⟩, hk_eq⟩ := hP
  rw [hmloc] at ht152 ht160 hm_in hm_wok hm_tab hm_fix hm_at hm_gas hm_roles hnb hMD
  have hk0 : k.toNat = 0 := by rw [← hlk]; exact hk_eq
  have h152_alloc : Allocated s (memW s (m.toNat + 152), 88) :=
    ((hWT.1.2.1 _ ht152).2 _ (by simp [htabFootprint])).1
  have h160_alloc : Allocated s (memW s (m.toNat + 160), 88) :=
    ((hWT.1.2.1 _ ht160).2 _ (by simp [htabFootprint])).1
  have hRich := frame_open_rich_run s hcode hAR m k hm hk hk0 hm_in.2 hnb h152_alloc h160_alloc v hv
  let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_open)).2
  have hout_dom : ∀ a : BitVec 64, ¬ ordinaryDomain a → post.memory a = s.memory a := by
    intro a ha
    have hdom_s : s.memaddrs = ordinaryDomain := hAR.1.memaddrs
    exact scratch_evaluate_mem_out_dom s _ (by rw [hdom_s]; exact ha)
  obtain ⟨tb, hEvmInvAt, hMsgOwned, hCS_post⟩ :=
    frameOpen_evmMsgReady_at (k := k) hAR hWT ht152 ht160 hm_in hm_wok hm_tab hm_fix hm_at hm_gas hm_roles hout_dom hRich
  obtain ⟨Nd, hTr_s, _⟩ := hm_at
  have hWT_s : WorldTypedWith s S Nd := ⟨hWT.1, hWT.2.1, hWT.2.2.1, hTr_s⟩
  obtain ⟨e, rec, stk, lg, q0, tb', hARp, _, hma, hbe, hgev, hgcc, hgsp, hgk, hhp_le,
    hfmp_rec, hfo, he8, hrec8, hstk8, hlg8, hq08, htb8,
    hrec_q0, htb_q0, hq0_lg, hlg_stk, hstk_e, he_sp,
    hss_m24, hm24_fmp, hm24_8, hrec16,
    he8w, he232, he16, he32, he192, he40, he64, he88, hlg0, hlg8w, hlg16,
    he112, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hRich
  have hcell : EvmBase.SameTypedCells s post S Nd :=
    frameOpen_sameTypedCells hAR hARp hWT_s hbe hma hout_dom hfmp_rec (by omega) hrec8 hfo
  have hMD_post : MsgDisjCodeStrong post := by
    intro g k_off hgk_mem hgn_ne0 hdb_ne0_p p hp
    have hgg : globN post g = globN s g := by
      have hm_of : ∀ s0 : String, ofString g = ofString s0 → ofString s0 ∈ R10Shards.P26_P28.coreWorldGlobals.map ofString := by
        intro s0 h
        have hg_in : g ∈ R10Shards.P26_P28.coreWorldGlobals := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk_mem
          rcases hgk_mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
        exact List.mem_map.2 ⟨g, hg_in, h⟩
      exact (globN_eq_of_lookup_eq ((hgk (ofString g)
        (fun h => (by decide : ofString "scratch_ptr" ∉ R10Shards.P26_P28.coreWorldGlobals.map ofString) (hm_of _ h))
        (fun h => (by decide : ofString "heap_ptr" ∉ R10Shards.P26_P28.coreWorldGlobals.map ofString) (hm_of _ h))
        (fun h => (by decide : ofString "frame_mem_ptr" ∉ R10Shards.P26_P28.coreWorldGlobals.map ofString) (hm_of _ h))
        (fun h => (by decide : ofString "ev" ∉ R10Shards.P26_P28.coreWorldGlobals.map ofString) (hm_of _ h))
        (fun h => (by decide : ofString "cur_cont" ∉ R10Shards.P26_P28.coreWorldGlobals.map ofString) (hm_of _ h))).symm)).symm
    have hgn_s : globN s g ≠ 0 := by rwa [hgg] at hgn_ne0
    have hr_eq : memW post (globN s g + k_off) = memW s (globN s g + k_off) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk_mem
      rcases hgk_mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact typed_record_root_preserved hAR hWT_s hcell "ws" 40 16 (by decide) hgn_s (by decide)
      · exact typed_record_root_preserved hAR hWT_s hcell "bs" 80 48 (by decide) hgn_s (by decide)
      · exact typed_record_root_preserved hAR hWT_s hcell "ts" 72 48 (by decide) hgn_s (by decide)
    rw [hgg, hr_eq] at hdb_ne0_p hp
    have hdb_S : memW s (globN s g + k_off) ∈ S := by
      have hdb_root : RootIn S (memW s (globN s g + k_off)) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk_mem
        rcases hgk_mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hWT.1.2.2.2.1 16 (by decide) hgn_s
        · exact hWT.1.2.2.2.2.1 48 (by decide) hgn_s
        · exact hWT.1.2.2.2.2.2.1 48 (by decide) hgn_s
      rcases hdb_root with h0 | hS_in
      · exact False.elim (hdb_ne0_p h0)
      · exact hS_in
    have hv_eq : htabValues post (memW s (globN s g + k_off)) =
        htabValues s (memW s (globN s g + k_off)) :=
      EvmBase.htabValues_eq hcell hdb_S (hWT.1.2.1 _ hdb_S).1
    rw [hv_eq] at hp
    rw [hgev, he112]
    exact hMD g k_off hgk_mem hgn_s hdb_ne0_p p hp
  exact ⟨hARp, hMD_post, tb.toNat :: S, hEvmInvAt, hMsgOwned, hCS_post hCS⟩

end MsgCodeStrongAndGetCodeUncond

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
