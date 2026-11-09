import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB3bCodeBoundedLookup
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB2dExtCodeChainNz

/-!
# Scratch Rung B3c: Bounded Payload Preservation & `get_code` (`CodeBoundedCtxNz`)

Proves `CodeDbPayloadBounded` preservation across layout/growth/`WorldEff`/`sk_make`/non-BAL `HtabExit`
and closes `get_code` bounded return under `CodeBoundedCtxNz`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

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

section CodeBoundedPres
open R10Shards.GbodyProcessMsg
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

theorem nodeDbEntriesBounded_of_preserved_payloads {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {db : Nat}
    (he : NodeDbEntriesBounded s db) (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hvalues : htabValues post db = htabValues s db)
    (hwords : ∀ p ∈ htabValues s db, memW post (p + 8) = memW s (p + 8)) :
    NodeDbEntriesBounded post db := by
  intro p hp
  rw [hvalues] at hp
  obtain ⟨hw, hlt⟩ := he p hp
  refine ⟨R10Shards.GbodyProcessMsg.wordsOK_transfer hAs.1 hAp.1 hw, ?_⟩
  rw [hwords p hp]; exact hlt

theorem protected_payload_disj_of_growth_bounded {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} {db p : Nat} {i : Ivl}
    (he : CodeDbPayloadBounded s S db) (hp : p ∈ htabValues s db)
    (hg : i = (0, 0) ∨
      (∃ j, ((∃ t ∈ S, j ∈ htabFootprint s t) ∨ j ∈ fixedObjects s) ∧ Inside i j.1 (j.1 + j.2)) ∨
      Inside i (globN s "heap_ptr") (globN post "heap_ptr")) :
    Disj (p, 16) i := by
  obtain ⟨hi, _, ht, hf⟩ := he.2 p hp
  rcases hg with rfl | ⟨j, hj, hij⟩ | hnew
  · simp [Disj]
  · have hd : Disj (p, 16) j := by
      rcases hj with ⟨t, ht', hj'⟩ | hj'
      · exact ht t ht' j hj'
      · exact hf j hj'
    unfold Inside at hij; unfold Disj at hd ⊢; dsimp only at hd ⊢
    rcases hd with hd | hd | hd | hd <;> omega
  · unfold Inside at hnew hi; unfold Disj; dsimp only at hi ⊢; omega

theorem codeDbPayloadBounded_of_owned_growth {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S S' : List Nat} {db : Nat}
    (he : CodeDbPayloadBounded s S db) (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hv : htabValues post db = htabValues s db)
    (hw : ∀ p ∈ htabValues s db, memW post (p + 8) = memW s (p + 8))
    (hg : ∀ i, ((∃ t ∈ S', i ∈ htabFootprint post t) ∨ i ∈ fixedObjects post) →
      i = (0, 0) ∨
      (∃ j, ((∃ t ∈ S, j ∈ htabFootprint s t) ∨ j ∈ fixedObjects s) ∧ Inside i j.1 (j.1 + j.2)) ∨
      Inside i (globN s "heap_ptr") (globN post "heap_ptr")) :
    CodeDbPayloadBounded post S' db := by
  refine ⟨nodeDbEntriesBounded_of_preserved_payloads he.1 hAs hAp hv hw, ?_⟩
  intro p hp
  rw [hv] at hp
  obtain ⟨hi, hb, _, _⟩ := he.2 p hp
  refine ⟨⟨hi.1, le_trans hi.2 hhp⟩, hb,
    fun t ht i hi' => protected_payload_disj_of_growth_bounded he hp (hg i (Or.inl ⟨t, ht, hi'⟩)),
    fun i hi' => protected_payload_disj_of_growth_bounded he hp (hg i (Or.inr hi'))⟩

theorem codeDbPayloadBounded_of_preserved_layout {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} {db : Nat}
    (he : CodeDbPayloadBounded s S db) (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hv : htabValues post db = htabValues s db)
    (hw : ∀ p ∈ htabValues s db, memW post (p + 8) = memW s (p + 8))
    (hf : ∀ t ∈ S, htabFootprint post t = htabFootprint s t)
    (hfixed : fixedObjects post = fixedObjects s) :
    CodeDbPayloadBounded post S db := by
  refine ⟨nodeDbEntriesBounded_of_preserved_payloads he.1 hAs hAp hv hw, ?_⟩
  intro p hp
  rw [hv] at hp
  obtain ⟨hi, hb, ht, hfix⟩ := he.2 p hp
  refine ⟨⟨hi.1, le_trans hi.2 hhp⟩, hb, ?_, ?_⟩
  · intro t ht' i hi'; rw [hf t ht'] at hi'; exact ht t ht' i hi'
  · intro i hi'; rw [hfixed] at hi'; exact hfix i hi'

theorem protected_payload_len_of_world_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} {db : Nat}
    (he : CodeDbPayloadBounded s S db) (hA : ArenaReady s)
    (hframe : ∀ a : BitVec 64, post.memory a ≠ s.memory a →
      (∃ i, ((∃ t ∈ S, i ∈ htabFootprint s t) ∨ i ∈ fixedObjects s) ∧
        0 < i.2 ∧ i.1 < a.toNat + 8 ∧ a.toNat < i.1 + i.2) ∨
      ((freeGap s).1 < a.toNat + 8 ∧ a.toNat < (freeGap s).1 + (freeGap s).2) ∨
      ((heapFree s).1 < a.toNat + 8 ∧ a.toNat < (heapFree s).1 + (heapFree s).2)) :
    ∀ p ∈ htabValues s db, memW post (p + 8) = memW s (p + 8) := by
  intro p hp
  obtain ⟨hin, hbound, ht, hfix⟩ := he.2 p hp
  have hb : p + 8 < 2 ^ 64 := by omega
  unfold memW
  have hm : post.memory (BitVec.ofNat 64 (p + 8)) = s.memory (BitVec.ofNat 64 (p + 8)) := by
    by_contra hn
    have hc := hframe (BitVec.ofNat 64 (p + 8)) hn
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb] at hc
    rcases hc with ⟨i, hi, _, h1, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
    · have hd : Disj (p, 16) i := by
        rcases hi with ⟨t, ht', hi'⟩ | hi'
        · exact ht t ht' i hi'
        · exact hfix i hi'
      unfold Disj at hd; dsimp only at hd; rcases hd with hd | hd | hd | hd <;> omega
    · have hh := hA.2.2.1; have hfmp := hA.2.2.2.1
      have hs : heapLimit ≤ scratchStart := by decide
      have hip := hin.2; unfold freeGap at h1; dsimp only at h1 hip; omega
    · have hip := hin.2; unfold heapFree at h1; dsimp only at h1 hip; omega
  rw [hm]

theorem codeDbPayloadBounded_of_witness_effect {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {db : Nat}
    (he : CodeDbPayloadBounded s S db)
    (hWT : WorldTypedWith s S Nd) (hA : ArenaReady s)
    (heff : WorldEff s post [] wsBufs wsGw) (hdb : db ∈ S) :
    CodeDbPayloadBounded post S db := by
  refine codeDbPayloadBounded_of_preserved_layout he hA heff.arena heff.hp_lo
    (htabValues_eq_of_witness_effect hWT hA heff db hdb)
    (protected_payload_len_of_world_frame he hA ?_)
    (htabFootprint_eq_of_witness_effect hWT hA heff)
    (fixedObjects_eq_of_witness_effect hWT hA heff)
  intro a hn
  rcases heff.cell_frame a hn with ⟨i, hi, _⟩ | ⟨b, hb, hpos, hlo, hhi⟩ | ⟨_, hlo, hhi⟩ | ⟨_, hlo, hhi⟩
  · cases hi
  · refine Or.inl ⟨bufferRegion s b, Or.inr ?_, hpos, hlo, hhi⟩
    have hgb : b ∈ globalBuffers := by
      simp only [wsBufs, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl <;> decide
    unfold fixedObjects
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨b, hgb, rfl⟩)))
  · exact Or.inr (Or.inl ⟨hlo, hhi⟩)
  · exact Or.inr (Or.inr ⟨hlo, hhi⟩)

theorem codeDbPayloadBounded_of_sk_make {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} (db : Nat)
    (h : CodeDbPayloadBounded s S db)
    (hc : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hfit : ∀ (_ : globN s "sk_buf" ≠ 0), globN s "sk_buf" + 52 ≤ 2 ^ 64)
    (v : ValueHOL 64)
    (hb : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make) =
      (some (.returned v), post))
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hvalues : htabValues post db = htabValues s db)
    (hfp : ∀ t ∈ S, htabFootprint post t = htabFootprint s t)
    (hfixed : fixedObjects post = fixedObjects s) : CodeDbPayloadBounded post S db := by
  have hr : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make)).1 := by
    rw [hb]; exact Or.inl ⟨v, rfl⟩
  obtain ⟨_, _, _, hnz, heff⟩ := eval_sk_make_body_evm s hc hma hfit (by rw [hb]; simp) hr
  rw [hb] at heff
  have hhp : globN s "heap_ptr" ≤ globN post "heap_ptr" := by
    unfold globN; rw [heff.globals]
  refine codeDbPayloadBounded_of_preserved_layout h hAs hAp hhp hvalues ?_ hfp hfixed
  intro p hp
  obtain ⟨_, hp64, _, hd⟩ := h.2 p hp
  have hmem : (globN s "sk_buf", 64) ∈ fixedObjects s := by
    unfold fixedObjects
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨("sk_buf", 64), by decide, by simp [hnz]⟩)))
  have hdj : Disj (p, 16) (globN s "sk_buf", 52) := by
    rcases hd _ hmem with h0 | h0 | h0 | h0
    · omega
    · omega
    · exact Or.inr (Or.inr (Or.inl h0))
    · exact Or.inr (Or.inr (Or.inr (by omega)))
  exact (sk_make_preserves_code_record s hc hma hfit p hp64 hdj v post hb).2

theorem codeDbPayloadBounded_of_nonbal_htab_exit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} (db : Nat)
    (he : CodeDbPayloadBounded s S db)
    (hAs : ArenaReady s) (hW : WorldTyped s S)
    (hdb : db ∈ S) (ht : locN s "t" ∈ S)
    (hne : db ≠ locN s "t") (hx : HtabExit s post)
    (hn : globN s "bal_accounts" ≠ locN s "t" ∧
      ∀ ad ∈ balRecords s, memW s ad ≠ locN s "t") :
    CodeDbPayloadBounded post S db := by
  have hw := (hW.1.2.1 db hdb).1
  have htw := (hW.1.2.1 (locN s "t") ht).1
  have hv : htabValues post db = htabValues s db :=
    htabValues_eq_of_htab_exit db hw htw (fun i hi => ((hW.1.2.1 db hdb).2 i hi).1) hAs hx
      (hW.1.2.2.1 db hdb (locN s "t") ht hne)
  have hwords : ∀ p ∈ htabValues s db, memW post (p + 8) = memW s (p + 8) := by
    intro p hp
    obtain ⟨hin, hp64, hd, _⟩ := he.2 p hp
    exact (htab_frame_preserves_code_record (locN s "t") p hin.2 hp64
      (htabFootprint_pos s _ htw.2.2.1 htw.2.2.2.2.1) (hd _ ht) hx.2.2.2.2.2.2.1).2
  refine ⟨nodeDbEntriesBounded_of_preserved_payloads he.1 hAs hx.1 hv hwords, ?_⟩
  intro p hp
  rw [hv] at hp
  obtain ⟨hi, hb, _, hf⟩ := he.2 p hp
  refine ⟨⟨hi.1, le_trans hi.2 hx.2.2.2.2.1⟩, hb, ?_, ?_⟩
  · intro t hm i hi'
    apply protected_payload_disj_of_growth_bounded he hp
    rcases table_coverage_of_htab_exit hAs hW ht hx t hm i hi' with ⟨u, hu, j, hj, hin⟩ | hfr
    · exact Or.inr (Or.inl ⟨j, Or.inl ⟨u, hu, hj⟩, hin⟩)
    · exact Or.inr (Or.inr hfr)
  · intro i hm
    rw [fixedObjects_eq_of_nonbal_htab_exit hAs hW ht hx hn] at hm
    exact hf i hm

theorem codeBoundedCtxNz_after_sk_call {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "sk_make") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    CodeBoundedCtxNz post S Nd := by
  obtain ⟨hAs, hWT, hCB, hc, hs⟩ := hctx
  have hbody := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "sk_make")
    _ _ _ _ _ values callee (by rw [hc]; exact lookup_sk_make) hl
  subst body
  let ce := callEntryStateHOLFinite s callee
  have hAce : ArenaReady ce := localsFree_arenaReady s _ _ hAs
  have hWTce : WorldTypedWith ce S Nd :=
    ⟨(tablesTyped_with_locals s callee (s.clock - 1) S).2 hWT.1, hWT.2.1, hWT.2.2.1, hWT.2.2.2⟩
  have hWce : WorldTyped ce S := (worldTyped_iff_with _ _).2 ⟨Nd, hWTce⟩
  have hfit : ∀ (_ : globN ce "sk_buf" ≠ 0), globN ce "sk_buf" + 52 ≤ 2 ^ 64 :=
    fun hn => key_buffer_fit_of_world s hAs hWT.2.2.1 hn
  have hr : Resumes (evaluateHOLFiniteState ce (sourceFnBody Guest.Software.guestFn_sk_make)).1 := by
    rw [hb]; exact Or.inl ⟨v, rfl⟩
  obtain ⟨_, _, _, hsk_nz, heff⟩ := eval_sk_make_body_evm ce hc hAs.1.memaddrs hfit (by rw [hb]; simp) hr
  rw [hb] at heff
  have hd : ∀ i ∈ worldTypedIvls ce S Nd, Disj i (globN ce "sk_buf", 52) := fun i hi => by
    have hd0 := bufferRegion_disj_le hWTce ("sk_buf", 64) (by decide) (by decide) 52 (by decide) i hi
    simpa [bufferRegion, hsk_nz] using Disj.flip hd0
  have hAp := arenaReady_of_sk_make hAce hc hAs.1.memaddrs hfit v hb
  obtain ⟨hWp, hfixed⟩ := worldTypedWith_of_sk_make hAce hAp hWTce hc hAs.1.memaddrs hfit v hb hd
  have hp_tabs := typed_tables_preserved_of_sk_make hWce hc hAs.1.memaddrs hfit v hb
  have hcells := @sameTypedCells_of_sk_make F ce post S Nd hc hAs.1.memaddrs hfit v hb hd
  have hm := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata ce
    (sourceFnBody Guest.Software.guestFn_sk_make)
  rw [hb] at hm
  have hg : ∀ name, globN post name = globN s name := fun name => by
    change globN post name = globN ce name; unfold globN; rw [heff.globals]
  refine ⟨hAp, hWp, ?_, hm.1.trans hc, hm.2.2.2.2 ▸ hs⟩
  intro g k hgk hgnz hdb_nz
  have hgnz_s : globN s g ≠ 0 := by rwa [hg g] at hgnz
  have hrec_eq : memW post (globN post g + k) = memW s (globN s g + k) := by
    rw [hg g]
    have hrec_sz : ∃ sz, (g, sz) ∈ typedRecords ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
      rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨40, by decide, by decide, by decide⟩
      · exact ⟨80, by decide, by decide, by decide⟩
      · exact ⟨72, by decide, by decide, by decide⟩
    obtain ⟨sz, htr, _, _⟩ := hrec_sz
    have hce_g : globN ce g = globN s g := rfl
    have hrec_ivl : (globN ce g, sz) ∈ worldTypedIvls ce S Nd := by
      unfold worldTypedIvls; simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map.2 ⟨(g, sz), htr, by rw [hce_g]; simp [hgnz_s]⟩)))))
    have hf : (globN s g, sz) ∈ fixedObjects s := by
      unfold fixedObjects
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.2 ⟨(g, sz), (show ∀ r ∈ typedRecords, r ∈ globalBuffers by decide) _ htr, by simp [hgnz_s]⟩)))
    have ha_lt : globN s g + k < 2 ^ 64 := by
      rcases hWT.2.2.1.1 _ hf with hz | ⟨ha, _⟩
      · dsimp at hz; omega
      · have hb0 := allocated_le_2pow64 hAs.2 ha; dsimp only at hb0; omega
    unfold memW
    rw [hcells.2.2.2.2.1 (globN s g + k) ha_lt ⟨(globN ce g, sz), hrec_ivl, by rw [hce_g]; omega, by rw [hce_g]; omega⟩]
    rfl
  rw [hrec_eq] at hdb_nz ⊢
  have hdb_S : memW s (globN s g + k) ∈ S := by
    have hrin : RootIn S (memW s (globN s g + k)) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
      rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hWT.1.2.2.2.1 16 (by decide) hgnz_s
      · exact hWT.1.2.2.2.2.1 48 (by decide) hgnz_s
      · exact hWT.1.2.2.2.2.2.1 48 (by decide) hgnz_s
    exact hrin.resolve_left hdb_nz
  exact codeDbPayloadBounded_of_sk_make (memW s (globN s g + k))
    ((codeDbPayloadBounded_with_locals_clock s S _ callee (s.clock - 1)).2 (hCB g k hgk hgnz_s hdb_nz))
    hc hAs.1.memaddrs hfit v hb hAce hAp (hp_tabs _ hdb_S).1 (fun t ht => (hp_tabs t ht).2) hfixed

end CodeBoundedPres

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
