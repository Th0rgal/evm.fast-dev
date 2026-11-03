import InitECandidate.Solver.Wave8GuestInv.Deliveries.M12.StepLemmas
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.Common

/-! Shared R13 W1 world-step and constructor-return infrastructure for `WkShard01.lean`,
built strictly on prebuilt `.olean` modules (`Deliveries.M12.StepLemmas`, `Deliveries.M26.Common`). -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.R13Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8Contracts.M12
open InitECandidate.Solver.Wave8Contracts.M26

/-! ## 1. Non-resuming outcomes, parameter lookup, and `trap_with` -/

theorem lookupCode_one_word {fname p1 : MlS} {body : ProgHOL 64} {retShape : ShapeHOL}
    {vals : List (ValueHOL 64)} {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one)], body, retShape))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, L, retShape)) :
    ∃ w1 : BitVec 64,
      vals = [.val (.word w1)] ∧
      L.lookup p1 = some (.val (.word w1)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup fname vals body L retShape hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | _⟩
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hx
    exact ⟨w1, rfl, by rw [← hx]; simp⟩
  · simp at hx

theorem lookupCode_two_words {fname p1 p2 : MlS} {body : ProgHOL 64} {retShape : ShapeHOL}
    {vals : List (ValueHOL 64)} {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hne : p1 ≠ p2)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one)], body, retShape))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, L, retShape)) :
    ∃ w1 w2 : BitVec 64,
      vals = [.val (.word w1), .val (.word w2)] ∧
      L.lookup p1 = some (.val (.word w1)) ∧
      L.lookup p2 = some (.val (.word w2)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup fname vals body L retShape hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
  · simp at hx
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL] at hx
    refine ⟨w1, w2, rfl, ?_, ?_⟩
    · rw [← hx.2]; simp [hne, Ne.symm hne]
    · rw [← hx.2]; simp [hne, Ne.symm hne]
  · simp at hx

theorem not_resumes_error : ¬ Wave8Contracts.M12.Resumes (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

theorem evaluate_call_trap_with_no_resumes {F : Type}
    (state : PanSemStateFiniteExact 64 F) (codeVal : BitVec 64)
    (hcode : state.code = originalRuntimeCode) :
    ¬ Wave8Contracts.M12.Resumes (evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "trap_with") [.const codeVal])).1 := by
  rw [evaluateHOLFiniteState_call]
  have hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const codeVal] =
      some [.val (.word codeVal)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hlookup := pan_one_word_lookup state.code.lookup (ofString "trap_with") (ofString "code")
    (sourceFnBody Guest.Software.guestFn_trap_with) codeVal (by rw [hcode]; exact lookup_trap_with)
  rw [hargs]; dsimp only; rw [hlookup]; dsimp only
  split
  · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h
  · have hout := evaluate_trap_with_body_outcomes
      (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
    rcases hbody : evaluateHOLFiniteState
      (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
      (sourceFnBody Guest.Software.guestFn_trap_with) with ⟨res, st⟩
    rw [hbody] at hout
    cases res with
    | none => exact absurd rfl hout.1
    | some r =>
      cases r with
      | returned v => exact absurd rfl (hout.2.1 v)
      | exception eid ev =>
        rintro (⟨_, h⟩ | ⟨e', v', h, hne⟩)
        · simp at h
        · simp at h; obtain ⟨rfl, rfl⟩ := h; exact hout.2.2 eid ev hne rfl
      | «break» | «continue» | error | timeOut | finalFfi _ =>
        rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h

/-! ## 2. `WorldFrameEff`: general world-step effect (`R s`, `gw ⊆ ["heap_ptr", "scratch_ptr"]`, free heap & free scratch) -/

structure WorldFrameEff {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (Rl : List Ivl) (gw : List String) : Prop where
  arena      : ArenaReady post
  hp_grows   : globN s "heap_ptr" ≤ globN post "heap_ptr"
  sp_shrinks : globN post "scratch_ptr" ≤ globN s "scratch_ptr"
  gw_kept    : Wave8Contracts.M12.GlobalsKept gw s post
  be_eq      : post.be = s.be
  out_dom    : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a
  cell_frame : ∀ a : BitVec 64,
                 (∀ i ∈ Rl ++ [Wave8Contracts.M12.freeGap s], ¬ CellHits a.toNat i) →
                 ¬ CellHits a.toNat (Wave8Contracts.M12.heapFree s) →
                 post.memory a = s.memory a
  byte_frame : ∀ b : Nat, b < 2 ^ 64 →
                 (∀ i ∈ Rl ++ [Wave8Contracts.M12.freeGap s], ¬ InIvl b i) →
                 ¬ InIvl b (Wave8Contracts.M12.heapFree s) →
                 memB post b = memB s b

theorem WorldFrameEff.refl {F : Type} (s : PanSemStateFiniteExact 64 F)
    (Rl : List Ivl) (gw : List String) (hA : ArenaReady s) :
    WorldFrameEff s s Rl gw :=
  ⟨hA, le_rfl, le_rfl, fun _ _ => rfl, rfl,
   fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem WorldFrameEff.with_locals_clock {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {gw : List String} (h : WorldFrameEff s post Rl gw)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    WorldFrameEff s { post with locals := L, clock := k } Rl gw :=
  ⟨⟨guestInv_with_locals_clock post L k h.arena.1, h.arena.2⟩,
   h.hp_grows, h.sp_shrinks, h.gw_kept, h.be_eq, h.out_dom, h.cell_frame, h.byte_frame⟩

theorem mem_eq_of_bytes_eq_ord {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hbe : post.be = s.be) (a : BitVec 64) (ha_dom : ordinaryDomain a)
    (hb : ∀ k : Nat, k < 8 → memB post (a.toNat + k) = memB s (a.toNat + k)) :
    post.memory a = s.memory a := by
  have hdom' := (Wave8Contracts.M12.ordinaryDomain_iff a).mp ha_dom
  have ha_ord : a.toNat % 8 = 0 ∧ sourceBase ≤ a.toNat ∧ a.toNat < heapEnd := by
    rw [Wave8Contracts.M12.sourceBase_val, Wave8Contracts.M12.heapEnd_val]; omega
  have hhe_lt : heapEnd ≤ 2 ^ 64 := by rw [Wave8Contracts.M12.heapEnd_val]; decide
  have hhe_8 : heapEnd % 8 = 0 := by decide
  have ha_hi : a.toNat + 8 ≤ 2 ^ 64 := by omega
  rcases hp_m : post.memory a with ⟨wp⟩
  rcases hs_m : s.memory a with ⟨ws⟩
  congr 1
  apply BitVec.eq_of_toNat_eq
  have hbyte_val : ∀ k : Nat, k < 8 →
      (panGetByteHOL (BitVec.ofNat 64 (a.toNat + k)) wp s.be).toNat =
      (panGetByteHOL (BitVec.ofNat 64 (a.toNat + k)) ws s.be).toNat := by
    intro k hk
    have hal_eq : panByteAlignHOL (BitVec.ofNat 64 (a.toNat + k)) = a := by
      apply BitVec.eq_of_toNat_eq
      rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hbk := hb k hk
    unfold memB at hbk
    rw [hal_eq, hp_m, hs_m, hbe] at hbk
    exact hbk
  have hshift : ∀ (w : BitVec 64) (idx : Nat), idx < 8 →
      w.toNat / 256 ^ idx % 256 =
      (panGetByteHOL (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))) w s.be).toNat := by
    intro w idx hidx
    unfold panGetByteHOL
    change w.toNat / 256 ^ idx % 256 =
      (UInt8.ofNat (w.toNat / 256 ^ (if s.be then 8 - 1 - (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8
        else (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8) % 256)).toNat
    have hexp : (if s.be then 8 - 1 - (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8
        else (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8) = idx := by
      have hmod_lt : (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat =
          a.toNat + (if s.be then 7 - idx else idx) :=
        Nat.mod_eq_of_lt (by cases s.be <;> simp <;> omega)
      rw [hmod_lt]
      cases s.be <;> simp <;> omega
    rw [hexp, UInt8.toNat_ofNat']
    have h256 : (2 ^ 8 : Nat) = 256 := by decide
    rw [h256, Nat.mod_mod]
  have hpow_eq : ∀ idx : Nat, idx < 8 → wp.toNat / 256 ^ idx % 256 = ws.toNat / 256 ^ idx % 256 := by
    intro idx hidx
    rw [hshift wp idx hidx, hshift ws idx hidx]
    exact hbyte_val (if s.be then 7 - idx else idx) (by cases s.be <;> simp <;> omega)
  have hdecomp : ∀ n : Nat, n < 2 ^ 64 →
      n = (n / 256 ^ 0 % 256) +
          (n / 256 ^ 1 % 256) * 256 ^ 1 +
          (n / 256 ^ 2 % 256) * 256 ^ 2 +
          (n / 256 ^ 3 % 256) * 256 ^ 3 +
          (n / 256 ^ 4 % 256) * 256 ^ 4 +
          (n / 256 ^ 5 % 256) * 256 ^ 5 +
          (n / 256 ^ 6 % 256) * 256 ^ 6 +
          (n / 256 ^ 7 % 256) * 256 ^ 7 := by
    intro n hn; omega
  rw [hdecomp wp.toNat wp.isLt, hdecomp ws.toNat ws.isLt]
  rw [hpow_eq 0 (by omega), hpow_eq 1 (by omega), hpow_eq 2 (by omega), hpow_eq 3 (by omega),
      hpow_eq 4 (by omega), hpow_eq 5 (by omega), hpow_eq 6 (by omega), hpow_eq 7 (by omega)]

theorem disj_fresh_heap_of_worldOwned {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hWT : Wave8Contracts.M12.WorldTypedWith s S Nd)
    (hOG : Wave8Contracts.M12.OwnedGrows s post
      (Wave8Contracts.M12.worldOwned s S Nd) (Wave8Contracts.M12.worldOwned post S Nd))
    (hno_new_world : ∀ o ∈ Wave8Contracts.M12.worldOwned post S Nd,
      o = (0, 0) ∨ ∃ j ∈ Wave8Contracts.M12.worldOwned s S Nd, Inside o j.1 (j.1 + j.2))
    {f : Ivl} (hf : Inside f (globN s "heap_ptr") (globN post "heap_ptr")) :
    Wave8Contracts.M12.IvlsDisj [f] (Wave8Contracts.M12.worldOwned post S Nd) := by
  have hwo_alloc : ∀ j ∈ Wave8Contracts.M12.worldOwned s S Nd, j.2 = 0 ∨ Allocated s j := by
    obtain ⟨hT, _, hF, hTr⟩ := hWT
    intro j hj
    unfold Wave8Contracts.M12.worldOwned at hj
    rcases List.mem_append.1 hj with h12 | hnd
    · rcases List.mem_append.1 h12 with htab | hfix
      · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 htab
        exact Or.inr (((hT.2.1 t ht).2 j hfp).1)
      · rcases hF.1 j hfix with h0 | ⟨hal, _⟩
        · exact Or.inl h0
        · exact Or.inr hal
    · unfold nodeExtents at hnd
      obtain ⟨n, hn, hni⟩ := List.mem_flatMap.1 hnd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hni
      rcases hni with rfl | rfl
      · exact Or.inr (hTr.1.1 n hn).2.1
      · unfold nodePath
        split
        · rename_i hp
          rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hp.1 with h0 | ⟨_, hal, _⟩
          · exact absurd h0 hp.2
          · exact Or.inr hal
        · exact Or.inl rfl
  intro x hx o ho
  simp only [List.mem_singleton] at hx; subst hx
  rcases hno_new_world o ho with rfl | ⟨j, hj, hin_oj⟩
  · exact Or.inr (Or.inl rfl)
  · rcases hwo_alloc j hj with hj0 | hal_j
    · exact Or.inr (Or.inl (by unfold Inside at hin_oj; omega))
    · rcases hal_j with ⟨_, hj2⟩ | ⟨hj1, _⟩
      · exact Or.inr (Or.inr (Or.inr (by unfold Inside at hin_oj hf; omega)))
      · have hp_lim := hAp.2.2.1
        have hs_fr := hAs.2.2.2.1
        have hs_gap := hAs.2.2.2.2.1
        rw [Wave8Contracts.M12.heapLimit_val] at hp_lim
        rw [Wave8Contracts.M12.scratchStart_val] at hs_fr
        exact Or.inr (Or.inr (Or.inl (by unfold Inside at hin_oj hf; omega)))

theorem WorldFrameEff.to_worldStep {F : Type}
    {R extra : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hW : WorldOK s)
    (hgw_sub : ∀ g ∈ gw, g = "heap_ptr" ∨ g = "scratch_ptr")
    (hextra_fix : ∀ x ∈ extra s, x ∈ fixedObjects s ∧
      ∀ S Nd, Wave8Contracts.M12.WorldTypedWith s S Nd →
        ∀ i ∈ Wave8Contracts.M12.worldTypedIvls s S Nd, i.2 = 0 ∨ Disj x i)
    (heff : WorldFrameEff s post (R s ++ extra s) gw)
    (hQ : ∀ S Nd, Wave8Contracts.M12.WorldTypedWith s S Nd →
      Wave8Contracts.M12.IvlsDisj (R s) (Wave8Contracts.M12.worldTypedIvls s S Nd) →
      Wave8Contracts.M12.WorldTypedWith post S Nd →
      (∀ o ∈ Wave8Contracts.M12.worldOwned post S Nd,
        o = (0, 0) ∨ ∃ j ∈ Wave8Contracts.M12.worldOwned s S Nd, Inside o j.1 (j.1 + j.2)) →
      Q s r post S Nd) :
    Wave8Contracts.M12.WorldStep R gw Wave8Contracts.M12.stdKeep Q s r post := by
  have hnonHeap_lookup : ∀ name, ofString name ≠ ofString "heap_ptr" →
      ofString name ≠ ofString "scratch_ptr" →
      s.globals.lookup (ofString name) = post.globals.lookup (ofString name) := by
    intro name h1 h2
    apply heff.gw_kept
    intro hm
    obtain ⟨g, hg, heq⟩ := List.mem_map.1 hm
    rcases hgw_sub g hg with rfl | rfl
    · exact h1 heq.symm
    · exact h2 heq.symm
  have hcore_eq : ∀ g ∈ Wave8Contracts.M12.coreWorldGlobals, globN post g = globN s g := by
    intro g hg
    have hne : ofString g ≠ ofString "heap_ptr" ∧ ofString g ≠ ofString "scratch_ptr" := by
      revert g hg; decide
    exact (Wave8Contracts.M12.globN_eq_of_lookup_eq (hnonHeap_lookup g hne.1 hne.2)).symm
  obtain ⟨S0, hWT0_ex⟩ := hW.2
  obtain ⟨Nd0, hTr0⟩ := hWT0_ex.2.2.2
  have hWT0 : Wave8Contracts.M12.WorldTypedWith s S0 Nd0 := ⟨hWT0_ex.1, hWT0_ex.2.1, hWT0_ex.2.2.1, hTr0⟩
  -- 1. `RecordsKept`:
  have hRK : Wave8Contracts.M12.RecordsKept R Wave8Contracts.M12.stdKeep s post := by
    intro rec hrec hgnz k hk hnoR
    have hsz_ex : ∃ sz : Nat, (rec.1, sz) ∈ Wave8Contracts.M12.typedRecords ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
      simp only [Wave8Contracts.M12.stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · refine ⟨40, by decide, ?_⟩; simp at hk; omega
      · refine ⟨80, by decide, ?_⟩; simp at hk; omega
      · refine ⟨72, by decide, ?_⟩; simp at hk; omega
      · refine ⟨88, by decide, ?_⟩; simp at hk; omega
    obtain ⟨sz, htr, hk8, hkle⟩ := hsz_ex
    have hfix0 := Wave8Contracts.M12.typedRec_in_fixedObjects s htr
    have hsz : (if globN s rec.1 = 0 then 0 else sz) = sz := if_neg hgnz
    rcases hWT0.2.2.1.1 _ hfix0 with h0 | ⟨hal0, hw0⟩
    · dsimp only at h0; rw [hsz] at h0; omega
    · have hb := Wave8Contracts.M12.allocated_le_2pow64 hW.1.2 hal0
      dsimp only at hb; rw [hsz] at hb
      rw [hsz] at hal0
      have ha64 : globN s rec.1 + k < 2 ^ 64 := by omega
      unfold memW
      have hbit : (BitVec.ofNat 64 (globN s rec.1 + k)).toNat = globN s rec.1 + k :=
        Nat.mod_eq_of_lt ha64
      by_cases hdom : ordinaryDomain (BitVec.ofNat 64 (globN s rec.1 + k))
      · rw [mem_eq_of_bytes_eq_ord heff.be_eq _ hdom]
        intro idx hidx
        rw [hbit]
        have hdj_fg := Wave8Contracts.M12.allocated_disj_freeGap hW.1.2 hal0
        have hdj_hf := Wave8Contracts.M12.allocated_disj_heapFree hW.1.2 hal0
        apply heff.byte_frame (globN s rec.1 + k + idx) (by omega)
        · intro x hx hbx
          rcases List.mem_append.1 hx with hxRE | hxfg
          · rcases List.mem_append.1 hxRE with hxR | hxE
            · apply hnoR x hxR
              obtain ⟨_, _⟩ := hbx; exact ⟨by omega, by omega⟩
            · have hwti := Wave8Contracts.M12.mem_worldTypedIvls_typedRec (s := s) (S := S0) (Nd := Nd0) htr
              rw [hsz] at hwti
              rcases (hextra_fix x hxE).2 S0 Nd0 hWT0 _ hwti with h0 | hdj
              · dsimp only at h0; omega
              · obtain ⟨_, _⟩ := hbx
                rcases hdj with h0 | h0 | h | h <;> (dsimp only at *; omega)
          · simp only [List.mem_singleton] at hxfg; subst hxfg
            obtain ⟨_, _⟩ := hbx
            rcases hdj_fg with h0 | h0 | h | h <;> (dsimp only at *; omega)
        · intro hbhf
          obtain ⟨_, _⟩ := hbhf
          rcases hdj_hf with h0 | h0 | h | h <;> (dsimp only at *; omega)
      · rw [heff.out_dom]
        rwa [hW.1.1.memaddrs]
  refine ⟨heff.arena, heff.hp_grows, heff.gw_kept, hRK, fun S Nd hWT hdisj => ?_⟩
  have hcell : Wave8Contracts.M12.SameTypedCells s post S Nd := by
    refine ⟨heff.be_eq, heff.arena.1.memaddrs.trans hW.1.1.memaddrs.symm, hW.1.1.memaddrs, ?_, ?_, ?_⟩
    · intro a hna
      apply heff.out_dom a
      rwa [hW.1.1.memaddrs]
    · intro a ha ha8 ⟨i, hi, ha1, ha2⟩
      by_cases hdom : ordinaryDomain (BitVec.ofNat 64 a)
      · have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
        rcases Wave8Contracts.M12.worldTypedIvls_allocated hWT hi with hi0 | hal_i
        · omega
        · have hdj_fg := Wave8Contracts.M12.allocated_disj_freeGap hW.1.2 hal_i
          have hdj_hf := Wave8Contracts.M12.allocated_disj_heapFree hW.1.2 hal_i
          apply mem_eq_of_bytes_eq_ord heff.be_eq _ hdom
          intro k hk
          rw [hbit]
          apply heff.byte_frame (a + k) (by omega)
          · intro x hx hbx
            rcases List.mem_append.1 hx with hxRE | hxfg
            · rcases List.mem_append.1 hxRE with hxR | hxE
              · have hdj := hdisj x hxR i hi
                obtain ⟨_, _⟩ := hbx; rcases hdj with h0 | h0 | h | h <;> omega
              · rcases (hextra_fix x hxE).2 S Nd hWT i hi with hi0 | hdj
                · omega
                · obtain ⟨_, _⟩ := hbx; rcases hdj with h0 | h0 | h | h <;> omega
            · simp only [List.mem_singleton] at hxfg; subst hxfg
              obtain ⟨_, _⟩ := hbx; rcases hdj_fg with h0 | h0 | h | h <;> omega
          · intro hbhf
            obtain ⟨_, _⟩ := hbhf; rcases hdj_hf with h0 | h0 | h | h <;> omega
      · apply heff.out_dom
        rwa [hW.1.1.memaddrs]
    · intro b hb ⟨i, hi, hb1, hb2⟩
      rcases Wave8Contracts.M12.worldTypedIvls_allocated hWT hi with hi0 | hal_i
      · omega
      · have hdj_fg := Wave8Contracts.M12.allocated_disj_freeGap hW.1.2 hal_i
        have hdj_hf := Wave8Contracts.M12.allocated_disj_heapFree hW.1.2 hal_i
        apply heff.byte_frame b hb
        · intro x hx hbx
          rcases List.mem_append.1 hx with hxRE | hxfg
          · rcases List.mem_append.1 hxRE with hxR | hxE
            · have hdj := hdisj x hxR i hi
              obtain ⟨_, _⟩ := hbx; rcases hdj with h0 | h0 | h | h <;> omega
            · rcases (hextra_fix x hxE).2 S Nd hWT i hi with hi0 | hdj
              · omega
              · obtain ⟨_, _⟩ := hbx; rcases hdj with h0 | h0 | h | h <;> omega
          · simp only [List.mem_singleton] at hxfg; subst hxfg
            obtain ⟨_, _⟩ := hbx; rcases hdj_fg with h0 | h0 | h | h <;> omega
        · intro hbhf
          obtain ⟨_, _⟩ := hbhf; rcases hdj_hf with h0 | h0 | h | h <;> omega
  have hfeq : fixedObjects post = fixedObjects s := by
    have hg : ∀ name, ofString name ≠ ofString "heap_ptr" → ofString name ≠ ofString "scratch_ptr" →
        globN post name = globN s name :=
      fun n h1 h2 => (Wave8Contracts.M12.globN_eq_of_lookup_eq (hnonHeap_lookup n h1 h2)).symm
    unfold fixedObjects
    rw [Wave8Contracts.M12.blockOutObjects_eq hW.1.2 hWT.2.2.1 hcell (hg "bo" (by decide) (by decide)),
        Wave8Contracts.M12.balObjects_eq hW.1.2 hWT.1 hWT.2.2.1 hcell (hg "bal_accounts" (by decide) (by decide)),
        hg "journal" (by decide) (by decide),
        hg "journal_cap" (by decide) (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "heap_ptr" ∧ ofString gn.1 ≠ ofString "scratch_ptr" := by
      revert gn hgn; decide
    rw [hg gn.1 hne.1 hne.2]
  have hFT_post := Wave8Contracts.M12.fixedTyped_of_eq heff.arena hWT.2.2.1
    heff.hp_grows heff.sp_shrinks hfeq
  obtain ⟨hWT_post, hOG⟩ := Wave8Contracts.M12.worldTypedWith_congr_w1 hW.1 heff.arena
    heff.hp_grows heff.sp_shrinks hcore_eq hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hno_new_world : ∀ o ∈ Wave8Contracts.M12.worldOwned post S Nd,
      o = (0, 0) ∨ ∃ j ∈ Wave8Contracts.M12.worldOwned s S Nd, Inside o j.1 (j.1 + j.2) := by
    intro o ho
    unfold Wave8Contracts.M12.worldOwned at ho
    simp only [List.mem_append] at ho
    rcases ho with (ho_htab | ho_fix) | ho_nd
    · obtain ⟨t, ht, hi⟩ := List.mem_flatMap.1 ho_htab
      rw [Wave8Contracts.M12.htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1] at hi
      refine Or.inr ⟨o, ?_, le_rfl, le_rfl⟩
      unfold Wave8Contracts.M12.worldOwned
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨t, ht, hi⟩))
    · rw [hfeq] at ho_fix
      refine Or.inr ⟨o, ?_, le_rfl, le_rfl⟩
      unfold Wave8Contracts.M12.worldOwned
      exact List.mem_append_left _ (List.mem_append_right _ ho_fix)
    · rw [Wave8Contracts.M12.nodeExtents_eq hWT.2.2.2.1 hcell] at ho_nd
      refine Or.inr ⟨o, ?_, le_rfl, le_rfl⟩
      unfold Wave8Contracts.M12.worldOwned
      exact List.mem_append_right _ ho_nd
  refine ⟨S, Nd, fun _ ht => ht, hWT_post, hOG, ?_, hQ S Nd hWT hdisj hWT_post hno_new_world⟩
  intro a hkeep hfresh
  apply heff.cell_frame a (fun x hx => ?_) hfresh
  rcases List.mem_append.1 hx with hxRE | hxfg
  · rcases List.mem_append.1 hxRE with hxR | hxE
    · exact hkeep x (List.mem_append_left _ (List.mem_append_right _ hxR))
    · have hx_wo : x ∈ Wave8Contracts.M12.worldOwned s S Nd := by
        unfold Wave8Contracts.M12.worldOwned
        exact List.mem_append_left _ (List.mem_append_right _ (hextra_fix x hxE).1)
      exact hkeep x (List.mem_append_left _ (List.mem_append_left _ hx_wo))
  · exact hkeep x (List.mem_append_right _ hxfg)

end InitECandidate.Solver.Wave8GuestInv.R13Shards
