import InitECandidate.Solver.Wave8GuestInv.R14Shards.NfNodeNewLeaf
import InitECandidate.Solver.Wave8GuestInv.R14Shards.NfNodeNewExt
import InitECandidate.Solver.Wave8GuestInv.R10Shards.SoloHtabSetBase
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_C08WkShard03

/-! Shared `nibbles_concat` and single-nibble heap allocation helpers for
`nf__delete_ext_finish` and `nf__collapse_branch` (`R16Shards`). -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R14Shards

theorem node_new_leaf_no_nonTrap_exn {F : Type}
    (st : PanSemStateFiniteExact 64 F) (hcode : st.code = originalRuntimeCode)
    (eid : MlS) (ev : ValueHOL 64) (hne : eid ≠ ofString "TrapErr") :
    (evaluateHOLFiniteState st (sourceFnBody Guest.Software.guestFn_node_new_leaf)).1 ≠
      some (.exception eid ev) := by
  intro hexn
  have hbody : sourceFnBody Guest.Software.guestFn_node_new_leaf =
      .decCall (ofString "nd") .one (ofString "alloc") [.const 64]
        (.seq (.store (.op .add [.var .local (ofString "nd"), .const 0]) (.const 1))
          (.seq (.store (.op .add [.var .local (ofString "nd"), .const 8]) (.const 0))
            (.seq (.store (.op .add [.var .local (ofString "nd"), .const 16]) (.const 0))
              (.seq (.store (.op .add [.var .local (ofString "nd"), .const 24]) (.const 0))
                (.seq (.store (.op .add [.var .local (ofString "nd"), .const 32]) (.var .local (ofString "nib")))
                  (.seq (.store (.op .add [.var .local (ofString "nd"), .const 40]) (.var .local (ofString "nlen")))
                    (.seq (.store (.op .add [.var .local (ofString "nd"), .const 48]) (.var .local (ofString "vptr")))
                      (.seq (.store (.op .add [.var .local (ofString "nd"), .const 56]) (.var .local (ofString "vlen")))
                        (.return (.var .local (ofString "nd"))))))))))) := rfl
  rw [hbody] at hexn
  obtain ⟨avals, _, acallee, _, _, _, ahl, ahexn | ⟨_, _, _, _, _, ahr, _⟩⟩ :=
    decCall_resumes_inv (Or.inr ⟨eid, ev, hexn, hne⟩)
  · obtain ⟨aeid, aev, aha, ahne, _⟩ := ahexn
    have ahsame := lookupCodeHOLFinite_installed_body st.code.lookup (ofString "alloc")
      _ _ _ _ _ avals acallee (by rw [hcode]; exact lookup_alloc) ahl
    subst ahsame
    obtain ⟨_, ahret⟩ := alloc_body_resumes_eq_returned (callEntryStateHOLFinite st acallee) hcode
      (by rw [aha]; exact Or.inr ⟨aeid, aev, rfl, ahne⟩)
    rw [aha] at ahret; cases ahret
  · rw [hexn] at ahr
    exact evaluate_noExnProg _ (by decide) _ eid ev ahr.symm

theorem node_new_ext_no_nonTrap_exn {F : Type}
    (st : PanSemStateFiniteExact 64 F) (hcode : st.code = originalRuntimeCode)
    (eid : MlS) (ev : ValueHOL 64) (hne : eid ≠ ofString "TrapErr") :
    (evaluateHOLFiniteState st (sourceFnBody Guest.Software.guestFn_node_new_ext)).1 ≠
      some (.exception eid ev) := by
  intro hexn
  have hbody : sourceFnBody Guest.Software.guestFn_node_new_ext =
      .decCall (ofString "nd") .one (ofString "alloc") [.const 56]
        (.seq (.store (.op .add [.var .local (ofString "nd"), .const 0]) (.const 2))
          (.seq (.store (.op .add [.var .local (ofString "nd"), .const 8]) (.const 0))
            (.seq (.store (.op .add [.var .local (ofString "nd"), .const 16]) (.const 0))
              (.seq (.store (.op .add [.var .local (ofString "nd"), .const 24]) (.const 0))
                (.seq (.store (.op .add [.var .local (ofString "nd"), .const 32]) (.var .local (ofString "nib")))
                  (.seq (.store (.op .add [.var .local (ofString "nd"), .const 40]) (.var .local (ofString "nlen")))
                    (.seq (.store (.op .add [.var .local (ofString "nd"), .const 48]) (.var .local (ofString "child")))
                      (.return (.var .local (ofString "nd")))))))))) := rfl
  rw [hbody] at hexn
  obtain ⟨avals, _, acallee, _, _, _, ahl, ahexn | ⟨_, _, _, _, _, ahr, _⟩⟩ :=
    decCall_resumes_inv (Or.inr ⟨eid, ev, hexn, hne⟩)
  · obtain ⟨aeid, aev, aha, ahne, _⟩ := ahexn
    have ahsame := lookupCodeHOLFinite_installed_body st.code.lookup (ofString "alloc")
      _ _ _ _ _ avals acallee (by rw [hcode]; exact lookup_alloc) ahl
    subst ahsame
    obtain ⟨_, ahret⟩ := alloc_body_resumes_eq_returned (callEntryStateHOLFinite st acallee) hcode
      (by rw [aha]; exact Or.inr ⟨aeid, aev, rfl, ahne⟩)
    rw [aha] at ahret; cases ahret
  · rw [hexn] at ahr
    exact evaluate_noExnProg _ (by decide) _ eid ev ahr.symm

theorem nibbles_concat_no_nonTrap_exn {F : Type}
    (st : PanSemStateFiniteExact 64 F) (hcode : st.code = originalRuntimeCode)
    (eid : MlS) (ev : ValueHOL 64) (hne : eid ≠ ofString "TrapErr") :
    (evaluateHOLFiniteState st (sourceFnBody Guest.Software.guestFn_nibbles_concat)).1 ≠
      some (.exception eid ev) := by
  intro hexn
  have hbody : sourceFnBody Guest.Software.guestFn_nibbles_concat =
      .decCall (ofString "out") .one (ofString "alloc")
        [.op .add [.var .local (ofString "al"), .var .local (ofString "bl")]]
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.var .local (ofString "out"), .var .local (ofString "a"), .var .local (ofString "al")])
          (.seq
            (.call (some (none, none)) (ofString "memcpy")
              [.op .add [.var .local (ofString "out"), .var .local (ofString "al")],
               .var .local (ofString "b"), .var .local (ofString "bl")])
            (.return (.var .local (ofString "out"))))) := rfl
  rw [hbody] at hexn
  obtain ⟨avals, abody, acallee, _, _, _, ahl, ahexn | ⟨arv, apost, harun, _, hcont_res, ahr, _⟩⟩ :=
    decCall_resumes_inv (Or.inr ⟨eid, ev, hexn, hne⟩)
  · obtain ⟨aeid, aev, aha, ahne, _⟩ := ahexn
    have ahsame := lookupCodeHOLFinite_installed_body st.code.lookup (ofString "alloc")
      _ _ _ _ _ avals acallee (by rw [hcode]; exact lookup_alloc) ahl
    subst ahsame
    obtain ⟨_, ahret⟩ := alloc_body_resumes_eq_returned (callEntryStateHOLFinite st acallee) hcode
      (by rw [aha]; exact Or.inr ⟨aeid, aev, rfl, ahne⟩)
    rw [aha] at ahret; cases ahret
  · set s0 := setVarHOLFinite (ofString "out") arv { apost with locals := st.locals }
    have hapost_code : apost.code = originalRuntimeCode := by
      have hm := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite st acallee) abody).1
      rw [harun] at hm; exact hm.trans hcode
    have hs0_code : s0.code = originalRuntimeCode := hapost_code
    obtain ⟨m1vals, m1body, m1c, _, _, _, hm1l, hm1exn | ⟨_, m1post, hm1run, _, hcont2_res, hm1_eq⟩⟩ :=
      call_void_flow_or_resumes hcont_res
    · obtain ⟨meid, mev, hme, _, _⟩ := hm1exn
      have hsame := lookupCodeHOLFinite_installed_body s0.code.lookup (ofString "memcpy")
        _ _ _ _ _ m1vals m1c (by rw [hs0_code]; exact lookup_memcpy) hm1l
      subst hsame
      exact memcpy_body_no_exception _ meid mev (congrArg Prod.fst hme)
    · set s1 : PanSemStateFiniteExact 64 F := { m1post with locals := s0.locals }
      have hs1_code : s1.code = originalRuntimeCode := by
        have hm := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s0 m1c) m1body).1
        rw [hm1run] at hm; exact hm.trans hs0_code
      obtain ⟨m2vals, m2body, m2c, _, _, _, hm2l, hm2exn | ⟨_, m2post, _, _, _, hm2_eq⟩⟩ :=
        call_void_flow_or_resumes hcont2_res
      · obtain ⟨meid, mev, hme, _, _⟩ := hm2exn
        have hsame := lookupCodeHOLFinite_installed_body s1.code.lookup (ofString "memcpy")
          _ _ _ _ _ m2vals m2c (by rw [hs1_code]; exact lookup_memcpy) hm2l
        subst hsame
        exact memcpy_body_no_exception _ meid mev (congrArg Prod.fst hme)
      · rw [hexn, hm1_eq, hm2_eq] at ahr
        exact evaluate_noExnProg _ (by decide) _ eid ev ahr.symm

/-- Lookup helper for a 4-word parameter function (`nibbles_concat`). -/
theorem pan_four_word_lookup
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (fname p1 p2 p3 p4 : MlS) (body : ProgHOL 64) (w1 w2 w3 w4 : BitVec 64)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (hlook : code fname = some ([(p1, .one), (p2, .one), (p3, .one), (p4, .one)], body, .one)) :
    lookupCodeHOLFinite code fname [.val (.word w1), .val (.word w2), .val (.word w3), .val (.word w4)] =
      some (body,
        (((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update
          (p2, .val (.word w2))).update (p3, .val (.word w3))).update (p4, .val (.word w4)),
        .one) := by
  have raw : lookupCodeHOLExact code fname
      [.val (.word w1), .val (.word w2), .val (.word w3), .val (.word w4)] =
      some (body,
        (fun k => if k = p4 then some (.val (.word w4))
          else if k = p3 then some (.val (.word w3))
          else if k = p2 then some (.val (.word w2))
          else if k = p1 then some (.val (.word w1))
          else none), .one) := by
    simp [lookupCodeHOLExact, hlook, shapeOfHOLExact, shapeEqHOL, h12, h13, h14, h23, h24, h34]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i hm; rw [raw] at hm; cases hm
  · rename_i fb fl fsh hf
    have heq := Option.some.inj (hf.symm.trans raw)
    rcases Prod.mk.inj heq with ⟨hb_eq, hrest⟩
    rcases Prod.mk.inj hrest with ⟨hfl, hs_eq⟩
    simp only [Option.some.injEq, Prod.mk.injEq]
    refine ⟨hb_eq, ?_, hs_eq⟩
    apply HolFiniteMapExact.ext
    funext k
    change fl k = _
    rw [hfl]
    by_cases hk4 : k = p4
    · subst hk4; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    · by_cases hk3 : k = p3
      · subst hk3; simp [HolFiniteMapExact.lookup_update, FUPDATE, hk4, Ne.symm hk4]
      · by_cases hk2 : k = p2
        · subst hk2; simp [HolFiniteMapExact.lookup_update, FUPDATE, hk4, hk3, Ne.symm hk4, Ne.symm hk3]
        · by_cases hk1 : k = p1
          · subst hk1; simp [HolFiniteMapExact.lookup_update, FUPDATE, hk4, hk3, hk2, Ne.symm hk4, Ne.symm hk3, Ne.symm hk2]
          · simp [HolFiniteMapExact.lookup_update, HolFiniteMapExact.empty, FUPDATE,
              hk4, hk3, hk2, hk1, Ne.symm hk4, Ne.symm hk3, Ne.symm hk2, Ne.symm hk1]

/-- Pure heap-allocation + fresh-write lifting: if `post` preserves `s` on every cell outside
`[globN s "heap_ptr", heapLimit)`, updates `heap_ptr` to `q` (`globN s "heap_ptr" ≤ q ≤ heapLimit`,
`q % 8 = 0`), and leaves other globals and `be` unchanged, then `NodeStep s post Nd Nd` holds! -/
theorem nodeStep_fresh_heap_only {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Nd : List Nat} {q : BitVec 64}
    (hAR : ArenaReady s) (hNd : NodeHeap s Nd)
    (hG_post : GuestInv post)
    (hpost_glob : post.globals = s.globals.update (ofString "heap_ptr", .val (.word q)))
    (hpost_be : post.be = s.be)
    (hq_lo : globN s "heap_ptr" ≤ q.toNat)
    (hq_hi : q.toNat ≤ heapLimit)
    (hq_al : q.toNat % 8 = 0)
    (hmem_outside : ∀ c : BitVec 64,
      (c.toNat < globN s "heap_ptr" ∨ q.toNat ≤ c.toNat) → post.memory c = s.memory c) :
    NodeStep s post Nd Nd := by
  have hA : ArenaOK s := hAR.2
  have hpost_hp : globN post "heap_ptr" = q.toNat := by
    unfold globN; rw [hpost_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hpost_sp : globN post "scratch_ptr" = globN s "scratch_ptr" := by
    unfold globN; rw [hpost_glob]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
  have hAR_post : ArenaReady post :=
    ⟨hG_post, arenaOK_update_heap hpost_glob (by have := hA.1; omega) hq_hi hq_al hA⟩
  have hgrow : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hpost_hp]; exact hq_lo
  have hsp_le : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hpost_sp]
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hhe_ge : heapLimit ≤ heapEnd := by decide
  have hmem_lt : ∀ c : BitVec 64, c.toNat < globN s "heap_ptr" → post.memory c = s.memory c :=
    fun c hlt => hmem_outside c (Or.inl hlt)
  have halloc_heap : ∀ {n : Nat}, n ∈ Nd → Inside (nodeIvl s n) sourceBase (globN s "heap_ptr") := by
    intro n hn
    have hp_n := hNd.1 n hn
    rcases hp_n.2.1 with h1 | h2
    · exact h1
    · have := hp_n.2.2.1.2
      have hsep : heapLimit ≤ scratchStart := by decide
      have := hA.2.2.1; have := hA.2.2.2.1
      obtain ⟨hsz, _, _⟩ := nodeSize_bounds (memW s n)
      dsimp [nodeIvl, Inside] at *; omega
  have hold_word_eq : ∀ n ∈ Nd, ∀ off, off + 8 ≤ nodeSize (memW s n) →
      memW post (n + off) = memW s (n + off) := by
    intro n hn off hoff
    have hins := halloc_heap hn
    dsimp [nodeIvl, Inside] at hins
    have hlt : n + off < globN s "heap_ptr" := by omega
    have hlt64 : n + off < 2 ^ 64 := by have := hA.2.1; omega
    unfold memW
    rw [hmem_lt (BitVec.ofNat 64 (n + off)) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]; exact hlt)]
  have hkinds : ∀ n ∈ Nd, memW post n = memW s n := by
    intro n hn
    obtain ⟨hsz, _, _⟩ := nodeSize_bounds (memW s n)
    simpa using hold_word_eq n hn 0 (by omega)
  have hivl_eq : ∀ n ∈ Nd, nodeIvl post n = nodeIvl s n := by
    intro n hn; simp [nodeIvl, hkinds n hn]
  have hNd_post : NodeHeap post Nd := by
    refine ⟨?_, ?_⟩
    · intro x hx_old
      have hp_x := hNd.1 x hx_old
      have hx_in := halloc_heap hx_old
      rw [hkinds x hx_old, hivl_eq x hx_old]
      refine ⟨hp_x.1, Or.inl ⟨hx_in.1, Nat.le_trans hx_in.2 hgrow⟩, hp_x.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · obtain ⟨ha1, ha2, _⟩ := hp_x.2.2.2.1
        exact Wave8Contracts.M26.wordsOK_of_guestInv post hAR_post.1 x (nodeSize (memW s x))
          ha1 ha2 hp_x.2.2.1.1 (Nat.le_trans hp_x.2.2.1.2 hhe_ge)
      · intro hk2
        have : nodeSize (memW s x) = 56 := by simp [nodeSize, hk2]
        rw [hold_word_eq x hx_old 48 (by omega)]; exact hp_x.2.2.2.2.1 hk2
      · intro hk3 i hi
        have : nodeSize (memW s x) = 176 := by simp [nodeSize, hk3]
        have heq : x + 32 + 8 * i = x + (32 + 8 * i) := by omega
        rw [heq, hold_word_eq x hx_old (32 + 8 * i) (by omega), ← heq]
        exact hp_x.2.2.2.2.2.1 hk3 i hi
      · intro hk12
        have : 56 ≤ nodeSize (memW s x) := by
          rcases hk12 with hk1 | hk2 <;> simp [nodeSize, *]
        rw [hold_word_eq x hx_old 32 (by omega), hold_word_eq x hx_old 40 (by omega)]
        exact keyIn_unchanged_below_hp hAR hgrow hpost_be hmem_lt hkinds (hp_x.2.2.2.2.2.2.1 hk12)
      · obtain ⟨hsz32, _, _⟩ := nodeSize_bounds (memW s x)
        rw [hold_word_eq x hx_old 16 (by omega)]; exact hp_x.2.2.2.2.2.2.2.1
      · intro hk1
        have : nodeSize (memW s x) = 64 := by simp [nodeSize, hk1]
        rw [hold_word_eq x hx_old 56 (by omega)]; exact hp_x.2.2.2.2.2.2.2.2.1 hk1
      · intro hk3
        have : nodeSize (memW s x) = 176 := by simp [nodeSize, hk3]
        rw [hold_word_eq x hx_old 168 (by omega)]; exact hp_x.2.2.2.2.2.2.2.2.2 hk3
    · intro x hx y hy hxy
      rw [hivl_eq x hx, hivl_eq y hy]
      exact hNd.2 x hx y hy hxy
  refine ⟨hAR_post, hgrow, hsp_le, hpost_be, hNd_post,
    fun _ h => h, hkinds, fun _ h => Or.inl h, ?_, ?_⟩
  · apply frameOutside_of_mem_lt_hp hAR
    intro a ha_out
    apply hmem_outside a
    rcases ha_out with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (by omega)
  · intro k hk
    rw [hpost_glob]
    have hne : ofString "heap_ptr" ≠ k := by rintro rfl; exact hk (by simp)
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hne]

/-- Full relational `NodeStep` + `KeyIn` postcondition of `nibbles_concat(wa, wal, wb, wbl)`
on normal return when `(wa, wal)` and `(wb, wbl)` are `KeyIn s Nd`. -/
theorem nibbles_concat_body_spec {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat)
    (wa wal wb wbl : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hAR : ArenaReady s) (hNd : NodeHeap s Nd)
    (hKeyA : KeyIn s Nd wa.toNat wal.toNat)
    (hKeyB : KeyIn s Nd wb.toNat wbl.toNat)
    (hlk_a : s.locals.lookup (ofString "a") = some (.val (.word wa)))
    (hlk_al : s.locals.lookup (ofString "al") = some (.val (.word wal)))
    (hlk_b : s.locals.lookup (ofString "b") = some (.val (.word wb)))
    (hlk_bl : s.locals.lookup (ofString "bl") = some (.val (.word wbl)))
    (rv : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_nibbles_concat)).1 =
      some (.returned rv)) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_nibbles_concat)).2
    ∃ wcat : BitVec 64,
      rv = .val (.word wcat) ∧
      (wal + wbl).toNat = wal.toNat + wbl.toNat ∧
      NodeStep s post Nd Nd ∧
      KeyIn post Nd wcat.toNat (wal.toNat + wbl.toNat) ∧
      (∀ c : BitVec 64, c.toNat < globN s "heap_ptr" → post.memory c = s.memory c) := by
  intro post
  have hG : GuestInv s := hAR.1
  have hA : ArenaOK s := hAR.2
  obtain ⟨hp, fp, sp, hhp, hhp_eq, hfp, hfp_eq, hsp, hsp_eq⟩ :=
    Wave8Contracts.M26.arenaOK_globals s hA
  have hhl_val : heapLimit = 2952790016 := rfl
  have h263_val : (2 ^ 63 : Nat) = 9223372036854775808 := by decide
  have h264_val : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
  have hal_bound : wal.toNat ≤ heapLimit := by
    by_cases hz : wal.toNat = 0
    · omega
    · obtain ⟨_, _, hphi⟩ := keyIn_heap hAR hKeyA hz; omega
  have hbl_bound : wbl.toNat ≤ heapLimit := by
    by_cases hz : wbl.toNat = 0
    · omega
    · obtain ⟨_, _, hphi⟩ := keyIn_heap hAR hKeyB hz; omega
  have hsum_lt64 : wal.toNat + wbl.toNat < 2 ^ 64 := by omega
  have hsum_eq : (wal + wbl).toNat = wal.toNat + wbl.toNat :=
    BitVec.toNat_add_of_lt hsum_lt64
  have hbody : sourceFnBody Guest.Software.guestFn_nibbles_concat =
      .decCall (ofString "out") .one (ofString "alloc")
        [.op .add [.var .local (ofString "al"), .var .local (ofString "bl")]]
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.var .local (ofString "out"), .var .local (ofString "a"), .var .local (ofString "al")])
          (.seq
            (.call (some (none, none)) (ofString "memcpy")
              [.op .add [.var .local (ofString "out"), .var .local (ofString "al")],
               .var .local (ofString "b"), .var .local (ofString "bl")])
            (.return (.var .local (ofString "out"))))) := rfl
  have hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_nibbles_concat)).1 :=
    Or.inl ⟨rv, hret⟩
  rw [hbody] at hres
  obtain ⟨avals, abody, acallee, aret, _, haargs, ahl, ahexn | ⟨arv, apost, harun, _, hcont_res, ahr_eq, ahp_eq⟩⟩ :=
    decCall_resumes_inv hres
  · obtain ⟨aeid, aev, aha, ahne, _⟩ := ahexn
    have ahsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "alloc")
      _ _ _ _ _ avals acallee (by rw [hcode]; exact lookup_alloc) ahl
    subst ahsame
    obtain ⟨_, ahret⟩ := alloc_body_resumes_eq_returned (callEntryStateHOLFinite s acallee) hcode
      (by rw [aha]; exact Or.inr ⟨aeid, aev, rfl, ahne⟩)
    rw [aha] at ahret; cases ahret
  · have havals : avals = [.val (.word (wal + wbl))] := by
      rw [evalListHOLFinite_eq_toExact] at haargs
      simpa [evalListHOLExact, evalHOLExact, hlk_al, hlk_bl, valueIsWord, valueWord, wordOpHOL, wordOp] using haargs.symm
    subst havals
    have ahl_ex := pan_one_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_alloc) (wal + wbl) (by rw [hcode]; exact lookup_alloc)
    rw [ahl_ex] at ahl
    obtain ⟨rfl, hrest_a⟩ := Prod.mk.inj (Option.some.inj ahl.symm)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrest_a
    have hn_ent : (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word (wal + wbl))))).locals.lookup
        (ofString "n") = some (.val (.word (wal + wbl))) := by
      simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have harun_info := Wave8Contracts.M26.alloc_body_run
      (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word (wal + wbl)))))
      hp (wal + wbl) hcode hhp hn_ent arv (by rw [harun])
    rw [harun] at harun_info
    obtain ⟨rfl, hcmp1, hcmp2, hapost_eq⟩ := harun_info
    dsimp only at hapost_eq
    set q : BitVec 64 := (hp + ((wal + wbl) + 7)) &&& ((0 : BitVec 64) - 8)
    have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hA.2.1
    have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hA.2.2.2.2.2.1
    obtain ⟨hq_eq, hq_hi, hq_al, hp_le_q⟩ := Wave8Contracts.M26.alloc_arith hp (wal + wbl) hhp_hi hhp_al hcmp1 hcmp2
    change q.toNat = hp.toNat + ((wal + wbl).toNat + 7) / 8 * 8 at hq_eq
    change q.toNat ≤ heapLimit at hq_hi
    rw [hsum_eq] at hq_eq
    have hfit_q : hp.toNat + wal.toNat + wbl.toNat ≤ q.toNat := by omega
    set s0 := setVarHOLFinite (ofString "out") (.val (.word hp)) { apost with locals := s.locals }
    have hs0_code : s0.code = originalRuntimeCode := by
      simp [s0, setVarHOLFinite]; rw [hapost_eq]; exact hcode
    have hs0_G : GuestInv s0 := by
      refine ⟨hs0_code, ?_, ?_, ?_⟩ <;> (simp [s0, setVarHOLFinite]; rw [hapost_eq])
      · exact hG.memaddrs
      · exact hG.shMemaddrs
      · exact hG.baseAddr
    have hs0_mem : s0.memory = s.memory := by
      simp [s0, setVarHOLFinite]; rw [hapost_eq]; rfl
    have hs0_be : s0.be = s.be := by
      simp [s0, setVarHOLFinite]; rw [hapost_eq]; rfl
    have hs0_glob : s0.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) := by
      simp [s0, setVarHOLFinite]; rw [hapost_eq]; rfl
    have hs0_out : s0.locals.lookup (ofString "out") = some (.val (.word hp)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs0_a : s0.locals.lookup (ofString "a") = some (.val (.word wa)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_a,
        show ofString "out" ≠ ofString "a" by decide]
    have hs0_al : s0.locals.lookup (ofString "al") = some (.val (.word wal)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_al,
        show ofString "out" ≠ ofString "al" by decide]
    have hs0_b : s0.locals.lookup (ofString "b") = some (.val (.word wb)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_b,
        show ofString "out" ≠ ofString "b" by decide]
    have hs0_bl : s0.locals.lookup (ofString "bl") = some (.val (.word wbl)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_bl,
        show ofString "out" ≠ ofString "bl" by decide]
    -- First `memcpy(out, a, al)`
    obtain ⟨m1vals, m1body, m1c, m1ret, _, hm1args, hm1l, hm1exn | ⟨m1rv, m1post, hm1run, _, hcont2_res, hm1_eq⟩⟩ :=
      call_void_flow_or_resumes hcont_res
    · obtain ⟨meid, mev, hme, _, _⟩ := hm1exn
      have hsame := lookupCodeHOLFinite_installed_body s0.code.lookup (ofString "memcpy")
        _ _ _ _ _ m1vals m1c (by rw [hs0_code]; exact lookup_memcpy) hm1l
      subst hsame
      exact absurd (congrArg Prod.fst hme) (memcpy_body_no_exception _ meid mev)
    · have hm1vals : m1vals = [.val (.word hp), .val (.word wa), .val (.word wal)] := by
        rw [evalListHOLFinite_eq_toExact] at hm1args
        simpa [evalListHOLExact, evalHOLExact, hs0_out, hs0_a, hs0_al] using hm1args.symm
      subst hm1vals
      have hm1l_ex := pan_three_word_lookup s0.code.lookup (ofString "memcpy")
        (ofString "dst") (ofString "src") (ofString "n")
        (sourceFnBody Guest.Software.guestFn_memcpy) hp wa wal
        (by decide) (by decide) (by decide) (by rw [hs0_code]; exact lookup_memcpy)
      rw [hm1l_ex] at hm1l
      obtain ⟨rfl, hrest_m1⟩ := Prod.mk.inj (Option.some.inj hm1l.symm)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrest_m1
      let m1entry := callEntryStateHOLFinite s0
        (((HolFiniteMapExact.empty.update (ofString "dst", .val (.word hp))).update
          (ofString "src", .val (.word wa))).update (ofString "n", .val (.word wal)))
      have hm1_dst : m1entry.locals.lookup (ofString "dst") = some (.val (.word hp)) := by
        simp [m1entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "dst" by decide, show ofString "src" ≠ ofString "dst" by decide]
      have hm1_src : m1entry.locals.lookup (ofString "src") = some (.val (.word wa)) := by
        simp [m1entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "src" by decide]
      have hm1_n : m1entry.locals.lookup (ofString "n") = some (.val (.word wal)) := by
        simp [m1entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hwa_nw : wa.toNat + wal.toNat < 2 ^ 64 := by
        by_cases hz : wal.toNat = 0
        · rw [hz]; exact wa.isLt
        · obtain ⟨_, _, hphi⟩ := keyIn_heap hAR hKeyA hz; omega
      have hdisj1 : Disj (hp.toNat, wal.toNat) (wa.toNat, wal.toNat) := by
        by_cases hz : wal.toNat = 0
        · exact Or.inl hz
        · obtain ⟨_, hheap, _⟩ := keyIn_heap hAR hKeyA hz
          rw [← hhp_eq] at hheap
          exact Or.inr (Or.inr (Or.inr hheap))
      have hrel1_raw := SoloHtabSet.memcpy_body_spec m1entry hp wa wal
        (by omega) hwa_nw (by omega) hdisj1
        hm1_dst hm1_src hm1_n m1rv (by rw [hm1run])
      have heff1_raw := Fast_C08WkShard03.memcpy_body_eff m1entry hp wal hs0_code
        (guestInv_callEntry s0 _ hs0_G) hm1_dst hm1_n (by rw [hm1run]; exact Or.inl ⟨m1rv, rfl⟩)
      rw [hm1run] at hrel1_raw heff1_raw
      obtain ⟨_, hrel1⟩ := hrel1_raw
      obtain ⟨heff1, _⟩ := heff1_raw
      dsimp only at hrel1 heff1
      -- Second `memcpy(out + al, b, bl)`
      set s1 : PanSemStateFiniteExact 64 F := { m1post with locals := s0.locals }
      have hs1_code : s1.code = originalRuntimeCode := by
        change m1post.code = originalRuntimeCode
        rw [hrel1.1]; exact hs0_code
      have hs1_G : GuestInv s1 :=
        ⟨hs1_code,
         by change m1post.memaddrs = _; rw [hrel1.2.1]; exact hs0_G.memaddrs,
         by change m1post.shMemaddrs = _; rw [hrel1.2.2.1]; exact hs0_G.shMemaddrs,
         by change m1post.baseAddr = _; rw [hrel1.2.2.2.1]; exact hs0_G.baseAddr⟩
      have hs1_glob : s1.globals = s0.globals := hrel1.2.2.2.2.2.1
      obtain ⟨m2vals, m2body, m2c, m2ret, _, hm2args, hm2l, hm2exn | ⟨m2rv, m2post, hm2run, _, _, hm2_eq⟩⟩ :=
        call_void_flow_or_resumes hcont2_res
      · obtain ⟨meid, mev, hme, _, _⟩ := hm2exn
        have hsame := lookupCodeHOLFinite_installed_body s1.code.lookup (ofString "memcpy")
          _ _ _ _ _ m2vals m2c (by rw [hs1_code]; exact lookup_memcpy) hm2l
        subst hsame
        exact absurd (congrArg Prod.fst hme) (memcpy_body_no_exception _ meid mev)
      · have hm2vals : m2vals = [.val (.word (hp + wal)), .val (.word wb), .val (.word wbl)] := by
          rw [evalListHOLFinite_eq_toExact] at hm2args
          simpa [s1, evalListHOLExact, evalHOLExact, hs0_out, hs0_al, hs0_b, hs0_bl,
            valueIsWord, valueWord, wordOpHOL, wordOp] using hm2args.symm
        subst hm2vals
        have hm2l_ex := pan_three_word_lookup s1.code.lookup (ofString "memcpy")
          (ofString "dst") (ofString "src") (ofString "n")
          (sourceFnBody Guest.Software.guestFn_memcpy) (hp + wal) wb wbl
          (by decide) (by decide) (by decide) (by rw [hs1_code]; exact lookup_memcpy)
        rw [hm2l_ex] at hm2l
        obtain ⟨rfl, hrest_m2⟩ := Prod.mk.inj (Option.some.inj hm2l.symm)
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrest_m2
        let m2entry := callEntryStateHOLFinite s1
          (((HolFiniteMapExact.empty.update (ofString "dst", .val (.word (hp + wal)))).update
            (ofString "src", .val (.word wb))).update (ofString "n", .val (.word wbl)))
        have hm2_dst : m2entry.locals.lookup (ofString "dst") = some (.val (.word (hp + wal))) := by
          simp [m2entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "n" ≠ ofString "dst" by decide, show ofString "src" ≠ ofString "dst" by decide]
        have hm2_src : m2entry.locals.lookup (ofString "src") = some (.val (.word wb)) := by
          simp [m2entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "n" ≠ ofString "src" by decide]
        have hm2_n : m2entry.locals.lookup (ofString "n") = some (.val (.word wbl)) := by
          simp [m2entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hp_al_nat : (hp + wal).toNat = hp.toNat + wal.toNat :=
          BitVec.toNat_add_of_lt (by omega)
        have hwb_nw : wb.toNat + wbl.toNat < 2 ^ 64 := by
          by_cases hz : wbl.toNat = 0
          · rw [hz]; exact wb.isLt
          · obtain ⟨_, _, hphi⟩ := keyIn_heap hAR hKeyB hz; omega
        have hdisj2 : Disj ((hp + wal).toNat, wbl.toNat) (wb.toNat, wbl.toNat) := by
          by_cases hz : wbl.toNat = 0
          · exact Or.inl hz
          · obtain ⟨_, hheap, _⟩ := keyIn_heap hAR hKeyB hz
            rw [← hhp_eq] at hheap
            rw [hp_al_nat]
            exact Or.inr (Or.inr (Or.inr (by omega)))
        have hrel2_raw := SoloHtabSet.memcpy_body_spec m2entry (hp + wal) wb wbl
          (by rw [hp_al_nat]; omega) hwb_nw (by omega) hdisj2
          hm2_dst hm2_src hm2_n m2rv (by rw [hm2run])
        have heff2_raw := Fast_C08WkShard03.memcpy_body_eff m2entry (hp + wal) wbl hs1_code
          (guestInv_callEntry s1 _ hs1_G) hm2_dst hm2_n (by rw [hm2run]; exact Or.inl ⟨m2rv, rfl⟩)
        rw [hm2run] at hrel2_raw heff2_raw
        obtain ⟨_, hrel2⟩ := hrel2_raw
        obtain ⟨heff2, _⟩ := heff2_raw
        dsimp only at hrel2 heff2
        -- Final `return out`
        set s2 : PanSemStateFiniteExact 64 F := { m2post with locals := s1.locals }
        have hs2_ret : evaluateHOLFiniteState s2 (.return (.var .local (ofString "out"))) =
            (some (.returned (.val (.word hp))), emptyLocalsHOLFinite s2) := by
          simp [s2, s1, evaluateHOLFiniteState_return, evalHOLExact, hs0_out,
            shapeOfHOLExact, sizeOfShapeWithContextHOL]
        have hr_final : rv = .val (.word hp) := by
          have hr1 := hret
          rw [hbody, ahr_eq, hm1_eq, hm2_eq, hs2_ret] at hr1
          injection hr1 with h1
          injection h1 with h2
          exact h2.symm
        have hpost_mem : post.memory = m2post.memory := by
          change (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_nibbles_concat)).2.memory = _
          rw [hbody, ahp_eq, hm1_eq, hm2_eq, hs2_ret]; rfl
        have hpost_glob : post.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) := by
          change (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_nibbles_concat)).2.globals = _
          rw [hbody, ahp_eq, hm1_eq, hm2_eq, hs2_ret]
          change m2post.globals = _
          rw [hrel2.2.2.2.2.2.1]
          change s1.globals = _
          rw [hs1_glob, hs0_glob]
        have hpost_be : post.be = s.be :=
          (evaluateHOLFiniteState_metadata s (sourceFnBody Guest.Software.guestFn_nibbles_concat)).2.2.1
        have hG_post : GuestInv post := guestInv_evaluate s _ hG
        -- Memory outside `[hp, q)` is unchanged!
        have hmem_outside : ∀ c : BitVec 64,
            (c.toNat < globN s "heap_ptr" ∨ q.toNat ≤ c.toNat) → post.memory c = s.memory c := by
          intro c hout
          rw [← hhp_eq] at hout
          have hc2 : m2post.memory c = m1post.memory c := by
            by_contra hne
            have hdom_c : s1.memaddrs c := heff2.out_dom c hne
            rw [hs1_G.memaddrs, Wave8Contracts.M26.ordinaryDomain_iff] at hdom_c
            have hc8 : c.toNat % 8 = 0 := hdom_c.2.2
            obtain ⟨iv, hiv, hpos, hhit⟩ := heff2.cell_frame c hne
            rw [List.mem_singleton.mp hiv] at hpos hhit
            unfold CellHits at hhit
            rw [hp_al_nat] at hhit
            dsimp only at hpos hhit
            rcases hout with h1 | h2 <;> omega
          have hc1 : m1post.memory c = s.memory c := by
            have hm1e_mem : m1entry.memory = s.memory := hs0_mem
            rw [← hm1e_mem]
            by_contra hne
            have hdom_c : s0.memaddrs c := heff1.out_dom c hne
            rw [hs0_G.memaddrs, Wave8Contracts.M26.ordinaryDomain_iff] at hdom_c
            have hc8 : c.toNat % 8 = 0 := hdom_c.2.2
            obtain ⟨iv, hiv, hpos, hhit⟩ := heff1.cell_frame c hne
            rw [List.mem_singleton.mp hiv] at hpos hhit
            dsimp [CellHits] at hpos hhit
            rcases hout with h1 | h2 <;> omega
          rw [hpost_mem, hc2, hc1]
        have hstep_post : NodeStep s post Nd Nd :=
          nodeStep_fresh_heap_only hAR hNd hG_post hpost_glob hpost_be
            (by rw [← hhp_eq]; exact hp_le_q) hq_hi hq_al hmem_outside
        have hpost_hp : globN post "heap_ptr" = q.toNat := by
          unfold globN; rw [hpost_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        -- Now prove `KeyIn post Nd hp.toNat (wal.toNat + wbl.toNat)`!
        have hKey_cat : KeyIn post Nd hp.toNat (wal.toNat + wbl.toNat) := by
          by_cases htot0 : wal.toNat + wbl.toNat = 0
          · exact Or.inl htot0
          · right
            have hpost_m2_mb : ∀ addr : Nat, memB post addr = memB m2post addr := by
              intro addr
              have hm2_be : m2post.be = s.be :=
                hrel2.2.2.2.2.1.trans (hrel1.2.2.2.2.1.trans hs0_be)
              unfold memB; rw [hpost_mem, hpost_be, hm2_be]
            have hm1e_mb : ∀ addr : Nat, memB m1entry addr = memB s addr := by
              intro addr
              have hm1e_mem : m1entry.memory = s.memory := hs0_mem
              have hm1e_be : m1entry.be = s.be := hs0_be
              unfold memB; rw [hm1e_mem, hm1e_be]
            refine ⟨?_, ?_, ?_, ?_⟩
            · -- `NibblesOK post hp.toNat (wal.toNat + wbl.toNat)`
              intro k hk
              rw [hpost_m2_mb]
              by_cases hka : k < wal.toNat
              · -- First segment `[0, wal)`: preserved by `memcpy2` and copied from `wa` by `memcpy1`!
                have hnot_in2 : ¬ InIvl (hp.toNat + k) ((hp + wal).toNat, wbl.toNat) := by
                  unfold InIvl; rw [hp_al_nat]; omega
                have hmb2 := hrel2.2.2.2.2.2.2.2.2 (hp.toNat + k) (by omega) hnot_in2
                change memB m2post (hp.toNat + k) = memB m2entry (hp.toNat + k) at hmb2
                have hm2e_mb : memB m2entry (hp.toNat + k) = memB m1post (hp.toNat + k) := by
                  unfold memB; rfl
                have hhp_k : (hp + BitVec.ofNat 64 k).toNat = hp.toNat + k := by
                  rw [BitVec.toNat_add_of_lt]
                  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
                have hwa_k : (wa + BitVec.ofNat 64 k).toNat = wa.toNat + k := by
                  rw [BitVec.toNat_add_of_lt]
                  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
                have hcp1 := hrel1.2.2.2.2.2.2.2.1 k hka
                rw [hhp_k, hwa_k] at hcp1
                have hal_nz : wal.toNat ≠ 0 := by omega
                have hnibA := (hKeyA.resolve_left hal_nz).1 k hka
                rw [hmb2, hm2e_mb, hcp1, hm1e_mb]
                exact hnibA
              · -- Second segment `[wal, wal + wbl)`: copied from `wb` by `memcpy2`, and `wb` was outside `[hp, hp + wal)`!
                have hkb : k - wal.toNat < wbl.toNat := by omega
                have hbl_nz : wbl.toNat ≠ 0 := by omega
                obtain ⟨hnibB, _, _, _⟩ := hKeyB.resolve_left hbl_nz
                obtain ⟨_, hwb_hp, _⟩ := keyIn_heap hAR hKeyB hbl_nz
                rw [← hhp_eq] at hwb_hp
                have hd2_k : ((hp + wal) + BitVec.ofNat 64 (k - wal.toNat)).toNat = hp.toNat + k := by
                  rw [BitVec.toNat_add_of_lt]
                  · rw [hp_al_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
                  · rw [hp_al_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
                have hs2_k : (wb + BitVec.ofNat 64 (k - wal.toNat)).toNat = wb.toNat + (k - wal.toNat) := by
                  rw [BitVec.toNat_add_of_lt]
                  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
                have hcp2 := hrel2.2.2.2.2.2.2.2.1 (k - wal.toNat) hkb
                rw [hd2_k, hs2_k] at hcp2
                have hm2e_mb : memB m2entry (wb.toNat + (k - wal.toNat)) = memB m1post (wb.toNat + (k - wal.toNat)) := rfl
                have hnot_in1 : ¬ InIvl (wb.toNat + (k - wal.toNat)) (hp.toNat, wal.toNat) := by
                  unfold InIvl; dsimp only; omega
                have hmb1 := hrel1.2.2.2.2.2.2.2.2 (wb.toNat + (k - wal.toNat)) (by omega) hnot_in1
                rw [hcp2, hm2e_mb, hmb1, hm1e_mb]
                exact hnibB (k - wal.toNat) hkb
            · -- `Allocated post (hp.toNat, wal.toNat + wbl.toNat)`
              left
              rw [hpost_hp]
              exact ⟨by rw [hhp_eq]; exact hA.1, by dsimp [Inside]; omega⟩
            · -- `Inside (hp.toNat, wal.toNat + wbl.toNat) sourceBase heapLimit`
              exact ⟨by rw [hhp_eq]; exact hA.1, by omega⟩
            · -- `∀ n ∈ Nd, Disj (hp.toNat, wal.toNat + wbl.toNat) (nodeIvl post n)`
              intro n hn
              rw [nodeIvl, hstep_post.kinds n hn]
              have hp_n := hNd.1 n hn
              have hn_in : Inside (nodeIvl s n) sourceBase (globN s "heap_ptr") := by
                rcases hp_n.2.1 with h1 | h2
                · exact h1
                · have := hp_n.2.2.1.2; have := hA.2.2.1; have := hA.2.2.2.1
                  have hsep : heapLimit ≤ scratchStart := by decide
                  obtain ⟨hsz, _, _⟩ := nodeSize_bounds (memW s n)
                  dsimp [nodeIvl, Inside] at *; omega
              rw [← hhp_eq] at hn_in
              exact Or.inr (Or.inr (Or.inr hn_in.2))
        exact ⟨hp, hr_final, hsum_eq, hstep_post, hKey_cat, fun c hlt => hmem_outside c (Or.inl hlt)⟩

/-- Allocating 8 bytes via `alloc(8)` and storing a single nibble `idx < 16` via `storeByte(nib, idx)`
produces a `NodeStep` and `KeyIn post Nd nib 1`. -/
theorem alloc8_storeByte_nibble_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat)
    (widx : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hAR : ArenaReady s) (hNd : NodeHeap s Nd)
    (hidx_lt : widx.toNat < 16)
    (hlk_idx : s.locals.lookup (ofString "idx") = some (.val (.word widx)))
    (cont : ProgHOL 64)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString "nib") .one (ofString "alloc") [.const 8]
        (.seq (.storeByte (.var .local (ofString "nib")) (.var .local (ofString "idx"))) cont))).1) :
    ∃ (wnib : BitVec 64) (s_nib : PanSemStateFiniteExact 64 F),
      s_nib.code = originalRuntimeCode ∧
      NodeStep s s_nib Nd Nd ∧
      KeyIn s_nib Nd wnib.toNat 1 ∧
      (∀ c : BitVec 64, c.toNat < globN s "heap_ptr" → s_nib.memory c = s.memory c) ∧
      s_nib.locals.lookup (ofString "nib") = some (.val (.word wnib)) ∧
      (∀ x : MlS, x ≠ ofString "nib" → s_nib.locals.lookup x = s.locals.lookup x) ∧
      Resumes (evaluateHOLFiniteState s_nib cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString "nib") .one (ofString "alloc") [.const 8]
          (.seq (.storeByte (.var .local (ofString "nib")) (.var .local (ofString "idx"))) cont))).1 =
        (evaluateHOLFiniteState s_nib cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString "nib") .one (ofString "alloc") [.const 8]
          (.seq (.storeByte (.var .local (ofString "nib")) (.var .local (ofString "idx"))) cont))).2 =
        { (evaluateHOLFiniteState s_nib cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s_nib cont).2.locals
            (ofString "nib", s.locals.lookup (ofString "nib")) } := by
  have hG : GuestInv s := hAR.1
  have hA : ArenaOK s := hAR.2
  obtain ⟨hp, fp, sp, hhp, hhp_eq, hfp, hfp_eq, hsp, hsp_eq⟩ :=
    Wave8Contracts.M26.arenaOK_globals s hA
  obtain ⟨avals, abody, acallee, aret, _, haargs, ahl, ahexn | ⟨arv, apost, harun, _, hcont_res, ahr_eq, ahp_eq⟩⟩ :=
    decCall_resumes_inv hres
  · obtain ⟨aeid, aev, aha, ahne, _⟩ := ahexn
    have ahsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "alloc")
      _ _ _ _ _ avals acallee (by rw [hcode]; exact lookup_alloc) ahl
    subst ahsame
    obtain ⟨_, ahret⟩ := alloc_body_resumes_eq_returned (callEntryStateHOLFinite s acallee) hcode
      (by rw [aha]; exact Or.inr ⟨aeid, aev, rfl, ahne⟩)
    rw [aha] at ahret; cases ahret
  · have havals : avals = [.val (.word 8)] := by
      rw [evalListHOLFinite_eq_toExact] at haargs
      simpa [evalListHOLExact, evalHOLExact] using haargs.symm
    subst havals
    have ahl_ex := pan_one_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_alloc) 8 (by rw [hcode]; exact lookup_alloc)
    rw [ahl_ex] at ahl
    obtain ⟨rfl, hrest_a⟩ := Prod.mk.inj (Option.some.inj ahl.symm)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrest_a
    have hn_ent : (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word 8)))).locals.lookup
        (ofString "n") = some (.val (.word 8)) := by
      simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have harun_info := Wave8Contracts.M26.alloc_body_run
      (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word 8))))
      hp 8 hcode hhp hn_ent arv (by rw [harun])
    rw [harun] at harun_info
    obtain ⟨rfl, hcmp1, hcmp2, hapost_eq⟩ := harun_info
    dsimp only at hapost_eq
    set q : BitVec 64 := (hp + (8 + 7)) &&& ((0 : BitVec 64) - 8)
    have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hA.2.1
    have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hA.2.2.2.2.2.1
    obtain ⟨hq_eq, hq_hi, hq_al, hp_le_q⟩ := Wave8Contracts.M26.alloc_arith hp 8 hhp_hi hhp_al hcmp1 hcmp2
    change q.toNat = hp.toNat + ((8 : BitVec 64).toNat + 7) / 8 * 8 at hq_eq
    change q.toNat ≤ heapLimit at hq_hi
    have h8 : ((8 : BitVec 64).toNat + 7) / 8 * 8 = 8 := by decide
    rw [h8] at hq_eq
    have hhl_lt : heapLimit < 2 ^ 64 := by decide
    have hhe_ge : heapLimit ≤ heapEnd := by decide
    set s0 := setVarHOLFinite (ofString "nib") (.val (.word hp)) { apost with locals := s.locals }
    have hs0_nib : s0.locals.lookup (ofString "nib") = some (.val (.word hp)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs0_idx : s0.locals.lookup (ofString "idx") = some (.val (.word widx)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_idx,
        show ofString "nib" ≠ ofString "idx" by decide]
    have hs0_ma : s0.memaddrs = ordinaryDomain := by
      simp [s0, setVarHOLFinite]; rw [hapost_eq]; exact hG.memaddrs
    have hs0_mem : s0.memory = s.memory := by
      simp [s0, setVarHOLFinite]; rw [hapost_eq]; rfl
    have halign_hp : panByteAlignHOL hp = hp := by
      apply BitVec.eq_of_toNat_eq
      rw [panByteAlign_toNat64]; omega
    have hdom_hp : s0.memaddrs (panByteAlignHOL hp) := by
      rw [halign_hp, hs0_ma]
      have hhp_bv : hp = BitVec.ofNat 64 hp.toNat := by simp
      rw [hhp_bv]
      exact Wave8Contracts.M26.ordinaryDomain_of_nat hp.toNat
        (by rw [hhp_eq]; exact hA.1) (by omega) hhp_al
    -- Evaluate `storeByte(nib, idx)` on `s0`
    obtain ⟨s_nib, hsb_run, hseq_eq⟩ :=
      seq_noResumes_left (fun _ _ h => storeByte_res_not_resumes h) hcont_res
    have hsb_inv := hsb_run
    rw [evaluateHOLFiniteState_storeByte] at hsb_inv
    simp only [evalHOLExact, hs0_nib, hs0_idx] at hsb_inv
    rcases hm_sb : @panMemStoreByteWord8HOL 64 _ s0.memory s0.memaddrs
        (fun a => Classical.propDecidable (s0.memaddrs a)) s0.be hp (BitVec.ofNat 8 widx.toNat) with _ | mem'
    · rw [hm_sb] at hsb_inv; simp at hsb_inv
    · rw [hm_sb] at hsb_inv
      injection hsb_inv with _ hs_nib_eq
      subst hs_nib_eq
      have hcell_frame : ∀ c : BitVec 64, c ≠ hp → mem' c = s.memory c := by
        intro c hne
        have hm' := hm_sb
        unfold panMemStoreByteWord8HOL at hm'
        rw [halign_hp] at hm'
        rcases s0.memory hp with ⟨cell⟩
        dsimp only at hm'
        have hdom_hp' : s0.memaddrs hp := by rwa [halign_hp] at hdom_hp
        rw [if_pos hdom_hp'] at hm'
        injection hm' with hmeq; subst hmeq
        rw [← hs0_mem]; simp [hne]
      obtain ⟨hsame_b, _⟩ := @SoloHtabSet.panMemStoreByte_other_byte s0.memory s0.memaddrs
        (fun a => Classical.propDecidable (s0.memaddrs a)) s0.be hp
        (BitVec.ofNat 8 widx.toNat) mem' hm_sb
      set s_nib' : PanSemStateFiniteExact 64 F := { s0 with memory := mem' }
      have hs_nib_code : s_nib'.code = originalRuntimeCode := by
        simp [s_nib', s0, setVarHOLFinite]; rw [hapost_eq]; exact hcode
      have hs_nib_G : GuestInv s_nib' := by
        refine ⟨hs_nib_code, ?_, ?_, ?_⟩ <;> (simp [s_nib', s0, setVarHOLFinite]; rw [hapost_eq])
        · exact hG.memaddrs
        · exact hG.shMemaddrs
        · exact hG.baseAddr
      have hs_nib_glob : s_nib'.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) := by
        simp [s_nib', s0, setVarHOLFinite]; rw [hapost_eq]; rfl
      have hs_nib_be : s_nib'.be = s.be := by
        simp [s_nib', s0, setVarHOLFinite]; rw [hapost_eq]; rfl
      have hmem_outside : ∀ c : BitVec 64,
          (c.toNat < globN s "heap_ptr" ∨ q.toNat ≤ c.toNat) → s_nib'.memory c = s.memory c := by
        intro c hout
        apply hcell_frame c
        rintro rfl
        rw [← hhp_eq] at hout
        omega
      have hstep : NodeStep s s_nib' Nd Nd :=
        nodeStep_fresh_heap_only hAR hNd hs_nib_G hs_nib_glob hs_nib_be
          (by rw [← hhp_eq]; exact hp_le_q) hq_hi hq_al hmem_outside
      have hKey_nib : KeyIn s_nib' Nd hp.toNat 1 := by
        right
        have hpost_hp : globN s_nib' "heap_ptr" = q.toNat := by
          unfold globN; rw [hs_nib_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro k hk
          have hk0 : k = 0 := by omega
          subst hk0
          have hhp0 : BitVec.ofNat 64 (hp.toNat + 0) = hp := by simp
          have hsn_mem : s_nib'.memory = mem' := rfl
          have hsn_be : s_nib'.be = s0.be := rfl
          unfold memB
          rw [hhp0, hsn_mem, hsn_be]
          have hgoal_lt : (BitVec.ofNat 8 widx.toNat).toNat < 16 := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hidx_lt
          rcases hcell_p : mem' (panByteAlignHOL hp) with ⟨vp⟩
          have hs_p : (panGetByteHOL hp vp s0.be).toNat = (BitVec.ofNat 8 widx.toNat).toNat := by
            simpa [hcell_p] using hsame_b
          simp [hcell_p, hs_p]; omega
        · left; rw [hpost_hp]; exact ⟨by rw [hhp_eq]; exact hA.1, by omega⟩
        · exact ⟨by rw [hhp_eq]; exact hA.1, by omega⟩
        · intro n hn
          rw [nodeIvl, hstep.kinds n hn]
          have hp_n := hNd.1 n hn
          have hn_in : Inside (nodeIvl s n) sourceBase (globN s "heap_ptr") := by
            rcases hp_n.2.1 with h1 | h2
            · exact h1
            · have := hp_n.2.2.1.2; have := hA.2.2.1; have := hA.2.2.2.1
              have hsep : heapLimit ≤ scratchStart := by decide
              obtain ⟨hsz, _, _⟩ := nodeSize_bounds (memW s n)
              dsimp [nodeIvl, Inside] at *; omega
          rw [← hhp_eq] at hn_in
          exact Or.inr (Or.inr (Or.inr hn_in.2))
      refine ⟨hp, s_nib', hs_nib_code, hstep, hKey_nib,
        fun c hlt => hmem_outside c (Or.inl hlt), hs0_nib, ?_, ?_, ?_, ?_⟩
      · intro x hx
        simp [s_nib', s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hx]
      · rwa [hseq_eq] at hcont_res
      · rw [ahr_eq, hseq_eq]
      · rw [ahp_eq, hseq_eq]

/-- Any `.call none fname args` never returns `none` (it either returns `some ...` or errors). -/
theorem call_none_ne_none {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fname : MlS) (args : List (ExpHOL 64)) :
    (evaluateHOLFiniteState s (.call none fname args)).1 ≠ none := by
  rw [evaluateHOLFiniteState_call]
  rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp
  · dsimp only
    rcases lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨eb, ec, er⟩
    · simp
    · dsimp only
      split
      · simp
      · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s ec) eb with ⟨er1, ep1⟩
        rcases er1 with _ | er1'
        · simp
        · cases er1' <;> simp
          split <;> simp

/-- Tail call `.call none "node_new_ext" [nibExp, nlenExp, chExp]` from state `st` with `NodeStep`: -/
theorem tail_call_node_new_ext {F : Type}
    (st : PanSemStateFiniteExact 64 F) (Nd : List Nat)
    (nibExp nlenExp chExp : ExpHOL 64)
    (wnib wnlen wch : BitVec 64)
    (hcode : st.code = originalRuntimeCode)
    (hAR : ArenaReady st) (hNd : NodeHeap st Nd)
    (hargs : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
      [nibExp, nlenExp, chExp] = some [.val (.word wnib), .val (.word wnlen), .val (.word wch)])
    (hKey : KeyIn st Nd wnib.toNat wnlen.toNat)
    (hch : RootIn Nd wch.toNat)
    (hres : Resumes (evaluateHOLFiniteState st (.call none (ofString "node_new_ext") [nibExp, nlenExp, chExp])).1) :
    ∃ Nd',
      NodeStep st (evaluateHOLFiniteState st (.call none (ofString "node_new_ext") [nibExp, nlenExp, chExp])).2 Nd Nd' ∧
      ∀ v, (evaluateHOLFiniteState st (.call none (ofString "node_new_ext") [nibExp, nlenExp, chExp])).1 =
        some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧ RootIn Nd' w.toNat := by
  obtain ⟨evals, ebody, ecallee, eret, _, heargs, hel_lk, heexn | ⟨erv, epost, herun, _, heout_eq⟩⟩ :=
    call_none_resumes_inv hres
  · obtain ⟨eid, ev, he_exn, hne_tr, he_call_eq⟩ := heexn
    have hevals : evals = [.val (.word wnib), .val (.word wnlen), .val (.word wch)] :=
      Option.some.inj (heargs.symm.trans hargs)
    subst hevals
    have hel_code : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "node_new_ext")
        [.val (.word wnib), .val (.word wnlen), .val (.word wch)] =
        some (ebody, ecallee, eret) := by rwa [← hcode]
    obtain ⟨rfl, _⟩ := lookup_param_exact lookup_node_new_ext hel_code
      [] "nib" .one [(ofString "nlen", .one), (ofString "child", .one)]
      [] (.val (.word wnib)) _ rfl rfl rfl (by decide)
    exact absurd (congrArg Prod.fst he_exn)
      (node_new_ext_no_nonTrap_exn (callEntryStateHOLFinite st ecallee) hcode eid ev hne_tr)
  · have hevals : evals = [.val (.word wnib), .val (.word wnlen), .val (.word wch)] :=
      Option.some.inj (heargs.symm.trans hargs)
    subst hevals
    have hel_code : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "node_new_ext")
        [.val (.word wnib), .val (.word wnlen), .val (.word wch)] =
        some (ebody, ecallee, eret) := by rwa [← hcode]
    obtain ⟨_, hep_nib⟩ := lookup_param_exact lookup_node_new_ext hel_code
      [] "nib" .one [(ofString "nlen", .one), (ofString "child", .one)]
      [] (.val (.word wnib)) _ rfl rfl rfl (by decide)
    obtain ⟨_, hep_nlen⟩ := lookup_param_exact lookup_node_new_ext hel_code
      [(ofString "nib", .one)] "nlen" .one [(ofString "child", .one)]
      [_] (.val (.word wnlen)) _ rfl rfl rfl (by decide)
    obtain ⟨_, hep_ch⟩ := lookup_param_exact lookup_node_new_ext hel_code
      [(ofString "nib", .one), (ofString "nlen", .one)] "child" .one []
      [_, _] (.val (.word wch)) [] rfl rfl rfl (by decide)
    obtain ⟨Nd_ext, hstep_ext, hret_ext⟩ := nodeStep_of_nodeFn nf_node_new_ext st hcode
      hAR hNd hel_lk
      (by intro n hn; rw [List.mem_singleton.mp hn]; simp [locN, callEntryStateHOLFinite, hep_ch]; exact hch)
      (by simp [locN, callEntryStateHOLFinite, hep_nib, hep_nlen]; exact hKey)
      (by rw [herun]; exact Or.inl ⟨erv, rfl⟩)
    rw [herun] at hstep_ext hret_ext
    dsimp only at hstep_ext hret_ext
    obtain ⟨wext, rfl, hwext_root⟩ := hret_ext erv rfl
    refine ⟨Nd_ext, ?_, ?_⟩
    · rw [heout_eq]; exact hstep_ext.with_locals_clock _ _
    · intro v hv; rw [heout_eq] at hv; injection hv with h1; injection h1 with h2; subst h2
      exact ⟨wext, rfl, hwext_root⟩

/-- Tail call `.call none "node_new_leaf" [nibExp, nlenExp, vptrExp, vlenExp]` from state `st` with `NodeStep`: -/
theorem tail_call_node_new_leaf {F : Type}
    (st : PanSemStateFiniteExact 64 F) (Nd : List Nat)
    (nibExp nlenExp vptrExp vlenExp : ExpHOL 64)
    (wnib wnlen wvptr wvlen : BitVec 64)
    (hcode : st.code = originalRuntimeCode)
    (hAR : ArenaReady st) (hNd : NodeHeap st Nd)
    (hargs : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
      [nibExp, nlenExp, vptrExp, vlenExp] =
      some [.val (.word wnib), .val (.word wnlen), .val (.word wvptr), .val (.word wvlen)])
    (hKey : KeyIn st Nd wnib.toNat wnlen.toNat)
    (hvlen : wvlen.toNat < 2 ^ 40)
    (hres : Resumes (evaluateHOLFiniteState st
      (.call none (ofString "node_new_leaf") [nibExp, nlenExp, vptrExp, vlenExp])).1) :
    ∃ Nd',
      NodeStep st (evaluateHOLFiniteState st
        (.call none (ofString "node_new_leaf") [nibExp, nlenExp, vptrExp, vlenExp])).2 Nd Nd' ∧
      ∀ v, (evaluateHOLFiniteState st
        (.call none (ofString "node_new_leaf") [nibExp, nlenExp, vptrExp, vlenExp])).1 =
        some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧ RootIn Nd' w.toNat := by
  obtain ⟨evals, ebody, ecallee, eret, _, heargs, hel_lk, heexn | ⟨erv, epost, herun, _, heout_eq⟩⟩ :=
    call_none_resumes_inv hres
  · obtain ⟨eid, ev, he_exn, hne_tr, _⟩ := heexn
    have hevals : evals = [.val (.word wnib), .val (.word wnlen), .val (.word wvptr), .val (.word wvlen)] :=
      Option.some.inj (heargs.symm.trans hargs)
    subst hevals
    have hel_code : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "node_new_leaf")
        [.val (.word wnib), .val (.word wnlen), .val (.word wvptr), .val (.word wvlen)] =
        some (ebody, ecallee, eret) := by rwa [← hcode]
    obtain ⟨rfl, _⟩ := lookup_param_exact lookup_node_new_leaf hel_code
      [] "nib" .one [(ofString "nlen", .one), (ofString "vptr", .one), (ofString "vlen", .one)]
      [] (.val (.word wnib)) _ rfl rfl rfl (by decide)
    exact absurd (congrArg Prod.fst he_exn)
      (node_new_leaf_no_nonTrap_exn (callEntryStateHOLFinite st ecallee) hcode eid ev hne_tr)
  · have hevals : evals = [.val (.word wnib), .val (.word wnlen), .val (.word wvptr), .val (.word wvlen)] :=
      Option.some.inj (heargs.symm.trans hargs)
    subst hevals
    have hel_code : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "node_new_leaf")
        [.val (.word wnib), .val (.word wnlen), .val (.word wvptr), .val (.word wvlen)] =
        some (ebody, ecallee, eret) := by rwa [← hcode]
    obtain ⟨_, hep_nib⟩ := lookup_param_exact lookup_node_new_leaf hel_code
      [] "nib" .one [(ofString "nlen", .one), (ofString "vptr", .one), (ofString "vlen", .one)]
      [] (.val (.word wnib)) _ rfl rfl rfl (by decide)
    obtain ⟨_, hep_nlen⟩ := lookup_param_exact lookup_node_new_leaf hel_code
      [(ofString "nib", .one)] "nlen" .one [(ofString "vptr", .one), (ofString "vlen", .one)]
      [_] (.val (.word wnlen)) _ rfl rfl rfl (by decide)
    obtain ⟨_, hep_vlen⟩ := lookup_param_exact lookup_node_new_leaf hel_code
      [(ofString "nib", .one), (ofString "nlen", .one), (ofString "vptr", .one)] "vlen" .one []
      [_, _, _] (.val (.word wvlen)) [] rfl rfl rfl (by decide)
    obtain ⟨Nd_lf, hstep_lf, hret_lf⟩ := nodeStep_of_nodeFn nf_node_new_leaf st hcode
      hAR hNd hel_lk
      (by intro n hn; cases hn)
      (by simp [locN, callEntryStateHOLFinite, hep_nib, hep_nlen, hep_vlen]; exact ⟨hKey, hvlen⟩)
      (by rw [herun]; exact Or.inl ⟨erv, rfl⟩)
    rw [herun] at hstep_lf hret_lf
    dsimp only at hstep_lf hret_lf
    obtain ⟨wlf, rfl, hwlf_root⟩ := hret_lf erv rfl
    refine ⟨Nd_lf, ?_, ?_⟩
    · rw [heout_eq]; exact hstep_lf.with_locals_clock _ _
    · intro v hv; rw [heout_eq] at hv; injection hv with h1; injection h1 with h2; subst h2
      exact ⟨wlf, rfl, hwlf_root⟩

/-- `mpt_fail(codeExp)` never returns `none`! -/
theorem mpt_fail_ne_none {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode)
    (codeExp : ExpHOL 64) :
    (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "mpt_fail") [codeExp])).1 ≠ none := by
  rw [evaluateHOLFiniteState_call]
  rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [codeExp] with _ | vs
  · simp
  · dsimp only
    rcases hlk : lookupCodeHOLFinite s.code.lookup (ofString "mpt_fail") vs with _ | ⟨fb, fc, fr⟩
    · simp
    · dsimp only
      split
      · simp
      · have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "mpt_fail")
          _ _ _ _ _ vs fc (by rw [hcode]; exact lookup_mpt_fail) hlk
        subst hsame
        have hbody : sourceFnBody Guest.Software.guestFn_mpt_fail =
            .seq (.raise (ofString "MptErr") (.var .local (ofString "code"))) (.return (.const 0)) := rfl
        have hf_not_ret : ∀ rv,
            (evaluateHOLFiniteState (callEntryStateHOLFinite s fc)
              (sourceFnBody Guest.Software.guestFn_mpt_fail)).1 ≠ some (.returned rv) := by
          intro rv hret_f
          rw [hbody, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_raise] at hret_f
          rcases hh1 : (callEntryStateHOLFinite s fc).eshapes.lookup (ofString "MptErr") with _ | esh
          · rw [hh1] at hret_f
            rcases hh2 : @evalHOLExact 64 F _ (callEntryStateHOLFinite s fc).toExact
                (fun a => Classical.propDecidable ((callEntryStateHOLFinite s fc).memaddrs a))
                (.var .local (ofString "code")) with _ | cv <;>
              (rw [hh2] at hret_f; dsimp only at hret_f; cases hret_f)
          · rw [hh1] at hret_f
            rcases hh2 : @evalHOLExact 64 F _ (callEntryStateHOLFinite s fc).toExact
                (fun a => Classical.propDecidable ((callEntryStateHOLFinite s fc).memaddrs a))
                (.var .local (ofString "code")) with _ | cv
            · rw [hh2] at hret_f; dsimp only at hret_f; cases hret_f
            · rw [hh2] at hret_f; dsimp only at hret_f
              by_cases hcond : shapeOfHOLExact cv = esh ∧
                  sizeOfShapeWithContextHOL (callEntryStateHOLFinite s fc).structs (shapeOfHOLExact cv) ≤ 32
              · rw [if_pos hcond] at hret_f; dsimp only at hret_f; cases hret_f
              · rw [if_neg hcond] at hret_f; dsimp only at hret_f; cases hret_f
        rcases hfr_ev : evaluateHOLFiniteState (callEntryStateHOLFinite s fc)
            (sourceFnBody Guest.Software.guestFn_mpt_fail) with ⟨fr_r, fr_p⟩
        rcases fr_r with _ | fr_r'
        · simp
        · cases fr_r' with
          | returned rv => exact absurd (congrArg Prod.fst hfr_ev) (hf_not_ret rv)
          | _ => simp

end InitECandidate.Solver.Wave8GuestInv.R16Shards
