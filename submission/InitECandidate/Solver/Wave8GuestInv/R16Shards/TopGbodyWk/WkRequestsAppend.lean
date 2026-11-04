import InitECandidate.Solver.Wave8GuestInv.ContractParts.C08
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.RlpHelpers
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc

theorem lookup_requests_append :
    originalRuntimeCode.lookup (ofString "requests_append") =
      some ([(ofString "type_byte", .one), (ofString "data", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_requests_append, .one) :=
  lookup_of_guestAst_getElem 876 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_requests_append) rfl

private theorem eval_call_memcpy_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dstExp srcExp nExp : ExpHOL 64)
    (dst0 src0 n0 : BitVec 64)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcExp =
      some (.val (.word src0)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])
    (out.1 = none →
      (0 < n0.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ heapEnd) ∧
      HeapByteEff s out.2 [(dst0.toNat, n0.toNat)] [] ∧
      out.2.locals = s.locals ∧ out.2.globals = s.globals) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  have hmc := M11.eval_call_memcpy_bre_gen s dstExp srcExp nExp dst0 src0 n0 [(0, heapEnd)]
    hcode hAR.1.memaddrs hdst hsrc hn
    (fun off _ hle => ⟨(0, heapEnd), List.mem_singleton.2 rfl, Nat.zero_le _, by rw [heapEnd_val]; exact hle⟩)
    (fun off _ hle => ⟨(0, heapEnd), List.mem_singleton.2 rfl, Nat.zero_le _, by rw [heapEnd_val]; exact hle⟩)
    hnt
  dsimp only at hmc ⊢
  refine ⟨fun hn0 => ?_, hmc.2⟩
  rw [evaluateHOLFiniteState_call] at hnt hn0 ⊢
  have ha : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) [dstExp, srcExp, nExp] =
      some [.val (.word dst0), .val (.word src0), .val (.word n0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hsrc, hn]
  have hlk := pan_three_word_lookup s.code.lookup (ofString "memcpy")
    (ofString "dst") (ofString "src") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_memcpy) dst0 src0 n0
    (by decide) (by decide) (by decide)
    (by rw [hcode]; exact M11.lookup_memcpy)
  rw [ha] at hnt hn0 ⊢; dsimp only at hnt hn0 ⊢
  rw [hlk] at hnt hn0 ⊢; dsimp only at hnt hn0 ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · rw [if_neg hcz] at hnt hn0 ⊢
    set cmap : HolFiniteMapExact MlS (ValueHOL 64) :=
      ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
        (ofString "src", ValueHOL.val (.word src0))).update (ofString "n", ValueHOL.val (.word n0))
    set ent := callEntryStateHOLFinite s cmap
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      have h1 : ofString "n" ≠ ofString "dst" := by decide
      have h2 : ofString "src" ≠ ofString "dst" := by decide
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2, Ne.symm h1, Ne.symm h2]
    have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hGe : GuestInv ent := guestInv_callEntry s cmap hAR.1
    rcases hb : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_memcpy) with ⟨br, bs⟩
    rw [hb] at hn0
    cases br with
    | none => simp at hn0
    | some r =>
      cases r with
      | returned rv =>
        dsimp only at hn0 ⊢
        by_cases hsh : shapeEqHOL (shapeOfHOLExact rv) .one = true
        · rw [if_pos hsh]
          have hcp := R13Shards.Keccak256.memcpy_body_eff ent dst0 n0 hcode hGe hent_dst hent_n
            (by rw [hb]; exact Or.inl ⟨rv, rfl⟩)
          rw [hb] at hcp; dsimp only at hcp
          have heff0 : R13Shards.Keccak256.ByteEff s ent [(dst0.toNat, n0.toNat)] :=
            (R13Shards.Keccak256.ByteEff.refl s _).locals_clock ent.locals ent.clock
          have heff_out : R13Shards.Keccak256.ByteEff s { bs with locals := s.locals } [(dst0.toNat, n0.toNat)] :=
            (heff0.trans hcp.1).locals_clock s.locals bs.clock
          exact ⟨hcp.2, HeapByteEff.of_byteEff hAR heff_out, rfl, heff_out.globals⟩
        · rw [if_neg hsh] at hn0; simp at hn0
      | _ => simp at hn0

private theorem storeByte_none_or_err {F : Type}
    (t : PanSemStateFiniteExact 64 F) (dst val : ExpHOL 64) :
    (evaluateHOLFiniteState t (.storeByte dst val)).1 = none ∧
      (evaluateHOLFiniteState t (.storeByte dst val)).2.locals = t.locals ∧
      (evaluateHOLFiniteState t (.storeByte dst val)).2.globals = t.globals ∨
      (evaluateHOLFiniteState t (.storeByte dst val)).1 = some .error := by
  rw [evaluateHOLFiniteState_storeByte]
  split
  · split
    · split
      · exact Or.inl ⟨rfl, rfl, rfl⟩
      · exact Or.inr rfl
    · exact Or.inr rfl
  · exact Or.inr rfl

private theorem eval_store_word_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dst val : ExpHOL 64) (cont : ProgHOL 64)
    (addr w : BitVec 64)
    (hma : s.memaddrs = ordinaryDomain)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst =
      some (.val (.word addr)))
    (hval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val =
      some (.val (.word w)))
    (hres : Resumes (evaluateHOLFiniteState s (.seq (.store dst val) cont)).1) :
    addr.toNat % 8 = 0 ∧ sourceBase ≤ addr.toNat ∧ addr.toNat < heapEnd ∧
    evaluateHOLFiniteState s (.store dst val) =
      (none, { s with memory := fun a => if a = addr then .word w else s.memory a }) := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store] at hres
  rw [evaluateHOLFiniteState_store]
  rw [hdst, hval] at hres ⊢
  by_cases hdom : s.memaddrs addr
  · have hord := (ordinaryDomain_iff addr).1 (hma ▸ hdom)
    refine ⟨hord.1, hord.2.1, hord.2.2, ?_⟩
    simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom, ↓reduceIte]
  · simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom] at hres
    exact False.elim (not_resumes_error hres)

private theorem eval_load_word_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (addrExp : ExpHOL 64) (cont : ProgHOL 64)
    (addr : BitVec 64)
    (hma : s.memaddrs = ordinaryDomain)
    (haddr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addrExp =
      some (.val (.word addr)))
    (hres : Resumes (evaluateHOLFiniteState s (.dec (ofString lname) .one (.load .one addrExp) cont)).1) :
    ∃ kw : BitVec 64,
      addr.toNat % 8 = 0 ∧ sourceBase ≤ addr.toNat ∧ addr.toNat < heapEnd ∧
      s.memory addr = .word kw ∧
      kw.toNat = memW s addr.toNat ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one addrExp) = some (.val (.word kw)) := by
  by_cases hdom : s.memaddrs addr
  · have hord := (ordinaryDomain_iff addr).1 (hma ▸ hdom)
    obtain ⟨kw, hm⟩ : ∃ kw, s.memory addr = .word kw := by cases s.memory addr with | word kw => exact ⟨kw, rfl⟩
    have hmw : kw.toNat = memW s addr.toNat := by
      unfold memW
      have hb : BitVec.ofNat 64 addr.toNat = addr :=
        BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt addr.isLt])
      rw [hb, hm]
    have hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one addrExp) = some (.val (.word kw)) := by
      simp [evalHOLExact, haddr, memLoadHOLExact, hdom, hm]
    exact ⟨kw, hord.1, hord.2.1, hord.2.2, hm, hmw, hev⟩
  · exfalso
    rw [evaluateHOLFiniteState_dec_total] at hres
    dsimp only at hres
    have hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one addrExp) = none := by
      simp [evalHOLExact, haddr, memLoadHOLExact, hdom]
    rw [hev] at hres
    exact not_resumes_error hres

private theorem eval_load_in_store_dst_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F) (addrExp : ExpHOL 64) (rest : List (ExpHOL 64))
    (val : ExpHOL 64) (cont : ProgHOL 64) (addr : BitVec 64)
    (hma : s.memaddrs = ordinaryDomain)
    (haddr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addrExp =
      some (.val (.word addr)))
    (hres : Resumes (evaluateHOLFiniteState s (.seq (.store (.op .add (.load .one addrExp :: rest)) val) cont)).1) :
    ∃ arrw : BitVec 64,
      addr.toNat % 8 = 0 ∧ sourceBase ≤ addr.toNat ∧ addr.toNat < heapEnd ∧
      s.memory addr = .word arrw ∧
      arrw.toNat = memW s addr.toNat ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one addrExp) = some (.val (.word arrw)) := by
  by_cases hdom : s.memaddrs addr
  · have hord := (ordinaryDomain_iff addr).1 (hma ▸ hdom)
    obtain ⟨arrw, hm⟩ : ∃ arrw, s.memory addr = .word arrw := by cases s.memory addr with | word arrw => exact ⟨arrw, rfl⟩
    have hmw : arrw.toNat = memW s addr.toNat := by
      unfold memW
      have hb : BitVec.ofNat 64 addr.toNat = addr :=
        BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt addr.isLt])
      rw [hb, hm]
    have hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one addrExp) = some (.val (.word arrw)) := by
      simp [evalHOLExact, haddr, memLoadHOLExact, hdom, hm]
    exact ⟨arrw, hord.1, hord.2.1, hord.2.2, hm, hmw, hev⟩
  · exfalso
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store] at hres
    have hdnone : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.op .add (.load .one addrExp :: rest)) = none := by
      simp [evalHOLExact, evalListHOLExact, memLoadHOLExact, haddr, hdom]
    rw [hdnone] at hres
    exact not_resumes_error hres

private theorem ivl_disj_bo_and_arr56 {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hWT : WorldTypedWith s S Nd)
    (hbo : globN s "bo" ≠ 0) (h56 : memW s (globN s "bo" + 56) ≠ 0) :
    Disj (globN s "bo", 88) (memW s (globN s "bo" + 56), 128) ∧
    (∀ t ∈ S, ∀ i ∈ htabFootprint s t,
      Disj i (globN s "bo", 88) ∧ Disj i (memW s (globN s "bo" + 56), 128)) ∧
    (∀ g ∈ (["ws", "bs", "ts"] : List String), ∀ sz, (g, sz) ∈ typedRecords → globN s g ≠ 0 →
      Disj (globN s g, sz) (globN s "bo", 88) ∧
      Disj (globN s g, sz) (memW s (globN s "bo" + 56), 128)) ∧
    (globN s "journal_cap" ≠ 0 →
      Disj (globN s "journal", 32 * globN s "journal_cap") (globN s "bo", 88) ∧
      Disj (globN s "journal", 32 * globN s "journal_cap") (memW s (globN s "bo" + 56), 128)) ∧
    (∀ i ∈ blockOutObjects s, i.2 = 24 →
      Disj i (globN s "bo", 88) ∧ Disj i (memW s (globN s "bo" + 56), 128)) ∧
    (∀ i ∈ balObjects s,
      Disj i (globN s "bo", 88) ∧ Disj i (memW s (globN s "bo" + 56), 128)) ∧
    (∀ o ∈ nodeExtents s Nd,
      Disj o (globN s "bo", 88) ∧ Disj o (memW s (globN s "bo" + 56), 128)) := by
  obtain ⟨hT, _, hF, hTr⟩ := hWT
  have hbo_fo : (globN s "bo", 88) ∈ fixedObjects s := by
    have := M13.typedRec_in_fixedObjects s (g := "bo") (sz := 88) (by decide)
    simpa [hbo] using this
  have h56_bo : (memW s (globN s "bo" + 56), 128) ∈ blockOutObjects s := by
    unfold blockOutObjects; simp [hbo, h56]
  have h56_fo : (memW s (globN s "bo" + 56), 128) ∈ fixedObjects s :=
    M13.blockOut_in_fixedObjects h56_bo
  have hnd := hF.2
  unfold fixedObjects at hnd
  rw [List.pairwise_append] at hnd
  obtain ⟨h123, _, hcross_bal⟩ := hnd
  rw [List.pairwise_append] at h123
  obtain ⟨h12, hpw_bo, hcross_bo⟩ := h123
  rw [List.pairwise_append] at h12
  obtain ⟨hpw_gb, _, hcross_jr⟩ := h12
  have hbo_gb : (globN s "bo", 88) ∈
      (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) :=
    List.mem_map.2 ⟨("bo", 88), by decide, by simp [hbo]⟩
  have hbo_in12 : (globN s "bo", 88) ∈
      (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) ++
        [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] :=
    List.mem_append_left _ hbo_gb
  refine ⟨hcross_bo _ hbo_in12 _ h56_bo, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht i hi
    exact ⟨(hT.2.1 t ht).2 i hi |>.2 _ hbo_fo, (hT.2.1 t ht).2 i hi |>.2 _ h56_fo⟩
  · intro g hg_mem sz htr hgnz
    have hg_gb : (g, sz) ∈ globalBuffers := by
      simp only [typedRecords, List.mem_cons, List.not_mem_nil, or_false] at htr
      rcases htr with h | h | h | h <;> (rw [h]; decide)
    have hg_ne_bo : g ≠ "bo" := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg_mem
      rcases hg_mem with rfl | rfl | rfl <;> decide
    have hdisj_gb : Disj (globN s g, sz) (globN s "bo", 88) := by
      have hsub : ∀ (l : List (String × Nat)),
          (l.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)).Pairwise Disj →
          (g, sz) ∈ l → ("bo", 88) ∈ l →
          Disj (globN s g, if globN s g = 0 then 0 else sz)
               (globN s "bo", if globN s "bo" = 0 then 0 else 88) := by
        intro l hpl h1 h2
        induction l with
        | nil => cases h1
        | cons hd tl ih =>
          rw [List.map_cons, List.pairwise_cons] at hpl
          rcases List.mem_cons.1 h1 with rfl | h1'
          · rcases List.mem_cons.1 h2 with h_eq | h2'
            · exact absurd (Prod.mk.inj h_eq).1.symm hg_ne_bo
            · exact hpl.1 _ (List.mem_map.2 ⟨("bo", 88), h2', rfl⟩)
          · rcases List.mem_cons.1 h2 with rfl | h2'
            · exact (hpl.1 _ (List.mem_map.2 ⟨(g, sz), h1', rfl⟩)).flip
            · exact ih hpl.2 h1' h2'
      simpa [hgnz, hbo] using hsub globalBuffers hpw_gb hg_gb (by decide)
    have hg_in12 : (globN s g, sz) ∈
        (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) ++
          [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] :=
      List.mem_append_left _ (List.mem_map.2 ⟨(g, sz), hg_gb, by simp [hgnz]⟩)
    exact ⟨hdisj_gb, hcross_bo _ hg_in12 _ h56_bo⟩
  · intro hjc
    have hj_in : (globN s "journal", 32 * globN s "journal_cap") ∈
        [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] := by
      simp [hjc]
    exact ⟨(hcross_jr _ hbo_gb _ hj_in).flip,
           hcross_bo _ (List.mem_append_right _ hj_in) _ h56_bo⟩
  · intro i hi hi24
    have hd1 : Disj i (globN s "bo", 88) := (hcross_bo _ hbo_in12 i hi).flip
    have hd2 : Disj i (memW s (globN s "bo" + 56), 128) := by
      unfold blockOutObjects at hpw_bo hi
      dsimp only at hpw_bo hi
      rw [List.pairwise_append] at hpw_bo
      obtain ⟨hpw_top4, _, hcross_top4_72⟩ := hpw_bo
      rw [List.pairwise_append] at hpw_top4
      obtain ⟨hpw_top3, _, hcross_top3_40⟩ := hpw_top4
      have h56_top3 : (memW s (globN s "bo" + 56), 128) ∈
          [if globN s "bo" = 0 ∨ memW s (globN s "bo" + 24) = 0 ∨ 16 * memW s (globN s "bo" + 80) + 16 = 0 then (0, 0)
           else (memW s (globN s "bo" + 24), 16 * memW s (globN s "bo" + 80) + 16),
           if globN s "bo" = 0 ∨ memW s (globN s "bo" + 32) = 0 ∨ 16 * memW s (globN s "bo" + 80) + 16 = 0 then (0, 0)
           else (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16),
           if globN s "bo" = 0 ∨ memW s (globN s "bo" + 56) = 0 ∨ 128 = 0 then (0, 0)
           else (memW s (globN s "bo" + 56), 128)] := by simp [hbo, h56]
      rcases List.mem_append.1 hi with hi4 | hi72
      · rcases List.mem_append.1 hi4 with htop3 | hi40
        · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false] at hpw_top3 htop3
          rcases htop3 with rfl | rfl | rfl
          · exact hpw_top3.1 _ (Or.inr (by simp [hbo, h56]))
          · exact hpw_top3.2.1 _ (by simp [hbo, h56])
          · simp [hbo, h56] at hi24
        · exact (hcross_top3_40 _ h56_top3 i hi40).flip
      · exact (hcross_top4_72 _ (List.mem_append_left _ h56_top3) i hi72).flip
    exact ⟨hd1, hd2⟩
  · intro i hi
    exact ⟨(hcross_bal _ (List.mem_append_left _ hbo_in12) i hi).flip,
           (hcross_bal _ (List.mem_append_right _ h56_bo) i hi).flip⟩
  · intro o ho
    exact ⟨(hTr.2.1 o ho).2 _ hbo_fo, (hTr.2.1 o ho).2 _ h56_fo⟩

private theorem ivlUnhit_of_two_disj {F : Type} {s s3 post : PanSemStateFiniteExact 64 F}
    {i : Ivl} {a1 a2 a3 : BitVec 64}
    (hAs : ArenaReady s) (hal : i = (0, 0) ∨ (i.2 ≠ 0 ∧ Allocated s i))
    (heff03 : HeapByteEff s s3 [] ["heap_ptr"])
    (hmem_post : ∀ a : BitVec 64, a ≠ a1 → a ≠ a2 → a ≠ a3 → post.memory a = s3.memory a)
    (hc1 : (globN s "bo" ≤ a1.toNat ∧ a1.toNat + 8 ≤ globN s "bo" + 88) ∨
           (memW s (globN s "bo" + 56) ≤ a1.toNat ∧ a1.toNat + 8 ≤ memW s (globN s "bo" + 56) + 128))
    (hc2 : (globN s "bo" ≤ a2.toNat ∧ a2.toNat + 8 ≤ globN s "bo" + 88) ∨
           (memW s (globN s "bo" + 56) ≤ a2.toNat ∧ a2.toNat + 8 ≤ memW s (globN s "bo" + 56) + 128))
    (hc3 : (globN s "bo" ≤ a3.toNat ∧ a3.toNat + 8 ≤ globN s "bo" + 88) ∨
           (memW s (globN s "bo" + 56) ≤ a3.toNat ∧ a3.toNat + 8 ≤ memW s (globN s "bo" + 56) + 128))
    (hd_bo : Disj i (globN s "bo", 88))
    (hd_56 : Disj i (memW s (globN s "bo" + 56), 128)) :
    R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post i := by
  intro a ha8 hhit
  rcases hal with rfl | ⟨hnz, hal_i⟩
  · unfold CellHits at hhit; omega
  · have hno_hit : ∀ x : BitVec 64,
        ((globN s "bo" ≤ x.toNat ∧ x.toNat + 8 ≤ globN s "bo" + 88) ∨
         (memW s (globN s "bo" + 56) ≤ x.toNat ∧ x.toNat + 8 ≤ memW s (globN s "bo" + 56) + 128)) →
        a ≠ x := by
      rintro x (⟨hx1, hx2⟩ | ⟨hx1, hx2⟩) rfl
      · unfold CellHits at hhit
        rcases hd_bo with d | d | d | d <;> omega
      · unfold CellHits at hhit
        rcases hd_56 with d | d | d | d <;> omega
    rw [hmem_post a (hno_hit a1 hc1) (hno_hit a2 hc2) (hno_hit a3 hc3)]
    by_contra hne3
    rcases i with ⟨i1, i2⟩
    have hsep : heapLimit = scratchStart := rfl
    obtain ⟨_, hs_hp, hs_fm, hs_sc, _⟩ := hAs.2
    rcases heff03.cell_frame a hne3 with ⟨_, hx, _⟩ | ⟨_, hfg⟩ | ⟨_, hhf⟩
    · cases hx
    · dsimp only [CellHits, freeGap] at hhit hfg
      rcases hal_i with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ <;> (dsimp only [Inside] at hlo hhi; omega)
    · dsimp only [CellHits, heapFree] at hhit hhf
      rcases hal_i with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ <;> (dsimp only [Inside] at hlo hhi; omega)

theorem «wk_requests_append» :
    WorldKeeps ReqRoom (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 72, 80])]
    ReqCountInc (ofString "requests_append") := by
  refine ⟨_, _, _, lookup_requests_append, fun {F} s hcode ⟨hW, hroom⟩ hparams hnt hres => ?_⟩
  have hAR : ArenaReady s := hW.1
  have hsb_val : sourceBase = 2701131776 := rfl
  have hhl_val : heapLimit = 2952790016 := rfl
  have hhe_val : heapEnd = 33806089704 := heapEnd_val
  obtain ⟨vals, hl_ra⟩ := hparams
  obtain ⟨tb, data0, n0, _, htb, hdata, hn0⟩ :=
    R13Shards.Keccak256.lookupCode_three_words (by decide) (by decide) (by decide)
      lookup_requests_append hl_ra
  set rest1 : ProgHOL 64 :=
    .seq (.storeByte (.var .local (ofString "blob")) (.var .local (ofString "type_byte")))
      (.seq (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "blob"), .const 1],
           .var .local (ofString "data"),
           .var .local (ofString "n")])
        (.dec (ofString "k") .one
          (.load .one (.op .add [.var .global (ofString "bo"), .const 64]))
          (.seq (.store
              (.op .add
                [.load .one (.op .add [.var .global (ofString "bo"), .const 56]),
                 .panop .mul [.var .local (ofString "k"), .const 16]])
              (.var .local (ofString "blob")))
            (.seq (.store
                (.op .add
                  [.load .one (.op .add [.var .global (ofString "bo"), .const 56]),
                   .panop .mul [.var .local (ofString "k"), .const 16],
                   .const 8])
                (.op .add [.var .local (ofString "n"), .const 1]))
              (.seq (.store
                  (.op .add [.var .global (ofString "bo"), .const 64])
                  (.op .add [.var .local (ofString "k"), .const 1]))
                (.return (.const 0)))))))
  have hbody : sourceFnBody Guest.Software.guestFn_requests_append =
      .decCall (ofString "blob") .one (ofString "alloc")
        [.op .add [.var .local (ofString "n"), .const 8]] rest1 := rfl
  rcases hrun_all : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_requests_append) with ⟨r_out, post⟩
  rw [hrun_all] at hnt hres
  rw [hbody] at hrun_all
  -- Step 1: `var 1 blob = alloc(n + 8)`
  have hnt_step1 : (evaluateHOLFiniteState s
      (.decCall (ofString "blob") .one (ofString "alloc")
        [.op .add [.var .local (ofString "n"), .const 8]] rest1)).1 ≠ some .timeOut := by
    rw [hrun_all]; exact hnt
  have hres_step1 : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString "blob") .one (ofString "alloc")
        [.op .add [.var .local (ofString "n"), .const 8]] rest1)).1 := by
    rw [hrun_all]; exact hres
  obtain ⟨blob, n_arg, q, s1, hn_arg_ev, hblob_hp, hblob8, hq_nat, hpq, hq_hi, hq8, hs1_hp, hs1_g, hs1_m, hs1_loc,
      heff01, hnt1, hres1, heq1⟩ :=
    eval_decCall_alloc_resumes s "blob" (.op .add [.var .local (ofString "n"), .const 8]) rest1
      [] ["heap_ptr"] hcode hAR (by simp) hnt_step1 hres_step1
  have hn_arg_eq : n_arg = n0 + 8 := by
    simp only [evalHOLExact, evalListHOLExact, hn0, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr] at hn_arg_ev
    injection hn_arg_ev with h'; injection h' with h''; injection h'' with h'''
    simpa [BitVec.add_zero] using h'''.symm
  subst hn_arg_eq
  rw [heq1] at hrun_all
  have hs1_blob : s1.locals.lookup (ofString "blob") = some (.val (.word blob)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_tb : s1.locals.lookup (ofString "type_byte") = some (.val (.word tb)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, htb,
      show ofString "blob" ≠ ofString "type_byte" by decide]
  have hs1_data : s1.locals.lookup (ofString "data") = some (.val (.word data0)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hdata,
      show ofString "blob" ≠ ofString "data" by decide]
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word n0)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hn0,
      show ofString "blob" ≠ ofString "n" by decide]
  -- Step 2: `storeByte blob type_byte`
  rw [evaluateHOLFiniteState_seq_line780] at hnt1 hres1 hrun_all
  rcases hsb2 : evaluateHOLFiniteState s1
      (.storeByte (.var .local (ofString "blob")) (.var .local (ofString "type_byte"))) with ⟨r2, s2⟩
  have h2_or := storeByte_none_or_err s1 (.var .local (ofString "blob")) (.var .local (ofString "type_byte"))
  rw [hsb2] at h2_or hnt1 hres1 hrun_all
  rcases h2_or with ⟨rfl, hs2_loc, hs2_g⟩ | hr2_err
  swap
  · dsimp only at hr2_err; subst hr2_err; exact False.elim (not_resumes_error hres1)
  dsimp only at hnt1 hres1 hrun_all hs2_loc hs2_g
  have hb_sb := R13Shards.Keccak256.byteEff_storeByte (Rl := [(blob.toNat, 1)]) heff01.arena.1
    (.var .local (ofString "blob")) (.var .local (ofString "type_byte"))
    (fun x hx _ => by
      simp [evalHOLExact, hs1_blob] at hx; subst hx
      exact ⟨(blob.toNat, 1), List.mem_singleton.2 rfl, le_rfl, by omega⟩)
  rw [hsb2] at hb_sb
  have heff12_b : HeapByteEff s1 s2 [(blob.toNat, 1)] [] := HeapByteEff.of_byteEff heff01.arena hb_sb.1
  -- Step 3: `memcpy(blob + 1, data, n)`
  rw [evaluateHOLFiniteState_seq_line780] at hnt1 hres1 hrun_all
  rcases hmc3 : evaluateHOLFiniteState s2
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "blob"), .const 1],
         .var .local (ofString "data"),
         .var .local (ofString "n")]) with ⟨r3, s3⟩
  have hnt_mc3 : r3 ≠ some .timeOut := by rintro rfl; rw [hmc3] at hnt1; exact hnt1 rfl
  have hs2_blob : s2.locals.lookup (ofString "blob") = some (.val (.word blob)) := hs2_loc ▸ hs1_blob
  have hs2_data : s2.locals.lookup (ofString "data") = some (.val (.word data0)) := hs2_loc ▸ hs1_data
  have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word n0)) := hs2_loc ▸ hs1_n
  have hdst3_ev : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
      (.op .add [.var .local (ofString "blob"), .const 1]) = some (.val (.word (blob + 1))) := by
    simp [evalHOLExact, evalListHOLExact, hs2_blob, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero]
  have hmc_step := eval_call_memcpy_resumes s2
    (.op .add [.var .local (ofString "blob"), .const 1])
    (.var .local (ofString "data")) (.var .local (ofString "n"))
    (blob + 1) data0 n0 heff12_b.arena.1.code heff12_b.arena hdst3_ev hs2_data hs2_n
    (by rw [hmc3]; exact hnt_mc3)
  dsimp only at hmc_step
  rw [hmc3] at hmc_step hnt1 hres1 hrun_all
  cases r3 with
  | some r3' =>
    exfalso; exact hmc_step.2 (by simp) hres1
  | none =>
    dsimp only at hnt1 hres1 hrun_all
    obtain ⟨hn0_dom, heff23_b, hs3_loc, hs3_g⟩ := hmc_step.1 rfl
    have hblob1_nat : (blob + 1).toNat = blob.toNat + 1 := by
      rw [BitVec.toNat_add]; change (blob.toNat + 1) % 2 ^ 64 = _
      exact Nat.mod_eq_of_lt (by omega)
    have hn0_nowrap : (n0 + 8).toNat = n0.toNat + 8 := by
      by_cases hpos : 0 < n0.toNat
      · have hle := (hn0_dom hpos).2
        rw [hblob1_nat, hhe_val] at hle
        rw [BitVec.toNat_add]; change (n0.toNat + 8) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt (by omega)
      · have hz : n0.toNat = 0 := by omega
        rw [BitVec.toNat_add]; change (n0.toNat + 8) % 2 ^ 64 = _
        omega
    rw [hn0_nowrap] at hpq
    -- Now `blob.toNat + n0.toNat + 8 ≤ q.toNat ≤ heapLimit`!
    -- Therefore BOTH `(blob.toNat, 1)` and `((blob + 1).toNat, n0.toNat)` lie inside `heapFree s`!
    have hs1_hp_le : globN s "heap_ptr" ≤ blob.toNat := by omega
    have heff03 : HeapByteEff s s3 [] ["heap_ptr"] := by
      have h12' : HeapByteEff s1 s2 [(blob.toNat, n0.toNat + 8)] ["heap_ptr"] :=
        heff12_b.mono (fun i hi _ => by
          simp at hi; subst hi
          exact Or.inl ⟨(blob.toNat, n0.toNat + 8), List.mem_singleton.2 rfl, le_rfl, by omega⟩) (by simp)
      have h23' : HeapByteEff s2 s3 [(blob.toNat, n0.toNat + 8)] ["heap_ptr"] :=
        heff23_b.mono (fun i hi _ => by
          simp at hi; subst hi
          exact Or.inl ⟨(blob.toNat, n0.toNat + 8), List.mem_singleton.2 rfl, by omega, by omega⟩) (by simp)
      have h01' : HeapByteEff s s1 [(blob.toNat, n0.toNat + 8)] ["heap_ptr"] :=
        heff01.mono (fun _ h => by cases h) (fun _ h => h)
      exact ((h01'.trans h12').trans h23').mono
        (fun i hi _ => by
          simp at hi; subst hi
          exact Or.inr (Or.inr ⟨by omega, by omega⟩))
        (fun _ h => h)
    -- Witness typing `(S0, Nd0)` from `hW`:
    obtain ⟨S0, hWT0_ex⟩ := hW.2
    obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
    -- Look up global `"bo"` in `s` (preserved in `s3`):
    obtain ⟨bow, hbow_s⟩ := hAR.2.2.2.2.2.2.2.2.2 "bo" (by decide)
    have hbow_nat : bow.toNat = globN s "bo" := by unfold GlobalWord at hbow_s; simp [globN, hbow_s]
    have hs3_bo_lookup : s3.globals.lookup (ofString "bo") = some (.val (.word bow)) := by
      unfold GlobalWord at hbow_s
      rw [hs3_g, hs2_g, hs1_g]
      simp [HolFiniteMapExact.lookup_update, FUPDATE, hbow_s,
        show ofString "heap_ptr" ≠ ofString "bo" by decide]
    -- Step 4: `var k = load(bo + 64)`
    have hbo64_ev : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
        (.op .add [.var .global (ofString "bo"), .const 64]) = some (.val (.word (bow + 64))) := by
      simp [evalHOLExact, evalListHOLExact, hs3_bo_lookup, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero]
    obtain ⟨kw, hbo64_8, hbo64_lo, hbo64_hi, hs3_mem64, hkw_mw3, hload64_ev⟩ :=
      eval_load_word_resumes s3 "k" (.op .add [.var .global (ofString "bo"), .const 64]) _
        (bow + 64) heff03.arena.1.memaddrs hbo64_ev hres1
    have hbo_nz : globN s "bo" ≠ 0 := by
      intro hz
      have hb0 : bow = 0 := BitVec.eq_of_toNat_eq (by rw [hbow_nat, hz]; rfl)
      subst hb0
      have : ((0 : BitVec 64) + 64).toNat = 64 := by decide
      rw [this, hsb_val] at hbo64_lo; omega
    -- `(globN s "bo", 88)` is allocated in `s`:
    have hbo_fo0 : (globN s "bo", 88) ∈ fixedObjects s := by
      have := M13.typedRec_in_fixedObjects s (g := "bo") (sz := 88) (by decide)
      simpa [hbo_nz] using this
    obtain ⟨hal_bo, hw_bo⟩ : Allocated s (globN s "bo", 88) ∧ WordsOK s (globN s "bo", 88) := by
      rcases hWT0.2.2.1.1 _ hbo_fo0 with h0 | hok
      · simp at h0
      · exact hok
    have hbo_bound := R10Shards.Fast_GbodyC17ToC21.ivl_allocated_bound hAR.2 hal_bo
    have hbow64_nat : (bow + 64).toNat = globN s "bo" + 64 := by
      rw [BitVec.toNat_add, hbow_nat]; change (globN s "bo" + 64) % 2 ^ 64 = _
      exact Nat.mod_eq_of_lt (by omega)
    have hbo_unhit03 : R10Shards.Fast_GbodyC17ToC21.IvlUnhit s s3 (globN s "bo", 88) := by
      intro a _ hhit
      by_contra hne
      have hsep : heapLimit = scratchStart := rfl
      obtain ⟨_, hs_hp, hs_fm, hs_sc, _⟩ := hAR.2
      rcases heff03.cell_frame a hne with ⟨_, hx, _⟩ | ⟨_, hfg⟩ | ⟨_, hhf⟩
      · cases hx
      · dsimp only [CellHits, freeGap] at hhit hfg
        rcases hal_bo with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ <;> (dsimp only [Inside] at hlo hhi; omega)
      · dsimp only [CellHits, heapFree] at hhit hhf
        rcases hal_bo with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ <;> (dsimp only [Inside] at hlo hhi; omega)
    have hkw_eq : kw.toNat = memW s (globN s "bo" + 64) := by
      rw [hkw_mw3, hbow64_nat]
      exact R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit hbo_unhit03
        (by have := hw_bo.1; omega) hbo_bound.2 ⟨by omega, by omega⟩
    have hkw_lt8 : kw.toNat < 8 := by rw [hkw_eq]; exact hroom
    -- Step through `.dec "k"`
    rw [evaluateHOLFiniteState_dec_total] at hnt1 hres1 hrun_all
    dsimp only at hnt1 hres1 hrun_all
    have hsh_kw : shapeEqHOL .one (shapeOfHOLExact (.val (.word kw) : ValueHOL 64)) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [hload64_ev] at hnt1 hres1 hrun_all; dsimp only at hnt1 hres1 hrun_all
    rw [if_pos hsh_kw] at hnt1 hres1 hrun_all; dsimp only at hnt1 hres1 hrun_all
    set s4 := setVarHOLFinite (ofString "k") (.val (.word kw)) s3
    have hs4_k : s4.locals.lookup (ofString "k") = some (.val (.word kw)) := by
      simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs4_blob : s4.locals.lookup (ofString "blob") = some (.val (.word blob)) := by
      have hs3_b : s3.locals.lookup (ofString "blob") = some (.val (.word blob)) := by
        dsimp only at hs3_loc; rw [hs3_loc]; exact hs2_blob
      simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_b,
        show ofString "k" ≠ ofString "blob" by decide]
    have hs4_n : s4.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      have hs3_n : s3.locals.lookup (ofString "n") = some (.val (.word n0)) := by
        dsimp only at hs3_loc; rw [hs3_loc]; exact hs2_n
      simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_n,
        show ofString "k" ≠ ofString "n" by decide]
    -- Step 5: `store (load(bo + 56) + k * 16) blob`
    have hbo56_ev4 : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
        (.op .add [.var .global (ofString "bo"), .const 56]) = some (.val (.word (bow + 56))) := by
      simp [evalHOLExact, evalListHOLExact, s4, setVarHOLFinite, hs3_bo_lookup,
        wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero]
    obtain ⟨arrw, _, _, _, hs4_mem56, harrw_mw4, hload56_ev4⟩ :=
      eval_load_in_store_dst_resumes s4 (.op .add [.var .global (ofString "bo"), .const 56])
        [.panop .mul [.var .local (ofString "k"), .const 16]]
        (.var .local (ofString "blob")) _ (bow + 56) heff03.arena.1.memaddrs hbo56_ev4 hres1
    have hbow56_nat : (bow + 56).toNat = globN s "bo" + 56 := by
      rw [BitVec.toNat_add, hbow_nat]; change (globN s "bo" + 56) % 2 ^ 64 = _
      exact Nat.mod_eq_of_lt (by omega)
    have harrw_eq : arrw.toNat = memW s (globN s "bo" + 56) := by
      have hm43 : memW s4 (bow + 56).toNat = memW s3 (bow + 56).toNat := rfl
      rw [harrw_mw4, hm43, hbow56_nat]
      exact R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit hbo_unhit03
        (by have := hw_bo.1; omega) hbo_bound.2 ⟨by omega, by omega⟩
    have hkmul_ev4 : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
        (.panop .mul [.var .local (ofString "k"), .const 16]) = some (.val (.word (kw * 16))) := by
      simp [evalHOLExact, evalListHOLExact, hs4_k, panOpHOL, valueIsWord, valueWord]
    have hdst5_ev : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
        (.op .add [.load .one (.op .add [.var .global (ofString "bo"), .const 56]),
                   .panop .mul [.var .local (ofString "k"), .const 16]]) =
        some (.val (.word (arrw + kw * 16))) := by
      have hl5 : @evalListHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
          [.load .one (.op .add [.var .global (ofString "bo"), .const 56]),
           .panop .mul [.var .local (ofString "k"), .const 16]] =
          some [.val (.word arrw), .val (.word (kw * 16))] := by
        unfold evalListHOLExact
        rw [hload56_ev4]
        unfold evalListHOLExact
        rw [hkmul_ev4]
        rfl
      unfold evalHOLExact
      rw [hl5]
      simp [wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero]
    obtain ⟨_, harr_lo, _, hst5_eq⟩ :=
      eval_store_word_resumes s4 _ (.var .local (ofString "blob")) _ (arrw + kw * 16) blob
        heff03.arena.1.memaddrs hdst5_ev hs4_blob hres1
    have hkw16_nat : (kw * 16).toNat = kw.toNat * 16 := by
      rw [BitVec.toNat_mul]; change (kw.toNat * 16) % 2 ^ 64 = _
      exact Nat.mod_eq_of_lt (by omega)
    have h56_nz : memW s (globN s "bo" + 56) ≠ 0 := by
      intro hz
      have ha0 : arrw = 0 := BitVec.eq_of_toNat_eq (by rw [harrw_eq, hz]; rfl)
      subst ha0
      have h0_add : ((0 : BitVec 64) + kw * 16) = kw * 16 := BitVec.zero_add _
      rw [h0_add, hkw16_nat, hsb_val] at harr_lo; omega
    -- `(memW s (globN s "bo" + 56), 128)` is allocated in `s`, disjoint from `(globN s "bo", 88)`:
    have h56_fo0 : (memW s (globN s "bo" + 56), 128) ∈ fixedObjects s :=
      M13.blockOut_in_fixedObjects (by unfold blockOutObjects; simp [hbo_nz, h56_nz])
    obtain ⟨hal_56, hw_56⟩ : Allocated s (memW s (globN s "bo" + 56), 128) ∧
        WordsOK s (memW s (globN s "bo" + 56), 128) := by
      rcases hWT0.2.2.1.1 _ h56_fo0 with h0 | hok
      · simp at h0
      · exact hok
    have h56_bound := R10Shards.Fast_GbodyC17ToC21.ivl_allocated_bound hAR.2 hal_56
    have hd_bo_56 := (ivl_disj_bo_and_arr56 hWT0 hbo_nz h56_nz).1
    have ha1_nat : (arrw + kw * 16).toNat = memW s (globN s "bo" + 56) + kw.toNat * 16 := by
      rw [BitVec.toNat_add, harrw_eq, hkw16_nat, Nat.mod_eq_of_lt (by omega)]
    rw [evaluateHOLFiniteState_seq_line780, hst5_eq] at hnt1 hres1 hrun_all
    dsimp only at hnt1 hres1 hrun_all
    set s5 : PanSemStateFiniteExact 64 F :=
      { s4 with memory := fun a => if a = arrw + kw * 16 then .word blob else s4.memory a }
    -- Note `bow + 56 ≠ arrw + kw * 16` because `(bo, 88)` and `(arr56, 128)` are disjoint!
    have h56_ne_a1 : bow + 56 ≠ arrw + kw * 16 := by
      intro heq
      have hnat := congrArg BitVec.toNat heq
      rw [hbow56_nat, ha1_nat] at hnat
      rcases hd_bo_56 with d | d | d | d <;> (dsimp only at *; omega)
    have hload56_ev5 : @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a))
        (.load .one (.op .add [.var .global (ofString "bo"), .const 56])) = some (.val (.word arrw)) := by
      have ha5 : @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a))
          (.op .add [.var .global (ofString "bo"), .const 56]) = some (.val (.word (bow + 56))) := hbo56_ev4
      have hdom56 : s5.memaddrs (bow + 56) := by
        rw [show s5.memaddrs = ordinaryDomain from heff03.arena.1.memaddrs,
          R10Shards.Fast_GbodyC17ToC21.ordinaryDomain_iff]
        refine ⟨by rw [hbow56_nat]; have := hw_bo.1; omega, ?_,
          by rw [hbow56_nat]; have := hbo_bound.1; omega⟩
        rw [hbow56_nat]
        rcases hal_bo with ⟨h, _⟩ | ⟨h, _⟩
        · dsimp only [Inside] at h; omega
        · dsimp only [Inside] at h
          have := hAR.2.1; have := hAR.2.2.1; have : heapLimit = scratchStart := rfl; omega
      have hm5 : s5.memory (bow + 56) = .word arrw := by
        change (if bow + 56 = arrw + kw * 16 then .word blob else s4.memory (bow + 56)) = .word arrw
        rw [if_neg h56_ne_a1]
        exact hs4_mem56
      unfold evalHOLExact
      rw [ha5]
      have hdom56' : s5.memaddrs (bow + 56#64) := hdom56
      have hm5' : s5.memory (bow + 56#64) = .word arrw := hm5
      simp [memLoadHOLExact, hdom56', hm5']
    -- Step 6: `store (load(bo + 56) + k * 16 + 8) (n + 1)`
    have hdst6_ev : @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a))
        (.op .add [.load .one (.op .add [.var .global (ofString "bo"), .const 56]),
                   .panop .mul [.var .local (ofString "k"), .const 16],
                   .const 8]) =
        some (.val (.word (arrw + (kw * 16 + 8)))) := by
      have hkmul5 : @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a))
          (.panop .mul [.var .local (ofString "k"), .const 16]) = some (.val (.word (kw * 16))) := hkmul_ev4
      have hl6 : @evalListHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a))
          [.load .one (.op .add [.var .global (ofString "bo"), .const 56]),
           .panop .mul [.var .local (ofString "k"), .const 16],
           .const 8] =
          some [.val (.word arrw), .val (.word (kw * 16)), .val (.word 8)] := by
        unfold evalListHOLExact
        rw [hload56_ev5]
        unfold evalListHOLExact
        rw [hkmul5]
        simp [evalListHOLExact, evalHOLExact]
      unfold evalHOLExact
      rw [hl6]
      simp [wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero]
    have hval6_ev : @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a))
        (.op .add [.var .local (ofString "n"), .const 1]) = some (.val (.word (n0 + 1))) := by
      have hn5 : s5.locals.lookup (ofString "n") = some (.val (.word n0)) := hs4_n
      simp [evalHOLExact, evalListHOLExact, hn5, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero]
    obtain ⟨_, _, _, hst6_eq⟩ :=
      eval_store_word_resumes s5 _ _ _ (arrw + (kw * 16 + 8)) (n0 + 1)
        heff03.arena.1.memaddrs hdst6_ev hval6_ev hres1
    have ha2_nat : (arrw + (kw * 16 + 8)).toNat = memW s (globN s "bo" + 56) + kw.toNat * 16 + 8 := by
      have hk16_8 : (kw * 16 + 8).toNat = kw.toNat * 16 + 8 := by
        rw [BitVec.toNat_add, hkw16_nat]; change (kw.toNat * 16 + 8) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt (by omega)
      rw [BitVec.toNat_add, harrw_eq, hk16_8, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [evaluateHOLFiniteState_seq_line780, hst6_eq] at hnt1 hres1 hrun_all
    dsimp only at hnt1 hres1 hrun_all
    set s6 : PanSemStateFiniteExact 64 F :=
      { s5 with memory := fun a => if a = arrw + (kw * 16 + 8) then .word (n0 + 1) else s5.memory a }
    -- Step 7: `store (bo + 64) (k + 1)`
    have hdst7_ev : @evalHOLExact 64 F _ s6.toExact (fun a => Classical.propDecidable (s6.memaddrs a))
        (.op .add [.var .global (ofString "bo"), .const 64]) = some (.val (.word (bow + 64))) := hbo64_ev
    have hval7_ev : @evalHOLExact 64 F _ s6.toExact (fun a => Classical.propDecidable (s6.memaddrs a))
        (.op .add [.var .local (ofString "k"), .const 1]) = some (.val (.word (kw + 1))) := by
      have hk6 : s6.locals.lookup (ofString "k") = some (.val (.word kw)) := hs4_k
      simp [evalHOLExact, evalListHOLExact, hk6, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero]
    obtain ⟨_, _, _, hst7_eq⟩ :=
      eval_store_word_resumes s6 _ _ _ (bow + 64) (kw + 1)
        heff03.arena.1.memaddrs hdst7_ev hval7_ev hres1
    rw [evaluateHOLFiniteState_seq_line780, hst7_eq] at hrun_all
    dsimp only at hrun_all
    set s7 : PanSemStateFiniteExact 64 F :=
      { s6 with memory := fun a => if a = bow + 64 then .word (kw + 1) else s6.memory a }
    -- Step 8: `return 0`
    have hret8 : evaluateHOLFiniteState s7 (.return (.const 0)) =
        (some (.returned (.val (.word 0))), emptyLocalsHOLFinite s7) := by
      rw [evaluateHOLFiniteState_return]
      simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [hret8] at hrun_all
    dsimp only at hrun_all
    obtain ⟨rfl, hpost_eq⟩ := Prod.mk.inj hrun_all
    -- Summarize `post` vs `s3`:
    have hpost_mem : post.memory = s7.memory := by
      rw [← hpost_eq]; rfl
    have hpost_g : post.globals = s3.globals := by
      rw [← hpost_eq]; simp [emptyLocalsHOLFinite, s7, s6, s5, s4, setVarHOLFinite]
    have hpost_be : post.be = s.be := by
      rw [← hpost_eq]; dsimp [emptyLocalsHOLFinite, s7, s6, s5, s4, setVarHOLFinite]; exact heff03.be
    have hpost_AR : ArenaReady post := by
      have hGp : GuestInv post := by
        rw [← hpost_eq]
        exact guestInv_congr (s := s3) rfl rfl rfl rfl heff03.arena.1
      exact ⟨hGp, arenaOK_congr hpost_g heff03.arena.2⟩
    have hpost_hp : globN s "heap_ptr" ≤ globN post "heap_ptr" := by
      have : globN post "heap_ptr" = globN s3 "heap_ptr" := by simp [globN, hpost_g]
      rw [this]; exact heff03.hp_le
    have hpost_gk : GlobalsKept ["heap_ptr"] s post := by
      intro k hk; rw [hpost_g]; exact heff03.globals k hk
    have hmem_p_s3 : ∀ a : BitVec 64,
        a ≠ arrw + kw * 16 → a ≠ arrw + (kw * 16 + 8) → a ≠ bow + 64 →
        post.memory a = s3.memory a := by
      intro a h1 h2 h3
      rw [hpost_mem]
      change (if a = bow + 64 then .word (kw + 1)
        else if a = arrw + (kw * 16 + 8) then .word (n0 + 1)
        else if a = arrw + kw * 16 then .word blob
        else s3.memory a) = s3.memory a
      rw [if_neg h3, if_neg h2, if_neg h1]
    have hc_a1 : (globN s "bo" ≤ (arrw + kw * 16).toNat ∧ (arrw + kw * 16).toNat + 8 ≤ globN s "bo" + 88) ∨
        (memW s (globN s "bo" + 56) ≤ (arrw + kw * 16).toNat ∧
         (arrw + kw * 16).toNat + 8 ≤ memW s (globN s "bo" + 56) + 128) :=
      Or.inr ⟨by rw [ha1_nat]; omega, by rw [ha1_nat]; omega⟩
    have hc_a2 : (globN s "bo" ≤ (arrw + (kw * 16 + 8)).toNat ∧ (arrw + (kw * 16 + 8)).toNat + 8 ≤ globN s "bo" + 88) ∨
        (memW s (globN s "bo" + 56) ≤ (arrw + (kw * 16 + 8)).toNat ∧
         (arrw + (kw * 16 + 8)).toNat + 8 ≤ memW s (globN s "bo" + 56) + 128) :=
      Or.inr ⟨by rw [ha2_nat]; omega, by rw [ha2_nat]; omega⟩
    have hc_a3 : (globN s "bo" ≤ (bow + 64).toNat ∧ (bow + 64).toNat + 8 ≤ globN s "bo" + 88) ∨
        (memW s (globN s "bo" + 56) ≤ (bow + 64).toNat ∧
         (bow + 64).toNat + 8 ≤ memW s (globN s "bo" + 56) + 128) :=
      Or.inl ⟨by rw [hbow64_nat]; omega, by rw [hbow64_nat]; omega⟩
    -- Prove `bo` word preservation at any offset `k ≠ 64` with `k + 8 ≤ 88, k % 8 = 0`:
    have hbo_word_keep : ∀ k : Nat, k % 8 = 0 → k + 8 ≤ 88 → k ≠ 64 →
        memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := by
      intro k hk8 hkle hkne
      have hak_lt : globN s "bo" + k < 2 ^ 64 := by omega
      let ak := BitVec.ofNat 64 (globN s "bo" + k)
      have hak_nat : ak.toNat = globN s "bo" + k := Nat.mod_eq_of_lt hak_lt
      have hne1 : ak ≠ arrw + kw * 16 := by
        intro heq; have h := congrArg BitVec.toNat heq; rw [hak_nat, ha1_nat] at h
        rcases hd_bo_56 with d | d | d | d <;> (dsimp only at *; omega)
      have hne2 : ak ≠ arrw + (kw * 16 + 8) := by
        intro heq; have h := congrArg BitVec.toNat heq; rw [hak_nat, ha2_nat] at h
        rcases hd_bo_56 with d | d | d | d <;> (dsimp only at *; omega)
      have hne3 : ak ≠ bow + 64 := by
        intro heq; have h := congrArg BitVec.toNat heq; rw [hak_nat, hbow64_nat] at h; omega
      have hm_ps3 : post.memory ak = s3.memory ak := hmem_p_s3 ak hne1 hne2 hne3
      have hm_s3s : s3.memory ak = s.memory ak :=
        hbo_unhit03 ak (by rw [hak_nat]; have := hw_bo.1; omega)
          (by unfold CellHits; rw [hak_nat]; omega)
      unfold memW; change (match post.memory ak with | .word w => w.toNat) =
        (match s.memory ak with | .word w => w.toNat)
      rw [hm_ps3, hm_s3s]
    -- Prove `RecordsKept`:
    have hRK : RecordsKept (fun _ => [])
        [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
         ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 72, 80])]
        s post := by
      obtain ⟨_, _, hd0_rec, _, _, _, _⟩ := ivl_disj_bo_and_arr56 hWT0 hbo_nz h56_nz
      intro rec hrec hgnz k hk _
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · dsimp only at hgnz hk ⊢
        have hfo := M13.typedRec_in_fixedObjects s (g := "ws") (sz := 40) (by decide)
        simp only [hgnz, ↓reduceIte] at hfo
        rcases hWT0.2.2.1.1 _ hfo with h0 | ⟨hal_r, hw_r⟩
        · simp at h0
        · obtain ⟨hd1, hd2⟩ := hd0_rec "ws" (by simp) 40 (by decide) hgnz
          have hu := ivlUnhit_of_two_disj hAR (Or.inr ⟨show (40 : Nat) ≠ 0 by omega, hal_r⟩)
            heff03 hmem_p_s3 hc_a1 hc_a2 hc_a3 hd1 hd2
          have hbnd := (R10Shards.Fast_GbodyC17ToC21.ivl_allocated_bound hAR.2 hal_r).2
          have hr8 := hw_r.1
          dsimp only at hbnd hr8
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl <;>
            exact R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit hu (by omega) hbnd ⟨by omega, by omega⟩
      · dsimp only at hgnz hk ⊢
        have hfo := M13.typedRec_in_fixedObjects s (g := "bs") (sz := 80) (by decide)
        simp only [hgnz, ↓reduceIte] at hfo
        rcases hWT0.2.2.1.1 _ hfo with h0 | ⟨hal_r, hw_r⟩
        · simp at h0
        · obtain ⟨hd1, hd2⟩ := hd0_rec "bs" (by simp) 80 (by decide) hgnz
          have hu := ivlUnhit_of_two_disj hAR (Or.inr ⟨show (80 : Nat) ≠ 0 by omega, hal_r⟩)
            heff03 hmem_p_s3 hc_a1 hc_a2 hc_a3 hd1 hd2
          have hbnd := (R10Shards.Fast_GbodyC17ToC21.ivl_allocated_bound hAR.2 hal_r).2
          have hr8 := hw_r.1
          dsimp only at hbnd hr8
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit hu (by omega) hbnd ⟨by omega, by omega⟩
      · dsimp only at hgnz hk ⊢
        have hfo := M13.typedRec_in_fixedObjects s (g := "ts") (sz := 72) (by decide)
        simp only [hgnz, ↓reduceIte] at hfo
        rcases hWT0.2.2.1.1 _ hfo with h0 | ⟨hal_r, hw_r⟩
        · simp at h0
        · obtain ⟨hd1, hd2⟩ := hd0_rec "ts" (by simp) 72 (by decide) hgnz
          have hu := ivlUnhit_of_two_disj hAR (Or.inr ⟨show (72 : Nat) ≠ 0 by omega, hal_r⟩)
            heff03 hmem_p_s3 hc_a1 hc_a2 hc_a3 hd1 hd2
          have hbnd := (R10Shards.Fast_GbodyC17ToC21.ivl_allocated_bound hAR.2 hal_r).2
          have hr8 := hw_r.1
          dsimp only at hbnd hr8
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit hu (by omega) hbnd ⟨by omega, by omega⟩
      · dsimp only at hk ⊢
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact hbo_word_keep _ (by omega) (by omega) (by omega)
    -- Prove `ReqCountInc`:
    have hReqInc : memW post (globN s "bo" + 64) = memW s (globN s "bo" + 64) + 1 := by
      have hb64 : BitVec.ofNat 64 (globN s "bo" + 64) = bow + 64 :=
        BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, hbow64_nat, Nat.mod_eq_of_lt (by omega)])
      have hmp : memW post (globN s "bo" + 64) = (kw + 1).toNat := by
        unfold memW
        rw [hb64, hpost_mem]
        have hm7 : s7.memory (bow + 64) = .word (kw + 1) := by simp [s7]
        rw [hm7]
      rw [hmp, ← hkw_eq, BitVec.toNat_add]
      change (kw.toNat + 1) % 2 ^ 64 = kw.toNat + 1
      exact Nat.mod_eq_of_lt (by omega)
    -- Assemble `WorldStep`:
    refine ⟨hpost_AR, hpost_hp, hpost_gk, hRK, fun S Nd hWT _ => ?_⟩
    obtain ⟨_, hd_tab, hd_rec, hd_jr, hd_bolst, hd_bal, hd_nd⟩ :=
      ivl_disj_bo_and_arr56 hWT hbo_nz h56_nz
    have hag : AllocatorGrows s post := by
      refine ⟨hpost_hp, ?_⟩
      have : globN post "scratch_ptr" = globN s3 "scratch_ptr" := by simp [globN, hpost_g]
      rw [this]; exact heff03.sp_le
    have hwgs : R10Shards.Fast_GbodyC17ToC21.WorldGlobalsSame s post :=
      R10Shards.Fast_GbodyC17ToC21.worldGlobalsSame_of_globalsKept hpost_gk
        (by intro gn hgn; revert gn hgn; decide)
        (by intro g hg; revert g hg; decide)
        (by decide) (by decide) (by decide)
    have hlow_mem : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 := by
      have hlow_eq : ∀ c : BitVec 64, c.toNat < sourceBase → post.memory c = s.memory c := by
        intro c hc
        have hn1 : c ≠ arrw + kw * 16 := by
          intro h; subst h; rw [ha1_nat] at hc
          rcases hal_56 with ⟨h1, _⟩ | ⟨h1, _⟩
          · omega
          · have := hAR.2.1; have := hAR.2.2.1; have : heapLimit = scratchStart := rfl; omega
        have hn2 : c ≠ arrw + (kw * 16 + 8) := by
          intro h; subst h; rw [ha2_nat] at hc
          rcases hal_56 with ⟨h1, _⟩ | ⟨h1, _⟩
          · omega
          · have := hAR.2.1; have := hAR.2.2.1; have : heapLimit = scratchStart := rfl; omega
        have hn3 : c ≠ bow + 64 := by
          intro h; subst h; rw [hbow64_nat] at hc
          rcases hal_bo with ⟨h1, _⟩ | ⟨h1, _⟩
          · omega
          · have := hAR.2.1; have := hAR.2.2.1; have : heapLimit = scratchStart := rfl; omega
        rw [hmem_p_s3 c hn1 hn2 hn3]
        by_contra hne
        have hdom := (R10Shards.Fast_GbodyC17ToC21.ordinaryDomain_iff c).1
          (hAR.1.memaddrs ▸ heff03.out_dom c hne)
        omega
      unfold memW
      rw [hlow_eq (BitVec.ofNat 64 8) (by rw [hsb_val]; decide),
          hlow_eq (BitVec.ofNat 64 16) (by rw [hsb_val]; decide)]
      exact ⟨rfl, rfl⟩
    have hwo_alloc := R10Shards.Fast_GbodyC17ToC21.worldOwned_zero_or_allocated hWT
    obtain ⟨hWT_post, hwo_eq, _, _, _⟩ :=
      R10Shards.Fast_GbodyC17ToC21.worldTypedWith_congr_bo hAR hpost_AR hpost_be hag hwgs hWT
        (fun t ht i hi => ivlUnhit_of_two_disj hAR
          (hwo_alloc i (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨t, ht, hi⟩))))
          heff03 hmem_p_s3 hc_a1 hc_a2 hc_a3 (hd_tab t ht i hi).1 (hd_tab t ht i hi).2)
        (fun hnz => by
          have hfo := M13.typedRec_in_fixedObjects s (g := "ws") (sz := 40) (by decide)
          simp only [hnz, ↓reduceIte] at hfo
          exact ivlUnhit_of_two_disj hAR
            (hwo_alloc _ (List.mem_append_left _ (List.mem_append_right _ hfo)))
            heff03 hmem_p_s3 hc_a1 hc_a2 hc_a3
            (hd_rec "ws" (by simp) 40 (by decide) hnz).1 (hd_rec "ws" (by simp) 40 (by decide) hnz).2)
        (fun hnz => by
          have hfo := M13.typedRec_in_fixedObjects s (g := "bs") (sz := 80) (by decide)
          simp only [hnz, ↓reduceIte] at hfo
          exact ivlUnhit_of_two_disj hAR
            (hwo_alloc _ (List.mem_append_left _ (List.mem_append_right _ hfo)))
            heff03 hmem_p_s3 hc_a1 hc_a2 hc_a3
            (hd_rec "bs" (by simp) 80 (by decide) hnz).1 (hd_rec "bs" (by simp) 80 (by decide) hnz).2)
        (fun hnz => by
          have hfo := M13.typedRec_in_fixedObjects s (g := "ts") (sz := 72) (by decide)
          simp only [hnz, ↓reduceIte] at hfo
          exact ivlUnhit_of_two_disj hAR
            (hwo_alloc _ (List.mem_append_left _ (List.mem_append_right _ hfo)))
            heff03 hmem_p_s3 hc_a1 hc_a2 hc_a3
            (hd_rec "ts" (by simp) 72 (by decide) hnz).1 (hd_rec "ts" (by simp) 72 (by decide) hnz).2)
        (fun hjc => by
          have hj_fo : (globN s "journal", 32 * globN s "journal_cap") ∈ fixedObjects s := by
            unfold fixedObjects
            apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
            simp [hjc]
          exact ivlUnhit_of_two_disj hAR
            (hwo_alloc _ (List.mem_append_left _ (List.mem_append_right _ hj_fo)))
            heff03 hmem_p_s3 hc_a1 hc_a2 hc_a3 (hd_jr hjc).1 (hd_jr hjc).2)
        (fun i hi hi24 => ivlUnhit_of_two_disj hAR
          (hwo_alloc i (List.mem_append_left _ (List.mem_append_right _ (M13.blockOut_in_fixedObjects hi))))
          heff03 hmem_p_s3 hc_a1 hc_a2 hc_a3 (hd_bolst i hi hi24).1 (hd_bolst i hi hi24).2)
        (fun i hi => by
          have hi_fo : i ∈ fixedObjects s := by
            unfold fixedObjects; exact List.mem_append_right _ hi
          exact ivlUnhit_of_two_disj hAR
            (hwo_alloc i (List.mem_append_left _ (List.mem_append_right _ hi_fo)))
            heff03 hmem_p_s3 hc_a1 hc_a2 hc_a3 (hd_bal i hi).1 (hd_bal i hi).2)
        (fun o ho => ivlUnhit_of_two_disj hAR
          (hwo_alloc o (List.mem_append_right _ ho))
          heff03 hmem_p_s3 hc_a1 hc_a2 hc_a3 (hd_nd o ho).1 (hd_nd o ho).2)
        (fun _ k hk => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact hbo_word_keep _ (by omega) (by omega) (by omega))
        hlow_mem
    refine ⟨S, Nd, fun _ ht => ht, hWT_post, ?_, ?_, hReqInc⟩
    · intro o ho
      rw [hwo_eq] at ho
      exact Or.inr (Or.inl ⟨o, ho, le_rfl, le_rfl⟩)
    · intro a hkeep hhf
      have hbo_wo : (globN s "bo", 88) ∈ worldOwned s S Nd :=
        List.mem_append_left _ (List.mem_append_right _ hbo_fo0)
      have h56_wo : (memW s (globN s "bo" + 56), 128) ∈ worldOwned s S Nd :=
        List.mem_append_left _ (List.mem_append_right _ h56_fo0)
      have hne1 : a ≠ arrw + kw * 16 := by
        rintro rfl
        exact hkeep _ (List.mem_append_left [freeGap s] (List.mem_append_left [] h56_wo))
          ⟨by rw [ha1_nat]; omega, by rw [ha1_nat]; omega⟩
      have hne2 : a ≠ arrw + (kw * 16 + 8) := by
        rintro rfl
        exact hkeep _ (List.mem_append_left [freeGap s] (List.mem_append_left [] h56_wo))
          ⟨by rw [ha2_nat]; omega, by rw [ha2_nat]; omega⟩
      have hne3 : a ≠ bow + 64 := by
        rintro rfl
        exact hkeep _ (List.mem_append_left [freeGap s] (List.mem_append_left [] hbo_wo))
          ⟨by rw [hbow64_nat]; omega, by rw [hbow64_nat]; omega⟩
      rw [hmem_p_s3 a hne1 hne2 hne3]
      by_contra hne
      rcases heff03.cell_frame a hne with ⟨_, hx, _⟩ | ⟨_, hfg⟩ | ⟨_, hchf⟩
      · cases hx
      · exact hkeep (freeGap s) (List.mem_append_right _ List.mem_cons_self) hfg
      · exact hhf hchf


end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
