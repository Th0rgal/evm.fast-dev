import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2Core
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2Invariant
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Compose
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_PtxPhase5

/-! Reusable Hoare and transition primitives for Phase 2 of `process_transaction`. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase2
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString InitE
open InitECandidate.Solver.GuestCodeLookup InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1
open InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.FastPhase5

theorem evalAt_add_panMul {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e1 : ExpHOL 64) (lname : String) (c x : BitVec 64)
    (h : evalAt s (.op .add [e1, .panop .mul [.var .local (ofString lname), .const c]]) =
      some (.val (.word x))) :
    ∃ a b : BitVec 64, evalAt s e1 = some (.val (.word a)) ∧
      s.locals.lookup (ofString lname) = some (.val (.word b)) ∧
      locN s lname = b.toNat ∧ x = a + b * c := by
  rcases h1 : evalAt s e1 with _ | v1
  · simp only [evalAt, evalHOLExact, evalListHOLExact] at h h1; rw [h1] at h; simp at h
  rcases v1 with wa | _ | _
  · cases wa with
    | word a =>
      have h1' := h1; simp only [evalAt, evalHOLExact, evalListHOLExact] at h h1'; rw [h1'] at h
      rcases hl : s.locals.lookup (ofString lname) with _ | v2
      · simp [hl] at h
      rcases v2 with wb | _ | _
      · cases wb with
        | word b =>
          simp only [hl, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self,
            ↓reduceIte, panOpHOL, wordOpHOL, wordOp, List.foldr, Option.some.injEq,
            ValueHOL.val.injEq, HolWordLab.word.injEq] at h
          exact ⟨a, b, rfl, rfl, by simp [locN, hl], by rw [← h]; simp⟩
      · simp [hl, valueIsWord] at h
      · simp [hl, valueIsWord] at h
  all_goals
    simp only [evalAt, evalHOLExact, evalListHOLExact] at h h1; rw [h1] at h
    rcases hl : s.locals.lookup (ofString lname) with _ | v2
    · simp [hl] at h
    rcases v2 with wb | _ | _
    · cases wb with | word _ => simp [hl, valueIsWord, panOpHOL] at h
    · simp [hl, valueIsWord] at h
    · simp [hl, valueIsWord] at h

theorem evalAt_add3_panMul {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e1 : ExpHOL 64) (lname : String) (c d x : BitVec 64)
    (h : evalAt s (.op .add [e1, .panop .mul [.var .local (ofString lname), .const c], .const d]) =
      some (.val (.word x))) :
    ∃ a b : BitVec 64, evalAt s e1 = some (.val (.word a)) ∧
      s.locals.lookup (ofString lname) = some (.val (.word b)) ∧
      locN s lname = b.toNat ∧ x = a + b * c + d := by
  rcases h1 : evalAt s e1 with _ | v1
  · simp only [evalAt, evalHOLExact, evalListHOLExact] at h h1; rw [h1] at h; simp at h
  rcases v1 with wa | _ | _
  · cases wa with
    | word a =>
      have h1' := h1; simp only [evalAt, evalHOLExact, evalListHOLExact] at h h1'; rw [h1'] at h
      rcases hl : s.locals.lookup (ofString lname) with _ | v2
      · simp [hl] at h
      rcases v2 with wb | _ | _
      · cases wb with
        | word b =>
          simp only [hl, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self,
            ↓reduceIte, panOpHOL, wordOpHOL, wordOp, List.foldr, Option.some.injEq,
            ValueHOL.val.injEq, HolWordLab.word.injEq] at h
          exact ⟨a, b, rfl, rfl, by simp [locN, hl], by rw [← h]; simp [BitVec.add_assoc]⟩
      · simp [hl, valueIsWord] at h
      · simp [hl, valueIsWord] at h
  all_goals
    simp only [evalAt, evalHOLExact, evalListHOLExact] at h h1; rw [h1] at h
    rcases hl : s.locals.lookup (ofString lname) with _ | v2
    · simp [hl] at h
    rcases v2 with wb | _ | _
    · cases wb with | word _ => simp [hl, valueIsWord, panOpHOL] at h
    · simp [hl, valueIsWord] at h
    · simp [hl, valueIsWord] at h

theorem evalAt_panMul_add1 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (lname : String) (c x : BitVec 64)
    (h : evalAt s (.panop .mul [.op .add [.var .local (ofString lname), .const 1], .const c]) =
      some (.val (.word x))) :
    ∃ b : BitVec 64, s.locals.lookup (ofString lname) = some (.val (.word b)) ∧
      locN s lname = b.toNat ∧ x = (b + 1) * c := by
  simp only [evalAt, evalHOLExact, evalListHOLExact] at h
  rcases hl : s.locals.lookup (ofString lname) with _ | v
  · simp [hl] at h
  rcases v with wb | _ | _
  · cases wb with
    | word b =>
      simp only [hl, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self,
        ↓reduceIte, panOpHOL, wordOpHOL, wordOp, List.foldr, Option.some.injEq,
        ValueHOL.val.injEq, HolWordLab.word.injEq] at h
      exact ⟨b, rfl, by simp [locN, hl], by rw [← h]; simp⟩
  · simp [hl, valueIsWord] at h
  · simp [hl, valueIsWord] at h

theorem flattenHOL_rfield_any {F : Type} (s : PanSemStateFiniteExact 64 F)
    (idx : Nat) (e : ExpHOL 64) (v : ValueHOL 64)
    (he : evalAt s (.rfield idx e) = some v)
    (hsh : ∃ fs : List (ValueHOL 64), evalAt s e = some (.rStruct fs) ∧
      ∀ f ∈ fs, ∃ w : HolWordLab 64, f = .val w) :
    (flattenHOL v).length = 1 := by
  obtain ⟨fs, he0, hfs⟩ := hsh
  simp only [evalAt] at he0; simp only [evalAt, evalHOLExact, he0] at he
  rcases hg : fs[idx]? with _ | f
  · simp [hg] at he
  · simp [hg] at he; subst he
    obtain ⟨w, rfl⟩ := hfs f (List.mem_of_getElem? hg); simp [flattenHOL]

theorem flattenHOL_var_or_const {v : ValueHOL 64} (hsh : shapeOfHOLExact v = .one) :
    (flattenHOL v).length = 1 := by
  obtain ⟨w, rfl⟩ := shape_one_word hsh; simp [flattenHOL]

theorem store_heapBuf_txal {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) (hE : TxEnv s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    (hT : TxAccessListOK s S Nd) {p sz : Nat} (hb : HeapBuf s S Nd p sz)
    (hd_tx : Disj (locN s "tx", 384) (p, sz))
    (hd_recs : memW s (locN s "tx") ≠ 0 → 0 < memW s (locN s "tx" + 216) →
      Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) (p, sz))
    {x : BitVec 64} {n : Nat} (hn : 0 < n) (hin : Inside (x.toNat, 8 * n) p (p + sz))
    {mem' : BitVec 64 → HolWordLab 64}
    (hm : ∀ a : BitVec 64, (∀ k, k < n → a ≠ x + BitVec.ofNat 64 (8 * k)) → mem' a = s.memory a) :
    let post : PanSemStateFiniteExact 64 F := { s with memory := mem' }
    ArenaReady post ∧ WorldTypedWith post S Nd ∧ TxEnv post ∧ TxAccessListOK post S Nd ∧
    HeapBuf post S Nd p sz ∧
    (∀ {q qsz : Nat}, HeapBuf s S Nd q qsz → Disj (q, qsz) (p, sz) →
      HeapBuf post S Nd q qsz ∧ IvlUnhit s post (q, qsz)) := by
  let post : PanSemStateFiniteExact 64 F := { s with memory := mem' }
  obtain ⟨hAp, hW', how_eq, _, _, _, hE', hbufs⟩ := store_heapBuf_world hA hE hW hb hn hin hm
  have hp_hi := (ivl_allocated_bound hA.2 (Or.inl hb.inside)).2
  have hx_hi : x.toNat + 8 * n ≤ 2 ^ 64 := by unfold Inside at hin; dsimp at hin hp_hi; omega
  have hu_tx : IvlUnhit s post (locN s "tx", 384) :=
    ivlUnhit_words hx_hi hm (by simp) (disj_of_inside_right hin hd_tx)
  have hu_recs : memW s (locN s "tx") ≠ 0 → 0 < memW s (locN s "tx" + 216) →
      IvlUnhit s post (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) :=
    fun hnz hpos => ivlUnhit_words hx_hi hm (by dsimp; omega) (disj_of_inside_right hin (hd_recs hnz hpos))
  have hT' := txAccessListOK_congr_unhit hA.2 (post := post) le_rfl rfl how_eq hT hu_tx hu_recs
  exact ⟨hAp, hW', hE', hT', ⟨hb.p8, hb.sz8, hb.inside, by rw [how_eq]; exact hb.disj⟩, hbufs⟩

theorem store_heapBuf_tabs {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) (hE : TxEnv s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    {p sz : Nat} (hb : HeapBuf s S Nd p sz)
    {x : BitVec 64} {n : Nat} (hn : 0 < n) (hin : Inside (x.toNat, 8 * n) p (p + sz))
    {mem' : BitVec 64 → HolWordLab 64}
    (hm : ∀ a : BitVec 64, (∀ k, k < n → a ≠ x + BitVec.ofNat 64 (8 * k)) → mem' a = s.memory a) :
    let post : PanSemStateFiniteExact 64 F := { s with memory := mem' }
    ArenaReady post ∧ WorldTypedWith post S Nd ∧ TxEnv post ∧ HeapBuf post S Nd p sz ∧
    (∀ {t klen : Nat}, HeapLocalTab s S t klen → HeapLocalTab post S t klen) ∧
    (∀ {q qsz : Nat}, HeapBuf s S Nd q qsz → Disj (q, qsz) (p, sz) →
      HeapBuf post S Nd q qsz ∧ IvlUnhit s post (q, qsz)) := by
  let post : PanSemStateFiniteExact 64 F := { s with memory := mem' }
  obtain ⟨hAp, hW', how_eq, hwrs_eq, hjrs_eq, hhdr_eq, hE', hbufs⟩ :=
    store_heapBuf_world hA hE hW hb hn hin hm
  have hp_hi := (ivl_allocated_bound hA.2 (Or.inl hb.inside)).2
  have hx_hi : x.toNat + 8 * n ≤ 2 ^ 64 := by unfold Inside at hin; dsimp at hin hp_hi; omega
  refine ⟨hAp, hW', hE', ⟨hb.p8, hb.sz8, hb.inside, by rw [how_eq]; exact hb.disj⟩, ?_, hbufs⟩
  intro t klen ht
  have hlt := localTab_congr ht.toLocalTab hwrs_eq hjrs_eq hhdr_eq
  have hfp_eq : htabFootprint post t = htabFootprint s t := by
    have ht_w := (hW.1.2.1 t ht.mem_S).1.1 (t, 88) (by simp [htabFootprint])
    refine (htabFootprint_eq_of_hdr_unhit ht_w.2.1 ?_ ?_).2
    · have : heapEnd ≤ 2 ^ 64 := by decide
      have := ht_w.1.2; omega
    · have how_t : (t, 88) ∈ worldOwned s S Nd :=
        List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl
          (List.mem_flatMap.2 ⟨t, ht.mem_S, by simp [htabFootprint]⟩))))
      exact ivlUnhit_words hx_hi hm (by simp) (disj_of_inside_right hin (disj_symm (hb.disj _ how_t)))
  exact ⟨hlt, by rw [hfp_eq]; exact ht.fp_heap⟩

theorem txEnv_htab_new {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) (hAp : ArenaReady post) (hag : AllocatorGrows s post)
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd) (hE : TxEnv s)
    (hfr : FrameOutside s post
      [(globN post "scratch_ptr", globN s "scratch_ptr" - globN post "scratch_ptr")]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    (hg_kept : ∀ k : MlS, k ∉ (["heap_ptr", "scratch_ptr"]).map ofString →
      s.globals.lookup k = post.globals.lookup k)
    {locals : HolFiniteMapExact MlS (ValueHOL 64)}
    (hidx : locals.lookup (ofString "index") = s.locals.lookup (ofString "index")) :
    TxEnv { post with locals := locals } := by
  have hbo_eq : globN post "bo" = globN s "bo" :=
    globN_eq_of_lookup (hg_kept (ofString "bo") (by decide))
  have hjcap_eq : globN post "journal_cap" = globN s "journal_cap" :=
    globN_eq_of_lookup (hg_kept (ofString "journal_cap") (by decide))
  have hw := bo_words hW.2.2.1 hE.bo_nz
  have hhi := (ivl_allocated_bound hA.2 hw.1).2
  have hbo_u : IvlUnhit s post (globN s "bo", 88) :=
    ivl_unhit_free_of_zero_or_allocated hA.2 hAp.2 hag hfr
      (fun k hk => List.mem_singleton.1 hk) rfl (fun _ => hw.2.1) (Or.inr hw.1)
  have hboW : ∀ k, k % 8 = 0 → k + 8 ≤ 88 → memW post (globN s "bo" + k) = memW s (globN s "bo" + k) :=
    fun k _ _ => memW_eq_of_ivlUnhit hbo_u (by have := hw.2.1; omega) hhi ⟨by dsimp; omega, by dsimp; omega⟩
  have hi := locN_congr s locals post.clock "index" hidx
  refine ⟨by show globN post "bo" ≠ 0; rw [hbo_eq]; exact hE.bo_nz,
    by show memW post (globN post "bo" + 24) ≠ 0; rw [hbo_eq, hboW 24 (by omega) (by omega)]; exact hE.bo24,
    by show memW post (globN post "bo" + 32) ≠ 0; rw [hbo_eq, hboW 32 (by omega) (by omega)]; exact hE.bo32,
    by show memW post (globN post "bo" + 40) ≠ 0; rw [hbo_eq, hboW 40 (by omega) (by omega)]; exact hE.bo40,
    by show memW post (globN post "bo" + 72) ≠ 0; rw [hbo_eq, hboW 72 (by omega) (by omega)]; exact hE.bo72,
    by show locN { post with locals := locals } "index" < memW post (globN post "bo" + 80);
       change locN { s with locals := locals, clock := post.clock } "index" < _;
       rw [hi, hbo_eq, hboW 80 (by omega) (by omega)]; exact hE.idx_lt,
    by show globN post "journal_cap" ≠ 0; rw [hjcap_eq]; exact hE.jcap_nz⟩

theorem txEnv_htab_set_local {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) (hAp : ArenaReady post) (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd) (hE : TxEnv s) {t : Nat} (htS : t ∈ S)
    (hfr : FrameOutside s post (htabFootprint s t)
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    (hg_kept : ∀ k : MlS, k ≠ ofString "heap_ptr" →
      s.globals.lookup k = post.globals.lookup k)
    {locals : HolFiniteMapExact MlS (ValueHOL 64)}
    (hidx : locals.lookup (ofString "index") = s.locals.lookup (ofString "index")) :
    TxEnv { post with locals := locals } := by
  have hbo_eq : globN post "bo" = globN s "bo" :=
    globN_eq_of_lookup (hg_kept (ofString "bo") (by decide))
  have hjcap_eq : globN post "journal_cap" = globN s "journal_cap" :=
    globN_eq_of_lookup (hg_kept (ofString "journal_cap") (by decide))
  have hsc_eq : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    globN_eq_of_lookup (hg_kept (ofString "scratch_ptr") (by decide))
  have hag : AllocatorGrows s post := ⟨hhp, by omega⟩
  have hw := bo_words hW.2.2.1 hE.bo_nz
  have hhi := (ivl_allocated_bound hA.2 hw.1).2
  have hbo_fix : (globN s "bo", 88) ∈ fixedObjects s := by
    simpa only [hE.bo_nz, if_false] using typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by simp [typedRecords])
  obtain ⟨_, _, _, _, _, hs_hp8, _, _⟩ := hA.2
  obtain ⟨_, _, _, _, _, hp_hp8, _, _⟩ := hAp.2
  have hfp_al : ∀ j ∈ htabFootprint s t, j.1 % 8 = 0 ∧ j.2 % 8 = 0 := fun j hj => by
    have hw := ((hW.1.2.1 t htS).1.1 j hj).2; exact ⟨hw.1, hw.2.1⟩
  have hbo_u : IvlUnhit s post (globN s "bo", 88) :=
    ivlUnhit_of_frameOutside_aligned hfr hfp_al
      ⟨hs_hp8, by omega⟩ (fun _ => hw.2.1)
      (fun j hj => disj_symm (((hW.1.2.1 t htS).2 j hj).2 _ hbo_fix))
      (ivl_disj_free_of_zero_or_allocated hA.2 hAp.2 hag (Or.inr hw.1)).1
  have hboW : ∀ k, k % 8 = 0 → k + 8 ≤ 88 → memW post (globN s "bo" + k) = memW s (globN s "bo" + k) :=
    fun k _ _ => memW_eq_of_ivlUnhit hbo_u (by have := hw.2.1; omega) hhi ⟨by dsimp; omega, by dsimp; omega⟩
  have hi := locN_congr s locals post.clock "index" hidx
  refine ⟨by show globN post "bo" ≠ 0; rw [hbo_eq]; exact hE.bo_nz,
    by show memW post (globN post "bo" + 24) ≠ 0; rw [hbo_eq, hboW 24 (by omega) (by omega)]; exact hE.bo24,
    by show memW post (globN post "bo" + 32) ≠ 0; rw [hbo_eq, hboW 32 (by omega) (by omega)]; exact hE.bo32,
    by show memW post (globN post "bo" + 40) ≠ 0; rw [hbo_eq, hboW 40 (by omega) (by omega)]; exact hE.bo40,
    by show memW post (globN post "bo" + 72) ≠ 0; rw [hbo_eq, hboW 72 (by omega) (by omega)]; exact hE.bo72,
    by show locN { post with locals := locals } "index" < memW post (globN post "bo" + 80);
       change locN { s with locals := locals, clock := post.clock } "index" < _;
       rw [hi, hbo_eq, hboW 80 (by omega) (by omega)]; exact hE.idx_lt,
    by show globN post "journal_cap" ≠ 0; rw [hjcap_eq]; exact hE.jcap_nz⟩

theorem step_htab_new_local {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : PtxCallees) (hcode : s.code = originalRuntimeCode)
    (hA : ArenaReady s) (hE : TxEnv s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    {klen cap : BitVec 64} (hklen : klen.toNat ∈ htabKeyLens) (hcap : cap.toNat ≤ htabCapMax)
    {vs : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret : ShapeHOL} {v : ValueHOL 64}
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const klen, .const cap] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_new") vs = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧
      ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
      TxEnv { post with locals := s.locals } ∧
      WorldTypedWith post (S ++ [w.toNat]) Nd ∧
      HeapLocalTab post (S ++ [w.toNat]) w.toNat klen.toNat ∧
      w.toNat ∉ S ∧
      (∀ {u uklen : Nat}, HeapLocalTab s S u uklen →
        HeapLocalTab post (S ++ [w.toNat]) u uklen) ∧
      (∀ {p sz : Nat}, HeapBuf s S Nd p sz →
        HeapBuf post (S ++ [w.toNat]) Nd p sz ∧ IvlUnhit s post (p, sz)) := by
  obtain ⟨v1, v2, he1, he2, hp1, hp2⟩ := params_two_values s
    (ofString "htab_new") (ofString "key_len") (ofString "cap") .one .one _ .one
    (by rw [hcode]; exact lookup_htab_new_fn) (.const klen) (.const cap) vs body callee ret ha hl
  have hv1 := evalAt_const_word s klen v1 he1; subst hv1
  have hv2 := evalAt_const_word s cap v2 he2; subst hv2
  set entry := callEntryStateHOLFinite s callee
  have hentry_kl : locN entry "key_len" = klen.toNat := by simp [entry, callEntryStateHOLFinite, locN, hp1]
  have hentry_cap : locN entry "cap" = cap.toNat := by simp [entry, callEntryStateHOLFinite, locN, hp2]
  have hready : HtabNewReady entry :=
    ⟨(arenaReady_with_locals s callee (s.clock - 1)).2 hA,
      by rw [hentry_kl]; exact hklen, by rw [hentry_cap]; exact hcap⟩
  have hspec := funSpec_at_lookup h.htab_new_spec s hcode vs body callee ret hl hready (by rw [hb]; simp)
  rw [hb] at hspec
  obtain ⟨w, rfl, hAp, hag, hwf_w, _, hhdr0_w, hfp_w, hfr, hg_kept⟩ := hspec v rfl
  change AllocatorGrows s post at hag
  change ∀ i ∈ htabFootprint post w.toNat, Allocated post i ∧ (Inside i (globN s "heap_ptr") (globN post "heap_ptr") ∨ Inside i (globN post "scratch_ptr") (globN s "scratch_ptr")) at hfp_w
  change FrameOutside s post [(globN post "scratch_ptr", globN s "scratch_ptr" - globN post "scratch_ptr")] (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") at hfr
  change ∀ k : MlS, k ∉ (["heap_ptr", "scratch_ptr"]).map ofString → s.globals.lookup k = post.globals.lookup k at hg_kept
  rw [hentry_kl] at hhdr0_w
  have hsc_eq := htab_new_scratch_unchanged hcode vs body callee ret (.val (.word w)) post hl hb
  have hmeta := (evaluateHOLFiniteState_metadata entry body).2.2.1; rw [hb] at hmeta
  obtain ⟨hw_not_S, hw_nz, hw_local, hW', hwrs_eq, hjrs_eq, hhdr_eq, hsurv⟩ :=
    worldTypedWith_htab_new hA hW hAp hag hwf_w hfp_w hfr hmeta hg_kept
  have hfp_heap_w : ∀ i ∈ htabFootprint post w.toNat, Inside i sourceBase (globN post "heap_ptr") := by
    intro i hi; rcases (hfp_w i hi).2 with hin | hin_sc
    · exact ⟨Nat.le_trans hA.2.1 hin.1, hin.2⟩
    · exfalso; rw [hsc_eq] at hin_sc
      have hi_pos : 0 < i.2 := by
        obtain ⟨_, _, hk1, _, hkstride, hncap, _⟩ := hwf_w
        simp only [htabFootprint, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl
        · dsimp; omega
        · dsimp; rw [hkstride]; exact Nat.mul_pos (by omega) (by omega)
        · dsimp; omega
        · dsimp; omega
      unfold Inside at hin_sc; omega
  have htab_w : HeapLocalTab post (S ++ [w.toNat]) w.toNat klen.toNat :=
    ⟨⟨by simp, hw_nz, hhdr0_w, hw_local⟩, hfp_heap_w⟩
  have hE' := txEnv_htab_new hA hAp hag hW hE hfr hg_kept (locals := s.locals) rfl
  refine ⟨w, rfl, hAp, hag.1, hE', hW', htab_w, hw_not_S, ?_, ?_⟩
  · intro u uklen hu
    have hlt_u := localTab_ext (u := w.toNat) hu.toLocalTab hwrs_eq hjrs_eq hhdr_eq
    have hi_u88 : Allocated s (u, 88) := ((hW.1.2.1 u hu.mem_S).2 (u, 88) (by simp [htabFootprint])).1
    have hu_unhit := ivl_unhit_free_of_zero_or_allocated hA.2 hAp.2 hag hfr
      (fun k hk => List.mem_singleton.1 hk) rfl (by simp) (Or.inr hi_u88)
    have hfp_u_eq : htabFootprint post u = htabFootprint s u := by
      refine (htabFootprint_eq_of_hdr_unhit (((hW.1.2.1 u hu.mem_S).1.1 (u, 88) (by simp [htabFootprint])).2.1) ?_ hu_unhit).2
      have hhi := (ivl_allocated_bound hA.2 hi_u88).2; dsimp at hhi; omega
    exact ⟨hlt_u, by rw [hfp_u_eq]; exact fun i hi => ⟨(hu.fp_heap i hi).1, Nat.le_trans (hu.fp_heap i hi).2 hag.1⟩⟩
  · intro p sz hb_p
    obtain ⟨hin', hd', hu'⟩ := hsurv (p, sz) (fun _ => hb_p.p8) hb_p.inside hb_p.disj
    exact ⟨⟨hb_p.p8, hb_p.sz8, hin', hd'⟩, hu'⟩

theorem step_htab_set_local {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : PtxCallees) (hcode : s.code = originalRuntimeCode)
    (hA : ArenaReady s) (hE : TxEnv s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    {t klen : Nat} (ht : HeapLocalTab s S t klen)
    {e_t e_key e_val : ExpHOL 64}
    (het : ∀ tv, evalAt s e_t = some tv → ∃ tw : BitVec 64, tv = .val (.word tw) ∧ tw.toNat = t)
    {vs : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret : ShapeHOL} {v : ValueHOL 64}
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [e_t, e_key, e_val] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_set") vs = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    TxEnv { post with locals := s.locals } ∧
    WorldTypedWith post S Nd ∧
    HeapLocalTab post S t klen ∧
    (∀ {u uklen : Nat}, HeapLocalTab s S u uklen → u ≠ t → HeapLocalTab post S u uklen) ∧
    (∀ {p sz : Nat}, HeapBuf s S Nd p sz →
      HeapBuf post S Nd p sz ∧ IvlUnhit s post (p, sz)) := by
  obtain ⟨v1, v2, v3, he1, _, _, hp1, _, _⟩ := params_three_values s
    (ofString "htab_set") (ofString "t") (ofString "key") (ofString "value")
    .one .one .one _ .one (by rw [hcode]; exact lookup_htab_set_fn)
    e_t e_key e_val vs body callee ret ha hl
  obtain ⟨tw, rfl, rfl⟩ := het v1 he1
  set entry := callEntryStateHOLFinite s callee
  have hentry_t : locN entry "t" = tw.toNat := by simp [entry, callEntryStateHOLFinite, locN, hp1]
  have hargwf : HtabArgWF entry := by
    refine ⟨(arenaReady_with_locals s callee (s.clock - 1)).2 hA, ?_, ?_⟩
    · rw [hentry_t]; exact (htabWF_with_locals s callee (s.clock - 1) tw.toNat).2 (hW.1.2.1 tw.toNat ht.mem_S).1
    · rw [hentry_t]; exact fun i hi => ((hW.1.2.1 tw.toNat ht.mem_S).2 i hi).1
  have hspec := funSpec_at_lookup h.htab_set_spec s hcode vs body callee ret hl hargwf (by rw [hb]; simp)
  rw [hb] at hspec
  obtain ⟨hAp, hwf_t, hhdr0_t, _, hhp, hfp_t, hfr, hg_kept⟩ := hspec v rfl
  rw [hentry_t] at hwf_t hhdr0_t hfp_t hfr
  change ArenaReady post at hAp
  change HtabWF post tw.toNat at hwf_t
  change hdr post tw.toNat 0 = hdr s tw.toNat 0 at hhdr0_t
  change globN s "heap_ptr" ≤ globN post "heap_ptr" at hhp
  change ∀ i ∈ htabFootprint post tw.toNat, Allocated post i ∧
    ((∃ j ∈ htabFootprint s tw.toNat, Inside i j.1 (j.1 + j.2)) ∨
      Inside i (globN s "heap_ptr") (globN s "heap_ptr" + (globN post "heap_ptr" - globN s "heap_ptr"))) at hfp_t
  change FrameOutside s post (htabFootprint s tw.toNat)
    (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") at hfr
  change ∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = post.globals.lookup k at hg_kept
  have hg_kept_list : ∀ name : MlS, name ∉ (["heap_ptr"] : List String).map ofString →
      s.globals.lookup name = post.globals.lookup name :=
    fun name hn => hg_kept name (fun h => hn (by simp [h]))
  have hmeta := (evaluateHOLFiniteState_metadata entry body).2.2.1
  rw [hb] at hmeta
  obtain ⟨hW', hwrs_eq, hjrs_eq, hhdr_eq, _, hsurv⟩ :=
    worldTypedWith_htab_set_local hA hW ht.mem_S ht.unassigned hAp hwf_t hhdr0_t hhp hfp_t hfr hmeta hg_kept_list
  have hfp_heap_t : ∀ i ∈ htabFootprint post tw.toNat, Inside i sourceBase (globN post "heap_ptr") := by
    intro i hi
    rcases (hfp_t i hi).2 with ⟨j, hj, hin_j⟩ | hin_fr
    · have hj_in := ht.fp_heap j hj
      exact ⟨Nat.le_trans hj_in.1 hin_j.1, Nat.le_trans (Nat.le_trans hin_j.2 hj_in.2) hhp⟩
    · exact ⟨Nat.le_trans hA.2.1 hin_fr.1, by unfold Inside at hin_fr; omega⟩
  have htab_t : HeapLocalTab post S tw.toNat klen :=
    ⟨localTab_congr ht.toLocalTab hwrs_eq hjrs_eq hhdr_eq, hfp_heap_t⟩
  have hE' := txEnv_htab_set_local hA hAp hhp hW hE ht.mem_S hfr hg_kept (locals := s.locals) rfl
  refine ⟨hAp, hhp, hE', hW', htab_t, ?_, ?_⟩
  · intro u uklen hu hut
    have hlt_u := localTab_congr hu.toLocalTab hwrs_eq hjrs_eq hhdr_eq
    obtain ⟨_, _, _, _, _, hs_hp8, _, _⟩ := hA.2
    obtain ⟨_, _, _, _, _, hp_hp8, _, _⟩ := hAp.2
    have hfp_al : ∀ j ∈ htabFootprint s tw.toNat, j.1 % 8 = 0 ∧ j.2 % 8 = 0 := fun j hj => by
      have hw := ((hW.1.2.1 tw.toNat ht.mem_S).1.1 j hj).2; exact ⟨hw.1, hw.2.1⟩
    have hi_u88 : Allocated s (u, 88) := ((hW.1.2.1 u hu.mem_S).2 (u, 88) (by simp [htabFootprint])).1
    have hsc_eq : globN post "scratch_ptr" = globN s "scratch_ptr" := globN_eq_of_lookup (hg_kept (ofString "scratch_ptr") (by decide))
    have hu_unhit := ivlUnhit_of_frameOutside_aligned hfr hfp_al ⟨hs_hp8, by omega⟩ (by simp)
      (fun j hj => disj_symm (hW.1.2.2.1 tw.toNat ht.mem_S u hu.mem_S (Ne.symm hut) j hj (u, 88) (by simp [htabFootprint])))
      (ivl_disj_free_of_zero_or_allocated hA.2 hAp.2 ⟨hhp, by omega⟩ (Or.inr hi_u88)).1
    have hfp_u_eq : htabFootprint post u = htabFootprint s u := by
      refine (htabFootprint_eq_of_hdr_unhit (((hW.1.2.1 u hu.mem_S).1.1 (u, 88) (by simp [htabFootprint])).2.1) ?_ hu_unhit).2
      have hhi := (ivl_allocated_bound hA.2 hi_u88).2; dsimp at hhi; omega
    exact ⟨hlt_u, by rw [hfp_u_eq]; exact fun i hi => ⟨(hu.fp_heap i hi).1, Nat.le_trans (hu.fp_heap i hi).2 hhp⟩⟩
  · intro p sz hb_p
    obtain ⟨hin', hd', hu'⟩ := hsurv (p, sz) (fun _ => hb_p.p8) hb_p.inside hb_p.disj
    exact ⟨⟨hb_p.p8, hb_p.sz8, hin', hd'⟩, hu'⟩

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase2
