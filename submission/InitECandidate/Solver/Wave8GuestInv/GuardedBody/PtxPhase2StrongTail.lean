import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2Strong

namespace InitECandidate.Solver.Wave8GuestInv.R13Shards
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.Wave8GuestInv

/-! ### Segment B part 2a L2: the position-79 `htab_set` on the `aa` table.

The invariant is strengthened over L1: every saved-buffer world must contain
the live table root, so the htab_set frame (which writes only inside the
table footprint and the fresh heap gap) transports each buffer world. -/

/-- Store-ready where every saved-buffer world contains the live table `t`. -/
def PtxStoreReadyIn {ι : Type} (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (t : Nat) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop := fun s =>
  WorldOK s ∧ TxEnv s ∧
  (∃ w : BitVec 64, s.locals.lookup (ofString "m") = some (.val (.word w))) ∧
  Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr") ∧
  WordsOK s (locN s "m", 176) ∧
  ∀ i, Disj (buffers i) (locN s "m", 176) ∧
    ∃ S Nd, t ∈ S ∧ WorldTypedWith s S Nd ∧
      PtxLiveBufferAt s S Nd (buffers i) (contents i) ∧
      IvlsDisj [(locN s "m", 176)] (worldOwned s S Nd)

theorem PtxStoreReadyIn.to_storeReady {ι F : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) {t : Nat}
    {s : PanSemStateFiniteExact 64 F} (hp : PtxStoreReadyIn buffers contents t s) :
    PtxMessageStoreReady buffers contents s := by
  refine ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, ?_⟩
  intro i
  obtain ⟨hd, S, Nd, _, hw, hb, hsep⟩ := hp.2.2.2.2.2 i
  exact ⟨hd, S, Nd, hw, hb, hsep⟩

/-- The one-table world witness for the `aa` region (positions 77..85). -/
def PtxMessageTablesA {F : Type} (s : PanSemStateFiniteExact 64 F) (aa : Nat) : Prop :=
  ∃ S Nd, WorldTypedWith s S Nd ∧ aa ∈ S ∧ hdr s aa 0 = 20 ∧
    (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ aa) ∧
    IvlsDisj [(locN s "m", 176)] (worldOwned s S Nd)

/-- The htab region after the `aa` allocation (positions 77..85): the
B-scalar frame with table-aware buffer worlds, plus the one-table world. -/
def PtxHtabAInv2 {ι : Type} (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop := fun s =>
  (∃ w : BitVec 64, s.locals.lookup (ofString "aa") = some (.val (.word w))) ∧
    (PtxStoreReadyIn buffers contents (locN s "aa") s ∧
      ∀ name ∈ names, ∃ w : BitVec 64,
        s.locals.lookup (ofString name) = some (.val (.word w))) ∧
    R16Shards.TxBacking s ∧ R16Shards.PtxPhase4LocalShapes s ∧
    PtxMessageTablesA s (locN s "aa")

/-- A `setVar` of a name other than `m` preserves the table-aware store
invariant (only the `m` and `index` locals are read by the store predicate). -/
theorem phase2_storeReadyIn_setVar_ne {ι F : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) {t : Nat} {name : MlS}
    (hne : ofString "m" ≠ name) (hni : ofString "index" ≠ name) (v : ValueHOL 64)
    {s : PanSemStateFiniteExact 64 F} (hp : PtxStoreReadyIn buffers contents t s) :
    PtxStoreReadyIn buffers contents t (setVarHOLFinite name v s) := by
  obtain ⟨hW, hE, hm, hin, hwok, hbufs⟩ := hp
  have hlu : ∀ str : String, ofString str ≠ name →
      (setVarHOLFinite name v s).locals.lookup (ofString str) =
        s.locals.lookup (ofString str) := by
    intro str hn
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm hn]
  have hmn : locN (setVarHOLFinite name v s) "m" = locN s "m" :=
    locN_setVar_ne _ "m" name v hne
  have hin2 : locN (setVarHOLFinite name v s) "index" = locN s "index" :=
    locN_setVar_ne _ "index" name v hni
  refine ⟨⟨⟨guestInv_setVar name v s hW.1.1, hW.1.2⟩, ?_⟩,
    ⟨hE.bo_nz, hE.bo24, hE.bo32, hE.bo40, hE.bo72, ?_, hE.jcap_nz⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨S, hWT⟩ := hW.2
    obtain ⟨Nd, hw⟩ := (worldTyped_iff_with s S).mp hWT
    exact ⟨S, (worldTyped_iff_with _ S).mpr ⟨Nd,
      (worldTypedWith_with_locals s (s.locals.update (name, v)) s.clock S Nd).mpr hw⟩⟩
  · rw [hin2]; exact hE.idx_lt
  · obtain ⟨w, hw⟩ := hm
    exact ⟨w, by rw [hlu "m" hne]; exact hw⟩
  · rw [hmn]; exact hin
  · rw [hmn]; exact hwok
  · intro i
    obtain ⟨hd, S, Nd, hmem, hw, hb, hsep⟩ := hbufs i
    refine ⟨?_, S, Nd, hmem,
      (worldTypedWith_with_locals s (s.locals.update (name, v)) s.clock S Nd).mpr hw, hb, ?_⟩
    · rw [hmn]; exact hd
    · rw [hmn]; exact hsep

/-- The htab region after the `aa` allocation, with table-aware buffer worlds. -/
theorem phase2_htab_new_store_ready_in {ι F : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    {s post : PanSemStateFiniteExact 64 F}
    (hp : PtxMessageStoreReady buffers contents s)
    (hAp : ArenaReady post) (hag : AllocatorGrows s post) {t : Nat}
    (hwf_t : HtabWF post t)
    (hfp_t : ∀ i ∈ htabFootprint post t, Allocated post i ∧
      (Inside i (globN s "heap_ptr") (globN post "heap_ptr") ∨
        Inside i (globN post "scratch_ptr") (globN s "scratch_ptr")))
    (hfr : FrameOutside s post
      [(globN post "scratch_ptr", globN s "scratch_ptr" - globN post "scratch_ptr")]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    (hbe : post.be = s.be) (hg_kept : GlobalsKept ["heap_ptr", "scratch_ptr"] s post) :
    PtxStoreReadyIn buffers contents t {post with locals := s.locals} := by
  have hgs : R16Shards.GbodyC17ToC21Common.WorldGlobalsSame s post :=
    R16Shards.GbodyC17ToC21Common.worldGlobalsSame_of_globalsKept hg_kept
      (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨hW_s, hE_s, hm_w, hin_m, hwok_m, hbufs⟩ := hp
  obtain ⟨hA_s, S0, hWT⟩ := hW_s
  obtain ⟨Nd0, hw0⟩ := (worldTyped_iff_with s S0).1 hWT
  have hext := R16Shards.GbodyC17ToC21Common.worldTypedWith_htab_new hA_s hw0 hAp hag hwf_t
    hfp_t hfr hbe hg_kept
  have hA_mid : ArenaReady {post with locals := s.locals} :=
    (arenaReady_with_locals post s.locals post.clock).mpr hAp
  have hW_mid_ext : WorldTypedWith {post with locals := s.locals} (S0 ++ [t]) Nd0 :=
    (worldTypedWith_with_locals post s.locals post.clock (S0 ++ [t]) Nd0).mpr
      hext.2.2.2.1
  refine ⟨⟨hA_mid, S0 ++ [t], (worldTyped_iff_with _ (S0 ++ [t])).2 ⟨Nd0, hW_mid_ext⟩⟩,
    phase2_htab_new_txEnv hA_s hAp hE_s hw0 hag hgs hfr, hm_w,
    ⟨hin_m.1, hin_m.2.trans hag.1⟩, ?_, ?_⟩
  · exact wordsOK_transfer hA_s.1 hA_mid.1 hwok_m
  · intro i
    obtain ⟨hd, S_i, Nd_i, hw_i, hb_i, hsep_i⟩ := hbufs i
    refine ⟨hd, S_i ++ [t], Nd_i, by simp, ?_, ?_, ?_⟩
    · exact (worldTypedWith_with_locals post s.locals post.clock (S_i ++ [t]) Nd_i).mpr
        ((R16Shards.GbodyC17ToC21Common.worldTypedWith_htab_new hA_s hw_i hAp hag hwf_t
          hfp_t hfr hbe hg_kept).2.2.2.1)
    · exact phase2_htab_new_live_buffer hA_s hw_i hAp hag hfp_t hfr hbe hgs hb_i
    · intro o ho j hj
      simp only [List.mem_singleton] at ho; subst o
      exact phase2_htab_new_world_disj hA_s hw_i hAp hag hfp_t hfr hbe hgs hin_m
        (fun j' hj' => hsep_i _ (by simp) j' hj') j hj

/-- Resuming after the `aa` allocation (position 77) with the strengthened
table-aware htab-region invariant. -/
theorem phase2_htabA_new_aa_resume2 (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) :
    DecCallResumeOn (PtxMessageBScalarReady buffers contents
      ["te", "sender", "mgas", "reservoir"])
      (PtxHtabAInv2 buffers contents ["te", "sender", "mgas", "reservoir"])
      (ofString "aa") (ofString "htab_new") [.const (20#64), .const (64#64)] := by
  intro F s vs body callee ret v post hc hp he hl hb
  have hsReady : PtxMessageStoreReady buffers contents s := hp.1.1
  have hA_s : ArenaReady s := hp.1.1.1.1
  have hE_s : TxEnv s := hp.1.1.2.1
  have htx : R16Shards.TxBacking s := hp.2.1
  have hp4 : R16Shards.PtxPhase4LocalShapes s := hp.2.2
  obtain ⟨S0, hWT⟩ := hp.1.1.1.2
  obtain ⟨Nd0, hw0⟩ := (worldTyped_iff_with s S0).mp hWT
  have hin_m : Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr") :=
    hsReady.2.2.2.1
  have hc2 := R16Shards.callee_param_two s (ofString "htab_new") (ofString "key_len")
    (ofString "cap") .one .one _ _
    (by rw [hc]; exact R10Shards.SoloHtabNew.lookup_htab_new) (.const (20#64)) (.const (64#64))
    (.val (.word (20#64))) (.val (.word (64#64))) vs body callee ret
    (by simp [evalAt, evalHOLExact]) (by simp [evalAt, evalHOLExact]) he hl
  have hkl : locN (callEntryStateHOLFinite s callee) "key_len" = 20 := by
    unfold locN callEntryStateHOLFinite; dsimp only; rw [hc2.2.1]; decide
  have hcap : locN (callEntryStateHOLFinite s callee) "cap" = 64 := by
    unfold locN callEntryStateHOLFinite; dsimp only; rw [hc2.2.2]; decide
  have hA_ent : ArenaReady (callEntryStateHOLFinite s callee) :=
    (arenaReady_with_locals s callee (s.clock - 1)).mpr hA_s
  have hW_ent : WorldTypedWith (callEntryStateHOLFinite s callee) S0 Nd0 :=
    (worldTypedWith_with_locals s callee (s.clock - 1) S0 Nd0).mpr hw0
  have hready : HtabNewReady (callEntryStateHOLFinite s callee) :=
    ⟨hA_ent, by rw [hkl]; decide, by rw [hcap]; decide⟩
  have hexit := FunSpec.at_lookup h.htab_new_spec s hc vs body callee ret hl hready
    (by rw [hb]; simp)
  rw [hb] at hexit
  obtain ⟨w, hvw, hAp, hag, hwf_t, hc3, hkl0, hfp_t, hfr, hgk⟩ := hexit v rfl
  subst hvw
  have hmeta := (InitECandidate.Solver.PanRunBounded.evaluateHOLFiniteState_metadata
    (callEntryStateHOLFinite s callee) body).2.2.1
  rw [hb] at hmeta
  have hgs : R16Shards.GbodyC17ToC21Common.WorldGlobalsSame s post :=
    R16Shards.GbodyC17ToC21Common.worldGlobalsSame_of_globalsKept hgk
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsr : PtxStoreReadyIn buffers contents w.toNat
      (setVarHOLFinite (ofString "aa") (.val (.word w)) {post with locals := s.locals}) :=
    phase2_storeReadyIn_setVar_ne buffers contents (by decide) (by decide) (.val (.word w))
      (phase2_htab_new_store_ready_in buffers contents hsReady hAp hag hwf_t hfp_t hfr hmeta hgk)
  have htxb0 : R16Shards.TxBacking post :=
    phase2_htab_new_txBacking hA_s hAp hE_s hw0 htx hag hgs hfr
  have htxb : R16Shards.TxBacking
      (setVarHOLFinite (ofString "aa") (.val (.word w)) {post with locals := s.locals}) :=
    htxb0
  have hnames : ∀ name ∈ (["te", "sender", "mgas", "reservoir"] : List String),
      ∃ w' : BitVec 64, (setVarHOLFinite (ofString "aa") (.val (.word w))
        {post with locals := s.locals}).locals.lookup (ofString name) =
        some (.val (.word w')) := by
    intro name hn
    obtain ⟨w', hw'⟩ := hp.1.2 name hn
    refine ⟨w', ?_⟩
    have hne : ofString name ≠ ofString "aa" := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl <;> decide
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm hne]
    exact hw'
  -- the world-with-aa witness: extend one saved-buffer world
  obtain ⟨i0⟩ := ‹Nonempty ι›
  obtain ⟨_, S_i, Nd_i, hw_i, hb_i, hsep_i⟩ := hsReady.2.2.2.2.2 i0
  have hW_i' := R16Shards.GbodyC17ToC21Common.worldTypedWith_htab_new hA_ent
    ((worldTypedWith_with_locals s callee (s.clock - 1) S_i Nd_i).mpr hw_i)
    hAp hag hwf_t hfp_t hfr hmeta hgk
  have haa : locN (setVarHOLFinite (ofString "aa") (.val (.word w))
      {post with locals := s.locals}) "aa" = w.toNat :=
    locN_setVar_same _ "aa" w
  have hmm : locN (setVarHOLFinite (ofString "aa") (.val (.word w))
      {post with locals := s.locals}) "m" = locN s "m" :=
    locN_setVar_ne _ "m" (ofString "aa") _ (by decide)
  have hw_mid : WorldTypedWith (setVarHOLFinite (ofString "aa") (.val (.word w))
      {post with locals := s.locals}) (S_i ++ [w.toNat]) Nd_i :=
    (worldTypedWith_with_locals post (s.locals.update (ofString "aa", .val (.word w)))
      post.clock (S_i ++ [w.toNat]) Nd_i).mpr hW_i'.2.2.2.1
  have hsr' : PtxStoreReadyIn buffers contents (locN (setVarHOLFinite (ofString "aa")
      (.val (.word w)) {post with locals := s.locals}) "aa")
      (setVarHOLFinite (ofString "aa") (.val (.word w)) {post with locals := s.locals}) := by
    rw [haa]; exact hsr
  refine ⟨⟨w, by
      simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]⟩, ⟨hsr', hnames⟩, htxb,
    phase2_p4Shapes_htab_new_aa s post (.val (.word w)) hp4,
    S_i ++ [w.toNat], Nd_i, ?_, ?_, ?_, ?_, ?_⟩
  · exact hw_mid
  · rw [haa]; simp
  · rw [haa]; exact hkl0.trans hkl
  · rw [haa]; exact hW_i'.2.2.1
  · intro o ho j hj
    simp only [List.mem_singleton] at ho; subst ho
    rw [hmm]
    exact phase2_htab_new_world_disj hA_s hw_i hAp hag hfp_t hfr hmeta hgs hin_m
      (fun j' hj' => hsep_i _ (by simp) j' hj') j hj

/-- The htab_set exit preserves the one-table world witness. -/
theorem phase2_htabExit_a_message_tables {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {aa : Nat}
    (hs : ArenaReady s) (hm : PtxMessageTablesA s aa)
    (hin : Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr"))
    (hl : locN post "m" = locN s "m") (hbe : post.be = s.be)
    (ht : locN s "t" = aa) (hx : HtabExit s post) :
    PtxMessageTablesA post aa := by
  obtain ⟨S, Nd, hw, ha, hal, haf, hd⟩ := hm
  have hf := R16Shards.MptC10C12.worldTypedWith_htab_set_local_csr hs hw
    (ht.symm ▸ ha) (ht.symm ▸ haf) hx hbe
  refine ⟨S, Nd, hf.1, ha, (hf.2.2.2.2.1 aa ha).trans hal, ?_, ?_⟩
  · simpa only [hf.2.1, hf.2.2.1] using haf
  · intro o ho j hj
    simp only [List.mem_singleton] at ho; subst o
    rw [hl]
    exact (hf.2.2.2.2.2.2 (locN s "m", 176) (by intro h; omega) hin
      (fun j hj => hd _ (by simp) j hj)).2.1 j hj

/-- The htab_set frame writes only inside the table footprint (which a world
containing the table owns) and the fresh heap gap (inside `heapFree`). -/
theorem phase2_frameOutside_of_htabExit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hx : HtabExit s post) (hmem : locN s "t" ∈ S)
    (hslim : globN s "heap_ptr" ≤ heapLimit)
    (hplim : globN post "heap_ptr" ≤ heapLimit) :
    FrameOutside s post (worldOwned s S Nd ++ [] ++ [freeGap s]) (heapFree s) := by
  obtain ⟨_, _, _, _, _, _, hfr, _⟩ := hx
  intro a hkeep hfresh
  refine hfr a ?_ ?_
  · intro i hi
    have hmem2 : i ∈ worldOwned s S Nd ++ [] ++ [freeGap s] := by
      unfold worldOwned
      apply List.mem_append.2; left
      apply List.mem_append.2; left
      apply List.mem_append.2; left
      apply List.mem_append.2; left
      exact List.mem_flatMap.2 ⟨locN s "t", hmem, hi⟩
    exact hkeep i hmem2
  · intro hcell
    obtain ⟨hc1, hc2⟩ := hcell
    refine hfresh ⟨hc1, ?_⟩
    unfold heapFree
    omega

/-- Table-aware store readiness transports across a world step whose frame
keeps every world that contains the table. -/
theorem phase2_storeReadyIn_world_step {ι F : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) {t : Nat}
    (s post : PanSemStateFiniteExact 64 F)
    (hp : PtxStoreReadyIn buffers contents t s)
    (ha : ArenaReady post) (he : TxEnv post)
    (hl : post.locals.lookup (ofString "m") = s.locals.lookup (ofString "m"))
    (hh : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hs : ∀ S Nd, WorldTypedWith s S Nd → t ∈ S →
      ∃ S' Nd', t ∈ S' ∧ WorldTypedWith post S' Nd' ∧
        OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd') ∧
        FrameOutside s post (worldOwned s S Nd ++ [] ++ [freeGap s]) (heapFree s)) :
    PtxStoreReadyIn buffers contents t post := by
  have hm : locN post "m" = locN s "m" := by simp only [locN, hl]
  have hf : ∀ i, ∃ S Nd, t ∈ S ∧ WorldTypedWith post S Nd ∧
      PtxLiveBufferAt post S Nd (buffers i) (contents i) ∧
      IvlsDisj [(locN s "m", 176)] (worldOwned post S Nd) := by
    intro i
    obtain ⟨hd, S, Nd, hmem, hw, hb, hmd⟩ := hp.2.2.2.2.2 i
    obtain ⟨S', Nd', hmem', hw', hg, hfr⟩ := hs S Nd hw hmem
    refine ⟨S', Nd', hmem', hw', ?_, ?_⟩
    · exact phase2_live_buffer_step s post S Nd S' Nd' (buffers i) (contents i) []
        hb hp.1.1.2 hw hh hg hfr (by simp) (by simp)
    · exact phase2_packed_owned_growth s post _ _ (locN s "m", 176)
        hp.2.2.2.1 hg hmd
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨S, Nd, _, hw, _, _⟩ := hf i
  refine ⟨⟨ha, S, (worldTyped_iff_with post S).mpr ⟨Nd, hw⟩⟩, he, ?_, ?_, ?_, ?_⟩
  · simpa only [hl] using hp.2.2.1
  · rw [hm]
    exact ⟨hp.2.2.2.1.1, hp.2.2.2.1.2.trans hh⟩
  · rw [hm]
    exact wordsOK_transfer hp.1.1.1 ha.1 hp.2.2.2.2.1
  · intro j
    rw [hm]
    exact ⟨(hp.2.2.2.2.2 j).1, hf j⟩

/-- Private address insertion into the `aa` table preserves the whole
htab-region invariant (position 79, and the warming loops' bodies). -/
theorem phase2_htabA_set {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (names : List String)
    (key value : ExpHOL 64) :
    Hoare (PtxHtabAInv2 buffers contents names)
      (.call (some (none, none)) (ofString "htab_set")
        [.var .local (ofString "aa"), key, value])
      (fun r s => r = none → PtxHtabAInv2 buffers contents names s) := by
  apply Hoare.call0_resume
  intro F s vs body callee ret v post hc hp ha hl hr
  obtain ⟨haa_w, ⟨hstore, hnames⟩, htx, hp4, hworld⟩ := hp
  obtain ⟨S, Nd, hw, ham, hal, haf, hdisj⟩ := hworld
  obtain ⟨v1, _, _, he1, _, _, hct, _, _⟩ := R16WkAcctWs.callee_param_three s
    (ofString "htab_set") (ofString "t") (ofString "key") (ofString "value")
    .one .one .one _ _ (by rw [hc]; exact EvmFrameSpecs.lookup_htab_set)
    _ _ _ vs body callee ret ha hl
  have hev : s.locals.lookup (ofString "aa") = some v1 := by
    simpa [evalAt, evalHOLExact] using he1
  obtain ⟨wa, hwa⟩ := haa_w
  have hv1 : v1 = .val (.word wa) := by
    rw [hev] at hwa
    exact Option.some.inj hwa
  subst hv1
  have haa : locN s "aa" = wa.toNat := by simp [locN, hwa]
  have ht : locN (callEntryStateHOLFinite s callee) "t" = locN s "aa" := by
    simp [locN, callEntryStateHOLFinite, hct, hwa]
  have hA_s : ArenaReady s := hstore.1.1
  have hE_s : TxEnv s := hstore.2.1
  have hin_m : Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr") :=
    hstore.2.2.2.1
  have hA_ent : ArenaReady (callEntryStateHOLFinite s callee) :=
    (arenaReady_with_locals s callee (s.clock - 1)).mpr hA_s
  have hw_ent : WorldTypedWith (callEntryStateHOLFinite s callee) S Nd :=
    (worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hw
  have ham_ent : locN (callEntryStateHOLFinite s callee) "t" ∈ S := ht.symm ▸ ham
  have harg : HtabArgWF (callEntryStateHOLFinite s callee) := by
    refine ⟨hA_ent, ?_, ?_⟩
    · rw [ht]
      exact (htabWF_with_locals s callee (s.clock - 1) _).mpr (hw.1.2.1 _ ham).1
    · rw [ht]
      exact fun i hi => ((hw.1.2.1 _ ham).2 i hi).1
  have hx := FunSpec.at_lookup htab_set_spec s hc vs body callee ret hl harg (by rw [hr]; simp)
  rw [hr] at hx
  have hx := hx v rfl
  -- move to the `pre` state that binds `t` to the `aa` value
  let pre := setVarHOLFinite (ofString "t") (.val (.word wa)) s
  have hmp : pre.locals.lookup (ofString "m") = s.locals.lookup (ofString "m") := by
    simp [pre, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "t" ≠ ofString "m" by decide]
  have hip : pre.locals.lookup (ofString "index") = s.locals.lookup (ofString "index") := by
    simp [pre, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "t" ≠ ofString "index" by decide]
  have haa_p : pre.locals.lookup (ofString "aa") = s.locals.lookup (ofString "aa") := by
    simp [pre, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "t" ≠ ofString "aa" by decide]
  have hmt : locN pre "m" = locN s "m" := locN_congr s pre.locals s.clock "m" hmp
  have hit : locN pre "index" = locN s "index" := locN_congr s pre.locals s.clock "index" hip
  have hap : locN pre "aa" = locN s "aa" := locN_congr s pre.locals s.clock "aa" haa_p
  have hpt : locN pre "t" = locN (callEntryStateHOLFinite s callee) "t" := by
    simp [pre, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      callEntryStateHOLFinite, hct]
  have hxp : HtabExit pre {post with locals := s.locals} := by
    change ArenaReady _ ∧ HtabWF _ _ ∧ _
    refine ⟨(arenaReady_with_locals post s.locals post.clock).mpr hx.1,
      (htabWF_with_locals post s.locals post.clock _).mpr (hpt.symm ▸ hx.2.1), ?_⟩
    change hdr post (locN pre "t") 0 = hdr s (locN pre "t") 0 ∧ _
    rw [hpt]
    exact hx.2.2
  have hbe := (InitECandidate.Solver.PanRunBounded.evaluateHOLFiniteState_metadata
    (callEntryStateHOLFinite s callee) body).2.2.1
  rw [hr] at hbe
  have hA_pre : ArenaReady pre := (arenaReady_with_locals s pre.locals s.clock).mpr hA_s
  have hE_pre : TxEnv pre := by
    rcases hE_s with ⟨b1, b2, b3, b4, b5, b6, b7⟩
    exact ⟨b1, b2, b3, b4, b5, by rw [hit]; exact b6, b7⟩
  have hw_pre : WorldTypedWith pre S Nd :=
    (worldTypedWith_with_locals s pre.locals s.clock S Nd).mpr hw
  have ht_pre : locN pre "t" = locN s "aa" := hpt.trans ht
  have ham_pre : locN pre "t" ∈ S := ht_pre.symm ▸ ham
  have haf_pre : ∀ a ∈ worldRoleSlots pre ++ journalRoleSlots pre, a.1 ≠ locN pre "t" := by
    intro a ha'
    rw [ht_pre]
    exact haf a ha'
  have hlim_s : globN pre "heap_ptr" ≤ heapLimit := hA_pre.2.2.1
  have hlim_p : globN {post with locals := s.locals} "heap_ptr" ≤ heapLimit :=
    ((arenaReady_with_locals post s.locals post.clock).mpr hx.1).2.2.1
  -- the store-ready part
  have hstore_pre : PtxStoreReadyIn buffers contents (locN s "aa") pre :=
    phase2_storeReadyIn_setVar_ne (name := ofString "t") buffers contents
      (by decide) (by decide) (.val (.word wa)) hstore
  have hstore' : PtxStoreReadyIn buffers contents (locN s "aa")
      {post with locals := s.locals} := by
    refine phase2_storeReadyIn_world_step buffers contents pre _ hstore_pre
      ((arenaReady_with_locals post s.locals post.clock).mpr hx.1) ?_
      hmp.symm hx.2.2.2.2.1 ?_
    · exact phase2_htabExit_txEnv (post := {post with locals := s.locals}) hA_pre hE_pre
        hw_pre ham_pre (by rw [hit]; rfl) hxp
    · intro S' Nd' hw' hmem'
      have hf' := R16Shards.MptC10C12.worldTypedWith_htab_set_local_csr hA_pre hw'
        (by rw [ht_pre]; exact hmem') haf_pre hxp hbe
      refine ⟨S', Nd', hmem', hf'.1, hf'.2.2.2.2.2.1, ?_⟩
      exact phase2_frameOutside_of_htabExit hxp (by rw [ht_pre]; exact hmem')
        hlim_s hlim_p
  -- the names part
  have hnames' : ∀ name ∈ names, ∃ w : BitVec 64,
      ({post with locals := s.locals}).locals.lookup (ofString name) =
        some (.val (.word w)) := by
    intro name hn
    obtain ⟨w, hw⟩ := hnames name hn
    exact ⟨w, hw⟩
  -- the backing part
  have htx' : R16Shards.TxBacking {post with locals := s.locals} :=
    phase2_htabExit_callEntry_backing callee hA_s hE_s hw ham_ent htx hx
  -- the world part
  have hdisj_pre : IvlsDisj [(locN pre "m", 176)] (worldOwned pre S Nd) := by
    intro o ho j hj
    simp only [List.mem_singleton] at ho; subst o
    rw [hmt]
    exact hdisj _ (by simp) j hj
  have hworld' : PtxMessageTablesA {post with locals := s.locals} (locN s "aa") :=
    phase2_htabExit_a_message_tables hA_pre
      ⟨S, Nd, hw_pre, ham, hal, by rw [← ht_pre]; exact haf_pre, hdisj_pre⟩
      (by rw [hmt]; exact hin_m) hmt.symm hbe ht_pre hxp
  -- the shapes part
  refine ⟨⟨wa, hwa⟩, ⟨hstore', hnames'⟩, htx', ?_, hworld'⟩
  · exact phase2_phase4_shapes_localsOnly s s.locals post.clock (fun _ _ => rfl) hp4

end InitECandidate.Solver.Wave8GuestInv.R13Shards
