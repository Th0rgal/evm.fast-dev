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

/-! ### Segment B part 2a L3: the warming loops on the `aa` table (positions 80..84).

A flowing `call0` restores the caller's locals, so the loop body (`htab_set`
followed by the counter bump) never yields `continue`, and the counter `i` —
which the region invariant never reads — can change freely. -/

/-- A flowing `call0` (no result binding) restores the caller's locals. Local
copy of the delivery-level `call0_flow`, reduced to the shape needed here. -/
private theorem phase2_call0_flow {F : Type} (s : PanSemStateFiniteExact 64 F) (fname : MlS)
    (args : List (ExpHOL 64))
    (hflow : (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = none ∨
      (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = some .continue) :
    ∃ cpost : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState s (.call (some (none, none)) fname args) =
        (none, { cpost with locals := s.locals }) := by
  rw [evaluateHOLFiniteState_call] at hflow ⊢
  revert hflow
  rcases hargs : evalListHOLFinite s
      (h := fun address => Classical.propDecidable (s.memaddrs address)) args with _ | values
  · intro h; rcases h with h | h <;> cases h
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, ret⟩
    · intro h; rcases h with h | h <;> cases h
    · dsimp only
      by_cases hz : s.clock = 0
      · simp only [hz, ↓reduceIte]; intro h; rcases h with h | h <;> cases h
      · simp only [hz, ↓reduceIte]
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
          ⟨res, cpost⟩
        rcases res with _ | r
        · intro h; rcases h with h | h <;> cases h
        · cases r with
          | returned v =>
            try dsimp only
            split
            · intro _; exact ⟨cpost, rfl⟩
            · intro h; rcases h with h | h <;> cases h
          | exception _ _ => (try dsimp only); intro h; rcases h with h | h <;> cases h
          | _ => (try dsimp only); intro h; rcases h with h | h <;> cases h

/-- The while rule of the R13 machinery, with the `IncrBody` side condition
weakened to the only fact the proof uses: the body never yields `continue`
when entered with the counter bound. -/
theorem hoare_while_less_noCont {names : List String}
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : LocalsOnly names P) (counter : MlS) (bound : ExpHOL 64) {body : ProgHOL 64}
    (hp : Hoare P body (fun r t => r = none → P t))
    (hnc : ∀ {F : Type} (st : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState st body).1 ≠ some .continue)
    (hnb : InitECandidate.Solver.GuestUniformClockBound.noTopBreak body = true) :
    Hoare P (.while (.cmp .less (.var .local counter) bound) body) (fun r t => r = none → P t) := by
  refine ⟨fun {F} s hcode hs _ hr => ?_⟩
  rcases hrun : evaluateHOLFiniteState s (.while (.cmp .less (.var .local counter) bound) body) with
    ⟨r, post⟩
  rw [hrun] at hr
  dsimp only at hr
  subst hr
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F),
      st.clock = k → st.code = originalRuntimeCode → P st →
      evaluateHOLFiniteState st (.while (.cmp .less (.var .local counter) bound) body) =
        (none, post) → P post from
    this s.clock s rfl hcode hs hrun
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk st_code hPst hst_run
    rw [evaluateHOLFiniteState_while_total] at hst_run
    split at hst_run
    · rename_i res hcond
      split at hst_run
      · rename_i hwnz
        split at hst_run
        · simp at hst_run
        · dsimp only at hst_run
          rw [fixClockHOLFinite_evaluateState] at hst_run
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hmeta := (InitECandidate.Solver.PanRunBounded.evaluateHOLFiniteState_metadata
            (decClockHOLFinite st) body).1
          have hno_brk :=
            InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak body hnb
              (decClockHOLFinite st)
          have hnc_w := hnc (decClockHOLFinite st)
          rcases bRun : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r1, mid⟩
          rw [bRun] at hst_run hrem hmeta hnc_w hno_brk
          have hclk_lt : mid.clock < k := by
            change mid.clock ≤ st.clock - 1 at hrem
            omega
          cases r1 with
          | none =>
            have hPmid := hp.run (decClockHOLFinite st) st_code
              (hP.decClock st hPst) (by rw [bRun]; simp)
              (by rw [bRun])
            rw [bRun] at hPmid
            exact ih mid.clock hclk_lt mid rfl (hmeta.trans st_code) hPmid hst_run
          | some r1' =>
            cases r1' with
            | «continue» => exact absurd rfl hnc_w
            | «break» => exact absurd rfl hno_brk
            | _ => simp at hst_run
      · simp at hst_run
        obtain ⟨_, rfl⟩ := hst_run
        exact hPst
    · simp at hst_run

/-- The strengthened region invariant reads only the listed locals (and is
clock-insensitive), so the loop-head clock tick preserves it. -/
theorem ptxHtabAInv2_locallyOnly {ι : Type} [Nonempty ι] (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String) :
    LocalsOnly (["aa", "m", "index", "tx", "sender", "gas", "tx_blob_gas_used",
      "price", "intrinsic"] ++ names) (PtxHtabAInv2 buffers contents names) := by
  intro F s locals k hl hp
  obtain ⟨haa_w, ⟨hstore, hnames⟩, htx, hp4, hworld⟩ := hp
  have hlk (n : String) (hn : n ∈ ["aa", "m", "index", "tx", "sender", "gas",
      "tx_blob_gas_used", "price", "intrinsic"] ++ names) :
      locals.lookup (ofString n) = s.locals.lookup (ofString n) := hl n hn
  have haa' : locN { s with locals := locals, clock := k } "aa" = locN s "aa" :=
    locN_congr s locals k "aa" (hlk "aa" (by simp))
  have hm' : locN { s with locals := locals, clock := k } "m" = locN s "m" :=
    locN_congr s locals k "m" (hlk "m" (by simp))
  have h7 : ∀ n ∈ (["tx", "index", "sender", "gas", "tx_blob_gas_used", "price",
      "intrinsic"] : List String),
      locals.lookup (ofString n) = s.locals.lookup (ofString n) := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hlk _ (by simp)
  have hstore' : PtxStoreReadyIn buffers contents
      (locN { s with locals := locals, clock := k } "aa")
      { s with locals := locals, clock := k } := by
    rw [haa']
    refine ⟨(R16Shards.WkBal.worldOK_with_locals s locals k).2 hstore.1,
      txEnv_with_locals s locals k (hlk "index" (by simp)) hstore.2.1, ?_, ?_, ?_, ?_⟩
    · obtain ⟨w, hw⟩ := hstore.2.2.1
      refine ⟨w, ?_⟩
      show locals.lookup (ofString "m") = some (.val (.word w))
      rw [hlk "m" (by simp)]
      exact hw
    · rw [hm']
      exact hstore.2.2.2.1
    · rw [hm']
      exact hstore.2.2.2.2.1
    · intro i
      obtain ⟨hd, S, Nd, hmem, hwS, hb, hsep⟩ := hstore.2.2.2.2.2 i
      rw [hm']
      refine ⟨hd, S, Nd, hmem, ?_, hb, ?_⟩
      · exact (worldTypedWith_with_locals s locals k S Nd).mpr hwS
      · exact hsep
  have hnames' : ∀ name ∈ names, ∃ w : BitVec 64,
      { s with locals := locals, clock := k }.locals.lookup (ofString name) =
        some (.val (.word w)) := by
    intro name hn
    obtain ⟨w, hw⟩ := hnames name hn
    refine ⟨w, ?_⟩
    show locals.lookup (ofString name) = some (.val (.word w))
    rw [hlk name (List.mem_append.2 (Or.inr hn))]
    exact hw
  have hworld' : PtxMessageTablesA { s with locals := locals, clock := k }
      (locN { s with locals := locals, clock := k } "aa") := by
    rw [haa']
    obtain ⟨S, Nd, hwS, ham, hhal, haf, hdisj⟩ := hworld
    refine ⟨S, Nd, (worldTypedWith_with_locals s locals k S Nd).mpr hwS, ham, hhal, haf, ?_⟩
    rw [hm']
    exact hdisj
  obtain ⟨wa, hwa⟩ := haa_w
  have haa_new : locals.lookup (ofString "aa") = some (.val (.word wa)) := by
    rw [hlk "aa" (by simp)]
    exact hwa
  refine ⟨⟨wa, haa_new⟩,
    ⟨hstore', hnames'⟩, htx, phase2_phase4_shapes_localsOnly s locals k h7 hp4, hworld'⟩

/-- Setting the loop counter `i` — a name the region invariant never reads —
preserves the invariant. -/
theorem phase2_htabAInv2_set_i {ι : Type} [Nonempty ι] (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String) (v : ValueHOL 64)
    (hne : ∀ n ∈ names, ofString n ≠ ofString "i")
    {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxHtabAInv2 buffers contents names s) :
    PtxHtabAInv2 buffers contents names (setVarHOLFinite (ofString "i") v s) := by
  have hlk : ∀ n ∈ (["aa", "m", "index", "tx", "sender", "gas", "tx_blob_gas_used",
      "price", "intrinsic"] ++ names : List String),
      (s.locals.update (ofString "i", v)).lookup (ofString n) = s.locals.lookup (ofString n) := by
    intro n hn
    have hni : ofString n ≠ ofString "i" := by
      rcases List.mem_append.1 hn with hb | hb
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      · exact hne n hb
    simp [HolFiniteMapExact.update, FUPDATE, Ne.symm hni]
  exact ptxHtabAInv2_locallyOnly buffers contents names s
    (s.locals.update (ofString "i", v)) s.clock hlk hp

/-- The loop counter increment preserves the region invariant. -/
theorem phase2_htabA_increment_hoare {ι : Type} [Nonempty ι] (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String)
    (hne : ∀ n ∈ names, ofString n ≠ ofString "i") :
    Hoare (PtxHtabAInv2 buffers contents names)
      (.assign .local (ofString "i")
        (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))
      (fun r s => r = none → PtxHtabAInv2 buffers contents names s) := by
  apply Hoare.assign
  · intro F s v hp _
    exact fun _ => phase2_htabAInv2_set_i buffers contents names v hne hp
  · exact fun _ _ hr => by cases hr

/-- The warming-loop body never yields `continue`: a flowing `call0` restores
the caller's locals, and the trailing assign never continues. -/
theorem phase2_warm_body_noCont (fname : MlS) (args : List (ExpHOL 64)) :
    ∀ {F : Type} (st : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState st
        (.seq (.call (some (none, none)) fname args)
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))).1 ≠
        some .continue := by
  intro F st
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hr : evaluateHOLFiniteState st (.call (some (none, none)) fname args) with ⟨r, mid⟩
  cases r with
  | none =>
    exact InitECandidate.Solver.PanRunBounded.evaluate_noTopContinue
      (.assign .local (ofString "i")
        (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))
      (by rfl) mid
  | some r' =>
    cases r' with
    | «continue» =>
      obtain ⟨cpost, hfin⟩ := phase2_call0_flow st fname args (Or.inr (by rw [hr]))
      rw [hr] at hfin
      simp at hfin
    | _ => simp

/-- One warming-loop body: the `htab_set` call followed by the counter bump
preserves the region invariant. -/
theorem phase2_htabA_warm_body {ι : Type} [Nonempty ι] (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String) (key : ExpHOL 64)
    (hne :∀ n ∈ names, ofString n ≠ ofString "i") :
    Hoare (PtxHtabAInv2 buffers contents names)
      (.seq (.call (some (none, none)) (ofString "htab_set")
          [.var .local (ofString "aa"), key, .const (BitVec.ofNat 64 1)])
        (.assign .local (ofString "i")
          (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))
      (fun r s => r = none → PtxHtabAInv2 buffers contents names s) := by
  refine Hoare.seq_fall
    (phase2_htabA_set buffers contents names key (.const (BitVec.ofNat 64 1))) ?_
  exact phase2_htabA_increment_hoare buffers contents names hne

/-- The warming loop over the `aa` table (positions 81..82 and 83..84)
preserves the region invariant. -/
theorem phase2_htabA_warm_while {ι : Type} [Nonempty ι] (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String) (key bound : ExpHOL 64)
    (hne : ∀ n ∈ names, ofString n ≠ ofString "i") :
    Hoare (PtxHtabAInv2 buffers contents names)
      (.while (.cmp .less (.var .local (ofString "i")) bound)
        (.seq (.call (some (none, none)) (ofString "htab_set")
            [.var .local (ofString "aa"), key, .const (BitVec.ofNat 64 1)])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))))
      (fun r s => r = none → PtxHtabAInv2 buffers contents names s) :=
  hoare_while_less_noCont (ptxHtabAInv2_locallyOnly buffers contents names)
    (ofString "i") bound (phase2_htabA_warm_body buffers contents names key hne)
    (phase2_warm_body_noCont (ofString "htab_set")
      [.var .local (ofString "aa"), key, .const (BitVec.ofNat 64 1)])
    (by rfl)

/-- Local copy of the R13 signed-comparison normalization (private there). -/
private theorem phase2_signed_less_eq (left right : BitVec 64) :
    Flapjack.Compiler.Encoders.Asm.holAsmSignedLess left right = left.slt right := by
  have bl := left.isLt
  have br := right.isLt
  simp only [Flapjack.Compiler.Encoders.Asm.holAsmSignedLess, BitVec.slt_eq_decide,
    BitVec.toInt_eq_msb_cond, BitVec.msb_eq_decide]
  repeat (any_goals first | split)
  all_goals simp_all only [decide_eq_true_eq]
  all_goals apply Bool.eq_iff_iff.mpr
  all_goals simp_all [decide_eq_true_eq]
  all_goals omega

/-- The bounded while rule of the R13 machinery, with the `IncrBody` side
condition weakened to the two semantic facts the proof uses: the body never
yields `continue`, and a normal body run increments the counter. -/
theorem while_less_noCont {names : List String}
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : LocalsOnly names P) (counter : MlS) (bound : ExpHOL 64)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn P body B)
    (hp : Hoare P body (fun r t => r = none → P t))
    (hnc : ∀ {F : Type} (st : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState st body).1 ≠ some .continue)
    (hincr : ∀ {F : Type} (st : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      st.locals.lookup counter = some (.val (.word w)) →
      (evaluateHOLFiniteState st body).1 = none →
      (evaluateHOLFiniteState st body).2.locals.lookup counter = some (.val (.word (w + 1)))) :
    TerminatingProgBoundedOn P (.while (.cmp .less (.var .local counter) bound) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  refine TerminatingProgBoundedOn.while_rank (signedUpRank counter)
    (fun s hs => hP.decClock s hs) hbody
    (fun s _ _ _ => signedUpRank_le counter s) ?_
  intro F s hcode hs ⟨result, hcond, hnz⟩ hflow
  change evalAt s _ = _ at hcond
  obtain ⟨w, v, hw, hv, hword⟩ := evalAt_cmp s .less _ _ result hcond
  simp only [evalAt, evalHOLExact] at hw
  have hwl : s.locals.lookup counter = some (.val (.word w)) := by simpa using hw
  have hnc_w := hnc (decClockHOLFinite s)
  have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none := by
    rcases hflow with h | h
    · exact h
    · exact absurd h hnc_w
  have hnt_b : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 ≠ some .timeOut := by
    rw [hnone]; simp
  have hP_post : P (evaluateHOLFiniteState (decClockHOLFinite s) body).2 :=
    hp.run (decClockHOLFinite s) hcode (hP.decClock s hs) hnt_b hnone
  refine ⟨hP_post, ?_⟩
  have hcmp : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .less w v = true := by
    by_contra h; simp [h] at hword; exact hnz hword
  have hlt : w.toInt < v.toInt := by
    simpa only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, phase2_signed_less_eq,
      BitVec.slt_iff_toInt_lt] using hcmp
  have hvmax := BitVec.toInt_le (x := v)
  have hwmin := BitVec.le_toInt w
  have hwmax := BitVec.toInt_le (x := w)
  have hone : (1 : BitVec 64).toInt = 1 := by decide
  have hnext : (w + 1).toInt = w.toInt + 1 := by
    rw [BitVec.toInt_add, hone]
    apply Int.bmod_eq_of_le <;> omega
  have hi' := hincr (decClockHOLFinite s) w hwl hnone
  simp only [signedUpRank, hi', hwl, hnext]
  omega

/-- A normal warming-loop body run increments the counter: the flowing call
restores the caller's locals, so the trailing assign bumps `i` from `w` to
`w + 1`. -/
theorem phase2_warm_body_incr (fname : MlS) (args : List (ExpHOL 64)) :
    ∀ {F : Type} (st : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      st.locals.lookup (ofString "i") = some (.val (.word w)) →
      (evaluateHOLFiniteState st
        (.seq (.call (some (none, none)) fname args)
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))).1 = none →
      (evaluateHOLFiniteState st
        (.seq (.call (some (none, none)) fname args)
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))).2.locals.lookup
          (ofString "i") = some (.val (.word (w + 1))) := by
  intro F st w hi hnone
  rw [evaluateHOLFiniteState_seq_line780] at hnone ⊢
  rcases hr : evaluateHOLFiniteState st (.call (some (none, none)) fname args) with ⟨r, mid⟩
  cases r with
  | none =>
    rw [hr] at hnone
    dsimp only at hnone ⊢
    obtain ⟨cpost, hfin⟩ := phase2_call0_flow st fname args (Or.inl (by rw [hr]))
    rw [hr] at hfin
    obtain ⟨-, hmid⟩ := Prod.mk.inj hfin
    subst hmid
    exact ((IncrBody.incr (c := ofString "i")).run {cpost with locals := st.locals} w hi).2
      hnone
  | some r' =>
    cases r' with
    | «continue» =>
      obtain ⟨cpost, hfin⟩ := phase2_call0_flow st fname args (Or.inr (by rw [hr]))
      rw [hr] at hfin
      simp at hfin
    | _ =>
      rw [hr] at hnone
      simp at hnone

/-- The warming-loop body is clock-bounded: the `htab_set` call plus one
assign step. -/
theorem phase2_htabA_warm_body_bound (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (names : List String)
    (key : ExpHOL 64) :
    TerminatingProgBoundedOn (PtxHtabAInv2 buffers contents names)
      (.seq (.call (some (none, none)) (ofString "htab_set")
          [.var .local (ofString "aa"), key, .const (BitVec.ofNat 64 1)])
        (.assign .local (ofString "i")
          (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))
      (K.htab_set + 1) := by
  have hcall : TerminatingProgBoundedOn (PtxHtabAInv2 buffers contents names)
      (.call (some (none, none)) (ofString "htab_set")
        [.var .local (ofString "aa"), key, .const (BitVec.ofNat 64 1)])
      (K.htab_set + 1) := by
    apply TerminatingProgBoundedOn.call_on h.fb_htab_set none _
    intro F s vs body callee ret hc hp he hl
    exact guestInv_callEntry s callee (worldOK_guestInv s hp.2.1.1.1)
  have hassign : TerminatingProgBoundedOn (PtxHtabAInv2 buffers contents names)
      (.assign .local (ofString "i")
        (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))
      0 :=
    R16Shards.PtxP1.bound_of_clock (P := PtxHtabAInv2 buffers contents names)
      (fun s => clock_assign s .local (ofString "i")
        (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))
  intro F s hc hp
  simpa only [Nat.add_zero] using seq_bound_trans hcall
    (phase2_htabA_set buffers contents names key (.const (BitVec.ofNat 64 1))) hassign s hc hp

/-- The warming loop over the `aa` table is clock-bounded. -/
theorem phase2_htabA_warm_while_bound (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (names : List String)
    (key bound : ExpHOL 64) (hne : ∀ n ∈ names, ofString n ≠ ofString "i") :
    TerminatingProgBoundedOn (PtxHtabAInv2 buffers contents names)
      (.while (.cmp .less (.var .local (ofString "i")) bound)
        (.seq (.call (some (none, none)) (ofString "htab_set")
            [.var .local (ofString "aa"), key, .const (BitVec.ofNat 64 1)])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))))
      ((2 ^ 64 + 1) * (K.htab_set + 1 + 1)) :=
  while_less_noCont (ptxHtabAInv2_locallyOnly buffers contents names) (ofString "i") bound
    (phase2_htabA_warm_body_bound h buffers contents names key)
    (phase2_htabA_warm_body buffers contents names key hne)
    (phase2_warm_body_noCont (ofString "htab_set")
      [.var .local (ofString "aa"), key, .const (BitVec.ofNat 64 1)])
    (phase2_warm_body_incr (ofString "htab_set")
      [.var .local (ofString "aa"), key, .const (BitVec.ofNat 64 1)])

/-! ### Segment B part 2a L5: the spine through the warming loops (positions 80..84).

Positions 80..84 are: initialize the loop counter, warm the `aa` table from
the precompile address table, re-initialize the counter, warm it from the
access-list address table. Both surrounding source `skip`s are included so
the lemma matches the exact source spine. -/

/-- Initializing the loop counter preserves the region invariant. -/
theorem phase2_htabA_assign0_hoare {ι : Type} [Nonempty ι] (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String)
    (hne : ∀ n ∈ names, ofString n ≠ ofString "i") :
    Hoare (PtxHtabAInv2 buffers contents names)
      (.assign .local (ofString "i") (.const (BitVec.ofNat 64 0)))
      (fun r s => r = none → PtxHtabAInv2 buffers contents names s) := by
  apply Hoare.assign
  · intro F s v hp _
    exact fun _ => phase2_htabAInv2_set_i buffers contents names v hne hp
  · exact fun _ _ hr => by cases hr

/-- The warming spine (positions 80..84 with its surrounding `skip`s)
preserves the region invariant, with a clock bound of two bounded warming
loops plus the tail's. -/
theorem phase2_htabA_warm_spine_bound (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (names : List String)
    (hne : ∀ n ∈ names, ofString n ≠ ofString "i")
    {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn (PtxHtabAInv2 buffers contents names) tail b) :
    TerminatingProgBoundedOn (PtxHtabAInv2 buffers contents names)
      (.seq .skip
        (.seq (.assign .local (ofString "i") (.const (BitVec.ofNat 64 0)))
          (.seq (.while (.cmp .less (.var .local (ofString "i"))
                  (.const (BitVec.ofNat 64 18)))
                (.seq (.call (some (none, none)) (ofString "htab_set")
                    [.var .local (ofString "aa"),
                     .op .add [.var .global (ofString "precompile_addrs"),
                       .panop .mul [.var .local (ofString "i"),
                         .const (BitVec.ofNat 64 20)]],
                     .const (BitVec.ofNat 64 1)])
                  (.assign .local (ofString "i")
                    (.op .add [.var .local (ofString "i"),
                      .const (BitVec.ofNat 64 1)]))))
            (.seq (.assign .local (ofString "i") (.const (BitVec.ofNat 64 0)))
              (.seq (.while (.cmp .less (.var .local (ofString "i"))
                      (.op .add [.var .local (ofString "nal"),
                        .const (BitVec.ofNat 64 1)]))
                    (.seq (.call (some (none, none)) (ofString "htab_set")
                        [.var .local (ofString "aa"),
                         .load .one (.op .add [.var .local (ofString "al_addrs"),
                           .panop .mul [.var .local (ofString "i"),
                             .const (BitVec.ofNat 64 8)]]),
                         .const (BitVec.ofNat 64 1)])
                      (.assign .local (ofString "i")
                        (.op .add [.var .local (ofString "i"),
                          .const (BitVec.ofNat 64 1)]))))
                (.seq .skip tail))))))
      ((2 ^ 64 + 1) * (K.htab_set + 1 + 1) +
        ((2 ^ 64 + 1) * (K.htab_set + 1 + 1) + b)) := by
  have hskip : Hoare (PtxHtabAInv2 buffers contents names) .skip
      (fun r s => r = none → PtxHtabAInv2 buffers contents names s) :=
    Hoare.skip (fun _ hp _ => hp)
  have hskipb : TerminatingProgBoundedOn (PtxHtabAInv2 buffers contents names) .skip 0 :=
    R16Shards.PtxP1.bound_of_clock (P := PtxHtabAInv2 buffers contents names)
      (fun s => clock_skip s)
  have ha0 : Hoare (PtxHtabAInv2 buffers contents names)
      (.assign .local (ofString "i") (.const (BitVec.ofNat 64 0)))
      (fun r s => r = none → PtxHtabAInv2 buffers contents names s) :=
    phase2_htabA_assign0_hoare buffers contents names hne
  have ha0b : TerminatingProgBoundedOn (PtxHtabAInv2 buffers contents names)
      (.assign .local (ofString "i") (.const (BitVec.ofNat 64 0))) 0 :=
    R16Shards.PtxP1.bound_of_clock (P := PtxHtabAInv2 buffers contents names)
      (fun s => clock_assign s .local (ofString "i") (.const (BitVec.ofNat 64 0)))
  intro F s hc hp
  simpa only [Nat.zero_add, Nat.add_zero] using
    seq_bound_trans hskipb hskip
      (seq_bound_trans ha0b ha0
        (seq_bound_trans
          (phase2_htabA_warm_while_bound h buffers contents names
            (.op .add [.var .global (ofString "precompile_addrs"),
              .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 20)]])
            (.const (BitVec.ofNat 64 18)) hne)
          (phase2_htabA_warm_while buffers contents names
            (.op .add [.var .global (ofString "precompile_addrs"),
              .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 20)]])
            (.const (BitVec.ofNat 64 18)) hne)
          (seq_bound_trans ha0b ha0
            (seq_bound_trans
              (phase2_htabA_warm_while_bound h buffers contents names
                (.load .one (.op .add [.var .local (ofString "al_addrs"),
                  .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]]))
                (.op .add [.var .local (ofString "nal"), .const (BitVec.ofNat 64 1)]) hne)
              (phase2_htabA_warm_while buffers contents names
                (.load .one (.op .add [.var .local (ofString "al_addrs"),
                  .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]]))
                (.op .add [.var .local (ofString "nal"), .const (BitVec.ofNat 64 1)]) hne)
              (seq_bound_trans hskipb hskip ht))))) s hc hp

/-! ### Segment B part 2a L6: the `ak := htab_new(52, 16)` rung.

The invariant strengthens over the warming spine: every saved-buffer world must
contain BOTH live table roots, and the region carries the two-table world
witness in the downstream `PtxMessageTables` shape. -/

/-- Store-ready where every saved-buffer world contains both live tables. -/
def PtxStoreReadyIn2 {ι : Type} (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (t1 t2 : Nat) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop := fun s =>
  WorldOK s ∧ TxEnv s ∧
  (∃ w : BitVec 64, s.locals.lookup (ofString "m") = some (.val (.word w))) ∧
  Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr") ∧
  WordsOK s (locN s "m", 176) ∧
  ∀ i, Disj (buffers i) (locN s "m", 176) ∧
    ∃ S Nd, t1 ∈ S ∧ t2 ∈ S ∧ WorldTypedWith s S Nd ∧
      PtxLiveBufferAt s S Nd (buffers i) (contents i) ∧
      IvlsDisj [(locN s "m", 176)] (worldOwned s S Nd)

/-- A `setVar` of a name other than `m` preserves the two-table store
invariant (only the `m` and `index` locals are read by the store predicate). -/
theorem phase2_storeReadyIn2_setVar_ne {ι F : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) {t1 t2 : Nat} {name : MlS}
    (hne : ofString "m" ≠ name) (hni : ofString "index" ≠ name) (v : ValueHOL 64)
    {s : PanSemStateFiniteExact 64 F} (hp : PtxStoreReadyIn2 buffers contents t1 t2 s) :
    PtxStoreReadyIn2 buffers contents t1 t2 (setVarHOLFinite name v s) := by
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
    obtain ⟨hd, S, Nd, hmem1, hmem2, hw, hb, hsep⟩ := hbufs i
    refine ⟨?_, S, Nd, hmem1, hmem2,
      (worldTypedWith_with_locals s (s.locals.update (name, v)) s.clock S Nd).mpr hw, hb, ?_⟩
    · rw [hmn]; exact hd
    · rw [hmn]; exact hsep

/-- The htab region after both table allocations, with two-table buffer worlds:
the old root stays in every world, the fresh root is appended. -/
theorem phase2_htab_new_store_ready_in2 {ι F : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    {s post : PanSemStateFiniteExact 64 F} {t1 : Nat}
    (hp : PtxStoreReadyIn buffers contents t1 s)
    (hAp : ArenaReady post) (hag : AllocatorGrows s post) {t : Nat}
    (hwf_t : HtabWF post t)
    (hfp_t : ∀ i ∈ htabFootprint post t, Allocated post i ∧
      (Inside i (globN s "heap_ptr") (globN post "heap_ptr") ∨
        Inside i (globN post "scratch_ptr") (globN s "scratch_ptr")))
    (hfr : FrameOutside s post
      [(globN post "scratch_ptr", globN s "scratch_ptr" - globN post "scratch_ptr")]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    (hbe : post.be = s.be) (hg_kept : GlobalsKept ["heap_ptr", "scratch_ptr"] s post) :
    PtxStoreReadyIn2 buffers contents t1 t {post with locals := s.locals} := by
  have hgs : R16Shards.GbodyC17ToC21Common.WorldGlobalsSame s post :=
    R16Shards.GbodyC17ToC21Common.worldGlobalsSame_of_globalsKept hg_kept
      (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨hW, hE, hm_w, hin_m, hwok_m, hbufs⟩ := hp
  obtain ⟨hA_s, S0, hWT⟩ := hW
  obtain ⟨Nd0, hw0⟩ := (worldTyped_iff_with s S0).1 hWT
  have hext := R16Shards.GbodyC17ToC21Common.worldTypedWith_htab_new hA_s hw0 hAp hag hwf_t
    hfp_t hfr hbe hg_kept
  have hA_mid : ArenaReady {post with locals := s.locals} :=
    (arenaReady_with_locals post s.locals post.clock).mpr hAp
  have hW_mid_ext : WorldTypedWith {post with locals := s.locals} (S0 ++ [t]) Nd0 :=
    (worldTypedWith_with_locals post s.locals post.clock (S0 ++ [t]) Nd0).mpr
      hext.2.2.2.1
  refine ⟨⟨hA_mid, S0 ++ [t], (worldTyped_iff_with _ (S0 ++ [t])).2 ⟨Nd0, hW_mid_ext⟩⟩,
    phase2_htab_new_txEnv hA_s hAp hE hw0 hag hgs hfr, hm_w,
    ⟨hin_m.1, hin_m.2.trans hag.1⟩, ?_, ?_⟩
  · exact wordsOK_transfer hA_s.1 hA_mid.1 hwok_m
  · intro i
    obtain ⟨hd, S_i, Nd_i, hmem1, hw_i, hb_i, hsep_i⟩ := hbufs i
    refine ⟨hd, S_i ++ [t], Nd_i, ?_, by simp, ?_, ?_, ?_⟩
    · exact List.mem_append.2 (Or.inl hmem1)
    · exact (worldTypedWith_with_locals post s.locals post.clock (S_i ++ [t]) Nd_i).mpr
        ((R16Shards.GbodyC17ToC21Common.worldTypedWith_htab_new hA_s hw_i hAp hag hwf_t
          hfp_t hfr hbe hg_kept).2.2.2.1)
    · exact phase2_htab_new_live_buffer hA_s hw_i hAp hag hfp_t hfr hbe hgs hb_i
    · intro o ho j hj
      simp only [List.mem_singleton] at ho; subst o
      exact phase2_htab_new_world_disj hA_s hw_i hAp hag hfp_t hfr hbe hgs hin_m
        (fun j' hj' => hsep_i _ (by simp) j' hj') j hj

/-- Setting `ak` (never read by Phase 4) preserves the Phase 4 caller-local
shapes. -/
theorem phase2_p4Shapes_htab_new_ak {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) (h : R16Shards.PtxPhase4LocalShapes s) :
    R16Shards.PtxPhase4LocalShapes
      (setVarHOLFinite (ofString "ak") v {post with locals := s.locals}) := by
  have hlu : ∀ name : String, ofString name ≠ ofString "ak" →
      (setVarHOLFinite (ofString "ak") v {post with locals := s.locals}).locals.lookup
        (ofString name) = s.locals.lookup (ofString name) := by
    intro name hn
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm hn]
  refine ⟨?_, ?_, ?_⟩
  · intro name hn
    have hne : ofString name ≠ ofString "ak" := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hlu name hne]
    exact h.1 name hn
  · rw [hlu "price" (by decide)]; exact h.2.1
  · rw [hlu "intrinsic" (by decide)]; exact h.2.2

/-- The htab region after both table allocations (positions 86..89): the
B-scalar frame with two-table buffer worlds, plus the two-table world witness
in the downstream `PtxMessageTables` shape. -/
def PtxHtabABInv {ι : Type} (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop := fun s =>
  (∃ w : BitVec 64, s.locals.lookup (ofString "aa") = some (.val (.word w))) ∧
  (∃ w : BitVec 64, s.locals.lookup (ofString "ak") = some (.val (.word w))) ∧
  (PtxStoreReadyIn2 buffers contents (locN s "aa") (locN s "ak") s ∧
    ∀ name ∈ names, ∃ w : BitVec 64,
      s.locals.lookup (ofString name) = some (.val (.word w))) ∧
  R16Shards.TxBacking s ∧ R16Shards.PtxPhase4LocalShapes s ∧
  PtxMessageTables s (locN s "aa") (locN s "ak")

/-- Resuming after the `ak` allocation (position 86) with the two-table
invariant. -/
theorem phase2_htabA_new_ak_resume (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (names : List String)
    (hne : ∀ name ∈ names, ofString name ≠ ofString "ak") :
    DecCallResumeOn (PtxHtabAInv2 buffers contents names)
      (PtxHtabABInv buffers contents names)
      (ofString "ak") (ofString "htab_new") [.const (52#64), .const (16#64)] := by
  intro F s vs body callee ret v post hc hp he hl hb
  obtain ⟨haa_w, ⟨hstore, hnames⟩, htx, hp4, hworld⟩ := hp
  obtain ⟨S_w, Nd_w, hw_w, ham_w, hal_w, haf_w, hdisj_w⟩ := hworld
  have hsReady : PtxMessageStoreReady buffers contents s := hstore.to_storeReady
  have hA_s : ArenaReady s := hstore.1.1
  have hE_s : TxEnv s := hstore.2.1
  have hin_m : Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr") :=
    hstore.2.2.2.1
  obtain ⟨S0, hWT⟩ := hstore.1.2
  obtain ⟨Nd0, hw0⟩ := (worldTyped_iff_with s S0).mp hWT
  have hc2 := R16Shards.callee_param_two s (ofString "htab_new") (ofString "key_len")
    (ofString "cap") .one .one _ _
    (by rw [hc]; exact R10Shards.SoloHtabNew.lookup_htab_new) (.const (52#64)) (.const (16#64))
    (.val (.word (52#64))) (.val (.word (16#64))) vs body callee ret
    (by simp [evalAt, evalHOLExact]) (by simp [evalAt, evalHOLExact]) he hl
  have hkl : locN (callEntryStateHOLFinite s callee) "key_len" = 52 := by
    unfold locN callEntryStateHOLFinite; dsimp only; rw [hc2.2.1]; decide
  have hcap : locN (callEntryStateHOLFinite s callee) "cap" = 16 := by
    unfold locN callEntryStateHOLFinite; dsimp only; rw [hc2.2.2]; decide
  have hA_ent : ArenaReady (callEntryStateHOLFinite s callee) :=
    (arenaReady_with_locals s callee (s.clock - 1)).mpr hA_s
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
  -- the world-with-ak witness: extend one saved-buffer world (it contains aa)
  obtain ⟨i0⟩ := ‹Nonempty ι›
  obtain ⟨_, S_i, Nd_i, hmem_aa_i, hw_i, hb_i, hsep_i⟩ := hstore.2.2.2.2.2 i0
  have hW_i' := R16Shards.GbodyC17ToC21Common.worldTypedWith_htab_new hA_ent
    ((worldTypedWith_with_locals s callee (s.clock - 1) S_i Nd_i).mpr hw_i)
    hAp hag hwf_t hfp_t hfr hmeta hgk
  have hak : locN (setVarHOLFinite (ofString "ak") (.val (.word w))
      {post with locals := s.locals}) "ak" = w.toNat :=
    locN_setVar_same _ "ak" w
  have haa_ne : locN (setVarHOLFinite (ofString "ak") (.val (.word w))
      {post with locals := s.locals}) "aa" = locN s "aa" :=
    locN_setVar_ne _ "aa" (ofString "ak") _ (by decide)
  have hmm : locN (setVarHOLFinite (ofString "ak") (.val (.word w))
      {post with locals := s.locals}) "m" = locN s "m" :=
    locN_setVar_ne _ "m" (ofString "ak") _ (by decide)
  have hw_mid : WorldTypedWith (setVarHOLFinite (ofString "ak") (.val (.word w))
      {post with locals := s.locals}) (S_i ++ [w.toNat]) Nd_i :=
    (worldTypedWith_with_locals post (s.locals.update (ofString "ak", .val (.word w)))
      post.clock (S_i ++ [w.toNat]) Nd_i).mpr hW_i'.2.2.2.1
  have hsr2 : PtxStoreReadyIn2 buffers contents
      (locN (setVarHOLFinite (ofString "ak") (.val (.word w))
        {post with locals := s.locals}) "aa")
      (locN (setVarHOLFinite (ofString "ak") (.val (.word w))
        {post with locals := s.locals}) "ak")
      (setVarHOLFinite (ofString "ak") (.val (.word w)) {post with locals := s.locals}) := by
    rw [haa_ne, hak]
    exact phase2_storeReadyIn2_setVar_ne buffers contents (name := ofString "ak")
      (by decide) (by decide) (.val (.word w))
      (phase2_htab_new_store_ready_in2 buffers contents hstore hAp hag hwf_t hfp_t
        hfr hmeta hgk)
  have htxb0 : R16Shards.TxBacking post :=
    phase2_htab_new_txBacking hA_s hAp hE_s hw0 htx hag hgs hfr
  have htxb : R16Shards.TxBacking
      (setVarHOLFinite (ofString "ak") (.val (.word w)) {post with locals := s.locals}) :=
    htxb0
  have hnames' : ∀ name ∈ names, ∃ w' : BitVec 64,
      (setVarHOLFinite (ofString "ak") (.val (.word w))
        {post with locals := s.locals}).locals.lookup (ofString name) =
        some (.val (.word w')) := by
    intro name hn
    obtain ⟨w', hw'⟩ := hnames name hn
    refine ⟨w', ?_⟩
    have hne' : ofString name ≠ ofString "ak" := hne name hn
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm hne']
    exact hw'
  obtain ⟨wa, hwa⟩ := haa_w
  have haa_lu : (setVarHOLFinite (ofString "ak") (.val (.word w))
      {post with locals := s.locals}).locals.lookup (ofString "aa") =
      s.locals.lookup (ofString "aa") := by
    have hne' : ofString "ak" ≠ ofString "aa" := by decide
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne']
  refine ⟨⟨wa, by rw [haa_lu]; exact hwa⟩, ⟨w, by
      simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]⟩, ⟨hsr2, hnames'⟩, htxb,
    phase2_p4Shapes_htab_new_ak s post (.val (.word w)) hp4,
    S_i ++ [w.toNat], Nd_i, hw_mid, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [haa_ne]; exact List.mem_append.2 (Or.inl hmem_aa_i)
  · rw [hak]; simp
  · rw [haa_ne]
    exact (hW_i'.2.2.2.2.2.2.1 (locN s "aa") hmem_aa_i).trans hal_w
  · rw [hak]; exact hkl0.trans hkl
  · rw [haa_ne]
    intro a ha'
    have h1 : a ∈ worldRoleSlots (callEntryStateHOLFinite s callee) ++
        journalRoleSlots (callEntryStateHOLFinite s callee) := by
      rw [← hW_i'.2.2.2.2.1, ← hW_i'.2.2.2.2.2.1]
      exact ha'
    exact haf_w a h1
  · rw [hak]; exact hW_i'.2.2.1
  · intro o ho j hj
    simp only [List.mem_singleton] at ho; subst o
    rw [hmm]
    exact phase2_htab_new_world_disj hA_s hw_i hAp hag hfp_t hfr hmeta hgs hin_m
      (fun j' hj' => hsep_i _ (by simp) j' hj') j hj

end InitECandidate.Solver.Wave8GuestInv.R13Shards
