import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2StrongTail

namespace InitECandidate.Solver.Wave8GuestInv.R13Shards
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.Wave8GuestInv

/-! ### Segment B part 2a L7: the warming loop on the `ak` table (positions 87..88). -/

/-- The htab_set exit preserves the two-table world witness. -/
theorem phase2_htabExit_ab_message_tables {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {aa ak : Nat}
    (hs : ArenaReady s) (hm : PtxMessageTables s aa ak)
    (hin : Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr"))
    (hl : locN post "m" = locN s "m") (hbe : post.be = s.be)
    (ht : locN s "t" = ak) (hx : HtabExit s post) :
    PtxMessageTables post aa ak := by
  obtain ⟨S, Nd, hw, ham, hkm, hal, hkl, haf, hkf, hd⟩ := hm
  have hf := R16Shards.MptC10C12.worldTypedWith_htab_set_local_csr hs hw
    (ht.symm ▸ hkm) (ht.symm ▸ hkf) hx hbe
  refine ⟨S, Nd, hf.1, ham, hkm, (hf.2.2.2.2.1 aa ham).trans hal,
    (hf.2.2.2.2.1 ak hkm).trans hkl, ?_, ?_, ?_⟩
  · simpa only [hf.2.1, hf.2.2.1] using haf
  · simpa only [hf.2.1, hf.2.2.1] using hkf
  · intro o ho j hj
    simp only [List.mem_singleton] at ho; subst o
    rw [hl]
    exact (hf.2.2.2.2.2.2 (locN s "m", 176) (by intro h; omega) hin
      (fun j hj => hd _ (by simp) j hj)).2.1 j hj

/-- Two-table store readiness transports across a world step whose frame
keeps every world that contains both tables. -/
theorem phase2_storeReadyIn2_world_step {ι F : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) {t1 t2 : Nat}
    (s post : PanSemStateFiniteExact 64 F)
    (hp : PtxStoreReadyIn2 buffers contents t1 t2 s)
    (ha : ArenaReady post) (he : TxEnv post)
    (hl : post.locals.lookup (ofString "m") = s.locals.lookup (ofString "m"))
    (hh : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hs : ∀ S Nd, WorldTypedWith s S Nd → t1 ∈ S → t2 ∈ S →
      ∃ S' Nd', t1 ∈ S' ∧ t2 ∈ S' ∧ WorldTypedWith post S' Nd' ∧
        OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd') ∧
        FrameOutside s post (worldOwned s S Nd ++ [] ++ [freeGap s]) (heapFree s)) :
    PtxStoreReadyIn2 buffers contents t1 t2 post := by
  have hm : locN post "m" = locN s "m" := by simp only [locN, hl]
  have hf : ∀ i, ∃ S Nd, t1 ∈ S ∧ t2 ∈ S ∧ WorldTypedWith post S Nd ∧
      PtxLiveBufferAt post S Nd (buffers i) (contents i) ∧
      IvlsDisj [(locN s "m", 176)] (worldOwned post S Nd) := by
    intro i
    obtain ⟨hd, S, Nd, hmem1, hmem2, hw, hb, hmd⟩ := hp.2.2.2.2.2 i
    obtain ⟨S', Nd', hmem1', hmem2', hw', hg, hfr⟩ := hs S Nd hw hmem1 hmem2
    refine ⟨S', Nd', hmem1', hmem2', hw', ?_, ?_⟩
    · exact phase2_live_buffer_step s post S Nd S' Nd' (buffers i) (contents i) []
        hb hp.1.1.2 hw hh hg hfr (by simp) (by simp)
    · exact phase2_packed_owned_growth s post _ _ (locN s "m", 176)
        hp.2.2.2.1 hg hmd
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨S, Nd, _, _, hw, _, _⟩ := hf i
  refine ⟨⟨ha, S, (worldTyped_iff_with post S).mpr ⟨Nd, hw⟩⟩, he, ?_, ?_, ?_, ?_⟩
  · simpa only [hl] using hp.2.2.1
  · rw [hm]
    exact ⟨hp.2.2.2.1.1, hp.2.2.2.1.2.trans hh⟩
  · rw [hm]
    exact wordsOK_transfer hp.1.1.1 ha.1 hp.2.2.2.2.1
  · intro j
    rw [hm]
    exact ⟨(hp.2.2.2.2.2 j).1, hf j⟩

/-- Key insertion into the `ak` table preserves the whole two-table region
invariant (the ak warming loop's body). -/
theorem phase2_htabAB_set {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (names : List String)
    (key value : ExpHOL 64) :
    Hoare (PtxHtabABInv buffers contents names)
      (.call (some (none, none)) (ofString "htab_set")
        [.var .local (ofString "ak"), key, value])
      (fun r s => r = none → PtxHtabABInv buffers contents names s) := by
  apply Hoare.call0_resume
  intro F s vs body callee ret v post hc hp ha hl hr
  obtain ⟨haa_w, hak_w, ⟨hstore, hnames⟩, htx, hp4, hworld⟩ := hp
  obtain ⟨S, Nd, hw, ham, hkm, hal, hkl, haf, hkf, hdisj⟩ := hworld
  obtain ⟨v1, _, _, he1, _, _, hct, _, _⟩ := R16WkAcctWs.callee_param_three s
    (ofString "htab_set") (ofString "t") (ofString "key") (ofString "value")
    .one .one .one _ _ (by rw [hc]; exact EvmFrameSpecs.lookup_htab_set)
    _ _ _ vs body callee ret ha hl
  have hev : s.locals.lookup (ofString "ak") = some v1 := by
    simpa [evalAt, evalHOLExact] using he1
  obtain ⟨wk, hwk⟩ := hak_w
  have hv1 : v1 = .val (.word wk) := by
    rw [hev] at hwk
    exact Option.some.inj hwk
  subst hv1
  have hak_root : locN s "ak" = wk.toNat := by simp [locN, hwk]
  have ht : locN (callEntryStateHOLFinite s callee) "t" = locN s "ak" := by
    simp [locN, callEntryStateHOLFinite, hct, hwk]
  have hA_s : ArenaReady s := hstore.1.1
  have hE_s : TxEnv s := hstore.2.1
  have hin_m : Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr") :=
    hstore.2.2.2.1
  have hA_ent : ArenaReady (callEntryStateHOLFinite s callee) :=
    (arenaReady_with_locals s callee (s.clock - 1)).mpr hA_s
  have hw_ent : WorldTypedWith (callEntryStateHOLFinite s callee) S Nd :=
    (worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hw
  have hkm_ent : locN (callEntryStateHOLFinite s callee) "t" ∈ S := ht.symm ▸ hkm
  have harg : HtabArgWF (callEntryStateHOLFinite s callee) := by
    refine ⟨hA_ent, ?_, ?_⟩
    · rw [ht]
      exact (htabWF_with_locals s callee (s.clock - 1) _).mpr (hw.1.2.1 _ hkm).1
    · rw [ht]
      exact fun i hi => ((hw.1.2.1 _ hkm).2 i hi).1
  have hx := FunSpec.at_lookup htab_set_spec s hc vs body callee ret hl harg (by rw [hr]; simp)
  rw [hr] at hx
  have hx := hx v rfl
  -- move to the `pre` state that binds `t` to the `ak` value
  let pre := setVarHOLFinite (ofString "t") (.val (.word wk)) s
  have hmp : pre.locals.lookup (ofString "m") = s.locals.lookup (ofString "m") := by
    simp [pre, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "t" ≠ ofString "m" by decide]
  have hip : pre.locals.lookup (ofString "index") = s.locals.lookup (ofString "index") := by
    simp [pre, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "t" ≠ ofString "index" by decide]
  have haa_p : pre.locals.lookup (ofString "aa") = s.locals.lookup (ofString "aa") := by
    simp [pre, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "t" ≠ ofString "aa" by decide]
  have hak_p : pre.locals.lookup (ofString "ak") = s.locals.lookup (ofString "ak") := by
    simp [pre, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "t" ≠ ofString "ak" by decide]
  have hmt : locN pre "m" = locN s "m" := locN_congr s pre.locals s.clock "m" hmp
  have hit : locN pre "index" = locN s "index" := locN_congr s pre.locals s.clock "index" hip
  have hap : locN pre "aa" = locN s "aa" := locN_congr s pre.locals s.clock "aa" haa_p
  have hkp : locN pre "ak" = locN s "ak" := locN_congr s pre.locals s.clock "ak" hak_p
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
  have ht_pre : locN pre "t" = locN s "ak" := hpt.trans ht
  have hkm_pre : locN pre "t" ∈ S := ht_pre.symm ▸ hkm
  have hkf_pre : ∀ a ∈ worldRoleSlots pre ++ journalRoleSlots pre, a.1 ≠ locN pre "t" := by
    intro a ha'
    rw [ht_pre]
    exact hkf a ha'
  have hlim_s : globN pre "heap_ptr" ≤ heapLimit := hA_pre.2.2.1
  have hlim_p : globN {post with locals := s.locals} "heap_ptr" ≤ heapLimit :=
    ((arenaReady_with_locals post s.locals post.clock).mpr hx.1).2.2.1
  -- the store-ready part
  have hstore_pre : PtxStoreReadyIn2 buffers contents (locN s "aa") (locN s "ak") pre :=
    phase2_storeReadyIn2_setVar_ne (name := ofString "t") buffers contents
      (by decide) (by decide) (.val (.word wk)) hstore
  have hstore' : PtxStoreReadyIn2 buffers contents (locN s "aa") (locN s "ak")
      {post with locals := s.locals} := by
    refine phase2_storeReadyIn2_world_step buffers contents pre _ hstore_pre
      ((arenaReady_with_locals post s.locals post.clock).mpr hx.1) ?_
      hmp.symm hx.2.2.2.2.1 ?_
    · exact phase2_htabExit_txEnv (post := {post with locals := s.locals}) hA_pre hE_pre
        hw_pre hkm_pre (by rw [hit]; rfl) hxp
    · intro S' Nd' hw' hmem1' hmem2'
      have hf' := R16Shards.MptC10C12.worldTypedWith_htab_set_local_csr hA_pre hw'
        (by rw [ht_pre]; exact hmem2') hkf_pre hxp hbe
      refine ⟨S', Nd', hmem1', hmem2', hf'.1, hf'.2.2.2.2.2.1, ?_⟩
      exact phase2_frameOutside_of_htabExit hxp (by rw [ht_pre]; exact hmem2')
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
    phase2_htabExit_callEntry_backing callee hA_s hE_s hw hkm_ent htx hx
  -- the world part
  have hdisj_pre : IvlsDisj [(locN pre "m", 176)] (worldOwned pre S Nd) := by
    intro o ho j hj
    simp only [List.mem_singleton] at ho; subst o
    rw [hmt]
    exact hdisj _ (by simp) j hj
  have hworld' : PtxMessageTables {post with locals := s.locals}
      (locN s "aa") (locN s "ak") :=
    phase2_htabExit_ab_message_tables hA_pre
      ⟨S, Nd, hw_pre, ham, hkm, hal, hkl, haf, hkf, hdisj_pre⟩
      (by rw [hmt]; exact hin_m) hmt.symm hbe ht_pre hxp
  -- the shapes part
  obtain ⟨wa, hwa⟩ := haa_w
  refine ⟨⟨wa, hwa⟩, ⟨wk, hwk⟩, ⟨hstore', hnames'⟩, htx', ?_, hworld'⟩
  · exact phase2_phase4_shapes_localsOnly s s.locals post.clock (fun _ _ => rfl) hp4

/-- The two-table region invariant reads only the listed locals (and is
clock-insensitive), so the loop-head clock tick preserves it. -/
theorem ptxHtabABInv_locallyOnly {ι : Type} [Nonempty ι] (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String) :
    LocalsOnly (["aa", "ak", "m", "index", "tx", "sender", "gas", "tx_blob_gas_used",
      "price", "intrinsic"] ++ names) (PtxHtabABInv buffers contents names) := by
  intro F s locals k hl hp
  obtain ⟨haa_w, hak_w, ⟨hstore, hnames⟩, htx, hp4, hworld⟩ := hp
  have hlk (n : String) (hn : n ∈ ["aa", "ak", "m", "index", "tx", "sender", "gas",
      "tx_blob_gas_used", "price", "intrinsic"] ++ names) :
      locals.lookup (ofString n) = s.locals.lookup (ofString n) := hl n hn
  have haa' : locN { s with locals := locals, clock := k } "aa" = locN s "aa" :=
    locN_congr s locals k "aa" (hlk "aa" (by simp))
  have hak' : locN { s with locals := locals, clock := k } "ak" = locN s "ak" :=
    locN_congr s locals k "ak" (hlk "ak" (by simp))
  have hm' : locN { s with locals := locals, clock := k } "m" = locN s "m" :=
    locN_congr s locals k "m" (hlk "m" (by simp))
  have h7 : ∀ n ∈ (["tx", "index", "sender", "gas", "tx_blob_gas_used", "price",
      "intrinsic"] : List String),
      locals.lookup (ofString n) = s.locals.lookup (ofString n) := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hlk _ (by simp)
  have hstore' : PtxStoreReadyIn2 buffers contents
      (locN { s with locals := locals, clock := k } "aa")
      (locN { s with locals := locals, clock := k } "ak")
      { s with locals := locals, clock := k } := by
    rw [haa', hak']
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
      obtain ⟨hd, S, Nd, hmem1, hmem2, hwS, hb, hsep⟩ := hstore.2.2.2.2.2 i
      rw [hm']
      refine ⟨hd, S, Nd, hmem1, hmem2, ?_, hb, ?_⟩
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
  have hworld' : PtxMessageTables { s with locals := locals, clock := k }
      (locN { s with locals := locals, clock := k } "aa")
      (locN { s with locals := locals, clock := k } "ak") := by
    rw [haa', hak']
    obtain ⟨S, Nd, hwS, ham, hkm, hal, hkl, haf, hkf, hdisj⟩ := hworld
    refine ⟨S, Nd, (worldTypedWith_with_locals s locals k S Nd).mpr hwS, ham, hkm,
      hal, hkl, haf, hkf, ?_⟩
    rw [hm']
    exact hdisj
  obtain ⟨wa, hwa⟩ := haa_w
  obtain ⟨wk, hwk⟩ := hak_w
  have haa_new : locals.lookup (ofString "aa") = some (.val (.word wa)) := by
    rw [hlk "aa" (by simp)]
    exact hwa
  have hak_new : locals.lookup (ofString "ak") = some (.val (.word wk)) := by
    rw [hlk "ak" (by simp)]
    exact hwk
  refine ⟨⟨wa, haa_new⟩, ⟨wk, hak_new⟩, ⟨hstore', hnames'⟩, htx,
    phase2_phase4_shapes_localsOnly s locals k h7 hp4, hworld'⟩

/-- Setting the loop counter `i` — a name the two-table region invariant never
reads — preserves the invariant. -/
theorem phase2_htabABInv_set_i {ι : Type} [Nonempty ι] (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String) (v : ValueHOL 64)
    (hne : ∀ n ∈ names, ofString n ≠ ofString "i")
    {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxHtabABInv buffers contents names s) :
    PtxHtabABInv buffers contents names (setVarHOLFinite (ofString "i") v s) := by
  have hlk : ∀ n ∈ (["aa", "ak", "m", "index", "tx", "sender", "gas", "tx_blob_gas_used",
      "price", "intrinsic"] ++ names : List String),
      (s.locals.update (ofString "i", v)).lookup (ofString n) = s.locals.lookup (ofString n) := by
    intro n hn
    have hni : ofString n ≠ ofString "i" := by
      rcases List.mem_append.1 hn with hb | hb
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      · exact hne n hb
    simp [HolFiniteMapExact.update, FUPDATE, Ne.symm hni]
  exact ptxHtabABInv_locallyOnly buffers contents names s
    (s.locals.update (ofString "i", v)) s.clock hlk hp

/-- The loop counter increment preserves the two-table region invariant. -/
theorem phase2_htabAB_increment_hoare {ι : Type} [Nonempty ι] (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String)
    (hne : ∀ n ∈ names, ofString n ≠ ofString "i") :
    Hoare (PtxHtabABInv buffers contents names)
      (.assign .local (ofString "i")
        (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))
      (fun r s => r = none → PtxHtabABInv buffers contents names s) := by
  apply Hoare.assign
  · intro F s v hp _
    exact fun _ => phase2_htabABInv_set_i buffers contents names v hne hp
  · exact fun _ _ hr => by cases hr

/-- One ak-warming-loop body: the `htab_set` call followed by the counter bump
preserves the two-table region invariant. -/
theorem phase2_htabAB_warm_body {ι : Type} [Nonempty ι] (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String) (key : ExpHOL 64)
    (hne : ∀ n ∈ names, ofString n ≠ ofString "i") :
    Hoare (PtxHtabABInv buffers contents names)
      (.seq (.call (some (none, none)) (ofString "htab_set")
          [.var .local (ofString "ak"), key, .const (BitVec.ofNat 64 1)])
        (.assign .local (ofString "i")
          (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))
      (fun r s => r = none → PtxHtabABInv buffers contents names s) := by
  refine Hoare.seq_fall
    (phase2_htabAB_set buffers contents names key (.const (BitVec.ofNat 64 1))) ?_
  exact phase2_htabAB_increment_hoare buffers contents names hne

/-- The warming loop over the `ak` table (positions 87..88) preserves the
two-table region invariant. -/
theorem phase2_htabAB_warm_while {ι : Type} [Nonempty ι] (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String) (key bound : ExpHOL 64)
    (hne : ∀ n ∈ names, ofString n ≠ ofString "i") :
    Hoare (PtxHtabABInv buffers contents names)
      (.while (.cmp .less (.var .local (ofString "i")) bound)
        (.seq (.call (some (none, none)) (ofString "htab_set")
            [.var .local (ofString "ak"), key, .const (BitVec.ofNat 64 1)])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))))
      (fun r s => r = none → PtxHtabABInv buffers contents names s) :=
  hoare_while_less_noCont (ptxHtabABInv_locallyOnly buffers contents names)
    (ofString "i") bound (phase2_htabAB_warm_body buffers contents names key hne)
    (phase2_warm_body_noCont (ofString "htab_set")
      [.var .local (ofString "ak"), key, .const (BitVec.ofNat 64 1)])
    (by rfl)

/-- The ak-warming-loop body is clock-bounded: the `htab_set` call plus one
assign step. -/
theorem phase2_htabAB_warm_body_bound (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (names : List String)
    (key : ExpHOL 64) :
    TerminatingProgBoundedOn (PtxHtabABInv buffers contents names)
      (.seq (.call (some (none, none)) (ofString "htab_set")
          [.var .local (ofString "ak"), key, .const (BitVec.ofNat 64 1)])
        (.assign .local (ofString "i")
          (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))
      (K.htab_set + 1) := by
  have hcall : TerminatingProgBoundedOn (PtxHtabABInv buffers contents names)
      (.call (some (none, none)) (ofString "htab_set")
        [.var .local (ofString "ak"), key, .const (BitVec.ofNat 64 1)])
      (K.htab_set + 1) := by
    apply TerminatingProgBoundedOn.call_on h.fb_htab_set none _
    intro F s vs body callee ret hc hp he hl
    exact guestInv_callEntry s callee (worldOK_guestInv s hp.2.2.1.1.1)
  have hassign : TerminatingProgBoundedOn (PtxHtabABInv buffers contents names)
      (.assign .local (ofString "i")
        (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))
      0 :=
    R16Shards.PtxP1.bound_of_clock (P := PtxHtabABInv buffers contents names)
      (fun s => clock_assign s .local (ofString "i")
        (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))
  intro F s hc hp
  simpa only [Nat.add_zero] using seq_bound_trans hcall
    (phase2_htabAB_set buffers contents names key (.const (BitVec.ofNat 64 1))) hassign s hc hp

/-- The warming loop over the `ak` table is clock-bounded. -/
theorem phase2_htabAB_warm_while_bound (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (names : List String)
    (key bound : ExpHOL 64) (hne : ∀ n ∈ names, ofString n ≠ ofString "i") :
    TerminatingProgBoundedOn (PtxHtabABInv buffers contents names)
      (.while (.cmp .less (.var .local (ofString "i")) bound)
        (.seq (.call (some (none, none)) (ofString "htab_set")
            [.var .local (ofString "ak"), key, .const (BitVec.ofNat 64 1)])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))))
      ((2 ^ 64 + 1) * (K.htab_set + 1 + 1)) :=
  while_less_noCont (ptxHtabABInv_locallyOnly buffers contents names) (ofString "i") bound
    (phase2_htabAB_warm_body_bound h buffers contents names key)
    (phase2_htabAB_warm_body buffers contents names key hne)
    (phase2_warm_body_noCont (ofString "htab_set")
      [.var .local (ofString "ak"), key, .const (BitVec.ofNat 64 1)])
    (phase2_warm_body_incr (ofString "htab_set")
      [.var .local (ofString "ak"), key, .const (BitVec.ofNat 64 1)])

/-- Initializing the loop counter preserves the two-table region invariant. -/
theorem phase2_htabAB_assign0_hoare {ι : Type} [Nonempty ι] (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String)
    (hne : ∀ n ∈ names, ofString n ≠ ofString "i") :
    Hoare (PtxHtabABInv buffers contents names)
      (.assign .local (ofString "i") (.const (BitVec.ofNat 64 0)))
      (fun r s => r = none → PtxHtabABInv buffers contents names s) := by
  apply Hoare.assign
  · intro F s v hp _
    exact fun _ => phase2_htabABInv_set_i buffers contents names v hne hp
  · exact fun _ _ hr => by cases hr

/-- The ak warming spine (counter init plus the loop) is clock-bounded with
the tail's bound. -/
theorem phase2_htabAB_warm_spine_bound (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (names : List String)
    (key bound : ExpHOL 64) (hne : ∀ n ∈ names, ofString n ≠ ofString "i")
    {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn (PtxHtabABInv buffers contents names) tail b) :
    TerminatingProgBoundedOn (PtxHtabABInv buffers contents names)
      (.seq (.assign .local (ofString "i") (.const (BitVec.ofNat 64 0)))
        (.seq (.while (.cmp .less (.var .local (ofString "i")) bound)
            (.seq (.call (some (none, none)) (ofString "htab_set")
                [.var .local (ofString "ak"), key, .const (BitVec.ofNat 64 1)])
              (.assign .local (ofString "i")
                (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))))
          tail))
      ((2 ^ 64 + 1) * (K.htab_set + 1 + 1) + b) := by
  have ha0 : TerminatingProgBoundedOn (PtxHtabABInv buffers contents names)
      (.assign .local (ofString "i") (.const (BitVec.ofNat 64 0))) 0 :=
    R16Shards.PtxP1.bound_of_clock (P := PtxHtabABInv buffers contents names)
      (fun s => clock_assign s .local (ofString "i") (.const (BitVec.ofNat 64 0)))
  have hwhile : TerminatingProgBoundedOn (PtxHtabABInv buffers contents names)
      (.while (.cmp .less (.var .local (ofString "i")) bound)
        (.seq (.call (some (none, none)) (ofString "htab_set")
            [.var .local (ofString "ak"), key, .const (BitVec.ofNat 64 1)])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))))
      ((2 ^ 64 + 1) * (K.htab_set + 1 + 1)) :=
    phase2_htabAB_warm_while_bound h buffers contents names key bound hne
  intro F s hc hp
  simpa only [Nat.zero_add, Nat.add_zero] using seq_bound_trans ha0
    (phase2_htabAB_assign0_hoare buffers contents names hne)
    (seq_bound_trans hwhile
      (phase2_htabAB_warm_while buffers contents names key bound hne) ht) s hc hp

/-! ### Segment B part 2a L8: the bridge into the frozen table-store frame and
the `empty := alloc(8)` rung (positions 89..90).

The frozen ite-region machinery runs on `PtxMessageTableStoreReady`, whose
`memW (m+40) < 2^63` component records the message gas bound. That fact is
orphaned upstream (the `PtxValidated` gas bound is dropped by the te-suffix and
message-prefix invariants), so this rung takes it as an explicit entry
hypothesis, exactly as the frozen `phase2_message_ready_of_access_tables`
treats it on the tail side. -/

/-- The two-table warming invariant plus the message-gas bound bridges into
the frozen table-store frame at the message's two live tables. -/
theorem phase2_htabAB_tableStoreReady {ι F : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (names : List String)
    {s : PanSemStateFiniteExact 64 F} (aa ak : Nat)
    (hp : PtxHtabABInv buffers contents names s)
    (hg : memW s (locN s "m" + 40) < 2 ^ 63)
    (haa : locN s "aa" = aa) (hak : locN s "ak" = ak) :
    PtxMessageTableStoreReady buffers contents ["aa", "ak"] aa ak s := by
  obtain ⟨hw_aa, hw_ak, ⟨hstore, hnames⟩, htxb, hp4, htables⟩ := hp
  have hsr : PtxMessageStoreReady buffers contents s := by
    obtain ⟨hW, hE, hm, hin, hwok, hbufs⟩ := hstore
    refine ⟨hW, hE, hm, hin, hwok, ?_⟩
    intro i
    obtain ⟨hd, S, Nd, _, _, hw, hb, hsep⟩ := hbufs i
    exact ⟨hd, S, Nd, hw, hb, hsep⟩
  rw [haa, hak] at htables
  refine ⟨⟨hsr, ?_⟩, htables, htxb, hp4, hg, haa, hak⟩
  intro name hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact hw_aa
  · exact hw_ak

/-- The `empty := alloc(8)` rung (positions 89..90): the skip after ak
warming, then the fresh empty-table allocation, which appends `empty` to the
scalar witness names. -/
theorem phase2_b2a_l8_empty_alloc_bound (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (names : List String)
    (aa ak : Nat) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn
      (PtxMessageTableStoreReady buffers contents ["empty", "aa", "ak"] aa ak) tail b) :
    TerminatingProgBoundedOn
      (fun s => PtxHtabABInv buffers contents names s ∧
        memW s (locN s "m" + 40) < 2 ^ 63 ∧ locN s "aa" = aa ∧ locN s "ak" = ak)
      (spinePlug 2 (spineAt 89 ptxCode) tail) (K.alloc + b + 1) := by
  have hshape : spinePlug 2 (spineAt 89 ptxCode) tail =
      .seq .skip (.decCall (ofString "empty") .one (ofString "alloc") [.const (8#64)] tail) := by
    simp only [ptxCode, sourceFunctionEntry, Guest.Software.guestFn_process_transaction]
    rfl
  rw [hshape]
  have hdec : TerminatingProgBoundedOn
      (PtxMessageTableStoreReady buffers contents ["aa", "ak"] aa ak)
      (.decCall (ofString "empty") .one (ofString "alloc") [.const (8#64)] tail)
      (K.alloc + b + 1) :=
    phase2_alloc_message_table_word_bound h buffers contents ["aa", "ak"] aa ak "empty"
      [.const (8#64)] (by decide) (by decide) (by decide) (by decide)
      (by intro n hn; simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
          rcases hn with rfl | rfl <;> decide)
      (by intro n hn; simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
          rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) ht
  intro F s hcode hp
  obtain ⟨hab, hg, haa, hak⟩ := hp
  have htsr := phase2_htabAB_tableStoreReady buffers contents names aa ak hab hg haa hak
  simpa only [Nat.zero_add] using seq_bound_trans
    (R16Shards.PtxP1.bound_of_clock
      (P := PtxMessageTableStoreReady buffers contents ["aa", "ak"] aa ak)
      (fun s => R16Shards.PtxP1.clock_skip s))
    (Hoare.skip (fun _ hp _ => hp)) hdec s hcode htsr

/-! ### Segment B part 2a L9: the create-vs-call ite (position 91). -/

/-- The ite at position 91 in its exact source shape. -/
theorem phase2_b2a_spine91 :
    spineAt 91 ptxCode =
      .seq (.ite (.cmp .equal
          (.load .one (.op .add [.var .local (ofString "tx"), .const (152#64)]))
          (.const (0#64)))
        (.decCall (ofString "sa") .one (ofString "get_account")
          [.var .local (ofString "sender")]
        (.decCall (ofString "ct") .one (ofString "alloc") [.const (24#64)]
        (.seq (.call (some (none, none)) (ofString "compute_contract_address")
          [.var .local (ofString "sender"),
           .op .sub [.load .one (.op .add [.var .local (ofString "sa"), .const (0#64)]),
             .const (1#64)],
           .var .local (ofString "ct")])
        phase2_message_create_stores)))
      phase2_message_call_stores)
      (spineAt 92 ptxCode) := by
  simp only [ptxCode, sourceFunctionEntry, Guest.Software.guestFn_process_transaction]
  rfl

/-- The ite plus the six final instructions as one seven-step spine plug. -/
theorem phase2_b2a_shape7 (tail : ProgHOL 64) :
    spinePlug 7 (spineAt 91 ptxCode) tail =
      .seq (.ite (.cmp .equal
          (.load .one (.op .add [.var .local (ofString "tx"), .const (152#64)]))
          (.const (0#64)))
        (.decCall (ofString "sa") .one (ofString "get_account")
          [.var .local (ofString "sender")]
        (.decCall (ofString "ct") .one (ofString "alloc") [.const (24#64)]
        (.seq (.call (some (none, none)) (ofString "compute_contract_address")
          [.var .local (ofString "sender"),
           .op .sub [.load .one (.op .add [.var .local (ofString "sa"), .const (0#64)]),
             .const (1#64)],
           .var .local (ofString "ct")])
        phase2_message_create_stores)))
      phase2_message_call_stores)
        (spinePlug 6 (spineAt 92 ptxCode) tail) := by
  rw [phase2_b2a_spine91]
  rfl

/-- The create-vs-call ite terminates on both branches. The no branch is pure
stores (clock-neutral); the yes branch is the account lookup, the fresh
address allocation, and the contract-address computation, whose trailing
creation stores are again clock-neutral. -/
theorem phase2_b2a_l9_ite_bound (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (aa ak : Nat) :
    TerminatingProgBoundedOn
      (PtxMessageTableStoreReady buffers contents ["empty", "aa", "ak"] aa ak)
      (.ite (.cmp .equal
          (.load .one (.op .add [.var .local (ofString "tx"), .const (152#64)]))
          (.const (0#64)))
        (.decCall (ofString "sa") .one (ofString "get_account")
          [.var .local (ofString "sender")]
        (.decCall (ofString "ct") .one (ofString "alloc") [.const (24#64)]
        (.seq (.call (some (none, none)) (ofString "compute_contract_address")
          [.var .local (ofString "sender"),
           .op .sub [.load .one (.op .add [.var .local (ofString "sa"), .const (0#64)]),
             .const (1#64)],
           .var .local (ofString "ct")])
        phase2_message_create_stores)))
      phase2_message_call_stores)
      (Nat.max
        (K.get_account + (K.alloc + (K.«compute_contract_address» + 1 + 0) + 1) + 1)
        0) := by
  have hptriv : Hoare
      (fun s => PtxMessageTableStoreReady buffers contents ["ct", "empty", "aa", "ak"] aa ak s ∧
        ∀ region ∈ [(locN s "ct", 20),
          (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
          (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)],
          Disj (locN s "m", 176) region ∧ ∀ i, Disj (buffers i) region)
      (.call (some (none, none)) (ofString "compute_contract_address")
        [.var .local (ofString "sender"),
         .op .sub [.load .one (.op .add [.var .local (ofString "sa"), .const (0#64)]),
           .const (1#64)],
         .var .local (ofString "ct")])
      (fun r _ => r = none → True) :=
    ⟨fun s hc hp hnt _ => trivial⟩
  have hentry : CallEntryOn
      (fun s => PtxMessageTableStoreReady buffers contents ["ct", "empty", "aa", "ak"] aa ak s ∧
        ∀ region ∈ [(locN s "ct", 20),
          (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
          (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)],
          Disj (locN s "m", 176) region ∧ ∀ i, Disj (buffers i) region)
      GuestInv (ofString "compute_contract_address")
      [.var .local (ofString "sender"),
       .op .sub [.load .one (.op .add [.var .local (ofString "sa"), .const (0#64)]),
         .const (1#64)],
       .var .local (ofString "ct")] :=
    fun s vs body callee ret hc hp he hl =>
      callEntryOn_guestInv _ _ s vs body callee ret hc hp.1.1.1.1.1.1 he hl
  have hcall : TerminatingProgBoundedOn
      (fun s => PtxMessageTableStoreReady buffers contents ["ct", "empty", "aa", "ak"] aa ak s ∧
        ∀ region ∈ [(locN s "ct", 20),
          (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
          (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)],
          Disj (locN s "m", 176) region ∧ ∀ i, Disj (buffers i) region)
      (.call (some (none, none)) (ofString "compute_contract_address")
        [.var .local (ofString "sender"),
         .op .sub [.load .one (.op .add [.var .local (ofString "sa"), .const (0#64)]),
           .const (1#64)],
         .var .local (ofString "ct")])
      (K.«compute_contract_address» + 1) :=
    TerminatingProgBoundedOn.call_on h.fb_compute_contract_address none
      [.var .local (ofString "sender"),
       .op .sub [.load .one (.op .add [.var .local (ofString "sa"), .const (0#64)]),
         .const (1#64)],
       .var .local (ofString "ct")] hentry
  have hcs : TerminatingProgBoundedOn (fun _ => True) phase2_message_create_stores 0 :=
    R16Shards.PtxP1.bound_of_clock (P := fun _ => True) phase2_message_create_stores_clock
  have hseq : TerminatingProgBoundedOn
      (fun s => PtxMessageTableStoreReady buffers contents ["ct", "empty", "aa", "ak"] aa ak s ∧
        ∀ region ∈ [(locN s "ct", 20),
          (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
          (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)],
          Disj (locN s "m", 176) region ∧ ∀ i, Disj (buffers i) region)
      (.seq (.call (some (none, none)) (ofString "compute_contract_address")
          [.var .local (ofString "sender"),
           .op .sub [.load .one (.op .add [.var .local (ofString "sa"), .const (0#64)]),
             .const (1#64)],
           .var .local (ofString "ct")])
        phase2_message_create_stores)
      (K.«compute_contract_address» + 1 + 0) :=
    seq_bound_trans hcall hptriv hcs
  have hct : TerminatingProgBoundedOn
      (PtxMessageTableStoreReady buffers contents ["empty", "aa", "ak"] aa ak)
      (.decCall (ofString "ct") .one (ofString "alloc") [.const (24#64)]
        (.seq (.call (some (none, none)) (ofString "compute_contract_address")
            [.var .local (ofString "sender"),
             .op .sub [.load .one (.op .add [.var .local (ofString "sa"), .const (0#64)]),
               .const (1#64)],
             .var .local (ofString "ct")])
          phase2_message_create_stores))
      (K.alloc + (K.«compute_contract_address» + 1 + 0) + 1) :=
    TerminatingProgBoundedOn.decCall_on h.fb_alloc (ofString "ct") .one [.const (24#64)]
      (Q := fun s => PtxMessageTableStoreReady buffers contents ["ct", "empty", "aa", "ak"] aa ak s ∧
        ∀ region ∈ [(locN s "ct", 20),
          (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
          (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)],
          Disj (locN s "m", 176) region ∧ ∀ i, Disj (buffers i) region)
      (fun s vs body callee ret hc hp he hl =>
        guestInv_callEntry s callee hp.1.1.1.1.1)
      (phase2_ct_alloc_ready_write_separated h buffers contents ["empty", "aa", "ak"] aa ak
        (by intro n hn; simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
            rcases hn with rfl | rfl | rfl <;> decide))
      hseq
  have hyes : TerminatingProgBoundedOn
      (fun s => PtxMessageTableStoreReady buffers contents ["empty", "aa", "ak"] aa ak s ∧
        CondTrue (.cmp .equal
          (.load .one (.op .add [.var .local (ofString "tx"), .const (152#64)]))
          (.const (0#64))) s)
      (.decCall (ofString "sa") .one (ofString "get_account")
        [.var .local (ofString "sender")]
        (.decCall (ofString "ct") .one (ofString "alloc") [.const (24#64)]
        (.seq (.call (some (none, none)) (ofString "compute_contract_address")
          [.var .local (ofString "sender"),
           .op .sub [.load .one (.op .add [.var .local (ofString "sa"), .const (0#64)]),
             .const (1#64)],
           .var .local (ofString "ct")])
        phase2_message_create_stores)))
      (K.get_account + (K.alloc + (K.«compute_contract_address» + 1 + 0) + 1) + 1) := by
    apply R16Shards.PtxP1.bound_mono
      (phase2_get_account_message_table_bound h buffers contents ["empty", "aa", "ak"] aa ak
        (ofString "sa") [.var .local (ofString "sender")]
        (by decide) (by decide) (by decide) (by decide)
        (by intro n hn; simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
            rcases hn with rfl | rfl | rfl <;> decide)
        (by intro n hn; simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
            rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        hct)
    intro F s hp
    exact hp.1
  have hno : TerminatingProgBoundedOn
      (fun s => PtxMessageTableStoreReady buffers contents ["empty", "aa", "ak"] aa ak s ∧
        CondFalse (.cmp .equal
          (.load .one (.op .add [.var .local (ofString "tx"), .const (152#64)]))
          (.const (0#64))) s)
      phase2_message_call_stores 0 := by
    apply R16Shards.PtxP1.bound_mono
      (R16Shards.PtxP1.bound_of_clock
        (P := PtxMessageTableStoreReady buffers contents ["empty", "aa", "ak"] aa ak)
        phase2_message_call_stores_clock)
    intro F s hp
    exact hp.1
  intro F state hcode hp
  exact TerminatingProgBoundedOn.ite_cond_on
    (P := PtxMessageTableStoreReady buffers contents ["empty", "aa", "ak"] aa ak) hyes hno
    state hcode hp

/-! ### Segment B part 2a L10 support: caller-locals transport for the joint
table-store invariant, dropping the helper local `ct`, and the out-bridge for
the contract-address call. -/

/-- The joint table-store invariant survives arbitrary caller-local and clock
changes as long as every variable it reads is preserved. -/
theorem phase2_b2a_tsr_localsOnly {ι : Type} (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String) (aa ak : Nat) :
    LocalsOnly (["m", "index", "aa", "ak"] ++ names ++
      ["tx", "index", "sender", "gas", "tx_blob_gas_used", "price", "intrinsic"])
      (PtxMessageTableStoreReady buffers contents names aa ak) := by
  intro F s locals k hl hp
  have hm : locN {s with locals := locals, clock := k} "m" = locN s "m" :=
    locN_congr s locals k "m" (hl "m" (by simp [List.mem_append]))
  have haa : locN {s with locals := locals, clock := k} "aa" = locN s "aa" :=
    locN_congr s locals k "aa" (hl "aa" (by simp [List.mem_append]))
  have hak : locN {s with locals := locals, clock := k} "ak" = locN s "ak" :=
    locN_congr s locals k "ak" (hl "ak" (by simp [List.mem_append]))
  have hmem : ∀ n ∈ (["tx", "index", "sender", "gas", "tx_blob_gas_used", "price",
      "intrinsic"] : List String), n ∈ (["m", "index", "aa", "ak"] ++ names ++
      ["tx", "index", "sender", "gas", "tx_blob_gas_used", "price", "intrinsic"]) := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [List.mem_append]
  refine ⟨?_, ?_, hp.2.2.1, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, by rw [hm]; exact hp.1.1.2.2.2.2.1, ?_⟩
      · exact localsFree_worldOK s locals k hp.1.1.1
      · exact txEnv_with_locals s locals k (hl "index" (by simp [List.mem_append])) hp.1.1.2.1
      · obtain ⟨w, hw⟩ := hp.1.1.2.2.1
        refine ⟨w, ?_⟩
        show locals.lookup (ofString "m") = some (.val (.word w))
        rw [hl "m" (by simp [List.mem_append])]
        exact hw
      · rw [hm]; exact hp.1.1.2.2.2.1
      · intro i
        obtain ⟨hd, S, Nd, hw, hb, hdi⟩ := hp.1.1.2.2.2.2.2 i
        exact ⟨by rw [hm]; exact hd, S, Nd,
          (worldTypedWith_with_locals s locals k S Nd).mpr hw, hb,
          by rw [hm]; exact hdi⟩
    · intro name hn
      obtain ⟨w, hw⟩ := hp.1.2 name hn
      refine ⟨w, ?_⟩
      show locals.lookup (ofString name) = some (.val (.word w))
      rw [hl name (by simp [List.mem_append, hn])]
      exact hw
  · obtain ⟨S, Nd, hw, ham, hkm, hal, hkl, haf, hkf, hd⟩ := hp.2.1
    exact ⟨S, Nd, (worldTypedWith_with_locals s locals k S Nd).mpr hw, ham, hkm,
      hal, hkl, haf, hkf, by rw [hm]; exact hd⟩
  · exact phase2_phase4_shapes_localsOnly (F := F) s locals k
      (fun n hn => hl n (hmem n hn)) hp.2.2.2.1
  · rw [hm]; exact hp.2.2.2.2.1
  · rw [haa]; exact hp.2.2.2.2.2.1
  · rw [hak]; exact hp.2.2.2.2.2.2

/-- The joint invariant only depends on its name list through the scalar
witnesses, so it weakens along sublist inclusion. -/
theorem phase2_b2a_tsr_weaken {ι : Type} (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) {names ns : List String}
    (hsub : ∀ n ∈ ns, n ∈ names) (aa ak : Nat) {F : Type}
    {t : PanSemStateFiniteExact 64 F}
    (hp : PtxMessageTableStoreReady buffers contents names aa ak t) :
    PtxMessageTableStoreReady buffers contents ns aa ak t :=
  ⟨⟨hp.1.1, fun name hn => hp.1.2 name (hsub name hn)⟩, hp.2.1, hp.2.2.1, hp.2.2.2.1,
    hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2⟩

/-- The contract-address call's third parameter is the caller's fresh
allocation word, so the callee's `out` slot reads the caller's `ct`. -/
theorem phase2_b2a_cca_out_bridge {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "sender"),
       .op .sub [.load .one (.op .add [.var .local (ofString "sa"), .const (0#64)]),
         .const (1#64)],
       .var .local (ofString "ct")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "compute_contract_address") vs =
      some (body, callee, ret))
    (hwct : ∃ w : BitVec 64, s.locals.lookup (ofString "ct") = some (.val (.word w))) :
    locN (callEntryStateHOLFinite s callee) "out" = locN s "ct" := by
  obtain ⟨v1, v2, v3, he1, he2, he3, hp1, hp2, hout⟩ :=
    R16Shards.PtxP1.params_three_values s (ofString "compute_contract_address")
    (ofString "addr") (ofString "nonce") (ofString "out") .one .one .one _ .one
    (by rw [hc]; exact R16Shards.WkBlockTxEnc.lookup_compute_contract_address)
    (.var .local (ofString "sender"))
    (.op .sub [.load .one (.op .add [.var .local (ofString "sa"), .const (0#64)]),
      .const (1#64)])
    (.var .local (ofString "ct"))
    vs body callee ret ha hl
  obtain ⟨w, hw⟩ := hwct
  have hv3 : v3 = .val (.word w) := Option.some.inj (he3.symm.trans hw)
  have h1 : locN (callEntryStateHOLFinite s callee) "out" = w.toNat := by
    simp only [locN, callEntryStateHOLFinite, hout, hv3]
  have h2 : locN s "ct" = w.toNat := by
    simp only [locN, hw]
  rw [h1, h2]

/-! ### Segment B part 2a L10: the `ct`-allocation resume invariant (Lemma A). -/

/-- Disjointness is preserved when the left interval shrinks towards its base. -/
private theorem disj_shrink_left {p m n : Nat} {j : Ivl} (h : Disj (p, m) j) (hmn : n ≤ m) :
    Disj (p, n) j := by
  unfold Disj at h
  rcases h with h | h | h | h
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr h))

/-- The invariant at the resume point of the `ct` allocation: the frozen
table-store cut with `ct` added to the scalar names, the contract-address
output separation for the message and its saved buffers, and selected
per-buffer and joint-table world witnesses whose typed intervals avoid the
same outputs. -/
theorem phase2_b2a_ct_alloc_inv (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (aa ak : Nat) :
    DecCallResumeOn (PtxMessageTableStoreReady buffers contents ["empty", "aa", "ak"] aa ak)
      (fun s => PtxMessageTableStoreReady buffers contents ["ct", "empty", "aa", "ak"] aa ak s ∧
        (∀ region ∈ [(locN s "ct", 20),
          (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
          (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)],
          Disj (locN s "m", 176) region ∧ ∀ i, Disj (buffers i) region) ∧
        (∀ i, ∃ S Nd, WorldTypedWith s S Nd ∧
          PtxLiveBufferAt s S Nd (buffers i) (contents i) ∧
          IvlsDisj [(locN s "m", 176)] (worldOwned s S Nd) ∧
          IvlsDisj [(locN s "ct", 20),
            (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
            (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)]
            (worldTypedIvls s S Nd)) ∧
        (∃ S Nd, WorldTypedWith s S Nd ∧ aa ∈ S ∧ ak ∈ S ∧
          hdr s aa 0 = 20 ∧ hdr s ak 0 = 52 ∧
          (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ aa) ∧
          (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ ak) ∧
          IvlsDisj [(locN s "m", 176)] (worldOwned s S Nd) ∧
          IvlsDisj [(locN s "ct", 20),
            (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
            (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)]
            (worldTypedIvls s S Nd)))
      (ofString "ct") (ofString "alloc") [.const 24#64] := by
  intro F s vs body callee ret v post hc hp he hl hb
  -- the frozen resume lemma gives the cut and the write separation
  obtain ⟨ht, hsep⟩ := phase2_ct_alloc_ready_write_separated h buffers contents
    ["empty", "aa", "ak"] aa ak
    (by intro n hn; simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl | rfl <;> decide)
    s vs body callee ret v post hc hp he hl hb
  -- the alloc world step and its memory/global framing
  have hh := R16Shards.PtxP1.funSpec_at_lookup h.wk_alloc s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hp.1.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hh
  have step := hh (Or.inl ⟨v, rfl⟩)
  have hmem : post.memory = s.memory :=
    phase2_alloc_memory s vs body callee ret v post hc hp.1.1.1 hl hb
  have hgn : ∀ g, ofString g ≠ ofString "heap_ptr" → globN post g = globN s g := by
    intro g hg
    have hne : ofString g ∉ (["heap_ptr"] : List String).map ofString := by
      simpa only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] using hg
    exact R16Shards.globN_eq_of_lookup (step.2.2.1 (ofString g) hne)
  have hwr : worldRoleSlots post = worldRoleSlots s := by
    simp only [worldRoleSlots, recRoles, nestRoles, balRecords, htabValues, nodeF, hdr, memW, hmem,
      hgn "ws" (by decide), hgn "bs" (by decide), hgn "ts" (by decide),
      hgn "bal_accounts" (by decide), hgn "bal_idx_accts" (by decide), hgn "bal_idx_stor" (by decide)]
    rfl
  have hjr : journalRoleSlots post = journalRoleSlots s := by
    simp only [journalRoleSlots, journalRole, memW, hmem, hgn "journal_n" (by decide),
      hgn "journal" (by decide), hgn "ts" (by decide)]
    rfl
  -- the allocation size is 24, so the fresh block is (w, 24)
  have hcn : locN (callEntryStateHOLFinite s callee) "n" = 24 := by
    obtain ⟨nv, hev, hn⟩ := R16Shards.PtxP1.params_one_value s (ofString "alloc") (ofString "n")
      .one _ .one (by rw [hc]; exact R16Shards.PtxP1.lookup_alloc) _ vs body callee ret he hl
    have hnv : nv = .val (.word 24) := by simpa [evalAt, evalHOLExact] using hev.symm
    subst nv
    simp [locN, callEntryStateHOLFinite, hn]
  have hrr : worldRoleSlots (setVarHOLFinite (ofString "ct") v {post with locals := s.locals})
        = worldRoleSlots s ∧
      journalRoleSlots (setVarHOLFinite (ofString "ct") v {post with locals := s.locals})
        = journalRoleSlots s := ⟨hwr, hjr⟩
  refine ⟨ht, hsep, ?_, ?_⟩
  · -- per-buffer witnesses
    intro i
    obtain ⟨hdm, S0, Nd0, hw0, hb0, hdi0⟩ := hp.1.1.2.2.2.2.2 i
    obtain ⟨S', Nd', hsub, hw', hg, hframe, hq⟩ := step.2.2.2.2 S0 Nd0
      ((worldTypedWith_with_locals s callee (s.clock - 1) S0 Nd0).mpr hw0) (by simp [IvlsDisj])
    obtain ⟨w, hvw, hd24⟩ := hq v rfl
    simp only [hcn] at hd24
    have hct : locN (setVarHOLFinite (ofString "ct") v {post with locals := s.locals}) "ct"
        = w.toNat := by
      simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hvw]
    have hmr : locN (setVarHOLFinite (ofString "ct") v {post with locals := s.locals}) "m"
        = locN s "m" := by
      simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "ct" ≠ ofString "m" by decide]
    have hct20 : IvlsDisj [(w.toNat, 20)] (worldTypedIvls post S' Nd') := by
      intro o ho j hj
      simp only [List.mem_singleton] at ho
      subst o
      exact disj_shrink_left (hd24 (w.toNat, 24) (by simp) j
        (worldTypedIvls_sub_worldOwned hj)) (by omega)
    refine ⟨S', Nd', (worldTypedWith_with_locals post _ post.clock S' Nd').mpr hw', ?_, ?_, ?_⟩
    · exact (phase2_live_buffer_with_locals post _ post.clock S' Nd' (buffers i) (contents i)).mpr
        (phase2_live_buffer_step s post S0 Nd0 S' Nd' (buffers i) (contents i) [] hb0
          hp.1.1.1.1.2 hw0 step.2.1 hg hframe (by simp) (by simp))
    · rw [hmr]
      exact phase2_packed_owned_growth s post _ _ (locN s "m", 176) hp.1.1.2.2.2.1 hg hdi0
    · rw [hct]
      exact phase2_contract_writes_disjoint_typed post S' Nd' w.toNat hw' hct20
  · -- the joint table witness
    obtain ⟨St, Ndt, hwt, ham, hkm, hal, hkl, haf, hkf, hmt⟩ := hp.2.1
    obtain ⟨St', Ndt', hsub, hw't, hgt, hframet, hqt⟩ := step.2.2.2.2 St Ndt
      ((worldTypedWith_with_locals s callee (s.clock - 1) St Ndt).mpr hwt) (by simp [IvlsDisj])
    obtain ⟨wt, hvwt, hd24t⟩ := hqt v rfl
    simp only [hcn] at hd24t
    have hctt : locN (setVarHOLFinite (ofString "ct") v {post with locals := s.locals}) "ct"
        = wt.toNat := by
      simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hvwt]
    have hct20t : IvlsDisj [(wt.toNat, 20)] (worldTypedIvls post St' Ndt') := by
      intro o ho j hj
      simp only [List.mem_singleton] at ho
      subst o
      exact disj_shrink_left (hd24t (wt.toNat, 24) (by simp) j
        (worldTypedIvls_sub_worldOwned hj)) (by omega)
    have hdraa : hdr (setVarHOLFinite (ofString "ct") v {post with locals := s.locals}) aa 0
        = hdr s aa 0 := by
      simp only [hdr, memW, setVarHOLFinite, hmem]
    have hdrak : hdr (setVarHOLFinite (ofString "ct") v {post with locals := s.locals}) ak 0
        = hdr s ak 0 := by
      simp only [hdr, memW, setVarHOLFinite, hmem]
    have hmrt : locN (setVarHOLFinite (ofString "ct") v {post with locals := s.locals}) "m"
        = locN s "m" := by
      simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "ct" ≠ ofString "m" by decide]
    refine ⟨St', Ndt', (worldTypedWith_with_locals post _ post.clock St' Ndt').mpr hw't,
      hsub aa ham, hsub ak hkm, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hdraa]; exact hal
    · rw [hdrak]; exact hkl
    · rw [hrr.1, hrr.2]; exact haf
    · rw [hrr.1, hrr.2]; exact hkf
    · rw [hmrt]
      exact phase2_packed_owned_growth s post _ _ (locN s "m", 176) hp.1.1.2.2.2.1 hgt hmt
    · rw [hctt]
      exact phase2_contract_writes_disjoint_typed post St' Ndt' wt.toNat hw't hct20t

/-! ### Segment B part 2a L10: the contract-address call invariant (Lemma B). -/

/-- The contract-address call preserves the joint table-store cut: the
frozen selected store and table consumers carry the cut across the concrete
byte-write effect, fed by the allocation's write separation. -/
theorem phase2_b2a_cca_hoare (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (aa ak : Nat) :
    Hoare (fun s =>
        PtxMessageTableStoreReady buffers contents ["ct", "empty", "aa", "ak"] aa ak s ∧
        (∀ region ∈ [(locN s "ct", 20),
          (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
          (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)],
          Disj (locN s "m", 176) region ∧ ∀ i, Disj (buffers i) region) ∧
        (∀ i, ∃ S Nd, WorldTypedWith s S Nd ∧
          PtxLiveBufferAt s S Nd (buffers i) (contents i) ∧
          IvlsDisj [(locN s "m", 176)] (worldOwned s S Nd) ∧
          IvlsDisj [(locN s "ct", 20),
            (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
            (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)]
            (worldTypedIvls s S Nd)) ∧
        (∃ S Nd, WorldTypedWith s S Nd ∧ aa ∈ S ∧ ak ∈ S ∧
          hdr s aa 0 = 20 ∧ hdr s ak 0 = 52 ∧
          (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ aa) ∧
          (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ ak) ∧
          IvlsDisj [(locN s "m", 176)] (worldOwned s S Nd) ∧
          IvlsDisj [(locN s "ct", 20),
            (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
            (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)]
            (worldTypedIvls s S Nd)))
      (.call (some (none, none)) (ofString "compute_contract_address")
        [.var .local (ofString "sender"),
         .op .sub [.load .one (.op .add [.var .local (ofString "sa"), .const (0#64)]),
           .const (1#64)],
         .var .local (ofString "ct")])
      (fun r t => r = none →
        PtxMessageTableStoreReady buffers contents ["ct", "empty", "aa", "ak"] aa ak t) := by
  refine Hoare.call0_resume ?_
  intro F s vs body callee ret v post hc hp he hl hb
  obtain ⟨ht, hsep, hw1, hw2⟩ := hp
  have hout : locN (callEntryStateHOLFinite s callee) "out" = locN s "ct" :=
    phase2_b2a_cca_out_bridge s hc vs body callee ret he hl (ht.1.2 "ct" (by simp))
  rw [← hout] at hsep hw1 hw2
  obtain ⟨S2, Nd2, hw2w, haaS2, hakS2, hal2, hkl2, haf2, hkf2, hm2, hd2⟩ := hw2
  have hArena : ArenaReady s := ht.1.1.1.1
  have hE : TxEnv s := ht.1.1.2.1
  have heff := phase2_compute_contract_address_effect s post vs body callee ret
    (some (.returned v)) hc hArena hl hb (by simp) (Or.inl ⟨v, rfl⟩)
  have hArenaE : ArenaReady (callEntryStateHOLFinite s callee) :=
    (arenaReady_with_locals s callee (s.clock - 1)).mpr hArena
  have hwE : WorldTypedWith (callEntryStateHOLFinite s callee) S2 Nd2 :=
    (worldTypedWith_with_locals s callee (s.clock - 1) S2 Nd2).mpr hw2w
  have hzero : ∀ region ∈ [(locN (callEntryStateHOLFinite s callee) "out", 20),
      (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
      (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)],
      region.2 = 0 → region.1 % 8 = 0 := by
    intro region hm hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · simp at hz
    · simp at hz; simp [hz]
    · simp at hz; simp [hz]
  have hboNZ : globN (callEntryStateHOLFinite s callee) "bo" ≠ 0 := hE.bo_nz
  have hboW := bo_words hwE.2.2.1 hboNZ
  have hboMem : (globN (callEntryStateHOLFinite s callee) "bo", 88)
      ∈ worldTypedIvls (callEntryStateHOLFinite s callee) S2 Nd2 := by
    simp only [worldTypedIvls, List.mem_append]
    left; left; left; left; right
    exact List.mem_map.2 ⟨("bo", 88), by decide, by simp [hboNZ]⟩
  have haa88 : (aa, 88) ∈ htabFootprint (callEntryStateHOLFinite s callee) aa := by
    simp [htabFootprint]
  have hAAmem : (aa, 88) ∈ worldTypedIvls (callEntryStateHOLFinite s callee) S2 Nd2 := by
    simp only [worldTypedIvls, List.mem_append]
    left; left; left; left; left
    exact List.mem_flatMap.mpr ⟨aa, haaS2, haa88⟩
  have hAAal := ((hwE.1.2.1 aa haaS2).1.1 (aa, 88) haa88).2
  have hAAalloc : Allocated (callEntryStateHOLFinite s callee) (aa, 88) :=
    ((hwE.1.2.1 aa haaS2).2 (aa, 88) haa88).1
  have hAAbound := (ivl_allocated_bound hArenaE.2 hAAalloc).2
  have hAAunhit : IvlUnhit (callEntryStateHOLFinite s callee) post (aa, 88) :=
    phase2_heapByteEff_allocated_unhit heff hArenaE ⟨hAAal.1, hAAal.2.1⟩ hAAalloc
      (fun j hj => disj_symm (hd2 j hj (aa, 88) hAAmem))
  have haa : hdr post aa 0 = hdr s aa 0 := by
    have haa8 := hAAal.1
    unfold hdr
    exact memW_eq_of_ivlUnhit hAAunhit (by omega) hAAbound ⟨by omega, by omega⟩
  have hak88 : (ak, 88) ∈ htabFootprint (callEntryStateHOLFinite s callee) ak := by
    simp [htabFootprint]
  have hakMem : (ak, 88) ∈ worldTypedIvls (callEntryStateHOLFinite s callee) S2 Nd2 := by
    simp only [worldTypedIvls, List.mem_append]
    left; left; left; left; left
    exact List.mem_flatMap.mpr ⟨ak, hakS2, hak88⟩
  have hakAl := ((hwE.1.2.1 ak hakS2).1.1 (ak, 88) hak88).2
  have hakAlloc : Allocated (callEntryStateHOLFinite s callee) (ak, 88) :=
    ((hwE.1.2.1 ak hakS2).2 (ak, 88) hak88).1
  have hakBound := (ivl_allocated_bound hArenaE.2 hakAlloc).2
  have hakUnhit : IvlUnhit (callEntryStateHOLFinite s callee) post (ak, 88) :=
    phase2_heapByteEff_allocated_unhit heff hArenaE ⟨hakAl.1, hakAl.2.1⟩ hakAlloc
      (fun j hj => disj_symm (hd2 j hj (ak, 88) hakMem))
  have hak : hdr post ak 0 = hdr s ak 0 := by
    have hak8 := hakAl.1
    unfold hdr
    exact memW_eq_of_ivlUnhit hakUnhit (by omega) hakBound ⟨by omega, by omega⟩
  have hbo : globN post "bo" = globN s "bo" := by
    have hg := heff.globals (ofString "bo") (by decide)
    change s.globals.lookup (ofString "bo") = post.globals.lookup (ofString "bo") at hg
    simp only [globN, hg]
  have hboR : ∀ j ∈ [(locN (callEntryStateHOLFinite s callee) "out", 20),
      (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
      (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)],
      Disj (globN (callEntryStateHOLFinite s callee) "bo", 88) j := fun j hj =>
    disj_symm (hd2 j hj (globN (callEntryStateHOLFinite s callee) "bo", 88) hboMem)
  have hbo88 : (88 : Nat) % 8 = 0 := by decide
  have hbohi : (globN (callEntryStateHOLFinite s callee) "bo", 88).1 % 8 = 0 ∧
      (globN (callEntryStateHOLFinite s callee) "bo", 88).2 % 8 = 0 := ⟨hboW.2.1, hbo88⟩
  have hbo8' : globN (callEntryStateHOLFinite s callee) "bo" % 8 = 0 := hboW.2.1
  have hbu : IvlUnhit (callEntryStateHOLFinite s callee) post
      (globN (callEntryStateHOLFinite s callee) "bo", 88) :=
    phase2_heapByteEff_allocated_unhit heff hArenaE hbohi hboW.1 hboR
  have hbob := (ivl_allocated_bound hArenaE.2 hboW.1).2
  have hlk : ∀ k ∈ ([40, 72] : List Nat),
      memW (callEntryStateHOLFinite s callee)
          (globN (callEntryStateHOLFinite s callee) "bo" + k) ≠ 0 ∧
        Allocated (callEntryStateHOLFinite s callee)
          (memW (callEntryStateHOLFinite s callee)
            (globN (callEntryStateHOLFinite s callee) "bo" + k), 24) ∧
        (memW (callEntryStateHOLFinite s callee)
          (globN (callEntryStateHOLFinite s callee) "bo" + k)) % 8 = 0 ∧
        memW (callEntryStateHOLFinite s callee)
            (globN (callEntryStateHOLFinite s callee) "bo" + k) + 24 ≤ 2 ^ 64 ∧
        ∀ j ∈ [(locN (callEntryStateHOLFinite s callee) "out", 20),
          (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
          (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)],
          Disj (memW (callEntryStateHOLFinite s callee)
            (globN (callEntryStateHOLFinite s callee) "bo" + k), 24) j := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    have hnz : memW (callEntryStateHOLFinite s callee)
        (globN (callEntryStateHOLFinite s callee) "bo" + k) ≠ 0 := by
      rcases hk with rfl | rfl
      · exact hE.bo40
      · exact hE.bo72
    have hmem_bo : (memW (callEntryStateHOLFinite s callee)
          (globN (callEntryStateHOLFinite s callee) "bo" + k), 24)
        ∈ blockOutObjects (callEntryStateHOLFinite s callee) := by
      rcases hk with rfl | rfl <;> simp [blockOutObjects, hboNZ, hnz]
    have hmem_fix : (memW (callEntryStateHOLFinite s callee)
          (globN (callEntryStateHOLFinite s callee) "bo" + k), 24)
        ∈ fixedObjects (callEntryStateHOLFinite s callee) :=
      List.mem_append_left _ (List.mem_append_right _ hmem_bo)
    obtain ⟨hal, hwords⟩ := (hwE.2.2.1.1 _ hmem_fix).resolve_left (by simp)
    refine ⟨hnz, hal, hwords.1, (ivl_allocated_bound hArenaE.2 hal).2, ?_⟩
    intro j hj
    have hmemW : (memW (callEntryStateHOLFinite s callee)
          (globN (callEntryStateHOLFinite s callee) "bo" + k), 24)
        ∈ worldTypedIvls (callEntryStateHOLFinite s callee) S2 Nd2 := by
      simp only [worldTypedIvls, List.mem_append]
      left; left; right
      rcases hk with rfl | rfl <;> simp [blockOutObjects, hboNZ, hnz]
    exact disj_symm (hd2 j hj _ hmemW)
  have hunhit : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat),
      ∀ region ∈ [(locN (callEntryStateHOLFinite s callee) "out", 20),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)],
        ¬ CellHits (globN (callEntryStateHOLFinite s callee) "bo" + k) region := by
    intro k hk region hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    have ha8 : (globN (callEntryStateHOLFinite s callee) "bo" + k) % 8 = 0 := by
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
    have hin : (globN (callEntryStateHOLFinite s callee) "bo", 88).1
          ≤ globN (callEntryStateHOLFinite s callee) "bo" + k ∧
        globN (callEntryStateHOLFinite s callee) "bo" + k + 8
          ≤ (globN (callEntryStateHOLFinite s callee) "bo", 88).1
            + (globN (callEntryStateHOLFinite s callee) "bo", 88).2 := by
      show globN (callEntryStateHOLFinite s callee) "bo"
          ≤ globN (callEntryStateHOLFinite s callee) "bo" + k ∧
        globN (callEntryStateHOLFinite s callee) "bo" + k + 8
          ≤ globN (callEntryStateHOLFinite s callee) "bo" + 88
      constructor <;> omega
    exact not_cellHits_of_disj ha8 (hzero region hr) hin (hboR region hr)
  have hTxEnv := phase2_compute_contract_address_txEnv h s post vs body callee ret
    (some (.returned v)) hc hl hb (by simp) (Or.inl ⟨v, rfl⟩) ht.1.1.1 hE hunhit
  have hStore := phase2_compute_contract_address_selected_store_ready h buffers contents
    s post vs body callee ret (some (.returned v))
    [(locN (callEntryStateHOLFinite s callee) "out", 20),
     (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
     (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)] rfl
    hc hl hb (by simp) (Or.inl ⟨v, rfl⟩) ht.1.1 hw1
    (fun i region hr => (hsep region hr).2 i) hunhit
  obtain ⟨hwr, hjr⟩ := phase2_heapByteEff_roles hArenaE hwE heff hd2
  have hTables := phase2_compute_contract_address_selected_tables h s post vs body callee ret
    (some (.returned v)) aa ak hc hl hb (by simp) (Or.inl ⟨v, rfl⟩) ht.1.1.1
    ht.1.1.2.2.2.1 hwr hjr haa hak
    ⟨S2, Nd2, hw2w, haaS2, hakS2, hal2, hkl2, haf2, hkf2, hm2, hd2⟩
  have hlu : ∀ k ∈ ([40, 72] : List Nat),
      IvlUnhit (callEntryStateHOLFinite s callee) post
        (memW (callEntryStateHOLFinite s callee)
          (globN (callEntryStateHOLFinite s callee) "bo" + k), 24) := by
    intro k hk
    have hsz8 : (24 : Nat) % 8 = 0 := by decide
    exact phase2_heapByteEff_allocated_unhit heff hArenaE ⟨(hlk k hk).2.2.1, hsz8⟩
      (hlk k hk).2.1 (hlk k hk).2.2.2.2
  have hTxB : R16Shards.TxBacking {post with locals := s.locals} :=
    R16Shards.PtxP34.txBacking_of_unhit_headers ht.2.2.1 hbo hboW.2.1 hbob hbu
      (fun k hk => (hlk k hk).2.2.1) (fun k hk => (hlk k hk).2.2.2.1) hlu
  have hShapes : R16Shards.PtxPhase4LocalShapes {post with locals := s.locals} :=
    phase2_phase4_shapes_localsOnly s s.locals post.clock (fun _ _ => rfl) ht.2.2.2.1
  have hstep := R16Shards.PtxP1.funSpec_at_lookup h.wk_compute_contract_address s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry ht.1.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hstep
  have step := hstep (Or.inl ⟨v, rfl⟩)
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨S1, Nd1, hw1w, hlb1, hmd1, hd1W⟩ := hw1 i
  obtain ⟨S1', Nd1', -, hw1', hg1, hframe1, -⟩ := step.2.2.2.2 S1 Nd1
    ((worldTypedWith_with_locals s callee (s.clock - 1) S1 Nd1).mpr hw1w) hd1W
  have hmall := ht.1.1.2.2.2.2.1.1
  have hm40eq : memW post (locN s "m" + 40) = memW s (locN s "m" + 40) :=
    phase2_world_frame_heap_disjoint (callEntryStateHOLFinite s callee) post
      (worldOwned (callEntryStateHOLFinite s callee) S1 Nd1)
      [(locN (callEntryStateHOLFinite s callee) "out", 20),
       (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
       (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)]
      (locN s "m", 176) (locN s "m" + 40) hArenaE.2 ht.1.1.2.2.2.1
      ⟨by omega, by omega⟩ (by simp [Nat.add_mod, hmall]) hframe1
      (hmd1 (locN s "m", 176) (by simp))
      (fun region hr => (hsep region hr).1)
      (worldOwned_zero_aligned ((worldTypedWith_with_locals s callee (s.clock - 1) S1 Nd1).mpr hw1w))
      hzero
  refine ⟨⟨hStore, ht.1.2⟩, hTables, hTxB, hShapes, ?_, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2⟩
  show memW post (locN s "m" + 40) < 2 ^ 63
  rw [hm40eq]
  exact ht.2.2.2.2.1

/-! ### Segment B part 2a L9 Hoare: the create-vs-call ite keeps the joint
table-store cut. -/

/-- Postcondition weakening for fallible Hoare posts. -/
theorem hoare_none_post_weaken {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Q Q' : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {prog : ProgHOL 64}
    (h : Hoare P prog (fun r t => r = none → Q t))
    (hQ : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F), Q t → Q' t) :
    Hoare P prog (fun r t => r = none → Q' t) :=
  ⟨fun s hc hp hnt hr => hQ _ (h.run s hc hp hnt hr)⟩

/-- The ite at position 91: both branches keep the three-name table-store
cut; the create branch drops the helper local `ct` after the creation
stores. -/
theorem phase2_b2a_l9_ite_hoare (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (aa ak : Nat) :
    Hoare (PtxMessageTableStoreReady buffers contents ["empty", "aa", "ak"] aa ak)
      (.ite (.cmp .equal
          (.load .one (.op .add [.var .local (ofString "tx"), .const (152#64)]))
          (.const (0#64)))
        (.decCall (ofString "sa") .one (ofString "get_account")
          [.var .local (ofString "sender")]
        (.decCall (ofString "ct") .one (ofString "alloc") [.const (24#64)]
        (.seq (.call (some (none, none)) (ofString "compute_contract_address")
          [.var .local (ofString "sender"),
           .op .sub [.load .one (.op .add [.var .local (ofString "sa"), .const (0#64)]),
             .const (1#64)],
           .var .local (ofString "ct")])
        phase2_message_create_stores)))
      phase2_message_call_stores)
      (fun r t => r = none →
        PtxMessageTableStoreReady buffers contents ["empty", "aa", "ak"] aa ak t) := by
  have hcs : Hoare (PtxMessageTableStoreReady buffers contents ["ct", "empty", "aa", "ak"] aa ak)
      phase2_message_create_stores
      (fun r t => r = none →
        PtxMessageTableStoreReady buffers contents ["empty", "aa", "ak"] aa ak t) :=
    hoare_none_post_weaken
      (phase2_message_create_stores_table_ready buffers contents
        ["ct", "empty", "aa", "ak"] aa ak (by simp) (by simp))
      (fun t => phase2_b2a_tsr_weaken buffers contents
        (fun n hn => List.mem_cons_of_mem _ hn) aa ak)
  have hseq := Hoare.seq_fall (phase2_b2a_cca_hoare h buffers contents aa ak) hcs
  have hct := Hoare.decCall_fall
    (names := ["m", "index", "aa", "ak"] ++ ["empty", "aa", "ak"] ++
      ["tx", "index", "sender", "gas", "tx_blob_gas_used", "price", "intrinsic"])
    (shape := .one)
    (by decide)
    (phase2_b2a_tsr_localsOnly buffers contents ["empty", "aa", "ak"] aa ak)
    (phase2_b2a_ct_alloc_inv h buffers contents aa ak) hseq
  have hsa := Hoare.decCall_fall
    (names := ["m", "index", "aa", "ak"] ++ ["empty", "aa", "ak"] ++
      ["tx", "index", "sender", "gas", "tx_blob_gas_used", "price", "intrinsic"])
    (shape := .one)
    (by decide)
    (phase2_b2a_tsr_localsOnly buffers contents ["empty", "aa", "ak"] aa ak)
    (phase2_get_account_message_table_ready h buffers contents ["empty", "aa", "ak"] aa ak
      (ofString "sa") [.var .local (ofString "sender")]
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    hct
  refine R16Shards.GbodyC17ToC21Common.Hoare.ite_fall ?_ ?_
  · exact Hoare.mono hsa (fun _ hp => hp.1)
  · exact Hoare.mono
      (phase2_message_call_stores_table_ready buffers contents ["empty", "aa", "ak"] aa ak
         (by simp)) (fun _ hp => hp.1)

/-! ### Segment B part 2a L10: the resolved create and call paths
(positions 89..97 with the position-91 ite resolved on either branch). -/

/-- l10, creation path: the empty-message allocation, the sender account
lookup, the fresh-address allocation, and the contract-address computation —
bridged across the call by `phase2_b2a_cca_hoare` — compose with the creation
stores, the final warming, and the pointer writes. -/
theorem phase2_b2a_l10_create_bound (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (aa ak : Nat)
    {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn
      (fun s => (PtxMessageReady s ∧ R16Shards.TxBacking s) ∧
        R16Shards.PtxPhase4LocalShapes s) tail b) :
    TerminatingProgBoundedOn
      (PtxMessageTableStoreReady buffers contents ["aa", "ak"] aa ak)
      (.decCall (ofString "empty") .one (ofString "alloc") [.const (8#64)]
        (.decCall (ofString "sa") .one (ofString "get_account")
          [.var .local (ofString "sender")]
        (.decCall (ofString "ct") .one (ofString "alloc") [.const (24#64)]
        (.seq (.call (some (none, none)) (ofString "compute_contract_address")
          [.var .local (ofString "sender"),
           .op .sub [.load .one (.op .add [.var .local (ofString "sa"), .const (0#64)]),
             .const (1#64)],
           .var .local (ofString "ct")])
        (.seq phase2_message_create_stores
          (spinePlug 6 (spineAt 92 ptxCode) tail))))))
      (K.alloc + (K.get_account + (K.alloc +
        (K.«compute_contract_address» + 1 + (K.htab_set + 1 + b)) + 1) + 1) + 1) := by
  have hentry : CallEntryOn
      (fun s =>
        PtxMessageTableStoreReady buffers contents ["ct", "empty", "aa", "ak"] aa ak s ∧
        (∀ region ∈ [(locN s "ct", 20),
          (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
          (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)],
          Disj (locN s "m", 176) region ∧ ∀ i, Disj (buffers i) region) ∧
        (∀ i, ∃ S Nd, WorldTypedWith s S Nd ∧
          PtxLiveBufferAt s S Nd (buffers i) (contents i) ∧
          IvlsDisj [(locN s "m", 176)] (worldOwned s S Nd) ∧
          IvlsDisj [(locN s "ct", 20),
            (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
            (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)]
            (worldTypedIvls s S Nd)) ∧
        (∃ S Nd, WorldTypedWith s S Nd ∧ aa ∈ S ∧ ak ∈ S ∧
          hdr s aa 0 = 20 ∧ hdr s ak 0 = 52 ∧
          (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ aa) ∧
          (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ ak) ∧
          IvlsDisj [(locN s "m", 176)] (worldOwned s S Nd) ∧
          IvlsDisj [(locN s "ct", 20),
            (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
            (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)]
            (worldTypedIvls s S Nd)))
      GuestInv (ofString "compute_contract_address")
      [.var .local (ofString "sender"),
       .op .sub [.load .one (.op .add [.var .local (ofString "sa"), .const (0#64)]),
         .const (1#64)],
       .var .local (ofString "ct")] :=
    fun s vs body callee ret hc hp he hl =>
      callEntryOn_guestInv _ _ s vs body callee ret hc hp.1.1.1.1.1.1 he hl
  have hcall : TerminatingProgBoundedOn
      (fun s =>
        PtxMessageTableStoreReady buffers contents ["ct", "empty", "aa", "ak"] aa ak s ∧
        (∀ region ∈ [(locN s "ct", 20),
          (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
          (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)],
          Disj (locN s "m", 176) region ∧ ∀ i, Disj (buffers i) region) ∧
        (∀ i, ∃ S Nd, WorldTypedWith s S Nd ∧
          PtxLiveBufferAt s S Nd (buffers i) (contents i) ∧
          IvlsDisj [(locN s "m", 176)] (worldOwned s S Nd) ∧
          IvlsDisj [(locN s "ct", 20),
            (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
            (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)]
            (worldTypedIvls s S Nd)) ∧
        (∃ S Nd, WorldTypedWith s S Nd ∧ aa ∈ S ∧ ak ∈ S ∧
          hdr s aa 0 = 20 ∧ hdr s ak 0 = 52 ∧
          (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ aa) ∧
          (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ ak) ∧
          IvlsDisj [(locN s "m", 176)] (worldOwned s S Nd) ∧
          IvlsDisj [(locN s "ct", 20),
            (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
            (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)]
            (worldTypedIvls s S Nd)))
      (.call (some (none, none)) (ofString "compute_contract_address")
        [.var .local (ofString "sender"),
         .op .sub [.load .one (.op .add [.var .local (ofString "sa"), .const (0#64)]),
           .const (1#64)],
         .var .local (ofString "ct")])
      (K.«compute_contract_address» + 1) :=
    TerminatingProgBoundedOn.call_on h.fb_compute_contract_address none
      [.var .local (ofString "sender"),
       .op .sub [.load .one (.op .add [.var .local (ofString "sa"), .const (0#64)]),
         .const (1#64)],
       .var .local (ofString "ct")] hentry
  have hinner : TerminatingProgBoundedOn
      (fun s =>
        PtxMessageTableStoreReady buffers contents ["ct", "empty", "aa", "ak"] aa ak s ∧
        (∀ region ∈ [(locN s "ct", 20),
          (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
          (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)],
          Disj (locN s "m", 176) region ∧ ∀ i, Disj (buffers i) region) ∧
        (∀ i, ∃ S Nd, WorldTypedWith s S Nd ∧
          PtxLiveBufferAt s S Nd (buffers i) (contents i) ∧
          IvlsDisj [(locN s "m", 176)] (worldOwned s S Nd) ∧
          IvlsDisj [(locN s "ct", 20),
            (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
            (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)]
            (worldTypedIvls s S Nd)) ∧
        (∃ S Nd, WorldTypedWith s S Nd ∧ aa ∈ S ∧ ak ∈ S ∧
          hdr s aa 0 = 20 ∧ hdr s ak 0 = 52 ∧
          (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ aa) ∧
          (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ ak) ∧
          IvlsDisj [(locN s "m", 176)] (worldOwned s S Nd) ∧
          IvlsDisj [(locN s "ct", 20),
            (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
            (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)]
            (worldTypedIvls s S Nd)))
      (.seq (.call (some (none, none)) (ofString "compute_contract_address")
          [.var .local (ofString "sender"),
           .op .sub [.load .one (.op .add [.var .local (ofString "sa"), .const (0#64)]),
             .const (1#64)],
           .var .local (ofString "ct")])
        (.seq phase2_message_create_stores
          (spinePlug 6 (spineAt 92 ptxCode) tail)))
      (K.«compute_contract_address» + 1 + (K.htab_set + 1 + b)) :=
    seq_bound_trans hcall (phase2_b2a_cca_hoare h buffers contents aa ak)
      (phase2_message_create_stores_final_bound h buffers contents
        ["ct", "empty", "aa", "ak"] aa ak (by simp) (by simp) (by simp) (by simp) ht)
  have hct : TerminatingProgBoundedOn
      (PtxMessageTableStoreReady buffers contents ["empty", "aa", "ak"] aa ak)
      (.decCall (ofString "ct") .one (ofString "alloc") [.const (24#64)]
        (.seq (.call (some (none, none)) (ofString "compute_contract_address")
            [.var .local (ofString "sender"),
             .op .sub [.load .one (.op .add [.var .local (ofString "sa"), .const (0#64)]),
               .const (1#64)],
             .var .local (ofString "ct")])
          (.seq phase2_message_create_stores
            (spinePlug 6 (spineAt 92 ptxCode) tail))))
      (K.alloc + (K.«compute_contract_address» + 1 + (K.htab_set + 1 + b)) + 1) :=
    TerminatingProgBoundedOn.decCall_on h.fb_alloc (ofString "ct") .one [.const (24#64)]
      (Q := fun s =>
        PtxMessageTableStoreReady buffers contents ["ct", "empty", "aa", "ak"] aa ak s ∧
        (∀ region ∈ [(locN s "ct", 20),
          (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
          (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)],
          Disj (locN s "m", 176) region ∧ ∀ i, Disj (buffers i) region) ∧
        (∀ i, ∃ S Nd, WorldTypedWith s S Nd ∧
          PtxLiveBufferAt s S Nd (buffers i) (contents i) ∧
          IvlsDisj [(locN s "m", 176)] (worldOwned s S Nd) ∧
          IvlsDisj [(locN s "ct", 20),
            (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
            (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)]
            (worldTypedIvls s S Nd)) ∧
        (∃ S Nd, WorldTypedWith s S Nd ∧ aa ∈ S ∧ ak ∈ S ∧
          hdr s aa 0 = 20 ∧ hdr s ak 0 = 52 ∧
          (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ aa) ∧
          (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ ak) ∧
          IvlsDisj [(locN s "m", 176)] (worldOwned s S Nd) ∧
          IvlsDisj [(locN s "ct", 20),
            (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
            (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)]
            (worldTypedIvls s S Nd)))
      (fun s vs body callee ret hc hp he hl =>
        guestInv_callEntry s callee hp.1.1.1.1.1)
      (phase2_b2a_ct_alloc_inv h buffers contents aa ak)
      hinner
  have hsa : TerminatingProgBoundedOn
      (PtxMessageTableStoreReady buffers contents ["empty", "aa", "ak"] aa ak)
      (.decCall (ofString "sa") .one (ofString "get_account")
          [.var .local (ofString "sender")]
        (.decCall (ofString "ct") .one (ofString "alloc") [.const (24#64)]
        (.seq (.call (some (none, none)) (ofString "compute_contract_address")
          [.var .local (ofString "sender"),
           .op .sub [.load .one (.op .add [.var .local (ofString "sa"), .const (0#64)]),
             .const (1#64)],
           .var .local (ofString "ct")])
        (.seq phase2_message_create_stores
          (spinePlug 6 (spineAt 92 ptxCode) tail)))))
      (K.get_account + (K.alloc +
        (K.«compute_contract_address» + 1 + (K.htab_set + 1 + b)) + 1) + 1) :=
    phase2_get_account_message_table_bound h buffers contents ["empty", "aa", "ak"] aa ak
      (ofString "sa") [.var .local (ofString "sender")]
      (by decide) (by decide) (by decide) (by decide)
      (by intro n hn; simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
          rcases hn with rfl | rfl | rfl <;> decide)
      (by intro n hn; simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
          rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      hct
  intro F s hc hp
  exact phase2_alloc_message_table_word_bound h buffers contents ["aa", "ak"] aa ak "empty"
    [.const (8#64)]
    (by decide) (by decide) (by decide) (by decide)
    (by intro n hn; simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl <;> decide)
    (by intro n hn; simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    hsa s hc hp

/-- l10, ordinary-call path: the empty-message allocation and the six
call-path stores compose with the final warming and the pointer writes via
the frozen call-stores final bound. -/
theorem phase2_b2a_l10_call_bound (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (aa ak : Nat)
    {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn
      (fun s => (PtxMessageReady s ∧ R16Shards.TxBacking s) ∧
        R16Shards.PtxPhase4LocalShapes s) tail b) :
    TerminatingProgBoundedOn
      (PtxMessageTableStoreReady buffers contents ["aa", "ak"] aa ak)
      (.decCall (ofString "empty") .one (ofString "alloc") [.const (8#64)]
        (.seq phase2_message_call_stores (spinePlug 6 (spineAt 92 ptxCode) tail)))
      (K.alloc + (K.htab_set + 1 + b) + 1) :=
  phase2_alloc_message_table_word_bound h buffers contents ["aa", "ak"] aa ak "empty"
    [.const (8#64)]
    (by decide) (by decide) (by decide) (by decide)
    (by intro n hn; simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl <;> decide)
    (by intro n hn; simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (phase2_message_call_stores_final_bound h buffers contents ["empty", "aa", "ak"] aa ak
      (by simp) (by simp) (by simp) ht)

/-! ### Segment B part 2a: the full spine cut (positions 87..97). -/

/-- The counter init plus the ak warming loop (positions 87..88). -/
theorem phase2_b2a_shape11 (tail : ProgHOL 64) :
    spinePlug 11 (spineAt 87 ptxCode) tail =
      .seq (.assign .local (ofString "i") (.const (BitVec.ofNat 64 0)))
        (spinePlug 10 (spineAt 88 ptxCode) tail) := by
  simp only [ptxCode, sourceFunctionEntry, Guest.Software.guestFn_process_transaction]
  rfl

/-- The ak warming loop with its exact source shape (position 88). -/
theorem phase2_b2a_shape10 (tail : ProgHOL 64) :
    spinePlug 10 (spineAt 88 ptxCode) tail =
      .seq (.while (.cmp .less (.var .local (ofString "i"))
          (.var .local (ofString "nkeys")))
        (.seq (.call (some (none, none)) (ofString "htab_set")
            [.var .local (ofString "ak"),
             .op .add [.var .local (ofString "al_keys"),
               .panop .mul [.var .local (ofString "i"), .const 52#64]],
             .const 1#64])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const 1#64]))))
        (spinePlug 9 (spineAt 89 ptxCode) tail) := by
  simp only [ptxCode, sourceFunctionEntry, Guest.Software.guestFn_process_transaction]
  rfl

/-- Splitting the post-warming spine at the create-vs-call ite. -/
theorem phase2_b2a_shape89 (tail : ProgHOL 64) :
    spinePlug 9 (spineAt 89 ptxCode) tail =
      spinePlug 2 (spineAt 89 ptxCode) (spinePlug 7 (spineAt 91 ptxCode) tail) := by
  simp only [ptxCode, sourceFunctionEntry, Guest.Software.guestFn_process_transaction]
  rfl

/-- The segment-B2a entry guard: the two-table invariant plus the orphaned
message gas bound and the pinned table roots. -/
def PtxB2aQ {ι : Type} (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (aa ak : Nat) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop := fun s =>
  PtxHtabABInv buffers contents names s ∧
    memW s (locN s "m" + 40) < 2 ^ 63 ∧ locN s "aa" = aa ∧ locN s "ak" = ak

/-- The segment guard reads only the listed locals (and is clock-insensitive). -/
theorem ptxB2aQ_locallyOnly {ι : Type} [Nonempty ι] (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String) (aa ak : Nat) :
    LocalsOnly (["aa", "ak", "m", "index", "tx", "sender", "gas", "tx_blob_gas_used",
      "price", "intrinsic"] ++ names) (PtxB2aQ buffers contents names aa ak) := by
  intro F s locals k hl hp
  refine ⟨ptxHtabABInv_locallyOnly buffers contents names s locals k hl hp.1, ?_, ?_, ?_⟩
  · rw [locN_congr s locals k "m" (hl "m" (by simp))]
    exact hp.2.1
  · rw [locN_congr s locals k "aa" (hl "aa" (by simp))]
    exact hp.2.2.1
  · rw [locN_congr s locals k "ak" (hl "ak" (by simp))]
    exact hp.2.2.2

/-- Setting the counter preserves the segment guard. -/
theorem phase2_b2a_q_set_i {ι : Type} [Nonempty ι] (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String) (aa ak : Nat)
    (v : ValueHOL 64) (hne : ∀ n ∈ names, ofString n ≠ ofString "i")
    {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxB2aQ buffers contents names aa ak s) :
    PtxB2aQ buffers contents names aa ak (setVarHOLFinite (ofString "i") v s) := by
  refine ⟨phase2_htabABInv_set_i buffers contents names v hne hp.1, ?_, ?_, ?_⟩
  · rw [locN_setVar_ne _ "m" (ofString "i") v (by decide)]
    exact hp.2.1
  · rw [locN_setVar_ne _ "aa" (ofString "i") v (by decide)]
    exact hp.2.2.1
  · rw [locN_setVar_ne _ "ak" (ofString "i") v (by decide)]
    exact hp.2.2.2

/-- The counter init preserves the segment guard. -/
theorem phase2_b2a_assign0_q {ι : Type} [Nonempty ι] (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String) (aa ak : Nat)
    (hne : ∀ n ∈ names, ofString n ≠ ofString "i") :
    Hoare (PtxB2aQ buffers contents names aa ak)
      (.assign .local (ofString "i") (.const (BitVec.ofNat 64 0)))
      (fun r s => r = none → PtxB2aQ buffers contents names aa ak s) := by
  apply Hoare.assign
  · intro F s v hp _
    exact fun _ => phase2_b2a_q_set_i buffers contents names aa ak v hne hp
  · exact fun _ _ hr => by cases hr

/-- The counter bump preserves the segment guard. -/
theorem phase2_b2a_increment_q {ι : Type} [Nonempty ι] (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String) (aa ak : Nat)
    (hne : ∀ n ∈ names, ofString n ≠ ofString "i") :
    Hoare (PtxB2aQ buffers contents names aa ak)
      (.assign .local (ofString "i")
        (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))
      (fun r s => r = none → PtxB2aQ buffers contents names aa ak s) := by
  apply Hoare.assign
  · intro F s v hp _
    exact fun _ => phase2_b2a_q_set_i buffers contents names aa ak v hne hp
  · exact fun _ _ hr => by cases hr

/-- Key insertion preserves the whole segment guard: the two-table invariant
as in `phase2_htabAB_set`, plus the message gas bound (the call frames the
message interval) and the pinned roots (a call0 restores the caller locals). -/
theorem phase2_b2a_set_q {ι : Type} [Nonempty ι] (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String) (aa ak : Nat)
    (key value : ExpHOL 64) :
    Hoare (PtxB2aQ buffers contents names aa ak)
      (.call (some (none, none)) (ofString "htab_set")
        [.var .local (ofString "ak"), key, value])
      (fun r s => r = none → PtxB2aQ buffers contents names aa ak s) := by
  apply Hoare.call0_resume
  intro F s vs body callee ret v post hc hp ha hl hr
  obtain ⟨hab, hg, hpa, hpk⟩ := hp
  obtain ⟨haa_w, hak_w, ⟨hstore, hnames⟩, htx, hp4, hworld⟩ := hab
  obtain ⟨S, Nd, hw, ham, hkm, hal, hkl, haf, hkf, hdisj⟩ := hworld
  obtain ⟨v1, _, _, he1, _, _, hct, _, _⟩ := R16WkAcctWs.callee_param_three s
    (ofString "htab_set") (ofString "t") (ofString "key") (ofString "value")
    .one .one .one _ _ (by rw [hc]; exact EvmFrameSpecs.lookup_htab_set)
    _ _ _ vs body callee ret ha hl
  have hev : s.locals.lookup (ofString "ak") = some v1 := by
    simpa [evalAt, evalHOLExact] using he1
  obtain ⟨wk, hwk⟩ := hak_w
  have hv1 : v1 = .val (.word wk) := by
    rw [hev] at hwk
    exact Option.some.inj hwk
  subst hv1
  have ht : locN (callEntryStateHOLFinite s callee) "t" = locN s "ak" := by
    simp [locN, callEntryStateHOLFinite, hct, hwk]
  have hA_s : ArenaReady s := hstore.1.1
  have hE_s : TxEnv s := hstore.2.1
  have hin_m : Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr") :=
    hstore.2.2.2.1
  have hA_ent : ArenaReady (callEntryStateHOLFinite s callee) :=
    (arenaReady_with_locals s callee (s.clock - 1)).mpr hA_s
  have hw_ent : WorldTypedWith (callEntryStateHOLFinite s callee) S Nd :=
    (worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hw
  have hkm_ent : locN (callEntryStateHOLFinite s callee) "t" ∈ S := ht.symm ▸ hkm
  have harg : HtabArgWF (callEntryStateHOLFinite s callee) := by
    refine ⟨hA_ent, ?_, ?_⟩
    · rw [ht]
      exact (htabWF_with_locals s callee (s.clock - 1) _).mpr (hw.1.2.1 _ hkm).1
    · rw [ht]
      exact fun i hi => ((hw.1.2.1 _ hkm).2 i hi).1
  have hx := FunSpec.at_lookup htab_set_spec s hc vs body callee ret hl harg (by rw [hr]; simp)
  rw [hr] at hx
  have hx := hx v rfl
  -- move to the `pre` state that binds `t` to the `ak` value
  let pre := setVarHOLFinite (ofString "t") (.val (.word wk)) s
  have hmp : pre.locals.lookup (ofString "m") = s.locals.lookup (ofString "m") := by
    simp [pre, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "t" ≠ ofString "m" by decide]
  have hip : pre.locals.lookup (ofString "index") = s.locals.lookup (ofString "index") := by
    simp [pre, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "t" ≠ ofString "index" by decide]
  have haa_p : pre.locals.lookup (ofString "aa") = s.locals.lookup (ofString "aa") := by
    simp [pre, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "t" ≠ ofString "aa" by decide]
  have hak_p : pre.locals.lookup (ofString "ak") = s.locals.lookup (ofString "ak") := by
    simp [pre, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "t" ≠ ofString "ak" by decide]
  have hmt : locN pre "m" = locN s "m" := locN_congr s pre.locals s.clock "m" hmp
  have hit : locN pre "index" = locN s "index" := locN_congr s pre.locals s.clock "index" hip
  have hap : locN pre "aa" = locN s "aa" := locN_congr s pre.locals s.clock "aa" haa_p
  have hkp : locN pre "ak" = locN s "ak" := locN_congr s pre.locals s.clock "ak" hak_p
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
  have ht_pre : locN pre "t" = locN s "ak" := hpt.trans ht
  have hkm_pre : locN pre "t" ∈ S := ht_pre.symm ▸ hkm
  have hkf_pre : ∀ a ∈ worldRoleSlots pre ++ journalRoleSlots pre, a.1 ≠ locN pre "t" := by
    intro a ha'
    rw [ht_pre]
    exact hkf a ha'
  have hlim_s : globN pre "heap_ptr" ≤ heapLimit := hA_pre.2.2.1
  have hlim_p : globN {post with locals := s.locals} "heap_ptr" ≤ heapLimit :=
    ((arenaReady_with_locals post s.locals post.clock).mpr hx.1).2.2.1
  -- the store-ready part
  have hstore_pre : PtxStoreReadyIn2 buffers contents (locN s "aa") (locN s "ak") pre :=
    phase2_storeReadyIn2_setVar_ne (name := ofString "t") buffers contents
      (by decide) (by decide) (.val (.word wk)) hstore
  have hstore' : PtxStoreReadyIn2 buffers contents (locN s "aa") (locN s "ak")
      {post with locals := s.locals} := by
    refine phase2_storeReadyIn2_world_step buffers contents pre _ hstore_pre
      ((arenaReady_with_locals post s.locals post.clock).mpr hx.1) ?_
      hmp.symm hx.2.2.2.2.1 ?_
    · exact phase2_htabExit_txEnv (post := {post with locals := s.locals}) hA_pre hE_pre
        hw_pre hkm_pre (by rw [hit]; rfl) hxp
    · intro S' Nd' hw' hmem1' hmem2'
      have hf' := R16Shards.MptC10C12.worldTypedWith_htab_set_local_csr hA_pre hw'
        (by rw [ht_pre]; exact hmem2') hkf_pre hxp hbe
      refine ⟨S', Nd', hmem1', hmem2', hf'.1, hf'.2.2.2.2.2.1, ?_⟩
      exact phase2_frameOutside_of_htabExit hxp (by rw [ht_pre]; exact hmem2')
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
    phase2_htabExit_callEntry_backing callee hA_s hE_s hw hkm_ent htx hx
  -- the world part
  have hdisj_pre : IvlsDisj [(locN pre "m", 176)] (worldOwned pre S Nd) := by
    intro o ho j hj
    simp only [List.mem_singleton] at ho; subst o
    rw [hmt]
    exact hdisj _ (by simp) j hj
  have hworld' : PtxMessageTables {post with locals := s.locals}
      (locN s "aa") (locN s "ak") :=
    phase2_htabExit_ab_message_tables hA_pre
      ⟨S, Nd, hw_pre, ham, hkm, hal, hkl, haf, hkf, hdisj_pre⟩
      (by rw [hmt]; exact hin_m) hmt.symm hbe ht_pre hxp
  -- the message interval is unhit, so the gas field survives
  have hcsr := R16Shards.MptC10C12.worldTypedWith_htab_set_local_csr hA_pre hw_pre
    hkm_pre hkf_pre hxp hbe
  have hu : IvlUnhit pre {post with locals := s.locals} (locN pre "m", 176) :=
    (hcsr.2.2.2.2.2.2 (locN pre "m", 176) (by intro h; omega)
      (by rw [hmt]; exact hin_m)
      (fun j hj => hdisj_pre (locN pre "m", 176) (by simp) j hj)).2.2
  have hsr_pre : PtxMessageStoreReady buffers contents pre := by
    obtain ⟨hW, hE, hm, hin, hwok, hbufs⟩ := hstore_pre
    refine ⟨hW, hE, hm, hin, hwok, ?_⟩
    intro i
    obtain ⟨hd, S', Nd', _, _, hw, hb, hsep⟩ := hbufs i
    exact ⟨hd, S', Nd', hw, hb, hsep⟩
  have hgas : memW {post with locals := s.locals}
      (locN {post with locals := s.locals} "m" + 40) < 2 ^ 63 := by
    have hf5 := phase2_message_unhit_fields hsr_pre hu 5 (by decide)
    rw [hmt] at hf5
    rw [show locN {post with locals := s.locals} "m" = locN s "m" from rfl,
      show (40 : Nat) = 8 * 5 from rfl, hf5]
    exact hg
  -- the shapes part
  obtain ⟨wa, hwa⟩ := haa_w
  refine ⟨⟨⟨wa, hwa⟩, ⟨wk, hwk⟩, ⟨hstore', hnames'⟩, htx', ?_, hworld'⟩, hgas, hpa, hpk⟩
  · exact phase2_phase4_shapes_localsOnly s s.locals post.clock (fun _ _ => rfl) hp4

/-- One ak-warming-loop body preserves the segment guard. -/
theorem phase2_b2a_warm_body_q {ι : Type} [Nonempty ι] (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String) (aa ak : Nat)
    (key : ExpHOL 64) (hne : ∀ n ∈ names, ofString n ≠ ofString "i") :
    Hoare (PtxB2aQ buffers contents names aa ak)
      (.seq (.call (some (none, none)) (ofString "htab_set")
          [.var .local (ofString "ak"), key, .const (BitVec.ofNat 64 1)])
        (.assign .local (ofString "i")
          (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))
      (fun r s => r = none → PtxB2aQ buffers contents names aa ak s) := by
  refine Hoare.seq_fall (phase2_b2a_set_q buffers contents names aa ak key
      (.const (BitVec.ofNat 64 1))) ?_
  exact phase2_b2a_increment_q buffers contents names aa ak hne

/-- The warming loop over the `ak` table preserves the segment guard. -/
theorem phase2_b2a_warm_while_q {ι : Type} [Nonempty ι] (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String) (aa ak : Nat)
    (key bound : ExpHOL 64) (hne : ∀ n ∈ names, ofString n ≠ ofString "i") :
    Hoare (PtxB2aQ buffers contents names aa ak)
      (.while (.cmp .less (.var .local (ofString "i")) bound)
        (.seq (.call (some (none, none)) (ofString "htab_set")
            [.var .local (ofString "ak"), key, .const (BitVec.ofNat 64 1)])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))))
      (fun r s => r = none → PtxB2aQ buffers contents names aa ak s) :=
  hoare_while_less_noCont (ptxB2aQ_locallyOnly buffers contents names aa ak)
    (ofString "i") bound (phase2_b2a_warm_body_q buffers contents names aa ak key hne)
    (phase2_warm_body_noCont (ofString "htab_set")
      [.var .local (ofString "ak"), key, .const (BitVec.ofNat 64 1)])
    (by rfl)

/-- The full segment-B2a cut: the ak warming loop, the empty-table
allocation, the create-vs-call ite, and the final source stores, clock-bound
with the tail's bound. The message gas bound is an explicit entry hypothesis
since it is orphaned upstream. -/
theorem phase2_b2a_bound (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (aa ak : Nat)
    {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn
      (fun s => (PtxMessageReady s ∧ R16Shards.TxBacking s) ∧
        R16Shards.PtxPhase4LocalShapes s) tail b) :
    TerminatingProgBoundedOn (PtxB2aQ buffers contents ["aa", "ak"] aa ak)
      (spinePlug 11 (spineAt 87 ptxCode) tail)
      ((2 ^ 64 + 1) * (K.«htab_set» + 1 + 1) +
        (K.«alloc» + (Nat.max (K.«get_account» + (K.«alloc» +
          (K.«compute_contract_address» + 1 + 0) + 1) + 1) 0 +
          (K.«htab_set» + 1 + b)) + 1)) := by
  have hl10 : TerminatingProgBoundedOn
      (PtxMessageTableStoreReady buffers contents ["empty", "aa", "ak"] aa ak)
      (spinePlug 7 (spineAt 91 ptxCode) tail)
      (Nat.max (K.«get_account» + (K.«alloc» +
          (K.«compute_contract_address» + 1 + 0) + 1) + 1) 0 +
        (K.«htab_set» + 1 + b)) := by
    rw [phase2_b2a_shape7 tail]
    exact seq_bound_trans (phase2_b2a_l9_ite_bound h buffers contents aa ak)
      (phase2_b2a_l9_ite_hoare h buffers contents aa ak)
      (phase2_final_source_bound h buffers contents ["empty", "aa", "ak"] aa ak
        (by simp) (by simp) ht)
  have hl8 : TerminatingProgBoundedOn (PtxB2aQ buffers contents ["aa", "ak"] aa ak)
      (spinePlug 2 (spineAt 89 ptxCode) (spinePlug 7 (spineAt 91 ptxCode) tail))
      (K.«alloc» + (Nat.max (K.«get_account» + (K.«alloc» +
          (K.«compute_contract_address» + 1 + 0) + 1) + 1) 0 +
        (K.«htab_set» + 1 + b)) + 1) :=
    phase2_b2a_l8_empty_alloc_bound h buffers contents ["aa", "ak"] aa ak hl10
  have hl9 : TerminatingProgBoundedOn (PtxB2aQ buffers contents ["aa", "ak"] aa ak)
      (spinePlug 9 (spineAt 89 ptxCode) tail)
      (K.«alloc» + (Nat.max (K.«get_account» + (K.«alloc» +
          (K.«compute_contract_address» + 1 + 0) + 1) + 1) 0 +
        (K.«htab_set» + 1 + b)) + 1) := by
    rw [phase2_b2a_shape89 tail]
    exact hl8
  have ha0 : TerminatingProgBoundedOn (PtxB2aQ buffers contents ["aa", "ak"] aa ak)
      (.assign .local (ofString "i") (.const (BitVec.ofNat 64 0))) 0 :=
    R16Shards.PtxP1.bound_of_clock (P := PtxB2aQ buffers contents ["aa", "ak"] aa ak)
      (fun s => clock_assign s .local (ofString "i") (.const (BitVec.ofNat 64 0)))
  have hwh : TerminatingProgBoundedOn (PtxB2aQ buffers contents ["aa", "ak"] aa ak)
      (.while (.cmp .less (.var .local (ofString "i"))
          (.var .local (ofString "nkeys")))
        (.seq (.call (some (none, none)) (ofString "htab_set")
            [.var .local (ofString "ak"),
             .op .add [.var .local (ofString "al_keys"),
               .panop .mul [.var .local (ofString "i"), .const 52#64]],
             .const 1#64])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const 1#64]))))
      ((2 ^ 64 + 1) * (K.«htab_set» + 1 + 1)) :=
    R16Shards.PtxP1.bound_mono
      (Q := PtxB2aQ buffers contents ["aa", "ak"] aa ak)
      (phase2_htabAB_warm_while_bound h buffers contents ["aa", "ak"]
        (.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "i"), .const 52#64]])
        (.var .local (ofString "nkeys")) (by decide))
      (fun _ hp => hp.1)
  intro F s hc hp
  rw [phase2_b2a_shape11 tail, phase2_b2a_shape10 tail]
  simpa only [Nat.zero_add, Nat.add_zero] using seq_bound_trans ha0
    (phase2_b2a_assign0_q buffers contents ["aa", "ak"] aa ak (by decide))
    (seq_bound_trans hwh
      (phase2_b2a_warm_while_q buffers contents ["aa", "ak"] aa ak
        (.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "i"), .const 52#64]])
        (.var .local (ofString "nkeys")) (by decide))
      hl9) s hc hp

end InitECandidate.Solver.Wave8GuestInv.R13Shards
