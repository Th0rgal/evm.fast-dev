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

end InitECandidate.Solver.Wave8GuestInv.R13Shards
