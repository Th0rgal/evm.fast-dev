import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2BackingF
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1BackingCut

/-!
# Phase 2 backing replay, the backing cut (guest spine 77..98)

Region 77..87 opens with the `aa := htab_new(20, 64)` allocation, inserts the
sender key, warms the table from the precompile and access-list address
tables (two bounded `htab_set` loops), and closes with the
`ak := htab_new(52, 16)` allocation. The message-gas bound born at the
region-D' slot-5 store (`memW m+40 < 2^63`) is threaded through every step
(the `htab_new`/`htab_set` frames leave the message interval unhit), so the
region composes with region D' ahead of it and the segment-B2a replay
behind it. The whole 34..98 spine is then assembled onto the Phase 1 cut's
`PtxPhase2BackingCut` obligation, closing the last documented gap of
`gbody_process_transaction_backing_strong`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R13Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

/-! ## Guards -/

/-- The message-scalar region before the `aa` allocation (position 77),
over the degenerate saved-buffer family: the message frame's scalar
store-ready plus the message-gas bound. -/
def ptxPhase2CutG0 {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxMessageBScalarReady ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames s ∧
    ptxPhase2FM40 s

/-- The htab region after the `aa` allocation (positions 77..85), over the
degenerate saved-buffer family: the region-`Tail` two-conjunct invariant
plus the message-gas bound. -/
def ptxPhase2CutG1 {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxHtabAInv2 ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames s

/-- The htab region after both allocations (positions 86..87), over the
degenerate saved-buffer family. -/
def ptxPhase2CutG2 {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxHtabABInv ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames s

/-! ## Name side conditions -/

theorem ptxPhase2Cut_fnames_ne_i : ∀ n ∈ ptxPhase2FNames, ofString n ≠ ofString "i" := by
  intro n hn
  simp only [ptxPhase2FNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> decide

theorem ptxPhase2Cut_fnames_ne_ak : ∀ n ∈ ptxPhase2FNames, ofString n ≠ ofString "ak" := by
  intro n hn
  simp only [ptxPhase2FNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> decide

/-! ## Locals-insensitivity of the pair guard -/

/-- The region guard with the message-gas bound reads only the listed
locals (and is clock-insensitive). -/
theorem ptxPhase2CutG1M40_locallyOnly {ι : Type} [Nonempty ι] (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String) :
    LocalsOnly (["aa", "m", "index", "tx", "sender", "gas", "tx_blob_gas_used",
      "price", "intrinsic"] ++ names)
      (fun s => PtxHtabAInv2 buffers contents names s ∧ ptxPhase2FM40 s) := by
  intro F s locals k hl hp
  refine ⟨ptxHtabAInv2_locallyOnly buffers contents names s locals k hl hp.1, ?_⟩
  show memW {s with locals := locals, clock := k}
    (locN {s with locals := locals, clock := k} "m" + 40) < 2 ^ 63
  rw [locN_congr s locals k "m" (hl "m" (by simp))]
  exact hp.2

/-! ## The counter steps -/

/-- Setting the loop counter `i` — a name the region guard never reads —
preserves the invariant with the message-gas bound. -/
theorem ptxPhase2Cut_increment_hoare {ι : Type} [Nonempty ι] (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String)
    (hne : ∀ n ∈ names, ofString n ≠ ofString "i") :
    Hoare (fun s => PtxHtabAInv2 buffers contents names s ∧ ptxPhase2FM40 s)
      (.assign .local (ofString "i")
        (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))
      (fun r s => r = none → PtxHtabAInv2 buffers contents names s ∧ ptxPhase2FM40 s) := by
  apply Hoare.assign
  · intro F s v hp _
    refine fun _ => ⟨phase2_htabAInv2_set_i buffers contents names v hne hp.1, ?_⟩
    have h1 : locN (setVarHOLFinite (ofString "i") v s) "m" = locN s "m" :=
      locN_setVar_ne _ "m" (ofString "i") v (by decide)
    show memW (setVarHOLFinite (ofString "i") v s)
      (locN (setVarHOLFinite (ofString "i") v s) "m" + 40) < 2 ^ 63
    rw [h1]
    exact hp.2
  · exact fun _ _ hr => by cases hr

/-- Initializing the loop counter preserves the region guard with the
message-gas bound. -/
theorem ptxPhase2Cut_assign0_hoare {ι : Type} [Nonempty ι] (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String)
    (hne : ∀ n ∈ names, ofString n ≠ ofString "i") :
    Hoare (fun s => PtxHtabAInv2 buffers contents names s ∧ ptxPhase2FM40 s)
      (.assign .local (ofString "i") (.const (BitVec.ofNat 64 0)))
      (fun r s => r = none → PtxHtabAInv2 buffers contents names s ∧ ptxPhase2FM40 s) := by
  apply Hoare.assign
  · intro F s v hp _
    refine fun _ => ⟨phase2_htabAInv2_set_i buffers contents names v hne hp.1, ?_⟩
    have h1 : locN (setVarHOLFinite (ofString "i") v s) "m" = locN s "m" :=
      locN_setVar_ne _ "m" (ofString "i") v (by decide)
    show memW (setVarHOLFinite (ofString "i") v s)
      (locN (setVarHOLFinite (ofString "i") v s) "m" + 40) < 2 ^ 63
    rw [h1]
    exact hp.2
  · exact fun _ _ hr => by cases hr

/-! ## Key insertion with the message-gas bound -/

/-- Private address insertion into the `aa` table preserves the whole
htab-region invariant together with the message-gas bound: the `htab_set`
frame leaves the message interval unhit, so the slot-5 word survives. -/
theorem ptxPhase2Cut_set_q {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (names : List String)
    (key value : ExpHOL 64) :
    Hoare (fun s => PtxHtabAInv2 buffers contents names s ∧ ptxPhase2FM40 s)
      (.call (some (none, none)) (ofString "htab_set")
        [.var .local (ofString "aa"), key, value])
      (fun r s => r = none → PtxHtabAInv2 buffers contents names s ∧ ptxPhase2FM40 s) := by
  apply Hoare.call0_resume
  intro F s vs body callee ret v post hc hp ha hl hr
  obtain ⟨hp', hm40⟩ := hp
  obtain ⟨haa_w, ⟨hstore, hnames⟩, htx, hp4, hworld⟩ := hp'
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
  -- the message interval is unhit, so the gas field survives
  have hcsr := R16Shards.MptC10C12.worldTypedWith_htab_set_local_csr hA_pre hw_pre
    ham_pre haf_pre hxp hbe
  have hu : IvlUnhit pre {post with locals := s.locals} (locN pre "m", 176) :=
    (hcsr.2.2.2.2.2.2 (locN pre "m", 176) (by intro h; omega)
      (by rw [hmt]; exact hin_m)
      (fun j hj => hdisj_pre (locN pre "m", 176) (by simp) j hj)).2.2
  have hsr_pre : PtxMessageStoreReady buffers contents pre :=
    hstore_pre.to_storeReady
  have hf5 := phase2_message_unhit_fields hsr_pre hu 5 (by decide)
  rw [hmt] at hf5
  refine ⟨⟨⟨wa, hwa⟩, ⟨hstore', hnames'⟩, htx', ?_, hworld'⟩, ?_⟩
  · exact phase2_phase4_shapes_localsOnly s s.locals post.clock (fun _ _ => rfl) hp4
  · show memW {post with locals := s.locals}
      (locN {post with locals := s.locals} "m" + 40) < 2 ^ 63
    rw [show locN {post with locals := s.locals} "m" = locN s "m" from rfl,
      show (40 : Nat) = 8 * 5 from rfl, hf5]
    exact hm40

/-! ## The warming loops -/

/-- One warming-loop body: the `htab_set` call followed by the counter bump
preserves the region guard with the message-gas bound. -/
theorem ptxPhase2Cut_warm_body {ι : Type} [Nonempty ι] (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String) (key : ExpHOL 64)
    (hne : ∀ n ∈ names, ofString n ≠ ofString "i") :
    Hoare (fun s => PtxHtabAInv2 buffers contents names s ∧ ptxPhase2FM40 s)
      (.seq (.call (some (none, none)) (ofString "htab_set")
          [.var .local (ofString "aa"), key, .const (BitVec.ofNat 64 1)])
        (.assign .local (ofString "i")
          (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))
      (fun r s => r = none → PtxHtabAInv2 buffers contents names s ∧ ptxPhase2FM40 s) := by
  refine Hoare.seq_fall
    (ptxPhase2Cut_set_q buffers contents names key (.const (BitVec.ofNat 64 1))) ?_
  exact ptxPhase2Cut_increment_hoare buffers contents names hne

/-- The warming-loop body is clock-bounded: the `htab_set` call plus one
assign step. -/
theorem ptxPhase2Cut_warm_body_bound (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (names : List String)
    (key : ExpHOL 64) :
    TerminatingProgBoundedOn (fun s => PtxHtabAInv2 buffers contents names s ∧ ptxPhase2FM40 s)
      (.seq (.call (some (none, none)) (ofString "htab_set")
          [.var .local (ofString "aa"), key, .const (BitVec.ofNat 64 1)])
        (.assign .local (ofString "i")
          (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))
      (K.«htab_set» + 1) := by
  have hcall : TerminatingProgBoundedOn
      (fun s => PtxHtabAInv2 buffers contents names s ∧ ptxPhase2FM40 s)
      (.call (some (none, none)) (ofString "htab_set")
        [.var .local (ofString "aa"), key, .const (BitVec.ofNat 64 1)])
      (K.«htab_set» + 1) := by
    apply TerminatingProgBoundedOn.call_on h.fb_htab_set none _
    intro F s vs body callee ret hc hp he hl
    exact guestInv_callEntry s callee (worldOK_guestInv s hp.1.2.1.1.1)
  have hassign : TerminatingProgBoundedOn
      (fun s => PtxHtabAInv2 buffers contents names s ∧ ptxPhase2FM40 s)
      (.assign .local (ofString "i")
        (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))
      0 :=
    R16Shards.PtxP1.bound_of_clock
      (P := fun s => PtxHtabAInv2 buffers contents names s ∧ ptxPhase2FM40 s)
      (fun s => clock_assign s .local (ofString "i")
        (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))
  intro F s hc hp
  simpa only [Nat.add_zero] using seq_bound_trans hcall
    (ptxPhase2Cut_set_q buffers contents names key (.const (BitVec.ofNat 64 1))) hassign s hc hp

/-- The warming loop over the `aa` table preserves the region guard with
the message-gas bound. -/
theorem ptxPhase2Cut_warm_while {ι : Type} [Nonempty ι] (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String) (key bound : ExpHOL 64)
    (hne : ∀ n ∈ names, ofString n ≠ ofString "i") :
    Hoare (fun s => PtxHtabAInv2 buffers contents names s ∧ ptxPhase2FM40 s)
      (.while (.cmp .less (.var .local (ofString "i")) bound)
        (.seq (.call (some (none, none)) (ofString "htab_set")
            [.var .local (ofString "aa"), key, .const (BitVec.ofNat 64 1)])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))))
      (fun r s => r = none → PtxHtabAInv2 buffers contents names s ∧ ptxPhase2FM40 s) :=
  hoare_while_less_noCont (ptxPhase2CutG1M40_locallyOnly buffers contents names)
    (ofString "i") bound (ptxPhase2Cut_warm_body buffers contents names key hne)
    (phase2_warm_body_noCont (ofString "htab_set")
      [.var .local (ofString "aa"), key, .const (BitVec.ofNat 64 1)])
    (by rfl)

/-- The warming loop over the `aa` table is clock-bounded. -/
theorem ptxPhase2Cut_warm_while_bound (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (names : List String)
    (key bound : ExpHOL 64) (hne : ∀ n ∈ names, ofString n ≠ ofString "i") :
    TerminatingProgBoundedOn (fun s => PtxHtabAInv2 buffers contents names s ∧ ptxPhase2FM40 s)
      (.while (.cmp .less (.var .local (ofString "i")) bound)
        (.seq (.call (some (none, none)) (ofString "htab_set")
            [.var .local (ofString "aa"), key, .const (BitVec.ofNat 64 1)])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))))
      ((2 ^ 64 + 1) * (K.«htab_set» + 1 + 1)) :=
  while_less_noCont (ptxPhase2CutG1M40_locallyOnly buffers contents names) (ofString "i") bound
    (ptxPhase2Cut_warm_body_bound h buffers contents names key)
    (ptxPhase2Cut_warm_body buffers contents names key hne)
    (phase2_warm_body_noCont (ofString "htab_set")
      [.var .local (ofString "aa"), key, .const (BitVec.ofNat 64 1)])
    (phase2_warm_body_incr (ofString "htab_set")
      [.var .local (ofString "aa"), key, .const (BitVec.ofNat 64 1)])

/-! ## Call entries and resumes -/

/-- The `aa` allocation's callee entry is a guest invocation: the scalar
message frame carries a well-typed world. -/
theorem ptxPhase2Cut_aa_callEntry :
    CallEntryOn ptxPhase2CutG0
      GuestInv (ofString "htab_new") [.const (20#64), .const (64#64)] := by
  intro F s vs body callee ret hc hp he hl
  exact guestInv_callEntry s callee (worldOK_guestInv s hp.1.1.1.1)

/-- The `ak` allocation's callee entry is a guest invocation: the region
invariant's store-ready part carries a well-typed world. -/
theorem ptxPhase2Cut_ak_callEntry :
    CallEntryOn (fun s => ptxPhase2CutG1 s ∧ ptxPhase2FM40 s)
      GuestInv (ofString "htab_new") [.const (52#64), .const (16#64)] := by
  intro F s vs body callee ret hc hp he hl
  exact guestInv_callEntry s callee (worldOK_guestInv s hp.1.2.1.1.1)

/-- Resuming after the `aa` allocation: the frozen resume for the scalar
message frame, plus the message-gas bound (the `htab_new` frame leaves the
message interval unhit). -/
theorem ptxPhase2Cut_aa_resume (h : PtxCallees) :
    DecCallResumeOn ptxPhase2CutG0
      (fun s => ptxPhase2CutG1 s ∧ ptxPhase2FM40 s)
      (ofString "aa") (ofString "htab_new") [.const (20#64), .const (64#64)] := by
  intro F s vs body callee ret v post hc hp he hl hb
  have hsReady : PtxMessageStoreReady ptxPhase2FDegBuf ptxPhase2FDegCont s := hp.1.1.1
  have hA_s : ArenaReady s := hp.1.1.1.1.1
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
  have hready : HtabNewReady (callEntryStateHOLFinite s callee) :=
    ⟨hA_ent, by rw [hkl]; decide, by rw [hcap]; decide⟩
  have hexit := FunSpec.at_lookup h.htab_new_spec s hc vs body callee ret hl hready
    (by rw [hb]; simp)
  rw [hb] at hexit
  obtain ⟨w, hvw, hAp, hag, hwf_t, hc3, hkl0, hfp_t, hfr, hgk⟩ := hexit v rfl
  subst hvw
  refine ⟨phase2_htabA_new_aa_resume2 h ptxPhase2FDegBuf ptxPhase2FDegCont s vs body
    callee ret (.val (.word w)) post hc hp.1 he hl hb, ?_⟩
  have h1 : locN (setVarHOLFinite (ofString "aa") (.val (.word w))
      {post with locals := s.locals}) "m" = locN s "m" := by
    rw [locN_setVar_ne _ "m" (ofString "aa") _ (by decide)]
    rfl
  have hu := phase2_htab_new_frame_unhit hA_s hAp hag hfr (Or.inl hin_m)
  have hf5 : memW post (locN s "m" + 40) = memW s (locN s "m" + 40) :=
    phase2_message_unhit_fields hsReady hu 5 (by decide)
  show memW (setVarHOLFinite (ofString "aa") (.val (.word w)) {post with locals := s.locals})
    (locN (setVarHOLFinite (ofString "aa") (.val (.word w)) {post with locals := s.locals})
      "m" + 40) < 2 ^ 63
  rw [h1]
  show memW post (locN s "m" + 40) < 2 ^ 63
  rw [hf5]
  exact hp.2

/-- Resuming after the `ak` allocation: the frozen two-table resume, plus
the message-gas bound (the `htab_new` frame leaves the message interval
unhit). -/
theorem ptxPhase2Cut_ak_resume (h : PtxCallees) :
    DecCallResumeOn (fun s => ptxPhase2CutG1 s ∧ ptxPhase2FM40 s)
      (fun s => ptxPhase2CutG2 s ∧ ptxPhase2FM40 s)
      (ofString "ak") (ofString "htab_new") [.const (52#64), .const (16#64)] := by
  intro F s vs body callee ret v post hc hp he hl hb
  obtain ⟨haa_w, ⟨hstore, hnames⟩, htx, hp4, hworld⟩ := hp.1
  have hsReady : PtxMessageStoreReady ptxPhase2FDegBuf ptxPhase2FDegCont s :=
    hstore.to_storeReady
  have hA_s : ArenaReady s := hstore.1.1
  have hin_m : Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr") :=
    hstore.2.2.2.1
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
  refine ⟨phase2_htabA_new_ak_resume h ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames
    ptxPhase2Cut_fnames_ne_ak s vs body callee ret (.val (.word w)) post hc hp.1 he hl hb, ?_⟩
  have h1 : locN (setVarHOLFinite (ofString "ak") (.val (.word w))
      {post with locals := s.locals}) "m" = locN s "m" := by
    rw [locN_setVar_ne _ "m" (ofString "ak") _ (by decide)]
    rfl
  have hu := phase2_htab_new_frame_unhit hA_s hAp hag hfr (Or.inl hin_m)
  have hf5 : memW post (locN s "m" + 40) = memW s (locN s "m" + 40) :=
    phase2_message_unhit_fields hsReady hu 5 (by decide)
  show memW (setVarHOLFinite (ofString "ak") (.val (.word w)) {post with locals := s.locals})
    (locN (setVarHOLFinite (ofString "ak") (.val (.word w)) {post with locals := s.locals})
      "m" + 40) < 2 ^ 63
  rw [h1]
  show memW post (locN s "m" + 40) < 2 ^ 63
  rw [hf5]
  exact hp.2

/-! ## The bridge into the segment-B2a replay -/

/-- The two-table region guard with the message-gas bound pins its own table
roots, so it is a segment-B2a entry: the `aa`/`ak` names part of the
two-table invariant comes from the table-root witnesses. -/
theorem ptxPhase2Cut_b2a_bridge {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : ptxPhase2CutG2 s ∧ ptxPhase2FM40 s) :
    PtxB2aQ ptxPhase2FDegBuf ptxPhase2FDegCont ["aa", "ak"] (locN s "aa") (locN s "ak") s := by
  obtain ⟨⟨haa, hak, ⟨hstore, hnames⟩, htx, hp4, hworld⟩, hm40⟩ := hp
  refine ⟨⟨haa, hak, ⟨hstore, ?_⟩, htx, hp4, hworld⟩, hm40, rfl, rfl⟩
  intro name hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact haa
  · exact hak

/-! ## The region shape -/

/-- The htab region (positions 77..87) as a literal program: the `aa`
allocation, the sender-key insertion, both warming loops, and the `ak`
allocation. -/
theorem ptxPhase2Cut_shape (tail : ProgHOL 64) :
    spinePlug 10 (spineAt 77 ptxCode) tail =
      .decCall (ofString "aa") .one (ofString "htab_new") [.const (20#64), .const (64#64)]
        (.seq .skip (.seq (.call (some (none, none)) (ofString "htab_set")
            [.var .local (ofString "aa"), .var .local (ofString "sender"),
              .const (BitVec.ofNat 64 1)])
          (.seq .skip (.seq (.assign .local (ofString "i") (.const (BitVec.ofNat 64 0)))
            (.seq (.while (.cmp .less (.var .local (ofString "i"))
                    (.const (BitVec.ofNat 64 18)))
                (.seq (.call (some (none, none)) (ofString "htab_set")
                    [.var .local (ofString "aa"),
                     .op .add [.var .global (ofString "precompile_addrs"),
                       .panop .mul [.var .local (ofString "i"),
                         .const (BitVec.ofNat 64 20)]],
                     .const (BitVec.ofNat 64 1)])
                  (.assign .local (ofString "i")
                    (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))))
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
                  (.seq .skip (.decCall (ofString "ak") .one (ofString "htab_new")
                    [.const (52#64), .const (16#64)] tail))))))))) := by
  simp only [ptxCode, sourceFunctionEntry, Guest.Software.guestFn_process_transaction]
  rfl

/-! ## The region bound -/

/-- The htab region (positions 77..87 with the segment-B2a spine behind it)
is clock-bounded: two `htab_new` allocations, one sender-key insertion, two
bounded warming loops, entering from the scalar message frame of region D'
with the message-gas bound. -/
theorem ptxPhase2Cut_bound (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn (fun s => ptxPhase2CutG2 s ∧ ptxPhase2FM40 s)
      (spinePlug 11 (spineAt 87 ptxCode) tail) b) :
    TerminatingProgBoundedOn ptxPhase2CutG0
      (spinePlug 10 (spineAt 77 ptxCode) (spinePlug 11 (spineAt 87 ptxCode) tail))
      (K.«htab_new» + ((K.«htab_set» + 1) +
        ((2 ^ 64 + 1) * (K.«htab_set» + 1 + 1) +
          ((2 ^ 64 + 1) * (K.«htab_set» + 1 + 1) + (K.«htab_new» + b + 1)))) + 1) := by
  have hak : TerminatingProgBoundedOn (fun s => ptxPhase2CutG1 s ∧ ptxPhase2FM40 s)
      (.decCall (ofString "ak") .one (ofString "htab_new") [.const (52#64), .const (16#64)]
        (spinePlug 11 (spineAt 87 ptxCode) tail))
      (K.«htab_new» + b + 1) :=
    TerminatingProgBoundedOn.decCall_on h.fb_htab_new (ofString "ak") .one
      [.const (52#64), .const (16#64)] ptxPhase2Cut_ak_callEntry (ptxPhase2Cut_ak_resume h) ht
  have hskip : Hoare (fun s => ptxPhase2CutG1 s ∧ ptxPhase2FM40 s) .skip
      (fun r s => r = none → ptxPhase2CutG1 s ∧ ptxPhase2FM40 s) :=
    Hoare.skip (fun _ hp _ => hp)
  have hskipb : TerminatingProgBoundedOn (fun s => ptxPhase2CutG1 s ∧ ptxPhase2FM40 s)
      .skip 0 :=
    R16Shards.PtxP1.bound_of_clock (P := fun s => ptxPhase2CutG1 s ∧ ptxPhase2FM40 s)
      (fun s => clock_skip s)
  have ha0 : Hoare (fun s => ptxPhase2CutG1 s ∧ ptxPhase2FM40 s)
      (.assign .local (ofString "i") (.const (BitVec.ofNat 64 0)))
      (fun r s => r = none → ptxPhase2CutG1 s ∧ ptxPhase2FM40 s) :=
    ptxPhase2Cut_assign0_hoare ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames
      ptxPhase2Cut_fnames_ne_i
  have ha0b : TerminatingProgBoundedOn (fun s => ptxPhase2CutG1 s ∧ ptxPhase2FM40 s)
      (.assign .local (ofString "i") (.const (BitVec.ofNat 64 0))) 0 :=
    R16Shards.PtxP1.bound_of_clock (P := fun s => ptxPhase2CutG1 s ∧ ptxPhase2FM40 s)
      (fun s => clock_assign s .local (ofString "i") (.const (BitVec.ofNat 64 0)))
  have hcallb : TerminatingProgBoundedOn (fun s => ptxPhase2CutG1 s ∧ ptxPhase2FM40 s)
      (.call (some (none, none)) (ofString "htab_set")
        [.var .local (ofString "aa"), .var .local (ofString "sender"),
          .const (BitVec.ofNat 64 1)])
      (K.«htab_set» + 1) := by
    apply TerminatingProgBoundedOn.call_on h.fb_htab_set none _
    intro F s vs body callee ret hc hp he hl
    exact guestInv_callEntry s callee (worldOK_guestInv s hp.1.2.1.1.1)
  have hwb82 : TerminatingProgBoundedOn (fun s => ptxPhase2CutG1 s ∧ ptxPhase2FM40 s)
      (.while (.cmp .less (.var .local (ofString "i")) (.const (BitVec.ofNat 64 18)))
        (.seq (.call (some (none, none)) (ofString "htab_set")
            [.var .local (ofString "aa"),
             .op .add [.var .global (ofString "precompile_addrs"),
               .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 20)]],
             .const (BitVec.ofNat 64 1)])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))))
      ((2 ^ 64 + 1) * (K.«htab_set» + 1 + 1)) :=
    ptxPhase2Cut_warm_while_bound h ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames
      (.op .add [.var .global (ofString "precompile_addrs"),
        .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 20)]])
      (.const (BitVec.ofNat 64 18)) ptxPhase2Cut_fnames_ne_i
  have hwq82 : Hoare (fun s => ptxPhase2CutG1 s ∧ ptxPhase2FM40 s)
      (.while (.cmp .less (.var .local (ofString "i")) (.const (BitVec.ofNat 64 18)))
        (.seq (.call (some (none, none)) (ofString "htab_set")
            [.var .local (ofString "aa"),
             .op .add [.var .global (ofString "precompile_addrs"),
               .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 20)]],
             .const (BitVec.ofNat 64 1)])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))))
      (fun r s => r = none → ptxPhase2CutG1 s ∧ ptxPhase2FM40 s) :=
    ptxPhase2Cut_warm_while ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames
      (.op .add [.var .global (ofString "precompile_addrs"),
        .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 20)]])
      (.const (BitVec.ofNat 64 18)) ptxPhase2Cut_fnames_ne_i
  have hwb84 : TerminatingProgBoundedOn (fun s => ptxPhase2CutG1 s ∧ ptxPhase2FM40 s)
      (.while (.cmp .less (.var .local (ofString "i"))
          (.op .add [.var .local (ofString "nal"), .const (BitVec.ofNat 64 1)]))
        (.seq (.call (some (none, none)) (ofString "htab_set")
            [.var .local (ofString "aa"),
             .load .one (.op .add [.var .local (ofString "al_addrs"),
               .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]]),
             .const (BitVec.ofNat 64 1)])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))))
      ((2 ^ 64 + 1) * (K.«htab_set» + 1 + 1)) :=
    ptxPhase2Cut_warm_while_bound h ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames
      (.load .one (.op .add [.var .local (ofString "al_addrs"),
        .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]]))
      (.op .add [.var .local (ofString "nal"), .const (BitVec.ofNat 64 1)])
      ptxPhase2Cut_fnames_ne_i
  have hwq84 : Hoare (fun s => ptxPhase2CutG1 s ∧ ptxPhase2FM40 s)
      (.while (.cmp .less (.var .local (ofString "i"))
          (.op .add [.var .local (ofString "nal"), .const (BitVec.ofNat 64 1)]))
        (.seq (.call (some (none, none)) (ofString "htab_set")
            [.var .local (ofString "aa"),
             .load .one (.op .add [.var .local (ofString "al_addrs"),
               .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]]),
             .const (BitVec.ofNat 64 1)])
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))))
      (fun r s => r = none → ptxPhase2CutG1 s ∧ ptxPhase2FM40 s) :=
    ptxPhase2Cut_warm_while ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames
      (.load .one (.op .add [.var .local (ofString "al_addrs"),
        .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]]))
      (.op .add [.var .local (ofString "nal"), .const (BitVec.ofNat 64 1)])
      ptxPhase2Cut_fnames_ne_i
  have hcont : TerminatingProgBoundedOn (fun s => ptxPhase2CutG1 s ∧ ptxPhase2FM40 s)
      (.seq .skip (.seq (.call (some (none, none)) (ofString "htab_set")
          [.var .local (ofString "aa"), .var .local (ofString "sender"),
            .const (BitVec.ofNat 64 1)])
        (.seq .skip (.seq (.assign .local (ofString "i") (.const (BitVec.ofNat 64 0)))
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
                (.seq .skip (.decCall (ofString "ak") .one (ofString "htab_new")
                  [.const (52#64), .const (16#64)]
                  (spinePlug 11 (spineAt 87 ptxCode) tail))))))))))
      ((K.«htab_set» + 1) + ((2 ^ 64 + 1) * (K.«htab_set» + 1 + 1) +
        ((2 ^ 64 + 1) * (K.«htab_set» + 1 + 1) + (K.«htab_new» + b + 1)))) := by
    intro F s hc hp
    simpa only [Nat.zero_add, Nat.add_zero] using
      seq_bound_trans hskipb hskip
        (seq_bound_trans hcallb
          (ptxPhase2Cut_set_q ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames
            (.var .local (ofString "sender")) (.const (BitVec.ofNat 64 1)))
          (seq_bound_trans hskipb hskip
            (seq_bound_trans ha0b ha0
              (seq_bound_trans hwb82 hwq82
                (seq_bound_trans ha0b ha0
                  (seq_bound_trans hwb84 hwq84
                    (seq_bound_trans hskipb hskip hak))))))) s hc hp
  have hmain : TerminatingProgBoundedOn ptxPhase2CutG0
      (spinePlug 10 (spineAt 77 ptxCode) (spinePlug 11 (spineAt 87 ptxCode) tail))
      (K.«htab_new» + ((K.«htab_set» + 1) +
        ((2 ^ 64 + 1) * (K.«htab_set» + 1 + 1) +
          ((2 ^ 64 + 1) * (K.«htab_set» + 1 + 1) + (K.«htab_new» + b + 1)))) + 1) := by
    rw [ptxPhase2Cut_shape (spinePlug 11 (spineAt 87 ptxCode) tail)]
    exact TerminatingProgBoundedOn.decCall_on h.fb_htab_new (ofString "aa") .one
      [.const (20#64), .const (64#64)] ptxPhase2Cut_aa_callEntry
      (ptxPhase2Cut_aa_resume h) hcont
  intro F s hc hp hnt
  obtain ⟨h1, h2⟩ := hmain s hc hp hnt
  exact ⟨by omega, h2⟩

/-! ## The spine split -/

/-- Splitting a plug at an inner spine position. -/
theorem ptxPhase2Cut_spinePlug_split (m : Nat) (k : Nat) (p : ProgHOL 64)
    (tail : ProgHOL 64) :
    spinePlug (m + k) p tail = spinePlug m p (spinePlug k (spineAt m p) tail) := by
  induction m generalizing p tail with
  | zero => simp [spineAt, spinePlug]
  | succ m ih => cases p <;> simp_all [spinePlug, spineAt, Nat.succ_add]

/-- The whole Phase 2 spine (positions 34..98) splits at the frozen region
boundaries: allocation entry, address loop, packed-key loop, the te-suffix
segment, region D', the backing cut, and the segment-B2a replay. -/
theorem ptxPhase2_split_shape (tail : ProgHOL 64) :
    ptxPhase2 tail =
      spinePlug 10 (spineAt 34 ptxCode) (spinePlug 5 (spineAt 44 ptxCode)
        (spinePlug 4 (spineAt 49 ptxCode) (spinePlug 16 (spineAt 53 ptxCode)
          (spinePlug 8 (spineAt 69 ptxCode) (spinePlug 10 (spineAt 77 ptxCode)
            (spinePlug 11 (spineAt 87 ptxCode) tail)))))) := by
  have h0 : ptxPhase2 tail = spinePlug 64 (spineAt 34 ptxCode) tail := rfl
  have h1 : spinePlug 64 (spineAt 34 ptxCode) tail =
      spinePlug 10 (spineAt 34 ptxCode) (spinePlug 54 (spineAt 44 ptxCode) tail) := by
    rw [show spineAt 44 ptxCode = spineAt 10 (spineAt 34 ptxCode) from
      spineAt_add 34 10 ptxCode]
    exact ptxPhase2Cut_spinePlug_split 10 54 (spineAt 34 ptxCode) tail
  have h2 : spinePlug 54 (spineAt 44 ptxCode) tail =
      spinePlug 5 (spineAt 44 ptxCode) (spinePlug 49 (spineAt 49 ptxCode) tail) := by
    rw [show spineAt 49 ptxCode = spineAt 5 (spineAt 44 ptxCode) from
      spineAt_add 44 5 ptxCode]
    exact ptxPhase2Cut_spinePlug_split 5 49 (spineAt 44 ptxCode) tail
  have h3 : spinePlug 49 (spineAt 49 ptxCode) tail =
      spinePlug 4 (spineAt 49 ptxCode) (spinePlug 45 (spineAt 53 ptxCode) tail) := by
    rw [show spineAt 53 ptxCode = spineAt 4 (spineAt 49 ptxCode) from
      spineAt_add 49 4 ptxCode]
    exact ptxPhase2Cut_spinePlug_split 4 45 (spineAt 49 ptxCode) tail
  have h4 : spinePlug 45 (spineAt 53 ptxCode) tail =
      spinePlug 16 (spineAt 53 ptxCode) (spinePlug 29 (spineAt 69 ptxCode) tail) := by
    rw [show spineAt 69 ptxCode = spineAt 16 (spineAt 53 ptxCode) from
      spineAt_add 53 16 ptxCode]
    exact ptxPhase2Cut_spinePlug_split 16 29 (spineAt 53 ptxCode) tail
  have h5 : spinePlug 29 (spineAt 69 ptxCode) tail =
      spinePlug 8 (spineAt 69 ptxCode) (spinePlug 21 (spineAt 77 ptxCode) tail) := by
    rw [show spineAt 77 ptxCode = spineAt 8 (spineAt 69 ptxCode) from
      spineAt_add 69 8 ptxCode]
    exact ptxPhase2Cut_spinePlug_split 8 21 (spineAt 69 ptxCode) tail
  have h6 : spinePlug 21 (spineAt 77 ptxCode) tail =
      spinePlug 10 (spineAt 77 ptxCode) (spinePlug 11 (spineAt 87 ptxCode) tail) := by
    rw [show spineAt 87 ptxCode = spineAt 10 (spineAt 77 ptxCode) from
      spineAt_add 77 10 ptxCode]
    exact ptxPhase2Cut_spinePlug_split 10 11 (spineAt 77 ptxCode) tail
  rw [h0, h1, h2, h3, h4, h5, h6]

/-! ## The packed-CR adapter -/

/-- The region-D2 packed-key replay entered from the region-E guard: the
per-state entry provides the retained family and scalar witnesses, so the
four-conjunct region-D2 conclusion can be read at the two-conjunct address
loop guard. The budget is region D2's own conclusion budget with `b`
abstract. -/
theorem ptxPhase2Cut_D2_adapter (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (hE : TerminatingProgBoundedOn ptxPhase2EInv tail b) :
    TerminatingProgBoundedOn (fun s => PtxAddressCountExit s ∧ PtxPhase2X s)
      (spinePlug 4 (spineAt 49 ptxCode) tail)
      (K.«alloc» + ((2 ^ 63 + 1) * ((2 ^ 63 + 1) * ((K.«memcpy» + 1) + (K.«memcpy» + 1) + 1) + 1) + b) + 1) := by
  intro F s hc hp
  exact ptxPhase2D_packedCR_bound (contents := phase2_saved_word s)
    (E := locN s "te") (T := locN s "tx") (A := locN s "al_addrs") (N := locN s "nal")
    h hE s hc ⟨hp.1, hp.2, ptxPhase2D_fam_entry hp.1, ptxPhase2D_scal_entry hp.1⟩

/-! ## The Phase 2 backing cut -/

/-- The b2a-region budget over a tail budget `b`. -/
def ptxPhase2CutB_b2a (b : Nat) : Nat :=
  (2 ^ 64 + 1) * (K.«htab_set» + 1 + 1) +
    (K.«alloc» + (Nat.max (K.«get_account» + (K.«alloc» +
      (K.«compute_contract_address» + 1 + 0) + 1) + 1) 0 +
      (K.«htab_set» + 1 + b)) + 1)

/-- The aa-region budget over a tail budget `b`. -/
def ptxPhase2CutB_aa (b : Nat) : Nat :=
  K.«htab_new» + ((K.«htab_set» + 1) +
    ((2 ^ 64 + 1) * (K.«htab_set» + 1 + 1) +
      ((2 ^ 64 + 1) * (K.«htab_set» + 1 + 1) + (K.«htab_new» + b + 1)))) + 1

/-- The message-store region budget over a tail budget `b`. -/
def ptxPhase2CutB_f (b : Nat) : Nat := K.«msg_new» + b + 1

/-- The e-header region budget over a tail budget `b`. -/
def ptxPhase2CutB_e (b : Nat) : Nat :=
  (K.«tx_is_blob» + 1) + (K.«tx_is_setcode» + 1) + (K.«alloc» + 1) +
    (K.«keccak256» + 1) + b

/-- The packed-key region budget over a tail budget `b`. -/
def ptxPhase2CutB_d2 (b : Nat) : Nat :=
  K.«alloc» + ((2 ^ 63 + 1) * ((2 ^ 63 + 1) * ((K.«memcpy» + 1) + (K.«memcpy» + 1) + 1) + 1) +
    b) + 1

/-- The address-loop region budget over a tail budget `b`. -/
def ptxPhase2CutB_b (b : Nat) : Nat := K.alloc + ((2 ^ 63 + 1) + b) + 1

/-- The allocation-entry region budget over a tail budget `b`. -/
def ptxPhase2CutB_pre (b : Nat) : Nat :=
  K.te_new + (K.tx_has_access_list + b + 1) + 1

/-- The composed region-budget tower over `b` fits inside the Phase 2 budget. -/
theorem ptxPhase2CutB_tower_le (b : Nat) :
    ptxPhase2CutB_pre (ptxPhase2CutB_b (ptxPhase2CutB_d2 (ptxPhase2CutB_e
      (ptxPhase2CutB_f (ptxPhase2CutB_aa (ptxPhase2CutB_b2a b)))))) ≤ ptxCost2 + b := by
  unfold ptxPhase2CutB_b2a ptxPhase2CutB_aa ptxPhase2CutB_f ptxPhase2CutB_e
    ptxPhase2CutB_d2 ptxPhase2CutB_b ptxPhase2CutB_pre ptxCost2
  simp only [Nat.max_zero]
  omega



/-- **The Phase 2 backing cut** (spine 34..98): the composed scope of the
frozen region replays and the backing cut above, entering from
`PtxValidatedBackingStrong` and handing the tail guard to the Phase 3 cut,
within the `ptxCost2` budget. -/
theorem ptxPhase2_backing_cut (h : PtxCallees) : PtxPhase2BackingCut := by
  intro tail b ht
  have hb2a : TerminatingProgBoundedOn (fun s => ptxPhase2CutG2 s ∧ ptxPhase2FM40 s)
      (spinePlug 11 (spineAt 87 ptxCode) tail) (ptxPhase2CutB_b2a b) := by
    intro F s hc hp
    exact phase2_b2a_bound h ptxPhase2FDegBuf ptxPhase2FDegCont (locN s "aa")
      (locN s "ak") ht s hc (ptxPhase2Cut_b2a_bridge hp)
  have hcut : TerminatingProgBoundedOn ptxPhase2CutG0
      (spinePlug 10 (spineAt 77 ptxCode) (spinePlug 11 (spineAt 87 ptxCode) tail))
      (ptxPhase2CutB_aa (ptxPhase2CutB_b2a b)) :=
    ptxPhase2Cut_bound h hb2a
  have hF : TerminatingProgBoundedOn ptxPhase2FDPrime
      (spinePlug 8 (spineAt 69 ptxCode)
        (spinePlug 10 (spineAt 77 ptxCode) (spinePlug 11 (spineAt 87 ptxCode) tail)))
      (ptxPhase2CutB_f (ptxPhase2CutB_aa (ptxPhase2CutB_b2a b))) :=
    ptxPhase2F_bound h hcut
  have hE : TerminatingProgBoundedOn ptxPhase2EInv
      (spinePlug 16 (spineAt 53 ptxCode)
        (spinePlug 8 (spineAt 69 ptxCode)
          (spinePlug 10 (spineAt 77 ptxCode) (spinePlug 11 (spineAt 87 ptxCode) tail))))
      (ptxPhase2CutB_e (ptxPhase2CutB_f (ptxPhase2CutB_aa (ptxPhase2CutB_b2a b)))) :=
    ptxPhase2E_bound h hF
  have hD2 : TerminatingProgBoundedOn (fun s => PtxAddressCountExit s ∧ PtxPhase2X s)
      (spinePlug 4 (spineAt 49 ptxCode)
        (spinePlug 16 (spineAt 53 ptxCode)
          (spinePlug 8 (spineAt 69 ptxCode)
            (spinePlug 10 (spineAt 77 ptxCode) (spinePlug 11 (spineAt 87 ptxCode) tail)))))
      (ptxPhase2CutB_d2
        (ptxPhase2CutB_e (ptxPhase2CutB_f (ptxPhase2CutB_aa (ptxPhase2CutB_b2a b))))) :=
    ptxPhase2Cut_D2_adapter h hE
  have hB : TerminatingProgBoundedOn (fun s => PtxAccessCountReady s ∧ PtxPhase2X s)
      (spinePlug 5 (spineAt 44 ptxCode)
        (spinePlug 4 (spineAt 49 ptxCode)
          (spinePlug 16 (spineAt 53 ptxCode)
            (spinePlug 8 (spineAt 69 ptxCode)
              (spinePlug 10 (spineAt 77 ptxCode)
                (spinePlug 11 (spineAt 87 ptxCode) tail))))))
      (ptxPhase2CutB_b (ptxPhase2CutB_d2
        (ptxPhase2CutB_e (ptxPhase2CutB_f (ptxPhase2CutB_aa (ptxPhase2CutB_b2a b)))))) :=
    ptxPhase2B_addressLoopX_bound h hD2
  have hPre : TerminatingProgBoundedOn (fun s => PtxValidatedStrong s ∧ PtxPhase2X s)
      (spinePlug 10 (spineAt 34 ptxCode)
        (spinePlug 5 (spineAt 44 ptxCode)
          (spinePlug 4 (spineAt 49 ptxCode)
            (spinePlug 16 (spineAt 53 ptxCode)
              (spinePlug 8 (spineAt 69 ptxCode)
                (spinePlug 10 (spineAt 77 ptxCode)
                  (spinePlug 11 (spineAt 87 ptxCode) tail)))))))
      (ptxPhase2CutB_pre (ptxPhase2CutB_b (ptxPhase2CutB_d2
        (ptxPhase2CutB_e (ptxPhase2CutB_f (ptxPhase2CutB_aa (ptxPhase2CutB_b2a b))))))) :=
    ptxPhase2_allocationEntryX_bound h hB
  have hmono : TerminatingProgBoundedOn PtxValidatedBackingStrong
      (spinePlug 10 (spineAt 34 ptxCode)
        (spinePlug 5 (spineAt 44 ptxCode)
          (spinePlug 4 (spineAt 49 ptxCode)
            (spinePlug 16 (spineAt 53 ptxCode)
              (spinePlug 8 (spineAt 69 ptxCode)
                (spinePlug 10 (spineAt 77 ptxCode)
                  (spinePlug 11 (spineAt 87 ptxCode) tail)))))))
      (ptxPhase2CutB_pre (ptxPhase2CutB_b (ptxPhase2CutB_d2
        (ptxPhase2CutB_e (ptxPhase2CutB_f (ptxPhase2CutB_aa (ptxPhase2CutB_b2a b))))))) :=
    R16Shards.PtxP1.bound_mono hPre (fun s hs => ⟨hs.1, ptxPhase2X_of_entry hs⟩)
  rw [ptxPhase2_split_shape tail]
  intro F s hc hp hnt
  obtain ⟨h1, h2⟩ := hmono s hc hp hnt
  refine ⟨?_, h2⟩
  have hle := ptxPhase2CutB_tower_le b
  omega

/-- The full R16k integration obligation with both backing cuts
discharged: the Phase 1 cut and the Phase 2 cut above compose into
`gbody_process_transaction_backing_strong_pmc_of_cuts_h4closed`. -/
theorem gbody_process_transaction_backing_strong_closed (h : PtxCallees)
    (hwk : PtxP34.PmcStrong) (hkeep : PmcBackingStrong)
    (hent : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      TxReadyBackingStrong s → TxReadyFullStrong s) :
    TerminatingFunBoundedOn TxReadyBackingStrong (ofString "process_transaction")
      K.«process_transaction» :=
  gbody_process_transaction_backing_strong_pmc_of_cuts_h4closed h hwk hkeep
    (ptxPhase1_backing_cut h hent) (ptxPhase2_backing_cut h)

end InitECandidate.Solver.Wave8GuestInv.R13Shards
