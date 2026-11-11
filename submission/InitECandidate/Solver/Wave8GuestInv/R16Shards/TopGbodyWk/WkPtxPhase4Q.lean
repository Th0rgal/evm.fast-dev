import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4P
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M25.rt_alloc

set_option Elab.async false
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
open InitECandidate.Solver.Wave8GuestInv.EvmBase (stdKeep)
open InitECandidate.Solver.Wave8GuestInv.R13Shards
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
open InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs

/-! # Phase 4Q: instructions 31-39 (the stable-logs segment, g8)

`dec stable_log_cap := nl; ite (cap = 0) (cap := 1) skip; decCall stable_logs :=
lst_new [8, cap]; store (stable_logs+8) := nl; dec stable_lp := load
[stable_logs+0]; assign i := 0; while (i < nl) (store (stable_lp + 8*i) :=
load [lp + 8*i]; i := i+1); decCall rl := lst_push [bo+72's data, 8];
store rl := stable_logs`.

The `lst_push` on the receipts list `bo+72` relocates or keeps the backing
array; the post-state's nonzero receipts backing (`PtxRelBase.rcpt_backing`)
is re-established by replaying the callee body (`lst_push` either retains the
old nonzero data word or installs a fresh `alloc` result).  The chain below
clones the `PtxCallees`-dependent lemmas of `PtxPhase34R11` with the proven
`M25.rt_alloc` in place of the kernel hypothesis `h.rt_alloc`. -/

/-- The allocator return contract supplies the nonzero word needed by the
concrete growth stores (clone of `alloc_return_nonzero`, over the proven
`rt_alloc`). -/
theorem p4Q_alloc_return_nonzero {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hA : ArenaReady (callEntryStateHOLFinite s callee))
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "alloc") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∃ np : BitVec 64, v = .val (.word np) ∧ np.toNat ≠ 0 ∧ ArenaReady post := by
  have ha := PtxP1.funSpec_at_lookup InitECandidate.Solver.Wave8Contracts.M25.rt_alloc s hc vs body callee ret hl hA
    (by rw [hr]; simp)
  rw [hr] at ha
  obtain ⟨np, hv, hpost, _, hf⟩ := ha v rfl
  exact ⟨np, hv, PtxP34.fresh_backing_nonzero hA.2 hf, hpost⟩

/-- The complete allocating branch establishes nonzero backing, including
copying and restoration of the temporary `np` local (clone over `rt_alloc`). -/
theorem p4Q_lst_push_alloc_branch_fall {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (l cap : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hcap : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (hr : evaluateHOLFiniteState s
      (.decCall (ofString "np") .one (ofString "alloc")
        [.panop .mul [.panop .mul
          [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]]
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.var .local (ofString "np"),
             .load .one (.op .add [.var .local (ofString "l"), .const 0]),
             .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
          (.seq
            (.store (.op .add [.var .local (ofString "l"), .const 0])
              (.var .local (ofString "np")))
            (.store (.op .add [.var .local (ofString "l"), .const 16])
              (.panop .mul [.var .local (ofString "cap"), .const 2]))))) = (none, post)) :
    memW post l.toNat ≠ 0 := by
  obtain ⟨vs, body, callee, ret, rv, allocated, done, hlookup, hrun, hcont, hmem, _⟩ :=
    PtxP34.dec_call_fall_inv hr
  have hentry : ArenaReady (callEntryStateHOLFinite s callee) :=
    (arenaReady_with_locals s callee (s.clock - 1)).2 hA
  obtain ⟨np, rfl, hnz, hpost⟩ :=
    p4Q_alloc_return_nonzero s vs body callee ret rv allocated hc hentry hlookup hrun
  have hb := PtxP34.lst_push_copy_stores_fall
    (setVarHOLFinite (ofString "np") (.val (.word np)) { allocated with locals := s.locals })
    done l cap np hpost.1.code
    (by simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "np" ≠ ofString "l" by decide] using hl)
    (by simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "np" ≠ ofString "cap" by decide] using hcap)
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hnz hcont
  simpa only [memW, hmem] using hb

/-- Both outcomes of the capacity check preserve nonzero backing. The growth
case obtains it from allocation; the skip case retains the entry fact
(clone over `rt_alloc`). -/
theorem p4Q_lst_push_capacity_branch_fall {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (l cap : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hcap : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (hb : memW s l.toNat ≠ 0)
    (cond : ExpHOL 64)
    (hr : evaluateHOLFiniteState s
      (.ite cond
        (.decCall (ofString "np") .one (ofString "alloc")
          [.panop .mul [.panop .mul
            [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]]
          (.seq
            (.call (some (none, none)) (ofString "memcpy")
              [.var .local (ofString "np"),
               .load .one (.op .add [.var .local (ofString "l"), .const 0]),
               .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
            (.seq
              (.store (.op .add [.var .local (ofString "l"), .const 0])
                (.var .local (ofString "np")))
              (.store (.op .add [.var .local (ofString "l"), .const 16])
                (.panop .mul [.var .local (ofString "cap"), .const 2]))))) .skip) =
      (none, post)) : memW post l.toNat ≠ 0 ∧
        (∀ k, k ≠ ofString "np" → post.locals.lookup k = s.locals.lookup k) := by
  rcases PtxP34.ite_skip_fall_inv hr with hg | rfl
  · exact ⟨p4Q_lst_push_alloc_branch_fall s post l cap hc hA hl hcap hg,
      fun k hk => PtxP34.lst_push_alloc_branch_lookup s post _ hg k hk⟩
  · exact ⟨hb, fun _ _ => rfl⟩

/-- The complete returned push suffix forces the capacity branch to fall
through, then preserves its nonzero data word through the common tail
(clone over `rt_alloc`). -/
theorem p4Q_lst_push_capacity_tail_returned {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (l n cap : BitVec 64) (v : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hcap : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (hb : memW s l.toNat ≠ 0)
    (hr : evaluateHOLFiniteState s
      (.seq
        (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
          (.decCall (ofString "np") .one (ofString "alloc")
            [.panop .mul [.panop .mul
              [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]]
            (.seq
              (.call (some (none, none)) (ofString "memcpy")
                [.var .local (ofString "np"),
                 .load .one (.op .add [.var .local (ofString "l"), .const 0]),
                 .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
              (.seq
                (.store (.op .add [.var .local (ofString "l"), .const 0])
                  (.var .local (ofString "np")))
                (.store (.op .add [.var .local (ofString "l"), .const 16])
                  (.panop .mul [.var .local (ofString "cap"), .const 2]))))) .skip)
        (.seq (.store (.op .add [.var .local (ofString "l"), .const 8])
          (.op .add [.var .local (ofString "n"), .const 1]))
          (.return (.op .add
            [.load .one (.op .add [.var .local (ofString "l"), .const 0]),
             .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]])))) =
      (some (.returned v), post)) : memW post l.toNat ≠ 0 := by
  obtain ⟨mid, hm, _⟩ := PtxP34.seq_returned_of_not_returned (by
    apply PtxP34.ite_not_returned
    · apply PtxP34.dec_call_not_returned
      intro a
      apply PtxP34.seq_not_returned
      · exact PtxP34.ignored_call_not_returned _ _ _ _
      · intro b
        apply PtxP34.seq_not_returned
        · exact PtxP34.store_not_returned _ _ _ _
        · intro c; exact PtxP34.store_not_returned _ _ _ _
    · simp [evaluateHOLFiniteState_skip]) hr
  obtain ⟨hbmid, hlocals⟩ := p4Q_lst_push_capacity_branch_fall s mid l cap hc hA hl hcap hb _ hm
  exact PtxP34.lst_push_branch_to_tail s mid post l n v _ hc hm hbmid
    (hlocals _ (by decide)) (hlocals _ (by decide)) hl hn hr

/-- The entire concrete push body preserves a nonzero backing word. The two
header reads are exposed from the returned execution, without extra evaluation
or branch-selection premises (clone over `rt_alloc`). -/
theorem p4Q_lst_push_body_backing_nonzero {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (l : BitVec 64) (v : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hb : memW s l.toNat ≠ 0)
    (hr : evaluateHOLFiniteState s (sourceFunctionEntry Guest.Software.guestFn_lst_push).2.2.1 =
      (some (.returned v), post)) : memW post l.toNat ≠ 0 := by
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_lst_push,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hr
  obtain ⟨n, mid, hr, hm⟩ := PtxP34.dec_word_returned_inv hr
  obtain ⟨cap, last, hr, hm'⟩ := PtxP34.dec_word_returned_inv hr
  have hs := p4Q_lst_push_capacity_tail_returned
    (setVarHOLFinite (ofString "cap") (.val (.word cap))
      (setVarHOLFinite (ofString "n") (.val (.word n)) s)) last l n cap v hc
    ((arenaReady_with_locals s _ s.clock).mpr hA) (by
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl,
        show ofString "cap" ≠ ofString "l" by decide,
        show ofString "n" ≠ ofString "l" by decide])
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "cap" ≠ ofString "n" by decide])
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hb hr
  simpa only [memW, hm, hm'] using hs


/-! ### The `lst_new` decCall engine (instruction 32)

`decCall stable_logs := lst_new [8, stable_log_cap]`.  The callee allocates a
fresh list header (24 bytes) plus an array of `capw` 8-byte slots above the
caller's `heap_ptr` and returns the header pointer.  Because `stable_logs` is
none of the locals `P4Data` reads, the invariant transports across the
`setVar` directly. -/

theorem p4Q_decCall_lst_new {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out)
    (hc : s.code = originalRuntimeCode)
    (capw : BitVec 64)
    (hcap_local : s.locals.lookup (ofString "stable_log_cap") = some (.val (.word capw)))
    (hcap_pos : 1 ≤ capw.toNat)
    (hmul_lt : 8 * capw.toNat < 2 ^ 64)
    (tail : ProgHOL 64)
    (htail : ∀ (lw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      lw.toNat = globN s "heap_ptr" →
      lw.toNat % 8 = 0 →
      lw.toNat ≠ 0 →
      memW mid lw.toNat = lw.toNat + 24 →
      memW mid (lw.toNat + 8) = 0 →
      memW mid (lw.toNat + 16) = capw.toNat →
      globN mid "heap_ptr" = lw.toNat + 24 + 8 * capw.toNat →
      globN s "heap_ptr" < globN mid "heap_ptr" →
      ArenaReady mid →
      globN mid "scratch_ptr" = globN s "scratch_ptr" →
      globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" →
      LstOK mid lw.toNat →
      lstObjects mid lw.toNat 8 = [(lw.toNat, 24), (lw.toNat + 24, 8 * capw.toNat)] →
      Disj (lw.toNat, 24) (lw.toNat + 24, 8 * capw.toNat) →
      (∀ i ∈ lstObjects mid lw.toNat 8,
        Allocated mid i ∧ WordsOK mid i ∧
        Inside i (globN s "heap_ptr") (globN mid "heap_ptr")) →
      FrameOutside s mid [(globN s "scratch_ptr", 0)]
        (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") →
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = mid.globals.lookup k) →
      (∀ S Nd, WorldTypedWith s S Nd →
        ∃ S2 N2, (∀ t ∈ S, t ∈ S2) ∧ WorldTypedWith mid S2 N2 ∧
          OwnedGrows s mid (worldOwned s S Nd) (worldOwned mid S2 N2) ∧
          FrameOutside s mid (worldOwned s S Nd ++ [freeGap s]) (heapFree s) ∧
          IvlsDisj [(lw.toNat, 24), (memW mid lw.toNat, 8 * capw.toNat)]
            (worldOwned mid S2 N2)) →
      mid.locals.lookup (ofString "stable_logs") = some (.val (.word lw)) →
      (∀ y, y ≠ ofString "stable_logs" → mid.locals.lookup y = s.locals.lookup y) →
      P4Data entry mid s_pmc w_out →
      mid.code = originalRuntimeCode →
      PtxRelRunStrong entry tail mid) :
    PtxRelRunStrong entry
      (.decCall (ofString "stable_logs") .one (ofString "lst_new")
        [(.const 0x0000000000000008#64), (.var .local (ofString "stable_log_cap"))] tail) s := by
  intro hres
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hres ⊢
  have harg : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [(.const 0x0000000000000008#64), (.var .local (ofString "stable_log_cap"))] =
      some [.val (.word 0x0000000000000008#64), .val (.word capw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hcap_local]
  rw [harg] at hres ⊢
  dsimp only at hres ⊢
  have hlk := pan_two_word_lookup s.code.lookup (ofString "lst_new")
    (ofString "esz") (ofString "cap") (sourceFnBody Guest.Software.guestFn_lst_new)
    0x0000000000000008#64 capw
    (by decide) (by rw [hc]; exact WkBal.lookup_lst_new_wk)
  rw [hlk] at hres ⊢
  dsimp only at hres ⊢
  by_cases hcz : s.clock = 0
  · simp only [hcz, ↓reduceIte] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [hcz, ↓reduceIte] at hres ⊢
    set cmap := (HolFiniteMapExact.empty.update
      (ofString "esz", ValueHOL.val (.word 0x0000000000000008#64))).update
      (ofString "cap", ValueHOL.val (.word capw)) with hcmap_def
    have hAR_ent : ArenaReady (callEntryStateHOLFinite s cmap) :=
      (arenaReady_with_locals s cmap (s.clock - 1)).2 h.base.world.1
    have hent_e : (callEntryStateHOLFinite s cmap).locals.lookup (ofString "esz") =
        some (.val (.word 0x0000000000000008#64)) := by
      simp [callEntryStateHOLFinite, hcmap_def, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "cap" ≠ ofString "esz" by decide]
    have hent_c : (callEntryStateHOLFinite s cmap).locals.lookup (ofString "cap") =
        some (.val (.word capw)) := by
      simp [callEntryStateHOLFinite, hcmap_def, HolFiniteMapExact.lookup_update, FUPDATE]
    have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
      (callEntryStateHOLFinite s cmap) (sourceFnBody Guest.Software.guestFn_lst_new)).1
    rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_lst_new) with ⟨rb, sb⟩
    have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_lst_new) = (rb, sb) := hb
    rw [hb] at hmeta
    simp only [hb] at hres ⊢
    cases rb with
    | none => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    | some cr =>
      cases cr with
      | timeOut | error | «break» | «continue» | finalFfi _ =>
        exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
      | exception eid ev =>
        dsimp only at hres ⊢
        have hspec := PtxP1.funSpec_at_lookup R13Wk06b.«wk_lst_new» s hc
          [.val (.word 0x0000000000000008#64), .val (.word capw)]
          (sourceFnBody Guest.Software.guestFn_lst_new)
          cmap .one hlk (PtxP1.worldOK_callEntry h.base.world cmap)
          (by rw [hb']; simp)
        rw [hb'] at hspec
        have hstep0 := hspec hres
        have hstep_s : WorldStep (bufRegions ([] : BufList)) ["heap_ptr"] stdKeep NoExtra s
            (some (.exception eid ev)) sb := by
          refine worldStep_congr_R ?_
            (R13Shards.worldStep_with_locals hstep0 s.locals s.clock)
          rfl
        have hex := ptxRelBase_exception_worldStep h.base
          (by intro p hp; cases hp) (by intro p hp; cases hp)
          (by intro g hg
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
              subst hg; decide)
          ptxKeepSub_stdKeep hstep_s
        exact ptxWorldStep_strong_with_locals_right' .empty sb.clock hex
      | returned v =>
        dsimp only at hres ⊢
        have hprops := WkBal.lst_new_heap_props (callEntryStateHOLFinite s cmap)
          0x0000000000000008#64 capw
          hAR_ent (by decide)
          (by rw [show (0x0000000000000008#64 : BitVec 64).toNat = 8 from rfl]; exact hmul_lt)
          (by rw [show (0x0000000000000008#64 : BitVec 64).toNat = 8 from rfl]; exact Nat.mul_mod_right 8 capw.toNat)
          hcap_pos hent_e hent_c v (congrArg Prod.fst hb')
        have hrun_snd : (evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
            (sourceFnBody Guest.Software.guestFn_lst_new)).2 = sb := congrArg Prod.snd hb'
        dsimp only at hprops
        rw [hrun_snd] at hprops
        obtain ⟨lw, rfl, hlw_eq, hlw_al, hlw_nz, hm0, hm8, hm16, hhp_sb, hhp_lt, hAsb, _,
          hsp_sb, hfmp_sb, hlst_sb, hobjs_sb, hdisj_sb, hobjs_props, hfr_sb, hgl_sb⟩ := hprops
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word lw) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word lw) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        simp only [hsh, ↓reduceIte] at hres ⊢
        have hspec := PtxP1.funSpec_at_lookup R13Wk06b.«wk_lst_new» s hc
          [.val (.word 0x0000000000000008#64), .val (.word capw)]
          (sourceFnBody Guest.Software.guestFn_lst_new)
          cmap .one hlk (PtxP1.worldOK_callEntry h.base.world cmap)
          (by rw [hb']; simp)
        rw [hb'] at hspec
        have hstep_ent := hspec (Or.inl ⟨(.val (.word lw) : ValueHOL 64), rfl⟩)
        have hstep_s : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra
            s (some (.returned (.val (.word lw)))) sb :=
          R13Shards.worldStep_with_locals hstep_ent s.locals s.clock
        have hsp : globN sb "scratch_ptr" ≤ globN s "scratch_ptr" := Nat.le_of_eq hsp_sb
        have hgrow_le : globN s "heap_ptr" ≤ globN sb "heap_ptr" := Nat.le_of_lt hhp_lt
        -- the invariant transport across the callee
        obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, _, hbo40_nz_e, hbo72_nz_e,
          S_e, Nd_e, hWT_e, _⟩ := h.base.ready_entry
        have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
          rw [ptxRegions_eq_bufRegions]
          exact validBufList_disj validBufList_ptxBufs hWT_e
        obtain ⟨logs, hll, hl_ok, hl_dj, hty⟩ := h.logs_facts
        obtain ⟨S_pmc, Nd_pmc, S_cur, Nd_cur, hty1, hty2, hWT_s, hty4, hty5, hty6, hty7, hty8,
          hty9⟩ := hty S_e Nd_e hWT_e hD_e
        have hunhit : PtxBlockOutUnhit s sb :=
          ptxBlockOutUnhit_of_fresh_heap hWT_s h.base.world.1 hAsb hfr_sb
        have hcells : PtxBoCells true entry s sb :=
          ptxBoCells_of_blockOutUnhit h.base (B := ([] : BufList)) (gw := ["heap_ptr"])
            (keep := stdKeep)
            (fun p hp => absurd hp (by simp))
            (fun p hp => absurd hp (by simp))
            (fun g hg => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
              subst hg
              decide)
            ptxKeepSub_stdKeep
            (by decide)
            (Or.inr (by simp [stdKeep]))
            hstep_s hunhit
        have hdata_sb : P4Data entry { sb with locals := s.locals, clock := sb.clock } s_pmc w_out :=
          p4Data_step_of_worldStep_cells h (B := ([] : BufList)) (gw := ["heap_ptr"])
            (keep := stdKeep)
            (fun p hp => absurd hp (by simp))
            (fun p hp => absurd hp (by simp))
            (fun g hg => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
              subst hg
              decide)
            (by decide) (by decide) ptxKeepSub_stdKeep
            hstep_s hsp hcells
        set mid := setVarHOLFinite (ofString "stable_logs") (.val (.word lw))
            { sb with locals := s.locals } with hmid_def
        have hdata_mid : P4Data entry mid s_pmc w_out :=
          p4Data_setVar (by decide) (by decide) (by decide) (by decide)
            (by intro name hn
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
                rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
            hdata_sb
        have hloc_name : mid.locals.lookup (ofString "stable_logs") = some (.val (.word lw)) := by
          rw [hmid_def]
          simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
        have hloc_rest : ∀ y, y ≠ ofString "stable_logs" →
            mid.locals.lookup y = s.locals.lookup y := by
          intro y hy
          rw [hmid_def]
          simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm hy]
        have hAR_mid : ArenaReady mid := (arenaReady_with_locals sb _ sb.clock).2 hAsb
        have hm0' : memW mid lw.toNat = lw.toNat + 24 := hm0
        have hm8' : memW mid (lw.toNat + 8) = 0 := hm8
        have hm16' : memW mid (lw.toNat + 16) = capw.toNat := hm16
        have hhp_mid : globN mid "heap_ptr" = lw.toNat + 24 + 8 * capw.toNat := hhp_sb
        have hlst_mid : LstOK mid lw.toNat := hlst_sb
        have hobjs_mid : lstObjects mid lw.toNat 8 =
            [(lw.toNat, 24), (lw.toNat + 24, 8 * capw.toNat)] := hobjs_sb
        have hdisj_mid : Disj (lw.toNat, 24) (lw.toNat + 24, 8 * capw.toNat) := hdisj_sb
        have hobjs_props' : ∀ i ∈ lstObjects mid lw.toNat 8,
            Allocated mid i ∧ WordsOK mid i ∧
            Inside i (globN s "heap_ptr") (globN mid "heap_ptr") := hobjs_props
        have hfr_mid : FrameOutside s mid [(globN s "scratch_ptr", 0)]
            (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") := hfr_sb
        have hgl_mid : ∀ k : MlS, k ≠ ofString "heap_ptr" →
            s.globals.lookup k = mid.globals.lookup k := hgl_sb
        have htyPr : ∀ S Nd, WorldTypedWith s S Nd →
            ∃ S2 N2, (∀ t ∈ S, t ∈ S2) ∧ WorldTypedWith mid S2 N2 ∧
              OwnedGrows s mid (worldOwned s S Nd) (worldOwned mid S2 N2) ∧
              FrameOutside s mid (worldOwned s S Nd ++ [freeGap s]) (heapFree s) ∧
              IvlsDisj [(lw.toNat, 24), (memW mid lw.toNat, 8 * capw.toNat)]
                (worldOwned mid S2 N2) := by
          intro S Nd hWT
          have hWT_ent' : WorldTypedWith (callEntryStateHOLFinite s cmap) S Nd :=
            (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals s cmap (s.clock - 1)
              S Nd).2 hWT
          obtain ⟨S2, N2, hsub, hWT_sb2, hOG2, hFO2, hQ2⟩ :=
            hstep_ent.2.2.2.2 S Nd hWT_ent' (by intro o ho; exact absurd ho (by simp))
          have hC : locN (callEntryStateHOLFinite s cmap) "esz" *
              locN (callEntryStateHOLFinite s cmap) "cap" < 2 ^ 64 := by
            simp only [locN, hent_e, hent_c]
            exact hmul_lt
          obtain ⟨w, hw, hdisj_w⟩ := hQ2 hC (.val (.word lw)) rfl
          have hwl2 : w = lw := by
            injection hw with h1
            injection h1 with h2
            exact h2.symm
          rw [hwl2] at hdisj_w
          refine ⟨S2, N2, hsub, ?_, hOG2, ?_, ?_⟩
          · exact (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals sb mid.locals
              mid.clock S2 N2).2 hWT_sb2
          · have hwo : worldOwned (callEntryStateHOLFinite s cmap) S Nd
                = worldOwned s S Nd := rfl
            have hfg : freeGap (callEntryStateHOLFinite s cmap) = freeGap s := rfl
            have hhf : heapFree (callEntryStateHOLFinite s cmap) = heapFree s := rfl
            intro a hkeep hfresh
            refine hFO2 a (fun i hi => ?_) (by rw [hhf]; exact hfresh)
            rcases List.mem_append.mp hi with hi | hi
            · rcases List.mem_append.mp hi with hi | hi
              · exact hkeep i (List.mem_append_left _ (by rw [← hwo]; exact hi))
              · exact absurd hi (by simp)
            · exact hkeep i (List.mem_append_right _ (by rw [← hfg]; exact hi))
          · simp only [locN, hent_e, hent_c] at hdisj_w
            exact hdisj_w
        have hsp_mid : globN mid "scratch_ptr" = globN s "scratch_ptr" := hsp_sb
        have hfmp_mid : globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" := hfmp_sb
        have hcode_mid : mid.code = originalRuntimeCode := (hmeta.trans hc)
        exact ptxWorldStep_strong_with_locals_right'
          (HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState mid tail).2.locals
            (ofString "stable_logs", s.locals.lookup (ofString "stable_logs")))
          (evaluateHOLFiniteState mid tail).2.clock
          (htail lw mid hlw_eq hlw_al hlw_nz hm0' hm8' hm16' hhp_mid hhp_lt hAR_mid
            hsp_mid hfmp_mid hlst_mid hobjs_mid hdisj_mid hobjs_props' hfr_mid hgl_mid
            htyPr hloc_name hloc_rest hdata_mid hcode_mid hres)


/-! ## The g8 spine: witness-threaded chain -/

/-- The typing chain carried through the g8 spine.  For every entry typing
`S0 Nd0` it exposes MY OWN witnesses `S N` (with the pmc witnesses `Sp Np`)
satisfying every `PtxAfterPhase4Data.typing` conjunct except `PtxRetSlices`,
plus the fresh-list disjunction and the out-list ownership.  Unlike
`P4Data`'s typing, the witnesses here are threaded explicitly through each
step, so the disjunctive facts always refer to reachable witnesses. -/
def p4Q8Chain {F : Type} (entry s_pmc : PanSemStateFiniteExact 64 F)
    (w_out lw capw : BitVec 64) (t : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ S0 Nd0, WorldTypedWith entry S0 Nd0 →
    IvlsDisj (ptxRegions entry) (worldTypedIvls entry S0 Nd0) →
    ∃ S N Sp Np,
      (∀ t' ∈ S0, t' ∈ S) ∧
      WorldTypedWith t S N ∧
      WorldTypedWith s_pmc Sp Np ∧
      OwnedGrows s_pmc t (worldOwned s_pmc Sp Np) (worldOwned t S N) ∧
      OwnedGrows entry t (worldOwned entry S0 Nd0) (worldOwned t S N) ∧
      FrameOutside entry t (worldOwned entry S0 Nd0 ++ ptxRegions entry ++ [freeGap entry])
        (heapFree entry) ∧
      (∀ o ∈ worldOwned t S N, Disj (w_out.toNat, 96) o) ∧
      IvlsDisj [(lw.toNat, 24), (lw.toNat + 24, 8 * capw.toNat)] (worldOwned t S N) ∧
      PmcLogsLiveOwned t S N (memW t (w_out.toNat + 16))

/-- The chain survives pure locals/clock updates. -/
theorem p4Q8Chain_with_locals {F : Type}
    {entry s_pmc t : PanSemStateFiniteExact 64 F} {w_out lw capw : BitVec 64}
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (h : p4Q8Chain entry s_pmc w_out lw capw t) :
    p4Q8Chain entry s_pmc w_out lw capw {t with locals := L, clock := k} := by
  intro S0 Nd0 hWT0 hD0
  obtain ⟨S, N, Sp, Np, hsub, hWTt, hWTp, hOGp, hOGe, hFO, hout, hfresh, hlist⟩ :=
    h S0 Nd0 hWT0 hD0
  refine ⟨S, N, Sp, Np, hsub, ?_, hWTp, hOGp, hOGe, hFO, hout, hfresh, hlist⟩
  exact (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals t L k S N).2 hWTt

/-- Every typed interval is an owned interval (membership sublist). -/
theorem p4Q8_worldTypedIvls_sub_worldOwned {F : Type}
    (t : PanSemStateFiniteExact 64 F) (S Nd : List Nat) :
    ∀ i ∈ worldTypedIvls t S Nd, i ∈ worldOwned t S Nd := by
  intro i hi
  unfold worldTypedIvls at hi
  unfold worldOwned
  simp only [List.mem_append] at hi ⊢
  rcases hi with ((((ht | hr) | hjr) | hbo) | hbal) | hnd
  · exact Or.inl (Or.inl ht)
  · obtain ⟨r, hrec, rfl⟩ := List.mem_map.1 hr
    refine Or.inl (Or.inr ?_)
    unfold fixedObjects
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    refine List.mem_map.2 ⟨r, ?_, rfl⟩
    simp only [typedRecords, List.mem_cons, List.not_mem_nil, or_false] at hrec
    rcases hrec with rfl | rfl | rfl | rfl <;> decide
  · refine Or.inl (Or.inr ?_)
    unfold fixedObjects
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    exact hjr
  · refine Or.inl (Or.inr ?_)
    unfold fixedObjects
    apply List.mem_append_left; apply List.mem_append_right
    exact hbo
  · refine Or.inl (Or.inr ?_)
    unfold fixedObjects
    exact List.mem_append_right _ hbal
  · exact Or.inr hnd

/-- The chain survives a single-cell store into one of the fresh blocks
(the `stable_logs` header or its backing array). -/
theorem p4Q8Chain_store {F : Type}
    {entry s_pmc t : PanSemStateFiniteExact 64 F} {w_out lw capw : BitVec 64}
    {base sz off : Nat} {w_base x : BitVec 64} {v : ValueHOL 64}
    {mem' : RiscV.Word 64 → HolWordLab 64}
    (h : p4Q8Chain entry s_pmc w_out lw capw t)
    (hW : WorldOK t)
    (hhp_pmc : globN s_pmc "heap_ptr" ≤ globN t "heap_ptr")
    (hhp_ent : globN entry "heap_ptr" ≤ globN t "heap_ptr")
    (hfp_ent : globN entry "frame_mem_ptr" ≤ globN t "frame_mem_ptr")
    (hsp_ent : globN t "scratch_ptr" ≤ globN entry "scratch_ptr")
    (hAR_ent : ArenaReady entry)
    (hR_fresh : Inside (base, sz) (globN entry "heap_ptr") (globN t "heap_ptr"))
    (hbase_lu : w_base.toNat = base)
    (hbase8 : base % 8 = 0) (hsz8 : sz % 8 = 0) (hoff8 : off % 8 = 0)
    (hin_blk : Inside (base, sz) sourceBase (globN t "heap_ptr"))
    (hx_eq : x = w_base + BitVec.ofNat 64 off)
    (hoff_fit : off + 8 * (flattenHOL v).length ≤ sz)
    (hst : @panMemStoresHOL 64 _ x (flattenHOL v) t.memaddrs
      (fun a => Classical.propDecidable (t.memaddrs a)) t.memory = some mem')
    (hblk : (base, sz) = (lw.toNat, 24) ∨ (base, sz) = (lw.toNat + 24, 8 * capw.toNat))
    (hw_out8 : w_out.toNat % 8 = 0)
    (hout_words : WordsOK t (w_out.toNat, 96))
    (hout_inside : Inside (w_out.toNat, 96) sourceBase (globN t "heap_ptr"))
    (hw_out_blk : Disj (w_out.toNat, 96) (base, sz))
    (hlogs_list : LogsListOK t (memW t (w_out.toNat + 16)))
    (hRh : Disj (memW t (w_out.toNat + 16), 24) (base, sz))
    (hRa : memW t (w_out.toNat + 16) ≠ 0 →
      Disj (memW t (memW t (w_out.toNat + 16)),
        8 * memW t (memW t (w_out.toNat + 16) + 8)) (base, sz))
    (hRe : memW t (w_out.toNat + 16) ≠ 0 → ∀ i, i < memW t (memW t (w_out.toNat + 16) + 8) →
      Disj (memW t (memW t (memW t (w_out.toNat + 16)) + 8 * i), 40) (base, sz)) :
    p4Q8Chain entry s_pmc w_out lw capw {t with memory := mem'} := by
  have hstep : WorldStep (fun _ => [(base, sz)]) [] stdKeep NoExtra t none
      {t with memory := mem'} :=
    worldStep_store_in_block hW hbase_lu hbase8 hsz8 hoff8 hin_blk hx_eq hoff_fit hst
  have hhp_eq : globN {t with memory := mem'} "heap_ptr" = globN t "heap_ptr" :=
    globN_eq_of_lookup (hstep.2.2.1 (ofString "heap_ptr") (by simp))
  have hsp_eq : globN {t with memory := mem'} "scratch_ptr" = globN t "scratch_ptr" :=
    globN_eq_of_lookup (hstep.2.2.1 (ofString "scratch_ptr") (by simp))
  have hsys : globN {t with memory := mem'} "vm_system_address" = globN t "vm_system_address" :=
    globN_eq_of_lookup (hstep.2.2.1 _ (by simp))
  have hAs : ArenaOK t := hW.1.2
  have hAp : ArenaOK {t with memory := mem'} := hstep.1.2
  have hAR_t : ArenaReady t := ⟨hW.1.1, hW.1.2⟩
  have hgS : GuestInv t := hW.1.1
  have hgrow : AllocatorGrows t {t with memory := mem'} :=
    ⟨by rw [hhp_eq], by rw [hsp_eq]⟩
  intro S0 Nd0 hWT0 hD0
  obtain ⟨S, N, Sp, Np, hsub, hWTt, hWTp, hOGp, hOGe, hFO, hout, hfresh, hlist⟩ :=
    h S0 Nd0 hWT0 hD0
  have hR_disj : IvlsDisj [(base, sz)] (worldTypedIvls t S N) := by
    intro i hi j hj
    rcases List.mem_singleton.1 hi with rfl
    have hjo : j ∈ worldOwned t S N := p4Q8_worldTypedIvls_sub_worldOwned t S N j hj
    exact hfresh (base, sz) (by rcases hblk with h | h <;> simp [h]) j hjo
  obtain ⟨S', N', hsub', hWT', hOG', hFO', -⟩ :=
    hstep.2.2.2.2 S N hWTt hR_disj
  have hold0 : ∀ j ∈ worldOwned t S N, j.2 = 0 → j.1 % 8 = 0 :=
    R13Shards.worldOwned_zero_aligned hWTt
  have hR0 : ∀ j ∈ [(base, sz)], j.2 = 0 → j.1 % 8 = 0 := by
    intro j hj hz
    rcases List.mem_singleton.1 hj with rfl
    exact hbase8
  have hRout : ∀ j ∈ [(base, sz)], Disj (w_out.toNat, 96) j := by
    intro j hj
    rcases List.mem_singleton.1 hj with rfl
    exact hw_out_blk
  have hb2 : ((w_out.toNat, 96) : Ivl).2 % 8 = 0 := by norm_num
  have hout_u : R13Shards.IvlUnhit t {t with memory := mem'} (w_out.toNat, 96) :=
    (@R13Shards.heap_ivl_survives_step _ _ _ hAs (by rw [hhp_eq])
      _ _ _ hold0 hR0 hOG' hFO' (w_out.toNat, 96) hw_out8 hb2
      hout_inside hout hRout).2.2
  have hout_hi : w_out.toNat + 96 ≤ 2 ^ 64 :=
    (R13Shards.ivl_allocated_bound hAs (Or.inl hout_inside)).2
  have hout_list : memW {t with memory := mem'} (w_out.toNat + 16) =
      memW t (w_out.toNat + 16) := by
    apply R13Shards.memW_eq_of_ivlUnhit hout_u
    · have := hout_words.1; omega
    · exact hout_hi
    · constructor <;> omega
  refine ⟨S', N', Sp, Np, fun t' ht' => hsub' t' (hsub t' ht'), hWT', hWTp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ptx_ownedGrows_trans hhp_pmc (by rw [hhp_eq]) hOGp hOG'
  · exact ptx_ownedGrows_trans hhp_ent (by rw [hhp_eq]) hOGe hOG'
  · refine ptx_frameOutside_trans_fresh hAR_ent hAR_t hhp_ent hfp_ent hsp_ent hOGe ?_ hFO hFO'
    intro j hj
    rcases List.mem_singleton.1 hj with rfl
    exact hR_fresh
  · intro o ho
    rcases hOG' o ho with rfl | ⟨j, hj, hin⟩ | hin
    · exact Or.inr (Or.inl rfl)
    · exact disj_of_inside_right hin (hout j hj)
    · rw [hhp_eq] at hin
      obtain ⟨h1, h2⟩ := hin
      exact Or.inr (Or.inl (by omega))
  · intro i hi j hj
    rcases hOG' j hj with rfl | ⟨k, hk, hin⟩ | hin
    · exact Or.inr (Or.inl rfl)
    · exact disj_of_inside_right hin (hfresh i hi k hk)
    · rw [hhp_eq] at hin
      obtain ⟨h1, h2⟩ := hin
      exact Or.inr (Or.inl (by omega))
  · rw [hout_list]
    by_cases hnz : memW t (w_out.toNat + 16) = 0
    · rw [hnz]; exact pmcLogsLiveOwned_zero _ _ _
    · exact PtxP34.logsLiveOwned_survives hAs hAp hgS hgrow hlogs_list hlist hsys hold0 hR0
        hOG' hFO' (by intro j hj; rcases List.mem_singleton.1 hj with rfl; exact hRh)
        (by intro j hj; rcases List.mem_singleton.1 hj with rfl; exact hRa hnz)
        (by intro i hi j hj; rcases List.mem_singleton.1 hj with rfl; exact hRe hnz i hi)


/-! ## Base-field transports across fresh-block stores -/

/-- `Disj` is symmetric. -/
theorem p4Q8_disj_symm {i j : Ivl} (h : Disj i j) : Disj j i := by
  unfold Disj at h ⊢
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

/-- A global buffer's block is an owned interval. -/
theorem p4Q8_buf_owned {F : Type} (t : PanSemStateFiniteExact 64 F)
    (S N : List Nat) (gn : String × Nat) (hg : gn ∈ globalBuffers)
    (hnz : globN t gn.1 ≠ 0) :
    (globN t gn.1, gn.2) ∈ worldOwned t S N := by
  have h1 : (globN t gn.1, gn.2) ∈ fixedObjects t := by
    unfold fixedObjects
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    refine List.mem_map.2 ⟨gn, hg, ?_⟩
    simp only [if_neg hnz]
  unfold worldOwned
  apply List.mem_append_left
  apply List.mem_append_right
  exact h1

/-- Every block-out object is an owned interval. -/
theorem p4Q8_blockOut_owned {F : Type} (t : PanSemStateFiniteExact 64 F)
    (S N : List Nat) : ∀ i ∈ blockOutObjects t, i ∈ worldOwned t S N := by
  intro i hi
  have h1 : i ∈ fixedObjects t := by
    unfold fixedObjects
    apply List.mem_append_left
    apply List.mem_append_right
    exact hi
  unfold worldOwned
  apply List.mem_append_left
  apply List.mem_append_right
  exact h1

/-- Instantiate the chain at the ready-entry witnesses. -/
theorem p4Q8_chain_witnesses {F : Type}
    {entry s_pmc t : PanSemStateFiniteExact 64 F} {w_out lw capw : BitVec 64}
    (hchain : p4Q8Chain entry s_pmc w_out lw capw t)
    (hready : TxReadyStrong entry) :
    ∃ S N, WorldTypedWith t S N ∧
      IvlsDisj [(lw.toNat, 24), (lw.toNat + 24, 8 * capw.toNat)] (worldOwned t S N) ∧
      (∀ o ∈ worldOwned t S N, Disj (w_out.toNat, 96) o) ∧
      (∀ i ∈ worldTypedIvls t S N, i ∈ worldOwned t S N) := by
  obtain ⟨⟨_, hbo_nz_e, _, _, _⟩, _, _, _, S_e, Nd_e, hWT_e, _⟩ := hready
  have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
    rw [ptxRegions_eq_bufRegions]
    exact validBufList_disj validBufList_ptxBufs hWT_e
  obtain ⟨S, N, Sp, Np, hsub, hWT, hWTp, hOGp, hOGe, hFO, hout, hfresh, hlist⟩ :=
    hchain S_e Nd_e hWT_e hD_e
  exact ⟨S, N, hWT, hfresh, hout, p4Q8_worldTypedIvls_sub_worldOwned t S N⟩

/-- A cell inside interval `(i1, i2)` cannot hit an interval disjoint from it. -/
theorem p4Q8_disj_noHits {a i1 i2 : Nat} {j : Ivl} (h : Disj (i1, i2) j) (hj2 : 0 < j.2)
    (ha : i1 ≤ a) (hfit : a + 8 ≤ i1 + i2) : ¬ CellHits a j := by
  intro hcc
  simp only [Disj, CellHits] at h hcc
  obtain ⟨hc1, hc2⟩ := hcc
  rcases h with h0 | h0 | h0 | h0 <;> omega

/-- The raw effect facts of a single-cell store into a fresh block. -/
theorem p4Q8_store_effect {F : Type}
    {t : PanSemStateFiniteExact 64 F} {base sz off : Nat} {w_base x : BitVec 64}
    {v : ValueHOL 64} {mem' : BitVec 64 → HolWordLab 64}
    (hW : WorldOK t)
    (hAR : ArenaReady {t with memory := mem'})
    (hcode : {t with memory := mem'}.code = originalRuntimeCode)
    (hbase_lu : w_base.toNat = base)
    (hbase8 : base % 8 = 0)
    (hsz0 : 0 < sz)
    (hsz8 : sz % 8 = 0)
    (hin_blk : Inside (base, sz) sourceBase (globN t "heap_ptr"))
    (hx_eq : x = w_base + BitVec.ofNat 64 off)
    (hoff_fit : off + 8 * (flattenHOL v).length ≤ sz)
    (hst : @panMemStoresHOL 64 _ x (flattenHOL v) t.memaddrs
      (fun a => Classical.propDecidable (t.memaddrs a)) t.memory = some mem') :
    (∀ a : BitVec 64, ¬ CellHits a.toNat (base, sz) →
      mem' a = t.memory a) ∧
    WorldEff t {t with memory := mem'} [(base, sz)] [] [] := by
  have h264 : heapEnd < 2 ^ 64 ∧ heapLimit ≤ heapEnd := ⟨by decide, by decide⟩
  have hhp_lim : globN t "heap_ptr" ≤ heapLimit := hW.1.2.2.1
  have hx_nat : x.toNat = base + off := by
    rw [hx_eq, BitVec.toNat_add, hbase_lu, BitVec.toNat_ofNat]
    have hoff_lt : off < 2 ^ 64 := by unfold Inside at hin_blk; omega
    rw [Nat.mod_eq_of_lt hoff_lt]
    exact Nat.mod_eq_of_lt (by unfold Inside at hin_blk; omega)
  have hcell : ∀ a : BitVec 64, ¬ CellHits a.toNat (base, sz) →
      mem' a = t.memory a := by
    intro a hnh
    apply panMemStoresHOL_frame_sysTx (flattenHOL v) x t.memory mem' hst a
    intro k hk h_eq
    apply hnh
    have ha_nat : a.toNat = base + off + 8 * k := by
      rw [h_eq, BitVec.toNat_add, hx_nat, BitVec.toNat_ofNat]
      have hk_lt : 8 * k < 2 ^ 64 := by unfold Inside at hin_blk; omega
      rw [Nat.mod_eq_of_lt hk_lt]
      exact Nat.mod_eq_of_lt (by unfold Inside at hin_blk; omega)
    unfold CellHits
    rw [ha_nat]
    exact ⟨by omega, by omega⟩
  refine ⟨hcell, ⟨hAR, hcode, rfl, rfl, rfl, le_of_eq (by rfl), rfl, le_of_eq (by rfl),
    fun _ _ => rfl, ⟨fun _ _ => Or.inl rfl, ?_⟩, ?_, ?_, ?_⟩⟩
  · rw [List.pairwise_iff_getElem]
    intro i j _ _ _ h1 _
    exact absurd rfl h1.1
  · intro a hne
    exact panMemStoresHOL_dom_of_ne (flattenHOL v) x t.memory mem' hst a hne
  · intro a hne
    have hc : CellHits a.toNat (base, sz) := by
      by_contra hcon
      exact hne (hcell a hcon)
    exact Or.inl ⟨(base, sz), by simp, ⟨hsz0, hc⟩⟩
  · intro b hb64 hnb
    refine Or.inl ⟨(base, sz), by simp, ?_⟩
    unfold memB at hnb
    dsimp only at hnb
    have hch : CellHits (panByteAlignHOL (BitVec.ofNat 64 b)).toNat (base, sz) := by
      by_contra hcon
      refine hnb ?_
      rw [hcell (panByteAlignHOL (BitVec.ofNat 64 b)) hcon]
    have hal_nat : (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := by
      rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb64]
    rw [hal_nat] at hch
    simp only [InIvl, CellHits] at hch ⊢
    omega

/-- `PtxBlockOutUnhit` across a fresh-block store. -/
theorem p4Q8_blockOutUnhit_store {F : Type}
    {entry s_pmc t : PanSemStateFiniteExact 64 F} {w_out lw capw : BitVec 64}
    {base sz : Nat} {mem' : BitVec 64 → HolWordLab 64}
    (hchain : p4Q8Chain entry s_pmc w_out lw capw t)
    (hready : TxReadyStrong entry)
    (hblk : (base, sz) = (lw.toNat, 24) ∨ (base, sz) = (lw.toNat + 24, 8 * capw.toNat))
    (hAR : ArenaReady t)
    (hEff : WorldEff t {t with memory := mem'} [(base, sz)] [] []) :
    PtxBlockOutUnhit t {t with memory := mem'} := by
  obtain ⟨S, N, hWT, hfresh, hout, _⟩ := p4Q8_chain_witnesses hchain hready
  refine ptxBlockOutUnhit_of_worldEff hEff hAR hWT ?_ (fun b hb => absurd hb (by simp))
  intro j hj i hi
  rcases List.mem_singleton.1 hj with rfl
  exact p4Q8_disj_symm
    (hfresh (base, sz) (by rcases hblk with h | h <;> simp [h]) i
      (p4Q8_blockOut_owned t S N i hi))

/-- The `bo` header cells survive a fresh-block store. -/
theorem p4Q8_bo_field_store {F : Type}
    {entry s_pmc t : PanSemStateFiniteExact 64 F} {w_out lw capw : BitVec 64}
    {base sz : Nat} {mem' : BitVec 64 → HolWordLab 64}
    (hchain : p4Q8Chain entry s_pmc w_out lw capw t)
    (hready : TxReadyStrong entry)
    (hblk : (base, sz) = (lw.toNat, 24) ∨ (base, sz) = (lw.toNat + 24, 8 * capw.toNat))
    (hsz0 : 0 < sz)
    (hstep : WorldStep (fun _ => [(base, sz)]) [] stdKeep NoExtra t none
      {t with memory := mem'})
    (hbo_nz : globN t "bo" ≠ 0) :
    ∀ off ∈ ([24, 32, 40, 56, 64, 72, 80] : List Nat),
      memW {t with memory := mem'} (globN t "bo" + off) = memW t (globN t "bo" + off) := by
  obtain ⟨S, N, hWT, hfresh, hout, _⟩ := p4Q8_chain_witnesses hchain hready
  have hbo_own : (globN t "bo", 88) ∈ worldOwned t S N :=
    p4Q8_buf_owned t S N ("bo", 88) (by decide) hbo_nz
  have hdisj_bo : Disj (globN t "bo", 88) (base, sz) :=
    p4Q8_disj_symm (hfresh (base, sz) (by rcases hblk with h | h <;> simp [h]) _ hbo_own)
  intro off hoff
  have hoff_le : off ≤ 80 := by simp at hoff; omega
  refine hstep.2.2.2.1 ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
    (by simp [stdKeep]) hbo_nz off ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff ⊢
    rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro i hi hhit
    rcases List.mem_singleton.1 hi with rfl
    dsimp only at hhit
    exact p4Q8_disj_noHits hdisj_bo hsz0 (Nat.le_add_right _ off) (by omega) hhit

/-- `PtxBoCells` across a fresh-block store. -/
theorem p4Q8_boCells_store {F : Type}
    {entry s_pmc t : PanSemStateFiniteExact 64 F} {w_out lw capw : BitVec 64}
    {base sz : Nat} {mem' : BitVec 64 → HolWordLab 64}
    (hbase : PtxRelBase true entry t)
    (hchain : p4Q8Chain entry s_pmc w_out lw capw t)
    (hblk : (base, sz) = (lw.toNat, 24) ∨ (base, sz) = (lw.toNat + 24, 8 * capw.toNat))
    (hsz0 : 0 < sz)
    (hstep : WorldStep (fun _ => [(base, sz)]) [] stdKeep NoExtra t none
      {t with memory := mem'})
    (hbo_unhit : PtxBlockOutUnhit t {t with memory := mem'}) :
    PtxBoCells true entry t {t with memory := mem'} := by
  have hbo_eq : globN {t with memory := mem'} "bo" = globN t "bo" :=
    globN_eq_of_lookup (hstep.2.2.1 (ofString "bo") (by simp))
  have hbo_s_entry : globN t "bo" = globN entry "bo" :=
    globN_eq_of_lookup (hbase.globals (ofString "bo") (by decide))
  obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, _, hbo40_nz_e, hbo72_nz_e,
    S_e, Nd_e, hWT_e, _⟩ := hbase.ready_entry
  have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
    rw [ptxRegions_eq_bufRegions]
    exact validBufList_disj validBufList_ptxBufs hWT_e
  have hbo_nz_s : globN t "bo" ≠ 0 := by rw [hbo_s_entry]; exact hbo_nz_e
  obtain ⟨Sc, Nc, _, hWT_w, _, _⟩ := hbase.typing S_e Nd_e hWT_e hD_e
  have hbo_field_s : ∀ off ∈ ([24, 32, 40, 72, 80] : List Nat),
      off % 8 = 0 → off + 8 ≤ 88 →
      memW {t with memory := mem'} (globN t "bo" + off) = memW t (globN t "bo" + off) := by
    intro off hoff _hoff8 _hlt
    refine p4Q8_bo_field_store hchain hbase.ready_entry hblk hsz0 hstep hbo_nz_s off ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff ⊢
    rcases hoff with rfl | rfl | rfl | rfl | rfl <;> simp
  have hbo24_s : memW t (globN t "bo" + 24) = memW entry (globN entry "bo" + 24) :=
    ptx_entry_bo_field_eq hWT_e hbase.globals hbase.records hbo_nz_e (by simp) (by omega)
  have hbo32_s : memW t (globN t "bo" + 32) = memW entry (globN entry "bo" + 32) :=
    ptx_entry_bo_field_eq hWT_e hbase.globals hbase.records hbo_nz_e (by simp) (by omega)
  have hbo40_s : memW t (globN t "bo" + 40) = memW entry (globN entry "bo" + 40) :=
    ptx_entry_bo_field_eq hWT_e hbase.globals hbase.records hbo_nz_e (by simp) (by omega)
  have hbo72_s : memW t (globN t "bo" + 72) = memW entry (globN entry "bo" + 72) :=
    ptx_entry_bo_field_eq hWT_e hbase.globals hbase.records hbo_nz_e (by simp) (by omega)
  have hbo80_s : memW t (globN t "bo" + 80) = memW entry (globN entry "bo" + 80) :=
    ptx_entry_bo_field_eq hWT_e hbase.globals hbase.records hbo_nz_e (by simp) (by omega)
  have hbo40_nz_s : memW t (globN t "bo" + 40) ≠ 0 := by rw [hbo40_s]; exact hbo40_nz_e
  have hbo72_nz_s : memW t (globN t "bo" + 72) ≠ 0 := by rw [hbo72_s]; exact hbo72_nz_e
  have hbo40_post : memW {t with memory := mem'} (globN {t with memory := mem'} "bo" + 40) =
      memW t (globN t "bo" + 40) := by
    rw [hbo_eq]; exact hbo_field_s 40 (by simp) (by decide) (by omega)
  have hbo72_post : memW {t with memory := mem'} (globN {t with memory := mem'} "bo" + 72) =
      memW t (globN t "bo" + 72) := by
    rw [hbo_eq]; exact hbo_field_s 72 (by simp) (by decide) (by omega)
  have hlog_hdr0 : memW {t with memory := mem'} (memW {t with memory := mem'}
      (globN {t with memory := mem'} "bo" + 40)) =
      memW t (memW t (globN t "bo" + 40)) := by
    rw [hbo40_post]
    have hm : (memW t (globN t "bo" + 40), 24) ∈ blockOutObjects t := by
      simp [blockOutObjects, hbo_nz_s, hbo40_nz_s]
    simpa using memW_eq_of_ptxBlockOutUnhit hbase.world.1 hWT_w hbo_unhit hm
      (off := 0) (by decide) (by decide)
  have hrcpt_hdr0 : memW {t with memory := mem'} (memW {t with memory := mem'}
      (globN {t with memory := mem'} "bo" + 72)) =
      memW t (memW t (globN t "bo" + 72)) := by
    rw [hbo72_post]
    simpa using ptx_receipt_header_eq_of_blockOutUnhit hbase.world.1 hWT_w hbo_unhit
      hbo_nz_s hbo72_nz_s (off := 0) (by simp)
  have hrcpt_hdr8 : memW {t with memory := mem'} (memW {t with memory := mem'}
      (globN {t with memory := mem'} "bo" + 72) + 8) =
      memW t (memW t (globN t "bo" + 72) + 8) := by
    rw [hbo72_post]
    exact ptx_receipt_header_eq_of_blockOutUnhit hbase.world.1 hWT_w hbo_unhit
      hbo_nz_s hbo72_nz_s (by simp)
  have hsl_eq : ∀ off ∈ ([24, 32] : List Nat), ∀ k, k ≤ locN entry "index" →
      memW {t with memory := mem'} (memW {t with memory := mem'}
        (globN {t with memory := mem'} "bo" + off) + 16 * k + 8) =
        memW t (memW t (globN t "bo" + off) + 16 * k + 8) := by
    intro off hoff k hk
    have hoff_in : off ∈ ([24, 32, 40, 72, 80] : List Nat) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl <;> simp
    have hbo_off_eq : memW {t with memory := mem'} (globN {t with memory := mem'} "bo" + off) =
        memW t (globN t "bo" + off) := by
      rw [hbo_eq]
      apply hbo_field_s off hoff_in
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
        rcases hoff with rfl | rfl <;> decide
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
        rcases hoff with rfl | rfl <;> omega
    rw [hbo_off_eq]
    have hp_nz : memW t (globN t "bo" + off) ≠ 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl
      · rw [hbo24_s]; exact hbo24_nz_e
      · rw [hbo32_s]; exact hbo32_nz_e
    apply ptx_slice_length_eq_of_blockOutUnhit hbase.world.1 hWT_w hbo_unhit hbo_nz_s hoff
      hp_nz
    rw [hbo80_s]; omega
  refine ⟨hbo_eq, by rw [hrcpt_hdr0]; exact hbase.rcpt_backing,
    by rw [hlog_hdr0]; exact hbase.log_backing, hrcpt_hdr8,
    fun off hoff k hk => hsl_eq off hoff k (Nat.le_of_lt hk), ?_⟩
  intro ht
  rw [hsl_eq 24 (by simp) (locN entry "index") le_rfl]
  exact hbase.tx_slice_cur ht

/-- `PtxRelBase` across a fresh-block store, with the typing field rebuilt from the
post-store chain witnesses. -/
theorem p4Q8Base_store {F : Type}
    {entry s_pmc t : PanSemStateFiniteExact 64 F} {w_out lw capw : BitVec 64}
    {base sz : Nat} {mem' : BitVec 64 → HolWordLab 64}
    (hbase : PtxRelBase true entry t)
    (hchain_t : p4Q8Chain entry s_pmc w_out lw capw t)
    (hchain : p4Q8Chain entry s_pmc w_out lw capw {t with memory := mem'})
    (hblk : (base, sz) = (lw.toNat, 24) ∨ (base, sz) = (lw.toNat + 24, 8 * capw.toNat))
    (hsz0 : 0 < sz)
    (hstep : WorldStep (fun _ => [(base, sz)]) [] stdKeep NoExtra t none
      {t with memory := mem'})
    (hcells : PtxBoCells true entry t {t with memory := mem'}) :
    PtxRelBase true entry {t with memory := mem'} := by
  obtain ⟨⟨_, hbo_nz_e, _, _, _⟩, _, _, _, S_e, Nd_e, hWT_e, _⟩ := hbase.ready_entry
  have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
    rw [ptxRegions_eq_bufRegions]
    exact validBufList_disj validBufList_ptxBufs hWT_e
  have hsub_e := hchain S_e Nd_e hWT_e hD_e
  obtain ⟨S_p, N_p, Sp_p, Np_p, hsub_p, hWT_p, hWTp_p, hOGp_p, hOGe_p, hFO_p, hout_p,
    hfresh_p, hlist_p⟩ := hsub_e
  have hworld_post : WorldOK {t with memory := mem'} :=
    ⟨hstep.1, S_p, (worldTyped_iff_with _ S_p).2 ⟨N_p, hWT_p⟩⟩
  have hbo_s_entry : globN t "bo" = globN entry "bo" :=
    globN_eq_of_lookup (hbase.globals (ofString "bo") (by decide))
  have hbo_nz_t : globN t "bo" ≠ 0 := by rw [hbo_s_entry]; exact hbo_nz_e
  have hfresh_disj : ∀ (name : String) (sz' : Nat), (name, sz') ∈ globalBuffers →
      globN t name ≠ 0 → Disj (globN t name, sz') (base, sz) := by
    intro name sz' hg hnz
    obtain ⟨S_w, N_w, hWT_w, hfresh_w, hout_w, _⟩ :=
      p4Q8_chain_witnesses hchain_t hbase.ready_entry
    have hown : (globN t name, sz') ∈ worldOwned t S_w N_w :=
      p4Q8_buf_owned t S_w N_w (name, sz') hg hnz
    exact p4Q8_disj_symm
      (hfresh_w (base, sz) (by rcases hblk with h | h <;> simp [h]) _ hown)
  have hR_keepcells : ∀ i ∈ [(base, sz)], ∀ rec ∈ ptxKeep, globN t rec.1 ≠ 0 →
      ∀ off ∈ rec.2, ¬ CellHits (globN t rec.1 + off) i := by
    intro i hi rec hr hn off hoff
    rcases List.mem_singleton.1 hi with rfl
    intro hhit
    simp only [ptxKeep, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      exact p4Q8_disj_noHits (hfresh_disj "ws" 40 (by decide) hn) hsz0
        (Nat.le_add_right _ off) (by omega) hhit
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      exact p4Q8_disj_noHits (hfresh_disj "bs" 80 (by decide) hn) hsz0
        (Nat.le_add_right _ off) (by omega) hhit
    · exact absurd hoff (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      exact p4Q8_disj_noHits (hfresh_disj "bo" 88 (by decide) hn) hsz0
        (Nat.le_add_right _ off) (by omega) hhit
  refine ⟨hbase.ready_entry, hbase.arena_entry,
    Nat.le_trans hbase.frame_entry
      (Nat.le_of_eq (globN_eq_of_lookup (hstep.2.2.1 (ofString "frame_mem_ptr") (by simp)))),
    Nat.le_trans
      (Nat.le_of_eq (globN_eq_of_lookup (hstep.2.2.1 (ofString "scratch_ptr") (by simp))))
      hbase.scratch_entry,
    hworld_post, Nat.le_trans hbase.heap_entry hstep.2.1, ?_, ?_, hcells.rcpt_backing,
    hcells.log_backing, hcells.rcpt_len_eq.trans hbase.rcpt_len_eq,
    fun off hoff k hk => (hcells.slices_prev off hoff k hk).trans
      (hbase.slices_prev off hoff k hk),
    hcells.tx_slice_cur, ?_⟩
  · intro k hk
    have hkg : k ∉ ([] : List String).map ofString := by simp
    exact (hbase.globals k hk).trans (hstep.2.2.1 k hkg)
  · intro rec hr hn off hoff hno
    obtain ⟨offs, hkr, hko⟩ := ptxKeepSub_stdKeep rec hr
    have heq : globN t rec.1 = globN entry rec.1 := by
      have hni : ofString rec.1 ∉ ptxGlobals.map ofString := by
        simp only [ptxKeep, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · decide
        · decide
        · simp at hoff
        · decide
      exact globN_eq_of_lookup (hbase.globals (ofString rec.1) hni)
    have hks := hstep.2.2.2.1 (rec.1, offs) hkr (by rw [heq]; exact hn)
      off (hko off hoff)
      (fun i hi => hR_keepcells i hi rec hr (by rw [heq]; exact hn) off hoff)
    rw [heq] at hks
    exact hks.trans (hbase.records rec hr hn off hoff hno)
  · intro S0 Nd0 hWT0 hD0
    obtain ⟨S', N', Sp', Np', hsub', hWT', hWTp', hOGp', hOGe', hFO', hout', hfresh',
      hlist'⟩ := hchain S0 Nd0 hWT0 hD0
    exact ⟨S', N', hsub', hWT', hOGe', hFO'⟩

/-! ## The g8 prologue: the stable-logs capacity fix and allocation

Instruction 31 (`dec stable_log_cap nl`), the zero-clamp `ite`
(instruction 32) and the `lst_new` allocation call (instruction 33).  The
clamp branches need the evaluated condition (the capacity is either the
fixed `1` or `nl`), so a condition-fact `ite` runner comes first. -/

/-- An `ite` runner that hands each branch the evaluated condition word:
the then-branch learns the word is nonzero, the else-branch that it is
zero. -/
theorem p4Q8_ite_cond {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    (cond : ExpHOL 64) (bt bf : ProgHOL 64) (tail : ProgHOL 64)
    (ht : ∀ b : BitVec 64, evalAt s cond = some (.val (.word b)) →
      b ≠ (0 : BitVec 64) → PtxRelRunStrong entry (.seq bt tail) s)
    (hf : ∀ b : BitVec 64, evalAt s cond = some (.val (.word b)) →
      b = (0 : BitVec 64) → PtxRelRunStrong entry (.seq bf tail) s) :
    PtxRelRunStrong entry (.seq (.ite cond bt bf) tail) s := by
  intro hres
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres ⊢
  dsimp only at hres ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) cond with _ | v
  · simp [hev] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · cases hv : v with
    | val w =>
      cases hw : w with
      | word b =>
        simp only [hev, hv, hw] at hres ⊢
        have hcond : evalAt s cond = some (.val (.word b)) := by
          show @evalHOLExact 64 F _ s.toExact
              (fun a => Classical.propDecidable (s.memaddrs a)) cond = _
          rw [hev, hv, hw]
        by_cases hb : b = (0 : BitVec 64)
        · simp only [hb, ↓reduceIte] at hres ⊢
          have hf'un : Resumes (evaluateHOLFiniteState s (ProgHOL.seq bf tail)).1 →
              WorldStep ptxRegions ptxGlobals ptxKeep PtxLogsAndSlices entry
                (evaluateHOLFiniteState s (ProgHOL.seq bf tail)).1
                (evaluateHOLFiniteState s (ProgHOL.seq bf tail)).2 := hf b hcond hb
          rw [evaluateHOLFiniteState_seq_line780] at hf'un
          dsimp only at hf'un
          exact hf'un hres
        · simp only [hb, ↓reduceIte] at hres ⊢
          have ht'un : Resumes (evaluateHOLFiniteState s (ProgHOL.seq bt tail)).1 →
              WorldStep ptxRegions ptxGlobals ptxKeep PtxLogsAndSlices entry
                (evaluateHOLFiniteState s (ProgHOL.seq bt tail)).1
                (evaluateHOLFiniteState s (ProgHOL.seq bt tail)).2 := ht b hcond hb
          rw [evaluateHOLFiniteState_seq_line780] at ht'un
          dsimp only at ht'un
          exact ht'un hres
    | rStruct _ | nStruct _ _ =>
      simp [hev, hv] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

/-- A two-element argument list evaluates to the element values. -/
theorem p4Q8_evalList_two {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e1 e2 : ExpHOL 64) (v1 v2 : ValueHOL 64)
    (h1 : evalAt s e1 = some v1) (h2 : evalAt s e2 = some v2) :
    evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [e1, e2] = some [v1, v2] := by
  simp only [evalListHOLFinite, evalListHOLExact, evalAt, evalHOLExact, toExact, h1, h2]

/-- Instructions 31-33: `dec stable_log_cap nl`, the zero-clamp `ite`,
and the `lst_new (8, stable_log_cap)` call allocating the stable-logs
list header on the fresh heap frontier. -/
theorem p4Q8_stableLogs_alloc {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out)
    (hc : s.code = originalRuntimeCode)
    (rest : ProgHOL 64)
    (nl_w lp_w : BitVec 64)
    (hnl : s.locals.lookup (ofString "nl") = some (.val (.word nl_w)))
    (hlp : s.locals.lookup (ofString "lp") = some (.val (.word lp_w)))
    (hnl28 : nl_w.toNat ≤ 2 ^ 28)
    (htail : ∀ (capw lw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      1 ≤ capw.toNat →
      nl_w.toNat ≤ capw.toNat →
      8 * capw.toNat < 2 ^ 64 →
      lw.toNat = globN s "heap_ptr" →
      lw.toNat % 8 = 0 →
      lw.toNat ≠ 0 →
      memW mid lw.toNat = lw.toNat + 24 →
      memW mid (lw.toNat + 8) = 0 →
      memW mid (lw.toNat + 16) = capw.toNat →
      globN mid "heap_ptr" = lw.toNat + 24 + 8 * capw.toNat →
      globN s "heap_ptr" < globN mid "heap_ptr" →
      ArenaReady mid →
      globN mid "scratch_ptr" = globN s "scratch_ptr" →
      globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" →
      LstOK mid lw.toNat →
      lstObjects mid lw.toNat 8 = [(lw.toNat, 24), (lw.toNat + 24, 8 * capw.toNat)] →
      Disj (lw.toNat, 24) (lw.toNat + 24, 8 * capw.toNat) →
      (∀ i ∈ lstObjects mid lw.toNat 8,
        Allocated mid i ∧ WordsOK mid i ∧
        Inside i (globN s "heap_ptr") (globN mid "heap_ptr")) →
      FrameOutside s mid [(globN s "scratch_ptr", 0)]
        (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") →
      (∀ k : MlS, k ≠ ofString "heap_ptr" →
        s.globals.lookup k = mid.globals.lookup k) →
      mid.locals.lookup (ofString "stable_logs") = some (.val (.word lw)) →
      mid.locals.lookup (ofString "stable_log_cap") = some (.val (.word capw)) →
      (∀ y, y ≠ ofString "stable_logs" → y ≠ ofString "stable_log_cap" →
        mid.locals.lookup y = s.locals.lookup y) →
      w_out.toNat + 96 ≤ lw.toNat →
      (∀ S0 Nd0 : List Nat, WorldTypedWith entry S0 Nd0 →
        IvlsDisj (ptxRegions entry) (worldTypedIvls entry S0 Nd0) →
        ∃ S_pmc' Nd_pmc' S_new Nd_new : List Nat,
          WorldTypedWith s_pmc S_pmc' Nd_pmc' ∧
          (∀ t' ∈ S0, t' ∈ S_new) ∧
          WorldTypedWith mid S_new Nd_new ∧
          OwnedGrows s_pmc mid (worldOwned s_pmc S_pmc' Nd_pmc')
            (worldOwned mid S_new Nd_new) ∧
          OwnedGrows entry mid (worldOwned entry S0 Nd0) (worldOwned mid S_new Nd_new) ∧
          FrameOutside entry mid
            (worldOwned entry S0 Nd0 ++ ptxRegions entry ++ [freeGap entry])
            (heapFree entry) ∧
          (∀ o ∈ worldOwned mid S_new Nd_new, Disj (w_out.toNat, 96) o) ∧
          IvlsDisj [(lw.toNat, 24), (lw.toNat + 24, 8 * capw.toNat)]
            (worldOwned mid S_new Nd_new) ∧
          PmcLogsLiveOwned mid S_new Nd_new (memW mid (w_out.toNat + 16)) ∧
          PmcLogsLiveOwned mid S_new Nd_new lw.toNat) →
      P4Data entry mid s_pmc w_out →
      mid.code = originalRuntimeCode →
      PtxRelRunStrong entry rest mid) :
    PtxRelRunStrong entry
      (.dec (ofString "stable_log_cap") .one (.var .local (ofString "nl"))
        (.seq (.ite (.cmp .equal (.var .local (ofString "stable_log_cap"))
            (.const 0x0000000000000000#64))
          (.assign .local (ofString "stable_log_cap")
            (.const 0x0000000000000001#64))
          .skip)
        (.decCall (ofString "stable_logs") .one (ofString "lst_new")
          [(.const 0x0000000000000008#64),
            (.var .local (ofString "stable_log_cap"))]
          rest))) s := by
  refine p4Run_dec (ofString "stable_log_cap") .one _ _ ?_
  intro v hev hsh
  have hevn : evalAt s (.var .local (ofString "nl")) = some (.val (.word nl_w)) := by
    simp only [evalAt, evalHOLExact, toExact, hnl]
  rw [hevn] at hev
  have hv : v = .val (.word nl_w) := (Option.some.inj hev).symm
  subst hv
  have hD1 : P4Data entry
      (setVarHOLFinite (ofString "stable_log_cap") (.val (.word nl_w)) s) s_pmc w_out :=
    p4Data_setVar (by decide) (by decide) (by decide) (by decide)
      (by intro nm hnm
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hnm
          rcases hnm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      h
  have hs1lu : (setVarHOLFinite (ofString "stable_log_cap")
      (.val (.word nl_w)) s).locals.lookup (ofString "stable_log_cap") =
      some (.val (.word nl_w)) := by
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have hs1fr : ∀ y : MlS, y ≠ ofString "stable_log_cap" →
      (setVarHOLFinite (ofString "stable_log_cap") (.val (.word nl_w)) s).locals.lookup y
        = s.locals.lookup y := by
    intro y hy
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hy, Ne.symm hy]
  have hA : ∀ a : BitVec 64,
      evalAt (setVarHOLFinite (ofString "stable_log_cap") (.val (.word nl_w)) s)
          (.var .local (ofString "stable_log_cap")) = some (.val (.word a)) →
      a = nl_w := by
    intro a ha
    have hla := evalAt_local
      (setVarHOLFinite (ofString "stable_log_cap") (.val (.word nl_w)) s)
      "stable_log_cap" a ha
    simp only [locN, hs1lu] at hla
    exact BitVec.eq_of_toNat_eq hla
  have hB : ∀ b' : BitVec 64,
      evalAt (setVarHOLFinite (ofString "stable_log_cap") (.val (.word nl_w)) s)
          (.const 0x0000000000000000#64) = some (.val (.word b')) →
      b' = (0 : BitVec 64) := by
    intro b' hb'
    have hc0 := evalAt_const
      (setVarHOLFinite (ofString "stable_log_cap") (.val (.word nl_w)) s)
      (0x0000000000000000#64 : BitVec 64) (.val (.word b')) hb'
    simpa using hc0
  refine p4Q8_ite_cond (.cmp .equal (.var .local (ofString "stable_log_cap"))
      (.const 0x0000000000000000#64))
    (.assign .local (ofString "stable_log_cap")
      (.const 0x0000000000000001#64))
    .skip
    (.decCall (ofString "stable_logs") .one (ofString "lst_new")
      [(.const 0x0000000000000008#64),
        (.var .local (ofString "stable_log_cap"))] rest) ?_ ?_
  · -- the clamp fires: the condition word is nonzero, so `nl` is 0
    intro b hcond hb
    obtain ⟨a, b', ha, hb', hwif⟩ := evalAt_cmp
      (setVarHOLFinite (ofString "stable_log_cap") (.val (.word nl_w)) s) .equal
      (.var .local (ofString "stable_log_cap"))
      (.const 0x0000000000000000#64) b hcond
    have hb'0 : b' = (0 : BitVec 64) := hB _ hb'
    have ha0 : a = nl_w := hA _ ha
    have hnl0 : nl_w = (0 : BitVec 64) := by
      rcases hbc : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal nl_w
          (0 : BitVec 64) with false | true
      · rw [ha0, hb'0] at hwif
        rw [hbc] at hwif
        simp at hwif
        exact (hb hwif).elim
      · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hbc
        exact hbc
    refine p4Run_assign (ofString "stable_log_cap")
      (.const 0x0000000000000001#64) _ ?_
    intro v13 hev13
    have hc13 : evalAt
        (setVarHOLFinite (ofString "stable_log_cap") (.val (.word nl_w)) s)
        (ExpHOL.const 0x0000000000000001#64) =
        some (.val (.word 0x0000000000000001#64)) := rfl
    rw [hc13] at hev13
    have hv13 : v13 = .val (.word 0x0000000000000001#64) :=
      (Option.some.inj hev13).symm
    subst hv13
    have hD2 : P4Data entry
        (setVarHOLFinite (ofString "stable_log_cap")
          (.val (.word 0x0000000000000001#64))
          (setVarHOLFinite (ofString "stable_log_cap") (.val (.word nl_w)) s))
        s_pmc w_out :=
      p4Data_setVar (by decide) (by decide) (by decide) (by decide)
        (by intro nm hnm
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hnm
            rcases hnm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        hD1
    have hs2lu : (setVarHOLFinite (ofString "stable_log_cap")
          (.val (.word 0x0000000000000001#64))
          (setVarHOLFinite (ofString "stable_log_cap") (.val (.word nl_w)) s)).locals.lookup
        (ofString "stable_log_cap") =
        some (.val (.word 0x0000000000000001#64)) := by
      simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
    have hs2fr : ∀ y : MlS, y ≠ ofString "stable_log_cap" →
        (setVarHOLFinite (ofString "stable_log_cap")
          (.val (.word 0x0000000000000001#64))
          (setVarHOLFinite (ofString "stable_log_cap") (.val (.word nl_w)) s)).locals.lookup y
          = (setVarHOLFinite (ofString "stable_log_cap")
              (.val (.word nl_w)) s).locals.lookup y := by
      intro y hy
      simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hy, Ne.symm hy]
    have hc2 : (setVarHOLFinite (ofString "stable_log_cap")
        (.val (.word 0x0000000000000001#64))
        (setVarHOLFinite (ofString "stable_log_cap") (.val (.word nl_w)) s)).code
        = s.code := rfl
    have hc8 : evalAt
        (setVarHOLFinite (ofString "stable_log_cap")
          (.val (.word 0x0000000000000001#64))
          (setVarHOLFinite (ofString "stable_log_cap") (.val (.word nl_w)) s))
        (ExpHOL.const 0x0000000000000008#64) =
        some (.val (.word 0x0000000000000008#64)) := rfl
    have hcap1 : evalAt
        (setVarHOLFinite (ofString "stable_log_cap")
          (.val (.word 0x0000000000000001#64))
          (setVarHOLFinite (ofString "stable_log_cap") (.val (.word nl_w)) s))
        (.var .local (ofString "stable_log_cap")) =
        some (.val (.word 0x0000000000000001#64)) := by
      simp only [evalAt, evalHOLExact, toExact, hs2lu]
    have harg := p4Q8_evalList_two
      (setVarHOLFinite (ofString "stable_log_cap")
        (.val (.word 0x0000000000000001#64))
        (setVarHOLFinite (ofString "stable_log_cap") (.val (.word nl_w)) s))
      (.const 0x0000000000000008#64) (.var .local (ofString "stable_log_cap"))
      (.val (.word 0x0000000000000008#64)) (.val (.word 0x0000000000000001#64))
      hc8 hcap1
    refine p4Run_decCall_lst_new hD2 (by rw [hc2]; exact hc)
      (ofString "stable_logs")
      [(.const 0x0000000000000008#64), (.var .local (ofString "stable_log_cap"))]
      (0x0000000000000008#64 : BitVec 64) (0x0000000000000001#64 : BitVec 64) rest
      (by decide) (by decide) (by decide) (by decide)
      (by intro nm hnm
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hnm
          rcases hnm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by decide) (by decide) (by decide) (by decide) harg ?_
    intro lw mid hlw_eq hlw_al hlw_nz hm0 hm8 hm16 hhp_sb hhp_lt hARmid hsp_mid hfmp_mid
      hlst_mid hobjs_mid hDisj_mid hobjs_props hFO_mid hgl_mid hlocm hlocl hchain0 hDmid hcmid
    have hslc : mid.locals.lookup (ofString "stable_log_cap") =
        some (.val (.word 0x0000000000000001#64)) :=
      (hlocl _ (by decide)).trans hs2lu
    have hwout : w_out.toNat + 96 ≤ lw.toNat := by
      rw [hlw_eq]; exact h.out_inside.2
    refine htail (0x0000000000000001#64 : BitVec 64) lw mid (by decide) ?_ (by decide)
      hlw_eq hlw_al hlw_nz hm0 hm8 hm16 hhp_sb hhp_lt hARmid hsp_mid hfmp_mid hlst_mid
      hobjs_mid hDisj_mid hobjs_props hFO_mid hgl_mid hlocm hslc ?_ hwout hchain0 hDmid hcmid
    · rw [hnl0]; simp
    · intro y hy1 hy2
      rw [(hlocl y hy1).trans (hs2fr y hy2), hs1fr y hy2]
  · -- the clamp does not fire: `stable_log_cap` stays `nl`, which is nonzero
    intro b hcond hb
    obtain ⟨a, b', ha, hb', hwif⟩ := evalAt_cmp
      (setVarHOLFinite (ofString "stable_log_cap") (.val (.word nl_w)) s) .equal
      (.var .local (ofString "stable_log_cap"))
      (.const 0x0000000000000000#64) b hcond
    have hb'0 : b' = (0 : BitVec 64) := hB _ hb'
    have ha0 : a = nl_w := hA _ ha
    have hnlne : nl_w ≠ (0 : BitVec 64) := by
      intro hz
      have hcmpt : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal nl_w
          (0 : BitVec 64) = true := by
        simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hz]
      rw [ha0, hb'0, hcmpt] at hwif
      simp at hwif
      simp [hwif] at hb
    have hnlpos : 1 ≤ nl_w.toNat := by
      have hn0 : nl_w.toNat ≠ 0 := by
        intro hc0
        exact hnlne (BitVec.eq_of_toNat_eq (by simpa using hc0))
      omega
    have hc8 : evalAt
        (setVarHOLFinite (ofString "stable_log_cap") (.val (.word nl_w)) s)
        (ExpHOL.const 0x0000000000000008#64) =
        some (.val (.word 0x0000000000000008#64)) := rfl
    have hcapn : evalAt
        (setVarHOLFinite (ofString "stable_log_cap") (.val (.word nl_w)) s)
        (.var .local (ofString "stable_log_cap")) =
        some (.val (.word nl_w)) := by
      simp only [evalAt, evalHOLExact, toExact, hs1lu]
    have harg := p4Q8_evalList_two
      (setVarHOLFinite (ofString "stable_log_cap") (.val (.word nl_w)) s)
      (.const 0x0000000000000008#64) (.var .local (ofString "stable_log_cap"))
      (.val (.word 0x0000000000000008#64)) (.val (.word nl_w)) hc8 hcapn
    have hmul : 8 * nl_w.toNat < 2 ^ 64 := by omega
    refine p4RelRunStrong_skip ?_
    refine p4Run_decCall_lst_new hD1 hc (ofString "stable_logs")
      [(.const 0x0000000000000008#64), (.var .local (ofString "stable_log_cap"))]
      (0x0000000000000008#64 : BitVec 64) nl_w rest
      (by decide) (by decide) (by decide) (by decide)
      (by intro nm hnm
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hnm
          rcases hnm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by decide) hnlpos hmul
      (by rw [show (0x0000000000000008#64 : BitVec 64).toNat = 8 from rfl]; omega) harg ?_
    intro lw mid hlw_eq hlw_al hlw_nz hm0 hm8 hm16 hhp_sb hhp_lt hARmid hsp_mid hfmp_mid
      hlst_mid hobjs_mid hDisj_mid hobjs_props hFO_mid hgl_mid hlocm hlocl hchain0 hDmid hcmid
    have hslc : mid.locals.lookup (ofString "stable_log_cap") =
        some (.val (.word nl_w)) :=
      (hlocl _ (by decide)).trans hs1lu
    have hwout : w_out.toNat + 96 ≤ lw.toNat := by
      rw [hlw_eq]; exact h.out_inside.2
    refine htail nl_w lw mid hnlpos (le_refl _) hmul
      hlw_eq hlw_al hlw_nz hm0 hm8 hm16 hhp_sb hhp_lt hARmid hsp_mid hfmp_mid hlst_mid
      hobjs_mid hDisj_mid hobjs_props hFO_mid hgl_mid hlocm hslc ?_ hwout hchain0 hDmid hcmid
    intro y hy1 hy2
    exact (hlocl y hy1).trans (hs1fr y hy2)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
