import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2BackingPre
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2BackingB

/-!
# Phase 2 backing replay, region B packing bounds (guest spine 49..52)

The clock-budget ladder for the BX-threaded packing loop: the two packed
copies, the inner `j < ns` loop, the record increment, the outer `i < nal`
loop, and the initialized counter prefix. The file closes with the
packed-key allocation resume that establishes the glue conjunct, and the
segment bound for `spinePlug 4 (spineAt 49 ptxCode) tail`.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R13Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards

/-! ## The inner-body and inner-loop bounds -/

/-- Two copies and the two clock-neutral counter assignments give the exact
active inner-body budget used by the source Phase 2 cost. -/
theorem ptxPhase2B_bodyBX_bound (h : PtxCallees) (addressSrc keySrc : ExpHOL 64) :
    TerminatingProgBoundedOn (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s)
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "al_keys"),
            .panop .mul [.var .local (ofString "k"), .const 52]], addressSrc, .const 20])
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "al_keys"),
              .panop .mul [.var .local (ofString "k"), .const 52], .const 20], keySrc, .const 32])
          (.seq
            (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
            (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))))
      ((K.memcpy + 1) + (K.memcpy + 1)) := by
  have hc : TerminatingProgBoundedOn (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s)
      (.seq
        (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
        (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1]))) 0 := by
    intro F s hcode hp hn
    have he := phase2_clock_seq
      (fun t => clock_assign t .local (ofString "k")
        (.op .add [.var .local (ofString "k"), .const 1]))
      (fun t => clock_assign t .local (ofString "j")
        (.op .add [.var .local (ofString "j"), .const 1])) s
    rw [he]
    exact ⟨by omega, le_rfl⟩
  intro F s hcode hp
  simpa only [Nat.add_zero] using seq_bound_trans
    (fun t hct hpt => phase2_packed_ns_nal_memcpy_bound h _ t hct hpt.2)
    (ptxPhase2BX_packed_address_copy_hoare h addressSrc)
    (fun t ht hpt => seq_bound_trans
      (fun t' hct' hpt' => phase2_packed_ns_nal_memcpy_bound h _ t' hct' hpt'.2)
      (ptxPhase2BX_packed_storage_copy_hoare h keySrc) hc t ht hpt) s hcode hp

/-- The cached-count inner loop has a uniform rank bound once its active body
bound is supplied; the rank is the remaining signed counter range. -/
theorem ptxPhase2B_innerWhileBX_bound {body : ProgHOL 64} {B : Nat}
    (hb : Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s) body
      (fun r s => r = none → ptxPhase2BX s ∧ PtxPackedNsNalIteration s))
    (hbody : TerminatingProgBoundedOn (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s) body B)
    (hinc : IncrBody (ofString "j") body) :
    TerminatingProgBoundedOn (fun s => ptxPhase2BX s ∧ PtxPackedNsNalIteration s)
      (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "ns"))) body)
      ((2 ^ 63 + 1) * (B + 1)) := by
  apply TerminatingProgBoundedOn.while_rank_active (fun s => 2 ^ 63 - locN s "j")
  · intro F s hp
    exact ⟨ptxPhase2BX_decClock s hp.1,
      ⟨phase2_packed_ns_iteration_decClock s hp.2.1, hp.2.2⟩⟩
  · intro F s hc hp
    obtain ⟨w, hw, hnz⟩ := hp.2
    have hg := (phase2_packed_ns_guard_eval s w hp.1.2.1 hw).mp hnz
    exact hbody s hc ⟨hp.1.1,
      ⟨⟨phase2_packed_iteration_guard_pre s hp.1.2.1.1 hg, hp.1.2.1.2⟩, hp.1.2.2⟩⟩
  · intro F s hc hp ha
    omega
  · intro F s hc hp ha hf
    obtain ⟨w, hw, hnz⟩ := ha
    have hg := (phase2_packed_ns_guard_eval s w hp.2.1 hw).mp hnz
    have hd : ptxPhase2BX (decClockHOLFinite s) ∧ PtxPackedNsNalIteration
        (decClockHOLFinite s) :=
      ⟨ptxPhase2BX_decClock s hp.1,
        ⟨phase2_packed_ns_iteration_decClock s hp.2.1, hp.2.2⟩⟩
    obtain ⟨j, hj⟩ := hp.2.1.1.2.2.2.1
    obtain ⟨hnc, hnext⟩ := hinc.run (decClockHOLFinite s) j hj
    have hnone := hf.resolve_right hnc
    have hpost := hb.run (decClockHOLFinite s) hc
      ⟨ptxPhase2BX_decClock s hp.1,
        ⟨⟨phase2_packed_iteration_guard_pre _ hd.2.1.1 hg, hd.2.1.2⟩, hd.2.2⟩⟩
      (by rw [hnone]; simp) hnone
    refine ⟨hpost, ?_⟩
    have hjn : locN s "j" = j.toNat := by simp [locN, hj]
    have hlt := (phase2_packed_inner_signed_bounds hp.2.1.1.2.1.1).1
    have hpl := (phase2_packed_inner_signed_bounds hpost.2.1.1.2.1.1).1
    have hpn : locN (evaluateHOLFiniteState (decClockHOLFinite s) body).2 "j" =
        (j.toNat + 1) % 2 ^ 64 := by
      simp [locN, hnext hnone, BitVec.toNat_add]
    rw [hjn] at hlt ⊢
    rw [hpn]
    have hmod : (j.toNat + 1) % 2 ^ 64 = j.toNat + 1 := Nat.mod_eq_of_lt (by omega)
    rw [hmod] at *
    omega

/-- The actual source inner loop and following record increment have the
advertised nested-loop clock budget. -/
theorem ptxPhase2B_innerTailBX_bound (h : PtxCallees) :
    TerminatingProgBoundedOn (fun s => ptxPhase2BX s ∧ PtxPackedNsNalIteration s)
      phase2_packed_source_inner_tail
      ((2 ^ 63 + 1) * ((K.memcpy + 1) + (K.memcpy + 1) + 1)) := by
  unfold phase2_packed_source_inner_tail
  have hb : TerminatingProgBoundedOn (fun s => ptxPhase2BX s ∧ PtxPackedNsNalIteration s) _
      ((2 ^ 63 + 1) * ((K.memcpy + 1) + (K.memcpy + 1) + 1)) :=
    ptxPhase2B_innerWhileBX_bound
      (ptxPhase2B_bodyBX_hoare h
        (.load .one (.op .add [.var .local (ofString "acc2"), .const 0]))
        (.op .add [.load .one (.op .add [.var .local (ofString "acc2"), .const 8]),
          .panop .mul [.var .local (ofString "j"), .const 32]]))
      (ptxPhase2B_bodyBX_bound h
        (.load .one (.op .add [.var .local (ofString "acc2"), .const 0]))
        (.op .add [.load .one (.op .add [.var .local (ofString "acc2"), .const 8]),
          .panop .mul [.var .local (ofString "j"), .const 32]]))
      (by ptx_incr)
  have ht : TerminatingProgBoundedOn
      (fun s => ptxPhase2BX s ∧ PtxPackedNsNalIteration s ∧
        locN s "k" = phase2_key_prefix s (locN s "i" + 1))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])) 0 := by
    intro F s hc hp hn
    rw [clock_assign]
    exact ⟨by omega, le_rfl⟩
  intro F s hc hp
  simpa only [Nat.add_zero] using seq_bound_trans hb
    (ptxPhase2B_innerWhileBX_hoare
      (ptxPhase2B_bodyBX_hoare h
        (.load .one (.op .add [.var .local (ofString "acc2"), .const 0]))
        (.op .add [.load .one (.op .add [.var .local (ofString "acc2"), .const 8]),
          .panop .mul [.var .local (ofString "j"), .const 32]]))
      (by decide) (by decide)) ht s hc hp

/-- The record-local declarations preserve the inner-loop clock budget. -/
theorem ptxPhase2B_outerBodyBX_bound (h : PtxCallees) :
    TerminatingProgBoundedOn (fun s => ptxPhase2BX s ∧ PtxPackedNalIteration s ∧
      locN s "i" < memW s (locN s "tx" + 216)) phase2_packed_source_outer_body
      ((2 ^ 63 + 1) * ((K.memcpy + 1) + (K.memcpy + 1) + 1)) := by
  unfold phase2_packed_source_outer_body
  apply dec_bound_trans (Q := fun s => ptxPhase2BX s ∧ PtxPackedNalIteration s ∧
    locN s "i" < memW s (locN s "tx" + 216) ∧
    locN s "acc2" = memW s (locN s "tx" + 208) + 24 * locN s "i")
  · intro F s v hp he
    have hd := phase2_packed_outer_declare_acc2 s hp.2.1.1 hp.2.2 v he
    exact ⟨ptxPhase2BX_setVar_scratch s v (ofString "acc2") hp.1
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
      phase2_packed_nal_set_other s hp.2.1 _ _ (by decide), hd.2⟩
  · apply dec_bound_trans (Q := fun s => ptxPhase2BX s ∧ PtxPackedNalIteration s ∧
      locN s "i" < memW s (locN s "tx" + 216) ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "ns") = some (.val (.word n))) ∧
      locN s "ns" = memW s (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16))
    · intro F s v hp he
      have hd := phase2_packed_outer_declare_ns s hp.2.1.1 hp.2.2.1 hp.2.2.2 v he
      exact ⟨ptxPhase2BX_setVar_scratch s v (ofString "ns") hp.1
          (Or.inr (Or.inr (Or.inr (Or.inr rfl)))),
        phase2_packed_nal_set_other s hp.2.1 _ _ (by decide), hd.2⟩
    · apply dec_bound_trans (Q := fun s =>
        ptxPhase2BX s ∧ PtxPackedNsNalIteration s)
      · intro F s v hp he
        have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using he.symm
        subst v
        exact ⟨ptxPhase2BX_setVar_scratch s (.val (.word 0)) (ofString "j") hp.1
            (Or.inr (Or.inl rfl)),
          phase2_packed_ns_reset s hp.2.1.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2,
          (phase2_packed_nal_set_other s hp.2.1 (ofString "j") (.val (.word 0))
            (by decide)).2⟩
      · exact ptxPhase2B_innerTailBX_bound h

/-- A decreasing record counter bounds the concrete outer packing loop. -/
theorem ptxPhase2B_outerWhileBX_bound (h : PtxCallees) :
    TerminatingProgBoundedOn (fun s => ptxPhase2BX s ∧ PtxPackedNalIteration s)
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
        phase2_packed_source_outer_body)
      ((2 ^ 63 + 1) * ((2 ^ 63 + 1) * ((K.memcpy + 1) + (K.memcpy + 1) + 1) + 1)) := by
  apply TerminatingProgBoundedOn.while_rank_active (fun s => 2 ^ 63 - locN s "i")
  · intro F s hp
    exact ⟨ptxPhase2BX_decClock s hp.1, phase2_packed_nal_iteration_decClock s hp.2⟩
  · intro F s hc hp
    obtain ⟨w, hw, hnz⟩ := hp.2
    have hg := (phase2_packed_outer_nal_guard s w hp.1.2.1 hp.1.2.2.1 hp.1.2.2.2 hw).mp hnz
    exact ptxPhase2B_outerBodyBX_bound h s hc ⟨hp.1.1, hp.1.2, hg⟩
  · intro F s hc hp ha
    omega
  · intro F s hc hp ha hf
    obtain ⟨w, hw, hnz⟩ := ha
    have hg := (phase2_packed_outer_nal_guard s w hp.2.1 hp.2.2.1 hp.2.2.2 hw).mp hnz
    have hd := phase2_packed_nal_iteration_decClock s hp.2
    have hinc : IncrBody (ofString "i") phase2_packed_source_outer_body := by
      unfold phase2_packed_source_outer_body phase2_packed_source_inner_tail
      ptx_incr
    obtain ⟨i, hi⟩ := hp.2.1.2.2.2.2.2.1
    obtain ⟨hnc, hnext⟩ := hinc.run (decClockHOLFinite s) i hi
    have hnone := hf.resolve_right hnc
    have hpost := (ptxPhase2B_outerBodyBX_hoare h).run
      (decClockHOLFinite s) hc ⟨ptxPhase2BX_decClock s hp.1, hd, hg⟩
      (by rw [hnone]; simp) hnone
    refine ⟨hpost, ?_⟩
    have hin : locN s "i" = i.toNat := by simp [locN, hi]
    have hlt := (phase2_packed_outer_signed_bounds hp.2.1).1
    have hpn : locN (evaluateHOLFiniteState (decClockHOLFinite s)
        phase2_packed_source_outer_body).2 "i" = (i.toNat + 1) % 2 ^ 64 := by
      simp [locN, hnext hnone, BitVec.toNat_add]
    rw [hin] at hlt ⊢
    rw [hpn, Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 64)]
    omega

/-! ## The initialized counter prefix -/

/-- The source packing loop discharges into the packed-keys readiness with the
glue conjunct, on both the enabled and the disabled branch. -/
theorem ptxPhase2B_packedWhileX_hoare (h : PtxCallees) :
    Hoare (fun s => (ptxPhase2BX s ∧ PtxPackedNalIteration s) ∨
        (ptxPhase2BX s ∧ PtxPackedKeysReady s ∧
          s.locals.lookup (ofString "i") = some (.val (.word 0)) ∧
          s.locals.lookup (ofString "nal") = some (.val (.word 0))))
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
        phase2_packed_source_outer_body)
      (fun r s => r = none → ptxPhase2BX s ∧ PtxPackedKeysReady s) := by
  refine ⟨fun {F} s hc hp hnt hr => ?_⟩
  rcases hp with hp | hp
  · have hout := (ptxPhase2B_outerWhileBX_hoare h).run s hc hp hnt hr
    exact ⟨hout.1, hout.2.1.1.2.1.1⟩
  · rw [phase2_zero_nal_loop s phase2_packed_source_outer_body hp.2.2.1 hp.2.2.2]
    exact ⟨hp.1, hp.2.1⟩

/-- Counter initialization, either packing branch, and the trailing statements
inside the declaration share the concrete packing-loop budget. -/
theorem ptxPhase2B_packedInitTailX_bound (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn (fun s => ptxPhase2BX s ∧ PtxPackedKeysReady s) tail b) :
    TerminatingProgBoundedOn (fun s => ptxPhase2BX s ∧ PtxPackedInitCases s)
      (.dec (ofString "k") .one (.const 0)
        (.seq (.assign .local (ofString "i") (.const 0))
          (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
            phase2_packed_source_outer_body) tail)))
      ((2 ^ 63 + 1) * ((2 ^ 63 + 1) * ((K.memcpy + 1) + (K.memcpy + 1) + 1) + 1) + b) := by
  apply dec_bound_trans (Q := fun s =>
    ∃ before, (ptxPhase2BX before ∧ PtxPackedInitCases before) ∧
      s = setVarHOLFinite (ofString "k") (.val (.word 0)) before)
  · intro F s v hp he
    have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using he.symm
    subst v
    exact ⟨s, hp, rfl⟩
  · have ha : Hoare (fun s => ∃ before, (ptxPhase2BX before ∧ PtxPackedInitCases before) ∧
        s = setVarHOLFinite (ofString "k") (.val (.word 0)) before)
      (.assign .local (ofString "i") (.const 0))
      (fun r s => r = none → (ptxPhase2BX s ∧ PtxPackedNalIteration s) ∨
        (ptxPhase2BX s ∧ PtxPackedKeysReady s ∧
          s.locals.lookup (ofString "i") = some (.val (.word 0)) ∧
          s.locals.lookup (ofString "nal") = some (.val (.word 0)))) := by
      apply Hoare.assign
      · intro F s v hp he
        obtain ⟨before, hp, rfl⟩ := hp
        have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using he.symm
        subst v
        intro _
        have hbx : ptxPhase2BX (setVarHOLFinite (ofString "k") (.val (.word 0)) before) :=
          ptxPhase2BX_setVar_scratch before (.val (.word 0)) (ofString "k") hp.1
            (Or.inl rfl)
        rcases hp.2 with hp | hp
        · exact Or.inl ⟨ptxPhase2BX_setVar_scratch _ (.val (.word 0)) (ofString "i") hbx
            (Or.inr (Or.inr (Or.inl rfl))), phase2_packed_init_state before hp⟩
        · exact Or.inr ⟨ptxPhase2BX_setVar_scratch _ (.val (.word 0)) (ofString "i") hbx
            (Or.inr (Or.inr (Or.inl rfl))), phase2_packed_zero_init before hp.1 hp.2⟩
      · exact fun _ _ hr => by cases hr
    have hb : TerminatingProgBoundedOn
        (fun s => ∃ before, (ptxPhase2BX before ∧ PtxPackedInitCases before) ∧
          s = setVarHOLFinite (ofString "k") (.val (.word 0)) before)
        (.assign .local (ofString "i") (.const 0)) 0 := by
      intro F s hc hp hn
      rw [clock_assign]
      exact ⟨by omega, le_rfl⟩
    have hl : TerminatingProgBoundedOn
        (fun s => (ptxPhase2BX s ∧ PtxPackedNalIteration s) ∨
          (ptxPhase2BX s ∧ PtxPackedKeysReady s ∧
            s.locals.lookup (ofString "i") = some (.val (.word 0)) ∧
            s.locals.lookup (ofString "nal") = some (.val (.word 0))))
        (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
          phase2_packed_source_outer_body)
        ((2 ^ 63 + 1) * ((2 ^ 63 + 1) * ((K.memcpy + 1) + (K.memcpy + 1) + 1) + 1)) := by
      intro F s hc hp hn
      rcases hp with hp | hp
      · exact ptxPhase2B_outerWhileBX_bound h s hc hp hn
      · rw [phase2_zero_nal_loop s phase2_packed_source_outer_body hp.2.2.1 hp.2.2.2]
        exact ⟨by dsimp; omega, le_rfl⟩
    have hinner : TerminatingProgBoundedOn
        (fun s => (ptxPhase2BX s ∧ PtxPackedNalIteration s) ∨
          (ptxPhase2BX s ∧ PtxPackedKeysReady s ∧
            s.locals.lookup (ofString "i") = some (.val (.word 0)) ∧
            s.locals.lookup (ofString "nal") = some (.val (.word 0))))
        (.seq (.while (.cmp .less (.var .local (ofString "i"))
            (.var .local (ofString "nal"))) phase2_packed_source_outer_body) tail)
        ((2 ^ 63 + 1) * ((2 ^ 63 + 1) * ((K.memcpy + 1) + (K.memcpy + 1) + 1) + 1) + b) := by
      intro F s hc hp hn
      exact seq_bound_trans hl (ptxPhase2B_packedWhileX_hoare h) ht s hc hp hn
    intro F s hc hp
    simpa only [Nat.zero_add] using seq_bound_trans hb ha hinner s hc hp

/-! ## The packed-key allocation resume -/

/-- Resuming after the packed-key allocation with the glue conjunct: the
callee leaves memory and every non-`heap_ptr` global untouched, the frozen
resume supplies the initialization cases, and the fresh buffer is disjoint
from the block-out record. -/
theorem ptxPhase2B_alKeysBX_resume (h : PtxCallees) :
    DecCallResumeOn (fun s => PtxAddressCountExit s ∧ PtxPhase2X s)
      (fun s => ptxPhase2BX s ∧ PtxPackedInitCases s) (ofString "al_keys") (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hi := phase2_count_cases_alloc_init h s vs body callee ret v post hc hp.1 ha hl hb
  have hbody : body = InitECandidate.Solver.GuestTrapAndLookup.sourceFnBody
      Guest.Software.guestFn_alloc :=
    InitECandidate.Solver.PanRunBounded.lookupCodeHOLFinite_installed_body s.code.lookup
      (ofString "alloc") [(ofString "n", .one)]
      (InitECandidate.Solver.GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_alloc) body
      .one ret vs callee
      (by rw [hc]; exact InitECandidate.Solver.GuestTrapAndLookup.lookup_alloc) hl
  rw [hbody] at hb
  obtain ⟨w0, hen, hsize, -⟩ := phase2_count_cases_alloc_eval s hp.1
  have hpc := R16Shards.callee_param_one_exp s (ofString "alloc") (ofString "n") .one
    (InitECandidate.Solver.GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_alloc) .one
    (by rw [hc]; exact InitECandidate.Solver.GuestTrapAndLookup.lookup_alloc)
    (.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8])
    (.val (.word w0)) vs body callee ret hen ha hl
  have hnloc : (callEntryStateHOLFinite s callee).locals.lookup (ofString "n") =
      some (.val (.word w0)) := hpc.2
  have hr := phase2_count_exit_access_ready hp.1
  have hA' : ArenaReady (callEntryStateHOLFinite s callee) :=
    (arenaReady_with_locals s callee (s.clock - 1)).mpr hr.1.1.1.1.1.1.1.1
  obtain ⟨hpw, hhp⟩ := hA'.2.2.2.2.2.2.2.2.2 "heap_ptr" (by simp [guestGlobalNames])
  have hcode' : (callEntryStateHOLFinite s callee).code = originalRuntimeCode := hc
  have hout1 : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (InitECandidate.Solver.GuestTrapAndLookup.sourceFnBody
        Guest.Software.guestFn_alloc)).1 = some (.returned v) := by rw [hb]
  obtain ⟨-, -, -, hEq⟩ := InitECandidate.Solver.Wave8Contracts.M27.alloc_body_run
    (callEntryStateHOLFinite s callee) hpw w0 hcode' hhp hnloc v hout1
  have hpost : post = (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (InitECandidate.Solver.GuestTrapAndLookup.sourceFnBody
        Guest.Software.guestFn_alloc)).2 := by rw [hb]
  have hmemF : ∀ a, post.memory a = s.memory a := by
    intro a
    rw [hpost, hEq]
    rfl
  have hgl (m : MlS) (hm : m ≠ ofString "heap_ptr") :
      post.globals.lookup m = s.globals.lookup m := by
    rw [hpost, hEq]
    have hentry : (callEntryStateHOLFinite s callee).globals = s.globals := rfl
    rw [hentry]
    show (s.globals.update (ofString "heap_ptr", _)).lookup m = s.globals.lookup m
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hm.symm]
  have hboG : globN post "bo" = globN s "bo" := by
    unfold globN
    rw [hgl (ofString "bo") (by decide)]
  have hjcG : globN post "journal_cap" = globN s "journal_cap" := by
    unfold globN
    rw [hgl (ofString "journal_cap") (by decide)]
  have htxPost : TxBacking {post with locals := s.locals} :=
    ptxPhase2_txBacking_of_mem_eq hp.2.2.1 hboG hmemF
  have hX : PtxPhase2X {post with locals := s.locals} := by
    refine ptxPhase2X_of_cells hp.2 htxPost rfl hboG hjcG rfl ?_
    intro k hk
    unfold memW
    rw [hmemF]
  have hX' : PtxPhase2X
      (setVarHOLFinite (ofString "al_keys") v {post with locals := s.locals}) :=
    ptxPhase2X_setVar_other _ v (by
      intro n hn
      simp only [ptxPhase2XNames, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) hX
  have hkeys : PtxPackedKeysReady
      (setVarHOLFinite (ofString "al_keys") v {post with locals := s.locals}) := by
    rcases hi with hi | hi
    · exact hi.2.1
    · exact hi.1
  obtain ⟨S, Nd, hW, hT, hd⟩ := hkeys.2.2.2.2
  have hnz : globN (setVarHOLFinite (ofString "al_keys") v {post with locals := s.locals})
      "bo" ≠ 0 := hX'.2.2.1.bo_nz
  have hbo_mem : (globN (setVarHOLFinite (ofString "al_keys") v
        {post with locals := s.locals}) "bo", 88) ∈
      worldOwned (setVarHOLFinite (ofString "al_keys") v {post with locals := s.locals}) S Nd := by
    have hm := typedRecord_mem_fixedObjects
      (setVarHOLFinite (ofString "al_keys") v {post with locals := s.locals})
      (r := ("bo", 88)) (by decide)
    simp only [hnz, ↓reduceIte] at hm
    simp only [worldOwned, List.mem_append]
    exact Or.inl (Or.inr hm)
  refine ⟨⟨hX', hnz, ?_⟩, hi⟩
  rcases hd (locN (setVarHOLFinite (ofString "al_keys") v
        {post with locals := s.locals}) "al_keys",
      (locN (setVarHOLFinite (ofString "al_keys") v
        {post with locals := s.locals}) "nkeys" * 52 + 8 + 7) / 8 * 8) (by simp)
    (globN (setVarHOLFinite (ofString "al_keys") v {post with locals := s.locals}) "bo", 88)
    hbo_mem with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

/-! ## Region B segment bound (guest spine 49..52) -/

/-- The packed-key allocation and packing loop compose with the tail. -/
theorem ptxPhase2B_packedX_bound (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn (fun s => ptxPhase2BX s ∧ PtxPackedKeysReady s) tail b) :
    TerminatingProgBoundedOn (fun s => PtxAddressCountExit s ∧ PtxPhase2X s)
      (spinePlug 4 (spineAt 49 ptxCode) tail)
      (K.alloc + ((2 ^ 63 + 1) * ((2 ^ 63 + 1) *
        ((K.memcpy + 1) + (K.memcpy + 1) + 1) + 1) + b) + 1) := by
  have he : spinePlug 4 (spineAt 49 ptxCode) tail =
      .decCall (ofString "al_keys") .one (ofString "alloc")
        [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]]
        (.dec (ofString "k") .one (.const 0)
          (.seq (.assign .local (ofString "i") (.const 0))
            (.seq (.while (.cmp .less (.var .local (ofString "i"))
              (.var .local (ofString "nal"))) phase2_packed_source_outer_body) tail))) := by
    simp only [ptxCode, sourceFunctionEntry, Guest.Software.guestFn_process_transaction,
      spineAt, spinePlug]
    rfl
  rw [he]
  apply TerminatingProgBoundedOn.decCall_on
    (Q := fun s => ptxPhase2BX s ∧ PtxPackedInitCases s) h.fb_alloc
  · intro F s vs body callee ret hc hp ha hl
    have hr := phase2_count_exit_access_ready hp.1
    exact guestInv_callEntry s callee hr.1.1.1.1.1.1.1.1.1
  · exact ptxPhase2B_alKeysBX_resume h
  · exact ptxPhase2B_packedInitTailX_bound h ht

end InitECandidate.Solver.Wave8GuestInv.R13Shards
