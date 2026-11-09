import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2BackingC

/-!
# Phase 2 backing replay, region D (guest spine 49..53, strengthened exit)

Region D replays the packed-key allocation and packing loop of region B, but
threads a strictly stronger invariant: alongside the auxiliary conjunct
`ptxPhase2BX` it carries a single-witness live frame for the three buffers
that must survive into region C (the transaction image `te`, the access-list
address array `al_addrs`, and the transaction header `tx`), together with
the scalar witnesses region C needs. The strengthened exit assembles
`ptxPhase2CRInv` (the region-C entry invariant, i.e. `PtxTeSufInv` without
the sender witness, which the Phase 1 caller frame supplies instead).
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

/-! ## The region-C entry invariant -/

/-- Region C of the Phase 2 spine starts at guest position 53 with the
packed-key loop finished. The invariant is `PtxTeSufInv` without the
sender witness: that witness is not recoverable at this cut and is
supplied by the Phase 1 caller frame instead. -/
def ptxPhase2CRInv {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxAccessCountReady s ∧
    (∃ w : BitVec 64, s.locals.lookup (ofString "nkeys") = some (.val (.word w))) ∧
    (∃ w : BitVec 64, s.locals.lookup (ofString "al_keys") = some (.val (.word w))) ∧
    (∃ w : BitVec 64, s.locals.lookup (ofString "al_addrs") = some (.val (.word w))) ∧
    PtxTeSufWitness s (locN s "al_addrs", (locN s "nal" + 1) * 8) ∧
    Inside (locN s "al_addrs", (locN s "nal" + 1) * 8) InitE.sourceBase (globN s "heap_ptr")

/-! ## The retained-buffer family -/

/-- The live frame carried through the packing loop: the transaction image
`te`, the access-list address array `al_addrs`, and the transaction header
`tx`, all under a single world/ownership witness anchored at the values
`E`, `T`, `A`, `N` of the corresponding locals. -/
def ptxPhase2DFam {F : Type} (contents : Nat → BitVec 64) (E T A N : Nat)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  locN s "te" = E ∧ locN s "tx" = T ∧ locN s "al_addrs" = A ∧ locN s "nal" = N ∧
    ∃ S Nd, WorldTypedWith s S Nd ∧ TxAccessListAt s S Nd T ∧
      PtxLiveBufferAt s S Nd (E, 200) contents ∧
      PtxLiveBufferAt s S Nd (A, (N + 1) * 8) contents ∧
      PtxLiveBufferAt s S Nd (T, 384) contents ∧
      Disj (T, 384) (E, 200)

/-- The packed-key allocation region retained by the loop. -/
def ptxPhase2DKeysRegion {F : Type} (s : PanSemStateFiniteExact 64 F) : Ivl :=
  (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)

/-- The full region-D family conjunct: the live frame plus the separation
of every retained buffer from the packed-key region. -/
def ptxPhase2DFull {F : Type} (contents : Nat → BitVec 64) (E T A N : Nat)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  ptxPhase2DFam contents E T A N s ∧
    Disj (E, 200) (ptxPhase2DKeysRegion s) ∧
    Disj (A, (N + 1) * 8) (ptxPhase2DKeysRegion s) ∧
    Disj (T, 384) (ptxPhase2DKeysRegion s)

/-- The family conjunct as carried through the packing loop: additionally
to the entry family, the packed-key region is disjoint from the world
ownership of the very same joint witness. -/
def ptxPhase2DFamR {F : Type} (contents : Nat → BitVec 64) (E T A N : Nat)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  locN s "te" = E ∧ locN s "tx" = T ∧ locN s "al_addrs" = A ∧ locN s "nal" = N ∧
    ∃ S Nd, WorldTypedWith s S Nd ∧ TxAccessListAt s S Nd T ∧
      PtxLiveBufferAt s S Nd (E, 200) contents ∧
      PtxLiveBufferAt s S Nd (A, (N + 1) * 8) contents ∧
      PtxLiveBufferAt s S Nd (T, 384) contents ∧
      Disj (T, 384) (E, 200) ∧
      IvlsDisj [ptxPhase2DKeysRegion s] (worldOwned s S Nd)

/-- The full region-D family conjunct through the packing loop. -/
def ptxPhase2DFullR {F : Type} (contents : Nat → BitVec 64) (E T A N : Nat)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  ptxPhase2DFamR contents E T A N s ∧
    Disj (E, 200) (ptxPhase2DKeysRegion s) ∧
    Disj (A, (N + 1) * 8) (ptxPhase2DKeysRegion s) ∧
    Disj (T, 384) (ptxPhase2DKeysRegion s)

/-- The scalar witnesses threaded alongside the family. -/
def ptxPhase2DScal {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  (∃ w : BitVec 64, s.locals.lookup (ofString "te") = some (.val (.word w))) ∧
    (∃ w : BitVec 64, s.locals.lookup (ofString "nal") = some (.val (.word w))) ∧
    (∃ w : BitVec 64, s.locals.lookup (ofString "nkeys") = some (.val (.word w))) ∧
    (∃ w : BitVec 64, s.locals.lookup (ofString "al_addrs") = some (.val (.word w))) ∧
    locN s "te" % 8 = 0

/-! ## The family at the cut -/

/-- The address-count exit provides the full retained family under its
single joint witness: the te and address buffers are snapshotted from the
address-joint, and the transaction header from its access-list witness. -/
theorem ptxPhase2D_fam_entry {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressCountExit s) :
    ptxPhase2DFam (phase2_saved_word s) (locN s "te") (locN s "tx")
      (locN s "al_addrs") (locN s "nal") s := by
  have hj := phase2_count_exit_joint hp
  have hr := phase2_count_exit_access_ready hp
  obtain ⟨hl, S₀, Nd₀, hW₀, hT₀, hd₀, htx₀, -⟩ := hr.1
  obtain ⟨S, Nd, hw, ht, hda, hde⟩ := hj.2
  refine ⟨rfl, rfl, rfl, rfl, S, Nd, hw, ht, ?_, ?_, ?_, ?_⟩
  · exact phase2_live_buffer_snapshot s S Nd _ hl.2.2.1 hde
  · exact phase2_live_buffer_snapshot s S Nd _ hj.1.2.2.1 hda
  · exact phase2_live_buffer_snapshot s S Nd _ ht.1.2.1 ht.2.1
  · exact htx₀

/-- The scalar witnesses are available at the cut. -/
theorem ptxPhase2D_scal_entry {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressCountExit s) : ptxPhase2DScal s := by
  have hj := phase2_count_exit_joint hp
  have hr := phase2_count_exit_access_ready hp
  refine ⟨hr.1.1.2.1, hr.2.1, ?_, hj.1.2.1, hr.1.1.2.2.2.1⟩
  rcases hp with hp | hp
  · exact hp.1.1.2.2.1
  · exact hp.1.2.2.1

/-! ## Locals and clock independence -/

/-- The anchor names of the scalar conjunct (and the family's anchors). -/
def ptxPhase2DNames : List String :=
  ["te", "tx", "al_addrs", "nal", "nkeys"]

/-- The full family conjunct transfers along a locals substitution that
preserves the anchor names and the packed-key locals. -/
theorem ptxPhase2D_full_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (hl : ∀ n ∈ ptxPhase2DNames, locals.lookup (ofString n) =
      s.locals.lookup (ofString n))
    (halk : locals.lookup (ofString "al_keys") = s.locals.lookup (ofString "al_keys"))
    {contents : Nat → BitVec 64} {E T A N : Nat}
    (hp : ptxPhase2DFull contents E T A N s) :
    ptxPhase2DFull contents E T A N {s with locals := locals, clock := clock} := by
  have hte := hl "te" (by simp [ptxPhase2DNames])
  have htx := hl "tx" (by simp [ptxPhase2DNames])
  have hta := hl "al_addrs" (by simp [ptxPhase2DNames])
  have htn := hl "nal" (by simp [ptxPhase2DNames])
  have hnk := hl "nkeys" (by simp [ptxPhase2DNames])
  obtain ⟨⟨he, hx, ha, hn, S, Nd, hw, ht, hb1, hb2, hb3, hd⟩, h1, h2, h3⟩ := hp
  have halk' : locN {s with locals := locals, clock := clock} "al_keys" =
      locN s "al_keys" := locN_congr s locals clock "al_keys" halk
  have hnk' : locN {s with locals := locals, clock := clock} "nkeys" =
      locN s "nkeys" := locN_congr s locals clock "nkeys" hnk
  refine ⟨⟨?_, ?_, ?_, ?_, S, Nd,
    (worldTypedWith_with_locals s locals clock S Nd).mpr hw,
    R16Shards.PtxP1.txAccessListAt_with_locals s locals clock ht,
    (phase2_live_buffer_with_locals s locals clock S Nd (E, 200) contents).mpr hb1,
    (phase2_live_buffer_with_locals s locals clock S Nd (A, (N + 1) * 8) contents).mpr hb2,
    (phase2_live_buffer_with_locals s locals clock S Nd (T, 384) contents).mpr hb3,
    hd⟩, ?_, ?_, ?_⟩
  · rw [locN_congr s locals clock "te" hte]; exact he
  · rw [locN_congr s locals clock "tx" htx]; exact hx
  · rw [locN_congr s locals clock "al_addrs" hta]; exact ha
  · rw [locN_congr s locals clock "nal" htn]; exact hn
  · simp only [ptxPhase2DKeysRegion, halk', hnk']; exact h1
  · simp only [ptxPhase2DKeysRegion, halk', hnk']; exact h2
  · simp only [ptxPhase2DKeysRegion, halk', hnk']; exact h3

/-- The scalar conjunct transfers along a locals substitution that
preserves the anchor names. -/
theorem ptxPhase2D_scal_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (hl : ∀ n ∈ ptxPhase2DNames, locals.lookup (ofString n) =
      s.locals.lookup (ofString n))
    (hp : ptxPhase2DScal s) :
    ptxPhase2DScal {s with locals := locals, clock := clock} := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨w, h⟩ := hp.1
    exact ⟨w, by rw [hl "te" (by simp [ptxPhase2DNames])]; exact h⟩
  · obtain ⟨w, h⟩ := hp.2.1
    exact ⟨w, by rw [hl "nal" (by simp [ptxPhase2DNames])]; exact h⟩
  · obtain ⟨w, h⟩ := hp.2.2.1
    exact ⟨w, by rw [hl "nkeys" (by simp [ptxPhase2DNames])]; exact h⟩
  · obtain ⟨w, h⟩ := hp.2.2.2.1
    exact ⟨w, by rw [hl "al_addrs" (by simp [ptxPhase2DNames])]; exact h⟩
  · rw [locN_congr s locals clock "te" (hl "te" (by simp [ptxPhase2DNames]))]
    exact hp.2.2.2.2

/-- The family conjunct survives a clock decrement. -/
theorem ptxPhase2D_full_decClock {F : Type} {contents : Nat → BitVec 64}
    {E T A N : Nat} {s : PanSemStateFiniteExact 64 F}
    (hp : ptxPhase2DFull contents E T A N s) :
    ptxPhase2DFull contents E T A N (decClockHOLFinite s) :=
  ptxPhase2D_full_with_locals s (decClockHOLFinite s).locals (s.clock - 1)
    (by intros; rfl) (by rfl) hp

/-- The scalar conjunct survives a clock decrement. -/
theorem ptxPhase2D_scal_decClock {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : ptxPhase2DScal s) : ptxPhase2DScal (decClockHOLFinite s) :=
  ptxPhase2D_scal_with_locals s (decClockHOLFinite s).locals (s.clock - 1)
    (by intros; rfl) hp

/-- The family conjunct survives a local assignment it does not mention. -/
theorem ptxPhase2D_full_setVar_other {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) (name : MlS)
    (hne : ∀ n ∈ ptxPhase2DNames, ofString n ≠ name)
    (hne' : ofString "al_keys" ≠ name)
    {contents : Nat → BitVec 64} {E T A N : Nat}
    (hp : ptxPhase2DFull contents E T A N s) :
    ptxPhase2DFull contents E T A N (setVarHOLFinite name v s) := by
  refine ptxPhase2D_full_with_locals s (s.locals.update (name, v)) s.clock ?_ ?_ hp
  · intro n hn
    simp [HolFiniteMapExact.update, FUPDATE,
      show name ≠ ofString n from (hne n hn).symm]
  · simp [HolFiniteMapExact.update, FUPDATE,
      show name ≠ ofString "al_keys" from hne'.symm]

/-- The scalar conjunct survives a local assignment it does not mention. -/
theorem ptxPhase2D_scal_setVar_other {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) (name : MlS)
    (hne : ∀ n ∈ ptxPhase2DNames, ofString n ≠ name)
    (hp : ptxPhase2DScal s) :
    ptxPhase2DScal (setVarHOLFinite name v s) := by
  refine ptxPhase2D_scal_with_locals s (s.locals.update (name, v)) s.clock ?_ hp
  intro n hn
  simp [HolFiniteMapExact.update, FUPDATE,
    show name ≠ ofString n from (hne n hn).symm]

/-- The loop family conjunct transfers along a locals substitution that
preserves the anchor names and the packed-key locals. -/
theorem ptxPhase2D_fullR_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (hl : ∀ n ∈ ptxPhase2DNames, locals.lookup (ofString n) =
      s.locals.lookup (ofString n))
    (halk : locals.lookup (ofString "al_keys") = s.locals.lookup (ofString "al_keys"))
    {contents : Nat → BitVec 64} {E T A N : Nat}
    (hp : ptxPhase2DFullR contents E T A N s) :
    ptxPhase2DFullR contents E T A N {s with locals := locals, clock := clock} := by
  have hte := hl "te" (by simp [ptxPhase2DNames])
  have htx := hl "tx" (by simp [ptxPhase2DNames])
  have hta := hl "al_addrs" (by simp [ptxPhase2DNames])
  have htn := hl "nal" (by simp [ptxPhase2DNames])
  have hnk := hl "nkeys" (by simp [ptxPhase2DNames])
  obtain ⟨⟨he, hx, ha, hn, S, Nd, hw, ht, hb1, hb2, hb3, hd, hrd⟩, h1, h2, h3⟩ := hp
  have halk' : locN {s with locals := locals, clock := clock} "al_keys" =
      locN s "al_keys" := locN_congr s locals clock "al_keys" halk
  have hnk' : locN {s with locals := locals, clock := clock} "nkeys" =
      locN s "nkeys" := locN_congr s locals clock "nkeys" hnk
  refine ⟨⟨?_, ?_, ?_, ?_, S, Nd,
    (worldTypedWith_with_locals s locals clock S Nd).mpr hw,
    R16Shards.PtxP1.txAccessListAt_with_locals s locals clock ht,
    (phase2_live_buffer_with_locals s locals clock S Nd (E, 200) contents).mpr hb1,
    (phase2_live_buffer_with_locals s locals clock S Nd (A, (N + 1) * 8) contents).mpr hb2,
    (phase2_live_buffer_with_locals s locals clock S Nd (T, 384) contents).mpr hb3,
    hd, ?_⟩, ?_, ?_, ?_⟩
  · rw [locN_congr s locals clock "te" hte]; exact he
  · rw [locN_congr s locals clock "tx" htx]; exact hx
  · rw [locN_congr s locals clock "al_addrs" hta]; exact ha
  · rw [locN_congr s locals clock "nal" htn]; exact hn
  · simp only [ptxPhase2DKeysRegion, halk', hnk']; exact hrd
  · simp only [ptxPhase2DKeysRegion, halk', hnk']; exact h1
  · simp only [ptxPhase2DKeysRegion, halk', hnk']; exact h2
  · simp only [ptxPhase2DKeysRegion, halk', hnk']; exact h3

/-- The loop family conjunct survives a clock decrement. -/
theorem ptxPhase2D_fullR_decClock {F : Type} {contents : Nat → BitVec 64}
    {E T A N : Nat} {s : PanSemStateFiniteExact 64 F}
    (hp : ptxPhase2DFullR contents E T A N s) :
    ptxPhase2DFullR contents E T A N (decClockHOLFinite s) :=
  ptxPhase2D_fullR_with_locals s (decClockHOLFinite s).locals (s.clock - 1)
    (by intros; rfl) (by rfl) hp

/-- The loop family conjunct survives a local assignment it does not mention. -/
theorem ptxPhase2D_fullR_setVar_other {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) (name : MlS)
    (hne : ∀ n ∈ ptxPhase2DNames, ofString n ≠ name)
    (hne' : ofString "al_keys" ≠ name)
    {contents : Nat → BitVec 64} {E T A N : Nat}
    (hp : ptxPhase2DFullR contents E T A N s) :
    ptxPhase2DFullR contents E T A N (setVarHOLFinite name v s) := by
  refine ptxPhase2D_fullR_with_locals s (s.locals.update (name, v)) s.clock ?_ ?_ hp
  · intro n hn
    simp [HolFiniteMapExact.update, FUPDATE,
      show name ≠ ofString n from (hne n hn).symm]
  · simp [HolFiniteMapExact.update, FUPDATE,
      show name ≠ ofString "al_keys" from hne'.symm]


/-! ## The packed-key allocation resume -/

/-- The packed-key allocation at guest position 49 preserves the retained
family under a grown world witness, separates every retained buffer from
the fresh packed-key region (which starts at the old heap pointer), and
establishes the region-D loop invariant conjointly with the auxiliary
conjunct, the initialization cases, and the scalar witnesses. -/
theorem ptxPhase2D_alKeys_resume (h : PtxCallees) (contents : Nat → BitVec 64)
    (E T A N : Nat) :
    DecCallResumeOn (fun s => PtxAddressCountExit s ∧ PtxPhase2X s ∧
        ptxPhase2DFam contents E T A N s ∧ ptxPhase2DScal s)
      (fun s => ptxPhase2BX s ∧ PtxPackedInitCases s ∧
        ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s ∧ PtxAccessCountReady s)
      (ofString "al_keys") (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hi := phase2_count_cases_alloc_init h s vs body callee ret v post hc hp.1 ha hl hb
  obtain ⟨w, rfl, hf⟩ := phase2_count_cases_alloc_fresh h s vs body callee ret v post
    hc hp.1 ha hl hb
  let out := setVarHOLFinite (ofString "al_keys") (.val (.word w))
    {post with locals := s.locals}
  -- The retained family under the grown world witness.
  have hr := phase2_count_exit_access_ready hp.1
  obtain ⟨heE, heT, heA, heN, S, Nd, hW, hT, hb1, hb2, hb3, hd⟩ := hp.2.2.1
  have hw := R16Shards.PtxP1.funSpec_at_lookup h.wk_alloc s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hr.1.1.1.1.1.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hw
  have step := hw (Or.inl ⟨.val (.word w), rfl⟩)
  obtain ⟨S', Nd', _, hW', hgrow, hframe, hret⟩ := step.2.2.2.2 S Nd
    ((worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hW) (by simp [IvlsDisj])
  have hArena : ArenaReady s := hr.1.1.1.1.1.1.1.1
  have hTOK : TxAccessListOK s S Nd := by
    unfold TxAccessListOK
    rw [heT]
    exact hT
  have hTp := R16Shards.PtxP1.txAccessListOK_survives_step hArena step.1.1 step.2.1 hW
    (R := []) (by simp) hgrow hframe hTOK (by simp) (by simp) (locals := s.locals) rfl
  have hb1' := phase2_live_buffer_step s post S Nd S' Nd' (E, 200) contents [] hb1
    hArena.2 hW step.2.1 hgrow hframe (by simp) (by simp)
  have hb2' := phase2_live_buffer_step s post S Nd S' Nd' (A, (N + 1) * 8) contents [] hb2
    hArena.2 hW step.2.1 hgrow hframe (by simp) (by simp)
  have hb3' := phase2_live_buffer_step s post S Nd S' Nd' (T, 384) contents [] hb3
    hArena.2 hW step.2.1 hgrow hframe (by simp) (by simp)
  -- The auxiliary conjunct via the concrete allocation body.
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
  have hA' : ArenaReady (callEntryStateHOLFinite s callee) :=
    (arenaReady_with_locals s callee (s.clock - 1)).mpr hArena
  obtain ⟨hpw, hhp⟩ := hA'.2.2.2.2.2.2.2.2.2 "heap_ptr" (by simp [guestGlobalNames])
  have hcode' : (callEntryStateHOLFinite s callee).code = originalRuntimeCode := hc
  have hout1 : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (InitECandidate.Solver.GuestTrapAndLookup.sourceFnBody
        Guest.Software.guestFn_alloc)).1 = some (.returned (.val (.word w))) := by rw [hb]
  obtain ⟨-, -, -, hEq⟩ := InitECandidate.Solver.Wave8Contracts.M27.alloc_body_run
    (callEntryStateHOLFinite s callee) hpw w0 hcode' hhp hnloc (.val (.word w)) hout1
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
    ptxPhase2_txBacking_of_mem_eq hp.2.1.2.1 hboG hmemF
  have hX : PtxPhase2X {post with locals := s.locals} := by
    refine ptxPhase2X_of_cells hp.2.1 htxPost rfl hboG hjcG rfl ?_
    intro k hk
    unfold memW
    rw [hmemF]
  have hX' : PtxPhase2X out :=
    ptxPhase2X_setVar_other _ (.val (.word w)) (by
      intro n hn
      simp only [ptxPhase2XNames, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) hX
  have hkeys : PtxPackedKeysReady out := by
    rcases hi with hi | hi
    · exact hi.2.1
    · exact hi.1
  obtain ⟨Sb, Ndb, hWb, hTb, hdb⟩ := hkeys.2.2.2.2
  have hnz : globN out "bo" ≠ 0 := hX'.2.2.1.bo_nz
  have hbo_mem : (globN out "bo", 88) ∈ worldOwned out Sb Ndb := by
    have hm := typedRecord_mem_fixedObjects out (r := ("bo", 88)) (by decide)
    simp only [hnz, ↓reduceIte] at hm
    simp only [worldOwned, List.mem_append]
    exact Or.inl (Or.inr hm)
  have hBX : ptxPhase2BX out := by
    refine ⟨hX', hnz, ?_⟩
    rcases hdb (locN out "al_keys",
        (locN out "nkeys" * 52 + 8 + 7) / 8 * 8) (by simp)
      (globN out "bo", 88) hbo_mem with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
  -- Transport of the family to the post-allocation state.
  have hTbase : TxAccessListAt {post with locals := s.locals} S' Nd' T := by
    have h1 : TxAccessListAt {post with locals := s.locals} S' Nd' (locN s "tx") := hTp
    rw [← heT]
    exact h1
  have hTout : TxAccessListAt out S' Nd' T :=
    R16Shards.PtxP1.txAccessListAt_with_locals {post with locals := s.locals}
      out.locals post.clock hTbase
  have hptr : locN out "al_keys" = w.toNat := by
    simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have hcount : locN out "nkeys" = locN s "nkeys" := by
    simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "al_keys" ≠ ofString "nkeys" by decide]
  have hEo : locN out "te" = E := by
    rw [show locN out "te" = locN s "te" by
      simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "al_keys" ≠ ofString "te" by decide]]
    exact heE
  have hTo : locN out "tx" = T := by
    rw [show locN out "tx" = locN s "tx" by
      simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "al_keys" ≠ ofString "tx" by decide]]
    exact heT
  have hAo : locN out "al_addrs" = A := by
    rw [show locN out "al_addrs" = locN s "al_addrs" by
      simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "al_keys" ≠ ofString "al_addrs" by decide]]
    exact heA
  have hNo : locN out "nal" = N := by
    rw [show locN out "nal" = locN s "nal" by
      simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "al_keys" ≠ ofString "nal" by decide]]
    exact heN
  have hWout : WorldTypedWith out S' Nd' :=
    (worldTypedWith_with_locals {post with locals := s.locals} out.locals out.clock S' Nd').mpr
      ((worldTypedWith_with_locals post s.locals post.clock S' Nd').mpr hW')
  -- The packed-key region is disjoint from the grown world ownership.
  have hcn : locN (callEntryStateHOLFinite s callee) "n" = locN s "nkeys" * 52 + 8 := by
    have h1 : locN (callEntryStateHOLFinite s callee) "n" = w0.toNat := by
      simp [locN, hnloc]
    rw [h1, hsize]
  obtain ⟨w', hv, hav⟩ := hret (.val (.word w)) rfl
  cases hv
  dsimp only at hav
  rw [hcn] at hav
  have hrdout : IvlsDisj [ptxPhase2DKeysRegion out] (worldOwned out S' Nd') := by
    change IvlsDisj [(locN out "al_keys", (locN out "nkeys" * 52 + 8 + 7) / 8 * 8)] _
    rw [hptr, hcount]
    exact hav
  have hfull : ptxPhase2DFullR contents E T A N out := by
    refine ⟨⟨hEo, hTo, hAo, hNo, S', Nd', hWout,
      hTout, hb1', hb2', hb3', hd, hrdout⟩, ?_, ?_, ?_⟩
    · show Disj (E, 200) (locN out "al_keys", (locN out "nkeys" * 52 + 8 + 7) / 8 * 8)
      rw [hptr, hcount]
      exact Or.inr (Or.inr (Or.inl (hb1.1.2.trans hf.2.1.1)))
    · show Disj (A, (N + 1) * 8) (locN out "al_keys", (locN out "nkeys" * 52 + 8 + 7) / 8 * 8)
      rw [hptr, hcount]
      exact Or.inr (Or.inr (Or.inl (hb2.1.2.trans hf.2.1.1)))
    · show Disj (T, 384) (locN out "al_keys", (locN out "nkeys" * 52 + 8 + 7) / 8 * 8)
      rw [hptr, hcount]
      exact Or.inr (Or.inr (Or.inl (hb3.1.2.trans hf.2.1.1)))
  have hscal' : ptxPhase2DScal out := by
    have h0 : ptxPhase2DScal {post with locals := s.locals} :=
      ptxPhase2D_scal_with_locals s s.locals post.clock (by intros; rfl) hp.2.2.2
    exact ptxPhase2D_scal_setVar_other _ (.val (.word w)) (ofString "al_keys")
      (by intro n hn
          simp only [ptxPhase2DNames, List.mem_cons, List.not_mem_nil, or_false] at hn
          rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide) h0
  -- The count-ready invariant at the resumed state: the stage-0 part comes
  -- from the generic scratch-stage resume, the environment separation from
  -- the single-witness world assembled above.
  have hstage : R16Shards.PtxP1.StageP 0 s := R16Shards.PtxP1.stage0 hr.1.1.1.1.1
  have hworld := R16Shards.PtxP1.resume_scratch_stage h.wk_alloc
    (gs := []) (by simp [R16Shards.PtxP1.ScratchSpec]) (fun _ => rfl)
    (by decide) (by decide) (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
    (by simp) (by decide) (n := 0) (name := ofString "al_keys") (by decide)
    [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]]
    s vs body callee ret (.val (.word w)) post hc hstage ha hl (by rw [hbody]; exact hb)
  have hh0 : globN s "heap_ptr" ≤ globN post "heap_ptr" := step.2.1
  have hh : globN s "heap_ptr" ≤ globN out "heap_ptr" := hh0
  have hsnd : locN out "sender" = locN s "sender" := by
    simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "al_keys" ≠ ofString "sender" by decide]
  have hmgas : locN out "mgas" = locN s "mgas" := by
    simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "al_keys" ≠ ofString "mgas" by decide]
  have hteq : locN out "te" = locN s "te" := hEo.trans heE.symm
  have htxq : locN out "tx" = locN s "tx" := hTo.trans heT.symm
  have hgS : GuestInv s := hr.1.1.1.1.1.1.1.1.1
  have hgO : GuestInv out := hworld.1.1.1.1.1
  have hinsnd : Inside (locN out "sender", 24) InitE.sourceBase (globN out "heap_ptr") := by
    rw [hsnd]
    exact ⟨hr.1.1.1.1.2.1.1, hr.1.1.1.1.2.1.2.trans hh⟩
  have hwssnd : WordsOK out (locN out "sender", 24) := by
    rw [hsnd]
    exact wordsOK_transfer hgS hgO hr.1.1.1.1.2.2.1
  have hmgasle : locN out "mgas" ≤ 16777216 := by rw [hmgas]; exact hr.1.1.1.1.2.2.2
  have hshapes : PtxPhase2LocalShapes out :=
    ptxPhase2LocalShapes_set_other _ (ptxPhase2LocalShapes_restore s post hr.1.1.1.2)
      (ofString "al_keys") (.val (.word w)) (by decide)
  have hlt : out.locals.lookup (ofString "te") = s.locals.lookup (ofString "te") := by
    simp [out, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "al_keys" ≠ ofString "te" by decide]
  have htewit : ∃ w : BitVec 64, out.locals.lookup (ofString "te") = some (.val (.word w)) := by
    rw [hlt]
    exact hr.1.1.2.1
  have hinste : Inside (locN out "te", 200) InitE.sourceBase (globN out "heap_ptr") := by
    rw [hteq]
    exact ⟨hr.1.1.2.2.1.1, hr.1.1.2.2.1.2.trans hh⟩
  have htal : locN out "te" % 8 = 0 := by rw [hteq]; exact hr.1.1.2.2.2.1
  have hwste : WordsOK out (locN out "te", 200) := by
    rw [hteq]
    exact wordsOK_transfer hgS hgO hr.1.1.2.2.2.2.1
  have htesn : ∃ S Nd, WorldTypedWith out S Nd ∧
      IvlsDisj [(locN out "te", 200)] (worldOwned out S Nd) := by
    refine ⟨S', Nd', hWout, ?_⟩
    rw [hEo]
    exact hb1'.2.1
  obtain ⟨S₀, Nd₀, hW₀, hT₀, hd₀, hdt, hrec⟩ := hr.1.2
  have htedisj : IvlsDisj [(locN out "te", 200)] (worldOwned out S' Nd') := by
    rw [hEo]
    exact hb1'.2.1
  have hTOKo : TxAccessListOK out S' Nd' := by
    unfold TxAccessListOK
    rw [hTo]
    exact hTout
  have hdt' : Disj (locN out "tx", 384) (locN out "te", 200) := by
    rw [htxq, hteq]
    exact hdt
  have hmemWout (p : Nat) : memW out p = memW s p := by
    unfold memW
    have h1 : out.memory (BitVec.ofNat 64 p) = s.memory (BitVec.ofNat 64 p) := hmemF _
    rw [h1]
  have hmemWtx (k : Nat) : memW out (locN s "tx" + k) = memW s (locN s "tx" + k) := hmemWout _
  have hrec' : 0 < memW out (locN out "tx" + 216) →
      Disj (memW out (locN out "tx" + 208), 24 * memW out (locN out "tx" + 216))
        (locN out "te", 200) := by
    intro hpos
    rw [htxq] at hpos
    have h0 : 0 < memW s (locN s "tx" + 216) := by rw [← hmemWtx]; exact hpos
    rw [htxq, hteq, hmemWtx, hmemWtx]
    exact hrec h0
  have hnaval : locN out "nal" = 0 ∨ locN out "nal" = memW out (locN out "tx" + 216) := by
    rcases hi with h1 | h2
    · exact Or.inr h1.2.2.2.2.2.2.2
    · refine Or.inl ?_
      simp [locN, out, h2.2]
  have hacr : PtxAccessCountReady out :=
    ⟨⟨⟨⟨⟨hworld.1, hinsnd, hwssnd, hmgasle⟩, hshapes⟩, htewit, hinste, htal, hwste, htesn⟩,
      S', Nd', hWout, hTOKo, htedisj, hdt', hrec'⟩, hscal'.2.1, hnaval⟩
  exact ⟨hBX, hi, hfull, hscal', hacr⟩

/-! ## The packing memcpy step -/

/-- Any interval disjoint from the packed-key region is disjoint from both
copy windows, and both windows are nonempty. -/
theorem ptxPhase2D_window_disj {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxPackedCopyIndex s) {win : Ivl}
    (hpair : win ∈ [(locN s "al_keys" + 52 * locN s "k", 20),
      (locN s "al_keys" + 52 * locN s "k" + 20, 32)])
    (input : Ivl) (hd : Disj input
      (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)) :
    Disj input win ∧ 0 < win.2 := by
  have h := phase2_packed_guarded_input_disjoint s hp input hd
  rcases List.mem_cons.mp hpair with heq | hm
  · refine ⟨?_, ?_⟩
    · rw [heq]
      exact h.1
    · have heq' := congrArg Prod.snd heq
      omega
  · refine ⟨?_, ?_⟩
    · rw [List.mem_singleton.mp hm]
      exact h.2
    · have heq' := congrArg Prod.snd (List.mem_singleton.mp hm)
      omega

/-- Either packing memcpy preserves the full retained family under a grown
world witness, keeping the packed-key region disjoint from the world
ownership of the very same witness. -/
theorem ptxPhase2D_full_copy (h : PtxCallees) {contents : Nat → BitVec 64}
    {E T A N : Nat} {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (dst src len : ExpHOL 64) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64)) (d n : BitVec 64)
    (hc : s.code = originalRuntimeCode)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dst, src, len] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hns : PtxPackedNsNalCopy s)
    (harena : ArenaReady s)
    (hp : ptxPhase2DFullR contents E T A N s)
    (hdst : evalAt s dst = some (.val (.word d)))
    (hlen : evalAt s len = some (.val (.word n)))
    (hpair : (d.toNat, n.toNat) ∈
      [(locN s "al_keys" + 52 * locN s "k", 20),
       (locN s "al_keys" + 52 * locN s "k" + 20, 32)]) :
    ptxPhase2DFullR contents E T A N {post with locals := s.locals} := by
  obtain ⟨heE, heT, heA, heN, S, Nd, hW, hT, hb1, hb2, hb3, hdT, hrd⟩ := hp.1
  have hindex : PtxPackedCopyIndex s := hns.1.1.2.1.1
  have hentry := phase2_memcpy_entry_destination s dst src len vs body callee ret d n
    hc hargs hl hdst hlen
  have hdest : (locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n") ∈
      [(locN s "al_keys" + 52 * locN s "k", 20),
       (locN s "al_keys" + 52 * locN s "k" + 20, 32)] := by
    change ((locN {s with locals := callee, clock := s.clock - 1} "dst",
      locN {s with locals := callee, clock := s.clock - 1} "n") : Ivl) ∈ _
    rw [hentry.1, hentry.2]
    exact hpair
  have hwinE := ptxPhase2D_window_disj s hindex hdest (E, 200) hp.2.1
  have hwinA := ptxPhase2D_window_disj s hindex hdest (A, (N + 1) * 8) hp.2.2.1
  have hwinT := ptxPhase2D_window_disj s hindex hdest (T, 384) hp.2.2.2
  have htxWin := ptxPhase2D_window_disj s hindex hdest (locN s "tx", 384) hns.1.1.2.1.2.1
  have hrecWin := ptxPhase2D_window_disj s hindex hdest
    (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) hns.1.1.2.1.2.2
  -- The window is disjoint from the typed world at the entry witness.
  have hdw : IvlsDisj [(locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n")]
      (worldTypedIvls (callEntryStateHOLFinite s callee) S Nd) := by
    apply phase2_packed_typed_of_owned (callEntryStateHOLFinite s callee) S Nd
    intro dest hmem region hregion
    simp only [List.mem_singleton] at hmem
    subst dest
    have hdis := hrd (ptxPhase2DKeysRegion s) (by simp) region hregion
    have hc' := phase2_packed_guarded_input_disjoint s hindex region (disj_symm hdis)
    rcases List.mem_cons.mp hdest with heq | hm
    · rw [heq]
      exact disj_symm hc'.1
    · rw [List.mem_singleton.mp hm]
      exact disj_symm hc'.2
  -- The concrete memcpy step under the family witness.
  have hentryW : WorldOK (callEntryStateHOLFinite s callee) :=
    R16Shards.PtxP1.worldOK_callEntry hns.1.1.1 callee
  have hs := R16Shards.PtxP1.funSpec_at_lookup h.wk_memcpy s hc vs body callee ret hl
    hentryW (by rw [he]; exact hn)
  rw [he] at hs
  have step := hs hr
  have hwe := (worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hW
  obtain ⟨S', Nd', -, hw', ho, hf, -⟩ := step.2.2.2.2 S Nd hwe hdw
  have hg : GlobalsKept [] s {post with locals := s.locals} :=
    phase2_memcpy_eval_globals h s post vs body callee ret r hc hl he hn hr hentryW
  have hh : globN s "heap_ptr" ≤ globN {post with locals := s.locals} "heap_ptr" :=
    (phase2_copy_globals_heap_eq s _ hg).symm.le
  have hz : ∀ region ∈ ([(locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n")] : List Ivl),
      region.2 = 0 → region.1 % 8 = 0 := by
    intro region hm he0
    simp only [List.mem_singleton] at hm
    subst region
    dsimp only at he0
    omega
  have hTOK : TxAccessListOK s S Nd := by
    unfold TxAccessListOK
    rw [heT]
    exact hT
  have hTp : TxAccessListOK {post with locals := s.locals} S' Nd' :=
    R16Shards.PtxP1.txAccessListOK_survives_step harena step.1.1 hh hW hz ho hf hTOK
      (by simpa only [List.mem_singleton, forall_eq] using htxWin.1)
      (fun hpos => by simpa only [List.mem_singleton, forall_eq] using hrecWin.1)
      (locals := s.locals) rfl
  have hb1' := phase2_live_buffer_step s {post with locals := s.locals} S Nd S' Nd'
    (E, 200) contents [(locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n")] hb1 harena.2 hW hh ho hf
    (by simpa only [List.mem_singleton, forall_eq] using hwinE.1) hz
  have hb2' := phase2_live_buffer_step s {post with locals := s.locals} S Nd S' Nd'
    (A, (N + 1) * 8) contents [(locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n")] hb2 harena.2 hW hh ho hf
    (by simpa only [List.mem_singleton, forall_eq] using hwinA.1) hz
  have hb3' := phase2_live_buffer_step s {post with locals := s.locals} S Nd S' Nd'
    (T, 384) contents [(locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n")] hb3 harena.2 hW hh ho hf
    (by simpa only [List.mem_singleton, forall_eq] using hwinT.1) hz
  have hrd' : IvlsDisj [ptxPhase2DKeysRegion {post with locals := s.locals}]
      (worldOwned {post with locals := s.locals} S' Nd') :=
    phase2_packed_owned_growth s post _ _ _ hindex.1.2.1 ho hrd
  refine ⟨⟨heE, heT, heA, heN, S', Nd',
    (worldTypedWith_with_locals post s.locals post.clock S' Nd').mpr hw',
    ?_, hb1', hb2', hb3', hdT, hrd'⟩, hp.2.1, hp.2.2.1, hp.2.2.2⟩
  have h1 : TxAccessListAt {post with locals := s.locals} S' Nd' (locN s "tx") := hTp
  rw [← heT]
  exact h1

/-- The count-ready invariant survives a packed copy whose only memory writes
hit the copied interval inside the packed-key region: the world separation
comes from the retained family, the preserved cells from the fine byte
frame, and the word-typed views transfer across the guest invariant. -/
theorem ptxPhase2D_acr_copy {F : Type} {contents : Nat → BitVec 64} {E T A N : Nat}
    {s post : PanSemStateFiniteExact 64 F} {dst len : Nat}
    (hbx : ptxPhase2BX s) (hns : PtxPackedNsNalCopy s)     (hacr : PtxAccessCountReady s)
    (_hc : s.code = originalRuntimeCode)
    (hloc : post.locals = s.locals)
    (hbe : R13Shards.Keccak256.ByteEff s post [(dst, len)])
    (hfull : ptxPhase2DFullR contents E T A N post)
    (hdst : Inside (dst, len) (locN s "al_keys")
      (locN s "al_keys" + (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)) :
    PtxAccessCountReady post := by
  obtain ⟨hl, S₀, Nd₀, hW₀, hT₀, hd₀, htx₀, hrec₀⟩ := hacr.1
  obtain ⟨heE, heT, heA, heN, S', Nd', hWT, hTAL, hlb1, hlb2, hlb3, hdT, -⟩ := hfull.1
  have htr := hl.1.1.1.1
  have hjc := hl.1.1.1.2.1
  have hbo40 := hl.1.1.1.2.2.1
  have hbo72 := hl.1.1.1.2.2.2.1
  have hbonz := htr.2.1
  have hbo24 := htr.2.2.1
  have hbo32 := htr.2.2.2.1
  have hidxlt := htr.2.2.2.2
  -- basic state facts
  have hA : ArenaReady s := hns.1.1.1.1
  have hAO : ArenaOK s := hA.2
  have hG : GuestInv s := hA.1
  have hgl : post.globals = s.globals := hbe.globals
  have hglobN (m : String) : globN post m = globN s m := by
    unfold globN
    rw [hgl]
  have hGP : GuestInv post :=
    ⟨by rw [hbe.code, hG.code], by rw [hbe.memaddrs, hG.memaddrs],
     by rw [hbe.shMemaddrs, hG.shMemaddrs], by rw [hbe.baseAddr, hG.baseAddr]⟩
  have hAOp : ArenaOK post := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hglobN "heap_ptr"]; exact hAO.1
    · rw [hglobN "heap_ptr"]; exact hAO.2.1
    · rw [hglobN "frame_mem_ptr"]; exact hAO.2.2.1
    · rw [hglobN "frame_mem_ptr", hglobN "scratch_ptr"]; exact hAO.2.2.2.1
    · rw [hglobN "scratch_ptr"]; exact hAO.2.2.2.2.1
    · rw [hglobN "heap_ptr"]; exact hAO.2.2.2.2.2.1
    · rw [hglobN "frame_mem_ptr"]; exact hAO.2.2.2.2.2.2.1
    · rw [hglobN "scratch_ptr"]; exact hAO.2.2.2.2.2.2.2.1
    · exact globalsWord_congr hgl hAO.2.2.2.2.2.2.2.2
  have hARp : ArenaReady post := ⟨hGP, hAOp⟩
  have hWOKp : WorldOK post := ⟨hARp, S', (worldTyped_iff_with post S').2 ⟨Nd', hWT⟩⟩
  have hlocN (n : String) : locN post n = locN s n := by unfold locN; rw [hloc]
  -- the fine frame from the byte effect
  have hfr : FrameOutside s post [(dst, len)]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
    intro a hkeep _
    by_contra hm
    obtain ⟨i, hi, hpos⟩ := hbe.cell_frame a hm
    exact hkeep i hi hpos.2
  have hmemWtx (k : Nat) (hk : k + 8 ≤ 384) :
      memW post (locN s "tx" + k) = memW s (locN s "tx" + k) := by
    apply ptxPhase2_memW_eq_of_frameOutside hA hfr
    · intro i hi hci
      simp only [List.mem_singleton] at hi
      subst i
      unfold CellHits at hci
      obtain ⟨h1, h2⟩ := hci
      obtain ⟨hd1, hd2⟩ := hdst
      rcases hns.1.1.2.1.2.1 with h | h | h | h
      · omega
      · omega
      · omega
      · omega
    · have hins := hT₀.1.2.1
      unfold Inside at hins
      obtain ⟨h1, h2⟩ := hins
      omega
  -- the block-out record cells
  have hF : FixedTyped s := hW₀.2.2.1
  have hbo_nz : globN s "bo" ≠ 0 := hbx.2.1
  have hbo_al := bo_words hF hbo_nz
  have hhp' : globN post "heap_ptr" ≤ heapLimit := by
    rw [hglobN "heap_ptr"]
    exact hAO.2.1
  have hmiss_bo : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat),
      ¬ CellHits (globN s "bo" + k) (dst, len) := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    obtain ⟨hd1, hd2⟩ := hdst
    unfold CellHits
    rcases hbx.2.2 with h | h
    · rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
    · rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
  have hcellsBo : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat),
      memW post (globN post "bo" + k) = memW s (globN s "bo" + k) := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rw [hglobN "bo"]
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      exact ptxPhase2BX_frame_word hAO hhp' hfr hbo_al.1
        (fun j hj hci => by
          simp only [List.mem_singleton] at hj
          subst j
          exact hmiss_bo _ (by simp) hci)
        ⟨by omega, by omega⟩
  -- the preserved views and values
  have hwte : WordsOK post (locN post "te", 200) := by
    rw [hlocN "te"]
    exact wordsOK_transfer hG hGP hl.2.2.2.2.1
  have hwssnd : WordsOK post (locN post "sender", 24) := by
    rw [hlocN "sender"]
    exact wordsOK_transfer hG hGP hl.1.1.2.2.1
  have hbo24p : memW post (globN post "bo" + 24) ≠ 0 := by
    rw [hcellsBo 24 (by simp)]; exact hbo24
  have hbo32p : memW post (globN post "bo" + 32) ≠ 0 := by
    rw [hcellsBo 32 (by simp)]; exact hbo32
  have hbo40p : memW post (globN post "bo" + 40) ≠ 0 := by
    rw [hcellsBo 40 (by simp)]; exact hbo40
  have hbo72p : memW post (globN post "bo" + 72) ≠ 0 := by
    rw [hcellsBo 72 (by simp)]; exact hbo72
  have hbonzp : globN post "bo" ≠ 0 := by rw [hglobN "bo"]; exact hbonz
  have hjcp : globN post "journal_cap" ≠ 0 := by rw [hglobN "journal_cap"]; exact hjc
  have hidxltp : locN post "index" < memW post (globN post "bo" + 80) := by
    rw [hlocN "index", hcellsBo 80 (by simp)]
    exact hidxlt
  have hTOKp : TxAccessListOK post S' Nd' := by
    unfold TxAccessListOK
    rw [heT]
    exact hTAL
  have hsnp : ∃ S Nd, WorldTypedWith post S Nd ∧ TxAccessListOK post S Nd :=
    ⟨S', Nd', hWT, hTOKp⟩
  have hTRSp : TxReadyStrong post :=
    ⟨⟨hWOKp, hbonzp, hbo24p, hbo32p, hidxltp⟩, hjcp, hbo40p, hbo72p, hsnp⟩
  have hinsndp : Inside (locN post "sender", 24) InitE.sourceBase (globN post "heap_ptr") := by
    rw [hlocN "sender", hglobN "heap_ptr"]
    exact hl.1.1.2.1
  have hmgasle : locN post "mgas" ≤ 16777216 := by rw [hlocN "mgas"]; exact hl.1.1.2.2.2
  have hshp : PtxPhase2LocalShapes post := by
    constructor
    · intro name hn
      obtain ⟨w, hw⟩ := hl.1.2.scalar name hn
      exact ⟨w, by rw [hloc]; exact hw⟩
    · obtain ⟨a, b, c, d, hw⟩ := hl.1.2.price
      exact ⟨a, b, c, d, by rw [hloc]; exact hw⟩
    · obtain ⟨a, b, hw⟩ := hl.1.2.enc
      exact ⟨a, b, by rw [hloc]; exact hw⟩
    · obtain ⟨a, b, c, hw⟩ := hl.1.2.intrinsic
      exact ⟨a, b, c, by rw [hloc]; exact hw⟩
  have htewitp : ∃ w : BitVec 64, post.locals.lookup (ofString "te") = some (.val (.word w)) := by
    rw [hloc]
    exact hl.2.1
  have hinstep : Inside (locN post "te", 200) InitE.sourceBase (globN post "heap_ptr") := by
    rw [hlocN "te", hglobN "heap_ptr"]
    exact hl.2.2.1
  have htalp : locN post "te" % 8 = 0 := by rw [hlocN "te"]; exact hl.2.2.2.1
  have htesnp : ∃ S Nd, WorldTypedWith post S Nd ∧
      IvlsDisj [(locN post "te", 200)] (worldOwned post S Nd) := by
    refine ⟨S', Nd', hWT, ?_⟩
    rw [heE]
    exact hlb1.2.1
  have htedisp : IvlsDisj [(locN post "te", 200)] (worldOwned post S' Nd') := by
    rw [heE]
    exact hlb1.2.1
  have hTALp : TxAccessListAt post S' Nd' (locN post "tx") := by
    rw [heT]
    exact hTAL
  have hdtp : Disj (locN post "tx", 384) (locN post "te", 200) := by
    rw [hlocN "tx", hlocN "te"]
    exact htx₀
  have hrecp : 0 < memW post (locN post "tx" + 216) →
      Disj (memW post (locN post "tx" + 208), 24 * memW post (locN post "tx" + 216))
        (locN post "te", 200) := by
    rw [hlocN "tx", hmemWtx 208 (by omega), hmemWtx 216 (by omega), hlocN "te"]
    exact hrec₀
  have hnawitp : ∃ w : BitVec 64, post.locals.lookup (ofString "nal") = some (.val (.word w)) := by
    rw [hloc]
    exact hacr.2.1
  have hnalvalp : locN post "nal" = 0 ∨ locN post "nal" = memW post (locN post "tx" + 216) := by
    rw [hlocN "nal", hlocN "tx", hmemWtx 216 (by omega)]
    exact hacr.2.2
  exact ⟨⟨⟨⟨⟨hTRSp, hinsndp, hwssnd, hmgasle⟩, hshp⟩, htewitp, hinstep, htalp, hwte, htesnp⟩,
    S', Nd', hWT, hTALp, htedisp, hdtp, hrecp⟩, hnawitp, hnalvalp⟩
