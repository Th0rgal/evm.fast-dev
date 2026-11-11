import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4G

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

/-! # Phase 4H: the loop-31 invariant and its transports -/

/-- The loop-31 invariant: the phase-4 data plus the loop locals (`i`, `nl`,
`lp`) as words, the loop bounds and the log-list length bound. -/
structure P4Loop31 {F : Type}
    (entry s s_pmc : PanSemStateFiniteExact 64 F) (w_out : BitVec 64) : Prop where
  data : P4Data entry s s_pmc w_out
  i_word : ∃ i : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word i))
  nl_word : ∃ nl : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word nl))
  lp_word : ∃ lp : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word lp))
  i_le : locN s "i" ≤ locN s "nl"
  nl_lt : locN s "nl" < 2 ^ 28
  len_bound : 8 * (memW s (memW s (globN s "bo" + 40) + 8) + (locN s "nl" - locN s "i"))
    < sourceBase

/-- The loop-31 `lst_push` arguments: the logs-list header and the element size. -/
def p4Loop31Args : List (ExpHOL 64) :=
  [(.load .one (.op .add [(.var .global (ofString "bo")), (.const 0x0000000000000028#64)])),
   (.const 0x0000000000000008#64)]

/-- The loop-31 source expression: the log entry at `lp + 8*i`. -/
def p4Loop31Src : ExpHOL 64 :=
  .load .one (.op .add [(.var .local (ofString "lp")),
    (.panop .mul [(.var .local (ofString "i")), (.const 0x0000000000000008#64)])])

/-- The loop-31 index-bump expression `i + 1`. -/
def p4Loop31I : ExpHOL 64 :=
  .op .add [(.var .local (ofString "i")), (.const 0x0000000000000001#64)]

/-- The loop-31 continuation `C`: store the log entry into the pushed slot, bump `i`. -/
def p4Loop31C : ProgHOL 64 :=
  .seq (.store (.var .local (ofString "slot")) p4Loop31Src)
       (.assign .local (ofString "i") p4Loop31I)

/-- Assembly of the loop-31 body engine: `p4Run_decCall_lst_push` applied to the
concrete body.  The list-header facts (`hl_choice`, `hlist_nz`, `harg`) and the
continuation obligation (`hC`) are isolated as hypotheses. -/
theorem p4Run_loop31Engine {F : Type} {entry u : PanSemStateFiniteExact 64 F}
    (hbase : PtxRelBase true entry u) (hcode : u.code = originalRuntimeCode)
    (w_l : BitVec 64)
    (hl_choice : w_l.toNat = memW u (globN u "bo" + 40) ∨
      w_l.toNat = memW u (globN u "bo" + 72))
    (hlist_nz : memW u w_l.toNat ≠ 0)
    (harg : evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a))
        p4Loop31Args = some [.val (.word w_l), .val (.word 8)])
    (hC : ∀ (w : BitVec 64) (post : PanSemStateFiniteExact 64 F),
      (∀ a : BitVec 64, ¬ CellHits a.toNat (w_l.toNat, 24) →
        ¬ CellHits a.toNat (InitECandidate.Solver.Wave8Contracts.M08.heapFree u) →
        post.memory a = u.memory a) →
      (w.toNat % 8 = 0 ∧
        Inside (w.toNat, 8) (memW post w_l.toNat)
          (memW post w_l.toNat + 8 * memW post (w_l.toNat + 16)) ∧
        memW post (w_l.toNat + 8) = memW u (w_l.toNat + 8) + 1 ∧
        w.toNat = memW post w_l.toNat + 8 * memW u (w_l.toNat + 8) ∧
        (memW u w_l.toNat ≠ 0 → ∀ k, k < memW u (w_l.toNat + 8) →
          memW post (memW post w_l.toNat + 8 * k) = memW u (memW u w_l.toNat + 8 * k))) →
      WorldStep (fun _ => []) ["heap_ptr"] stdKeep RetListSlotStrong
        (callEntryStateHOLFinite u ((HolFiniteMapExact.empty.update
          (ofString "l", .val (.word w_l))).update (ofString "esz", .val (.word 8))))
        (some (.returned (.val (.word w)))) post →
      post.code = originalRuntimeCode →
      PtxRelRunStrong entry p4Loop31C
        (setVarHOLFinite (ofString "slot") (.val (.word w)) {post with locals := u.locals})) :
    PtxRelRunStrong entry p4Loop31Body u :=
  p4Run_decCall_lst_push hbase hcode w_l hl_choice hlist_nz (ofString "slot")
    p4Loop31Args p4Loop31C harg hC

/-- The bare-assign terminal runner: the assign's eval post is exactly
`setVarHOLFinite name v s`; the terminal WorldStep is supplied by `htail`. -/
theorem p4Run_bareAssign {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    (name : MlS) (e : ExpHOL 64)
    (htail : ∀ v : ValueHOL 64, evalAt s e = some v →
      WorldStep ptxRegions ptxGlobals ptxKeep PtxLogsAndSlices entry none
        (setVarHOLFinite name v s)) :
    PtxRelRunStrong entry (.assign .local name e) s := by
  intro hres
  rw [evaluateHOLFiniteState_assign] at hres ⊢
  rcases hev : evalAt s e with _ | v
  · simp [hev] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [hev] at hres ⊢
    by_cases hvalid : isValidValueHOLFinite s .local name v = true
    · simp only [hvalid, ↓reduceIte] at hres ⊢
      exact htail v hev
    · simp only [hvalid, Bool.false_eq_true, ↓reduceIte] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

/-- The loop-31 `hC` obligation, assembled from `p4Run_store` and the
bare-assign terminal.  All semantic facts (the store-eval facts and the
terminal WorldStep) are isolated in the hypothesis-bundle `hWSA`. -/
theorem p4Run_loop31_hC {F : Type}
    {entry u post : PanSemStateFiniteExact 64 F} {w : BitVec 64}
    (hWSA : ∀ (a : BitVec 64) (v : ValueHOL 64) (mem' : RiscV.Word 64 → HolWordLab 64)
      (v' : ValueHOL 64),
      evalAt (setVarHOLFinite (ofString "slot") (.val (.word w))
          {post with locals := u.locals}) (.var .local (ofString "slot")) =
        some (.val (.word a)) →
      evalAt (setVarHOLFinite (ofString "slot") (.val (.word w))
          {post with locals := u.locals}) p4Loop31Src = some v →
      @panMemStoresHOL 64 _ a (flattenHOL v)
        (setVarHOLFinite (ofString "slot") (.val (.word w))
          {post with locals := u.locals}).memaddrs
        (fun address => Classical.propDecidable ((setVarHOLFinite (ofString "slot")
          (.val (.word w)) {post with locals := u.locals}).memaddrs address))
        (setVarHOLFinite (ofString "slot") (.val (.word w))
          {post with locals := u.locals}).memory = some mem' →
      evalAt {setVarHOLFinite (ofString "slot") (.val (.word w))
          {post with locals := u.locals} with memory := mem'} p4Loop31I = some v' →
      WorldStep ptxRegions ptxGlobals ptxKeep PtxLogsAndSlices entry none
        (setVarHOLFinite (ofString "i") v' {setVarHOLFinite (ofString "slot")
          (.val (.word w)) {post with locals := u.locals} with memory := mem'})) :
    PtxRelRunStrong entry p4Loop31C
      (setVarHOLFinite (ofString "slot") (.val (.word w)) {post with locals := u.locals}) :=
  p4Run_store (.var .local (ofString "slot")) p4Loop31Src
    (.assign .local (ofString "i") p4Loop31I)
    (fun a v mem' hdst hsrc hmem' =>
      p4Run_bareAssign (ofString "i") p4Loop31I
        (fun v' hev' => hWSA a v mem' v' hdst hsrc hmem' hev'))

/-- A `PtxRelBase` at a state with `ArenaReady` yields the `none`-WorldStep at
that same state: `worldStep_refl` lifted through `ptxRelBase_step_worldStep`,
converting the trivial `NoExtra` predicate to `PtxLogsAndSlices` (vacuous at
`r = none`). -/
theorem ptxRelBase_worldStep_none {F : Type}
    {entry s : PanSemStateFiniteExact 64 F} {B : BufList}
    (h : PtxRelBase true entry s)
    (hB : ValidBufList B)
    (hBsub : ∀ p ∈ B, p ∈ ptxBufs ∧ p.1 ∉ ptxGlobals)
    (hAR : ArenaReady s) :
    WorldStep ptxRegions ptxGlobals ptxKeep PtxLogsAndSlices entry none s := by
  have hb := ptxRelBase_step_worldStep h hB hBsub
    (fun g hg => absurd hg (by simp)) ptxKeepSub_stdKeep
    (WkBal.worldStep_refl (bufRegions B) [] (r := none) (post := s) hAR rfl)
  exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, fun S Nd hWT hD =>
    let ⟨S', Nd', hsub, hW', hOG, hFO, _⟩ := hb.2.2.2.2 S Nd hWT hD
    ⟨S', Nd', hsub, hW', hOG, hFO, (by intro val hv; cases hv),
      (by intro val hv; cases hv)⟩⟩

/-- The loop-31 terminal WorldStep: from a `PtxRelBase` at the stored state
(locals-only `setVar "i"` change), the `none`-WorldStep at the bumped state. -/
theorem p4Loop31_terminalWorldStep {F : Type}
    {entry s : PanSemStateFiniteExact 64 F} {B : BufList}
    (h : PtxRelBase true entry s)
    (hB : ValidBufList B) (hBsub : ∀ p ∈ B, p ∈ ptxBufs ∧ p.1 ∉ ptxGlobals)
    (hAR : ArenaReady s) (v' : ValueHOL 64) :
    WorldStep ptxRegions ptxGlobals ptxKeep PtxLogsAndSlices entry none
      (setVarHOLFinite (ofString "i") v' s) := by
  have hws := ptxRelBase_worldStep_none h hB hBsub hAR
  exact WkBal.worldStep_with_locals_right
    (setVarHOLFinite (ofString "i") v' s).locals s.clock
    (fun _ _ hQ =>
      ⟨retTransactionLogs_congr_memory_heap_bo_ptx rfl rfl rfl rfl hQ.1,
        ptxRetSlices_congr_memory_heap_bo rfl rfl rfl rfl hQ.2⟩) hws

/-- Re-anchor the lst_push callee-WorldStep (given at the call-entry state)
to the caller state `u`: the call entry differs only in locals and clock. -/
theorem p4Loop31_calleeStepAtU {F : Type}
    {u post : PanSemStateFiniteExact 64 F} {w w_l : BitVec 64}
    (hcallee : WorldStep (fun _ => []) ["heap_ptr"] stdKeep RetListSlotStrong
      (callEntryStateHOLFinite u ((HolFiniteMapExact.empty.update
        (ofString "l", .val (.word w_l))).update (ofString "esz", .val (.word 8))))
      (some (.returned (.val (.word w)))) post) :
    WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra u
      (some (.returned (.val (.word w)))) post := by
  refine worldStep_congr_R ?_
    (R13Shards.worldStep_with_locals hcallee u.locals u.clock)
  rfl

/-- Transport the entry-anchored base across the lst_push callee step (from
`u` to the callee's `post`), via `ptxRelBase_step_cells` at the empty buffer
list.  The pointer- and cells-facts are isolated as hypotheses. -/
theorem p4Loop31_baseTransport {F : Type}
    {entry u post : PanSemStateFiniteExact 64 F} {w w_l : BitVec 64}
    (hbase : PtxRelBase true entry u)
    (hcallee : WorldStep (fun _ => []) ["heap_ptr"] stdKeep RetListSlotStrong
      (callEntryStateHOLFinite u ((HolFiniteMapExact.empty.update
        (ofString "l", .val (.word w_l))).update (ofString "esz", .val (.word 8))))
      (some (.returned (.val (.word w)))) post)
    (hsp : globN post "scratch_ptr" ≤ globN u "scratch_ptr")
    (hfmp : globN u "frame_mem_ptr" ≤ globN post "frame_mem_ptr")
    (hcells : PtxBoCells true entry u post) :
    PtxRelBase true entry post :=
  ptxRelBase_step_cells hbase (by intro p hp; cases hp) (by intro p hp; cases hp)
    (by intro g hg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        subst hg; decide)
    ptxKeepSub_stdKeep (p4Loop31_calleeStepAtU hcallee) hsp hfmp hcells

/-- The single-cell store WorldStep (at the empty region family, `r = none`):
writing 8 bytes at `x` inside the currently-owned set.  The typing-, record-
and ArenaReady-facts are isolated as hypotheses. -/
theorem p4Loop31_storeWorldStep {F : Type}
    {s : PanSemStateFiniteExact 64 F} {x : BitVec 64}
    {mem' : RiscV.Word 64 → HolWordLab 64}
    (hAR : ArenaReady {s with memory := mem'})
    (hmem' : ∀ a, a ≠ x → mem' a = s.memory a)
    (hty : ∀ S Nd, WorldTypedWith s S Nd →
      IvlsDisj ((fun _ => []) s) (worldTypedIvls s S Nd) →
      (WorldTypedWith {s with memory := mem'} S Nd ∧
        worldOwned {s with memory := mem'} S Nd = worldOwned s S Nd ∧
        TxEnv {s with memory := mem'}) ∧
      (∃ o ∈ worldOwned s S Nd, Inside (x.toNat, 8) o.1 (o.1 + o.2)))
    (hrec : ∀ r ∈ stdKeep, globN s r.1 ≠ 0 → ∀ k ∈ r.2,
      memW {s with memory := mem'} (globN s r.1 + k) = memW s (globN s r.1 + k)) :
    WorldStep (fun _ => []) [] stdKeep NoExtra s none {s with memory := mem'} := by
  refine ⟨hAR, le_of_eq (by rfl), fun k hk => by rfl, ?_, ?_⟩
  · intro r hr hnz k hk _
    exact hrec r hr hnz k hk
  · intro S Nd hWT _
    obtain ⟨⟨hWT', hown, _⟩, hxo⟩ := hty S Nd hWT (by intro i hi; cases hi)
    refine ⟨S, Nd, fun _ ht => ht, hWT', ?_, ?_, trivial⟩
    · intro o ho
      rw [hown] at ho
      exact Or.inr (Or.inl ⟨o, ho, le_refl _, le_refl _⟩)
    · intro a hkeep _
      by_cases hax : a = x
      · subst hax
        obtain ⟨o, ho, h1, h2⟩ := hxo
        exact absurd (hkeep o
          (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl ho)))))
          (fun hc => hc (by unfold CellHits; omega))
      · exact hmem' a hax

/-- The complete hWSA-base chain: from the entry-anchored base at `u` through
the callee step, the `slot`-setVar and the single-cell slot-store, to the
entry-anchored base at the stored bumped state.  The remaining semantic cores
(`hsp`/`hfmp`/`hcells`, the store-facts, `ArenaReady`s) are hypotheses. -/
theorem p4Loop31_baseStored {F : Type}
    {entry u post : PanSemStateFiniteExact 64 F} {w w_l : BitVec 64}
    {mem' : RiscV.Word 64 → HolWordLab 64}
    (hbase : PtxRelBase true entry u)
    (hcallee : WorldStep (fun _ => []) ["heap_ptr"] stdKeep RetListSlotStrong
      (callEntryStateHOLFinite u ((HolFiniteMapExact.empty.update
        (ofString "l", .val (.word w_l))).update (ofString "esz", .val (.word 8))))
      (some (.returned (.val (.word w)))) post)
    (hsp : globN post "scratch_ptr" ≤ globN u "scratch_ptr")
    (hfmp : globN u "frame_mem_ptr" ≤ globN post "frame_mem_ptr")
    (hcells : PtxBoCells true entry u post)
    (hARs : ArenaReady {setVarHOLFinite (ofString "slot") (.val (.word w))
        {post with locals := u.locals} with memory := mem'})
    (hmem' : ∀ a, a ≠ w → mem' a =
      (setVarHOLFinite (ofString "slot") (.val (.word w)) {post with locals := u.locals}).memory a)
    (hty : ∀ S Nd, WorldTypedWith (setVarHOLFinite (ofString "slot") (.val (.word w))
          {post with locals := u.locals}) S Nd →
        IvlsDisj ((fun _ => []) (setVarHOLFinite (ofString "slot") (.val (.word w))
          {post with locals := u.locals})) (worldTypedIvls (setVarHOLFinite (ofString "slot")
          (.val (.word w)) {post with locals := u.locals}) S Nd) →
        (WorldTypedWith {setVarHOLFinite (ofString "slot") (.val (.word w))
            {post with locals := u.locals} with memory := mem'} S Nd ∧
          worldOwned {setVarHOLFinite (ofString "slot") (.val (.word w))
            {post with locals := u.locals} with memory := mem'} S Nd =
            worldOwned (setVarHOLFinite (ofString "slot") (.val (.word w))
              {post with locals := u.locals}) S Nd ∧
          TxEnv {setVarHOLFinite (ofString "slot") (.val (.word w))
            {post with locals := u.locals} with memory := mem'}) ∧
        (∃ o ∈ worldOwned (setVarHOLFinite (ofString "slot") (.val (.word w))
            {post with locals := u.locals}) S Nd, Inside (w.toNat, 8) o.1 (o.1 + o.2)))
    (hrec : ∀ r ∈ stdKeep, globN (setVarHOLFinite (ofString "slot") (.val (.word w))
          {post with locals := u.locals}) r.1 ≠ 0 → ∀ k ∈ r.2,
        memW {setVarHOLFinite (ofString "slot") (.val (.word w))
            {post with locals := u.locals} with memory := mem'}
            (globN (setVarHOLFinite (ofString "slot") (.val (.word w))
              {post with locals := u.locals}) r.1 + k) =
          memW (setVarHOLFinite (ofString "slot") (.val (.word w))
            {post with locals := u.locals}) (globN (setVarHOLFinite (ofString "slot")
              (.val (.word w)) {post with locals := u.locals}) r.1 + k))
    (hcells2 : PtxBoCells true entry (setVarHOLFinite (ofString "slot") (.val (.word w))
        {post with locals := u.locals}) {setVarHOLFinite (ofString "slot") (.val (.word w))
        {post with locals := u.locals} with memory := mem'}) :
    PtxRelBase true entry {setVarHOLFinite (ofString "slot") (.val (.word w))
      {post with locals := u.locals} with memory := mem'} := by
  have hb1 := p4Loop31_baseTransport hbase hcallee hsp hfmp hcells
  have hb2 : PtxRelBase true entry (setVarHOLFinite (ofString "slot")
      (.val (.word w)) {post with locals := u.locals}) :=
    ptxRelBase_with_locals hb1 (u.locals.update (ofString "slot", (.val (.word w) : ValueHOL 64)))
      post.clock
  have hstep2 : WorldStep (bufRegions ([] : BufList)) [] stdKeep NoExtra
      (setVarHOLFinite (ofString "slot") (.val (.word w)) {post with locals := u.locals}) none
      {setVarHOLFinite (ofString "slot") (.val (.word w)) {post with locals := u.locals}
        with memory := mem'} :=
    worldStep_congr_R rfl (p4Loop31_storeWorldStep hARs hmem' hty hrec)
  exact ptxRelBase_step_cells hb2 (by intro p hp; cases hp) (by intro p hp; cases hp)
    (fun g hg => absurd hg (by simp))
    ptxKeepSub_stdKeep hstep2
    (le_of_eq rfl) (le_of_eq rfl) hcells2

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
