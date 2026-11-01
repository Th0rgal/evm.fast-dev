import InitECandidate.Solver.Wave8GuestInv.ContractParts.C13

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.FinishChild

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

/-- Compose two bounds across a guard established on normal fall-through. -/
theorem seq_cut
    {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn P first a)
    (hp : Hoare P first (fun r t => r = none → Q t))
    (h2 : TerminatingProgBoundedOn Q second b) :
    TerminatingProgBoundedOn P (.seq first second) (a + b) := by
  intro F s hc hs hnt
  have hm := PanRunBounded.evaluateHOLFiniteState_metadata s first
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases he : evaluateHOLFiniteState s first with ⟨r, t⟩
  simp only [he] at hm hnt ⊢
  cases r with
  | none =>
    have hn : (evaluateHOLFiniteState s first).1 ≠ some .timeOut := by simp [he]
    have hb := h1 s hc hs hn
    have hq := hp.run s hc hs hn
    rw [he] at hb hq
    have ht := h2 t (hm.1.trans hc) (hq rfl) hnt
    exact ⟨by dsimp only at hb ht ⊢; omega, by dsimp only at hb ht ⊢; omega⟩
  | some r =>
    have hn : (evaluateHOLFiniteState s first).1 ≠ some .timeOut := by simpa [he] using hnt
    have hb := h1 s hc hs hn
    rw [he] at hb
    exact ⟨by dsimp only at hb ⊢; omega, hb.2⟩

theorem bound_mono
    {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {p : ProgHOL 64} {k : Nat} (h : TerminatingProgBoundedOn Q p k)
    (hp : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q s) :
    TerminatingProgBoundedOn P p k := fun s hc hs => h s hc (hp s hs)

theorem dec_cut
    {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64} {k : Nat}
    (hi : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init =
        some v → Q (setVarHOLFinite name v s))
    (hb : TerminatingProgBoundedOn Q body k) :
    TerminatingProgBoundedOn P (.dec name shape init body) k := by
  intro F s hc hs hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · rename_i v hv
    revert hnt
    split <;> intro hnt
    · simpa only [setVarHOLFinite] using hb (setVarHOLFinite name v s) hc (hi s v hs hv) hnt
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

theorem hoare_seq
    {P Q R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {a b : ProgHOL 64}
    (ha : Hoare P a (fun r s => r = none → Q s))
    (hb : Hoare Q b (fun r s => r = none → R s)) :
    Hoare P (.seq a b) (fun r s => r = none → R s) :=
  Hoare.seq ⟨fun s hc hs hn => ⟨ha.run s hc hs hn, fun hne he => (hne he).elim⟩⟩ hb

theorem hoare_ite
    {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (cond : ExpHOL 64) {a b : ProgHOL 64}
    (ha : Hoare P a (fun r s => r = none → Q s))
    (hb : Hoare P b (fun r s => r = none → Q s)) :
    Hoare P (.ite cond a b) (fun r s => r = none → Q s) :=
  Hoare.ite (ha.mono fun _ h => h.1) (hb.mono fun _ h => h.1)
    (fun _ _ h => by cases h)

/-- While the child is still current, its saved local agrees with `ev`. -/
def Current : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => EvmInv s ∧ locN s "child" = globN s "ev"

theorem current_locals : LocalsOnly ["child"] Current := by
  intro F s ls k hl hs
  exact ⟨localsFree_evmInv s ls k hs.1,
    (locN_congr s ls k "child" (hl "child" (by simp))).trans hs.2⟩

theorem current_guest {F : Type} (s : PanSemStateFiniteExact 64 F) (h : Current s) :
    GuestInv s := evmInv_guestInv s h.1

theorem current_rollback {F : Type} (s : PanSemStateFiniteExact 64 F) (h : Current s) :
    RollbackReady s := by
  unfold RollbackReady
  rw [h.2]
  exact rollbackReadyAt_of_evmInv s h.1

theorem rollback_guest {F : Type} (s : PanSemStateFiniteExact 64 F) (h : RollbackReady s) :
    GuestInv s := h.1.1

theorem current_step {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {gw : List String} (h : Current s) (hs : EvmStep gw s post)
    (hev : ofString "ev" ∉ gw.map ofString) :
    Current { post with locals := s.locals } := by
  refine ⟨localsFree_evmInv post s.locals post.clock hs.1, ?_⟩
  change locN s "child" = globN post "ev"
  rw [h.2]
  simp only [globN, hs.2.2.1 _ hev]

/-- A part of a fixed buffer avoids the world and every frame object. -/
theorem evm_buffer_part {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hi : EvmInvAt s S) (hw : WorldTypedWith s S Nd)
    (gn : String × Nat) (hg : gn ∈ globalBuffers)
    (hu : gn.1 ∉ typedRecords.map Prod.fst) (n : Nat) (hn : n ≤ gn.2) :
    ∀ j ∈ worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten,
      Disj (bufferRegion s (gn.1, n)) j := by
  intro j hj
  rcases List.mem_append.mp hj with hj | hj
  · exact bufferRegion_disj_le hw gn hg hu n hn j hj
  · obtain ⟨os, hos, hj⟩ := List.mem_flatten.mp hj
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.mp hos
    have hf : bufferRegion s gn ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨gn, hg, rfl⟩
    have hd := (hi.2.2.2.2.2.2.2.2.1 ec hec j hj).2 _ hf
    have hd := hd.flip
    by_cases hz : globN s gn.1 = 0
    · exact Or.inl (by simp [bufferRegion, hz])
    · simp only [bufferRegion, hz, ↓reduceIte] at hd ⊢
      unfold Disj at hd ⊢
      dsimp only at hd ⊢
      omega

def createBuffers : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl :=
  fun s => [bufferRegion s ("keccak_pad", 136), bufferRegion s ("keccak_st", 200),
    bufferRegion s ("mpt_nib_scratch", 64), bufferRegion s ("sk_buf", 52)]

theorem evm_createBuffers {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) :
    EvmAvoids createBuffers s := by
  obtain ⟨ha, S, hi⟩ := (evmInv_iff_at s).mp h
  obtain ⟨Nd, hw⟩ := (worldTyped_iff_with s S).mp hi.1
  refine ⟨ha, S, hi, Nd, hw.2.2.2, ?_⟩
  intro i hm
  simp only [createBuffers, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact evm_buffer_part hi hw ("keccak_pad", 136) (by decide) (by decide) 136 (by decide)
  · exact evm_buffer_part hi hw ("keccak_st", 200) (by decide) (by decide) 200 (by decide)
  · exact evm_buffer_part hi hw ("mpt_nib_scratch", 64) (by decide) (by decide) 64 (by decide)
  · exact evm_buffer_part hi hw ("sk_buf", 64) (by decide) (by decide) 52 (by decide)

theorem lookup_finish_child : originalRuntimeCode.lookup (ofString "finish_child") =
    some ((sourceFunctionEntry Guest.Software.guestFn_finish_child).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 583 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_finish_child) rfl

theorem lookup_rollback_child_access : originalRuntimeCode.lookup (ofString "rollback_child_access") =
    some ((sourceFunctionEntry Guest.Software.guestFn_rollback_child_access).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 593 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rollback_child_access) rfl


/-- Changing the two output words leaves the child's access-table guard intact. -/
theorem rollback_output_frame {F : Type} {s post : PanSemStateFiniteExact 64 F} {c : Nat}
    (hs : RollbackReadyAt s c) (hp : GuestInv post)
    (hg : post.globals = s.globals)
    (hm : ∀ a : BitVec 64, a ≠ BitVec.ofNat 64 (c + 120) →
      a ≠ BitVec.ofNat 64 (c + 128) → post.memory a = s.memory a) :
    RollbackReadyAt post c := by
  have hc : c + 280 < 2 ^ 64 := by
    rcases hs.2.1 with ha | ha
    · have := hs.1.2.2.1
      have : heapLimit < 2 ^ 64 := by decide
      have := ha.2
      omega
    · have : scratchEnd < 2 ^ 64 := by decide
      have := ha.2
      omega
  have hn (a : Nat) (ha : a < 2 ^ 64) (h1 : a ≠ c + 120) (h2 : a ≠ c + 128) :
      memW post a = memW s a := by
    unfold memW
    rw [hm]
    · intro he
      have he := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
        Nat.mod_eq_of_lt (show c + 120 < 2 ^ 64 by omega)] at he
      exact h1 he
    · intro he
      have he := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
        Nat.mod_eq_of_lt (show c + 128 < 2 ^ 64 by omega)] at he
      exact h2 he
  have hk (k : Nat) (h : k ∈ [168, 176]) : memW post (c + k) = memW s (c + k) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> exact hn _ (by omega) (by omega) (by omega)
  have hu (k : Nat) (h : k ∈ [168, 176]) :
      ∀ i ∈ htabFootprint s (memW s (c + k)), IvlUnhit s post i := by
    intro i hi a ha hh
    have hd := ((hs.2.2.2.1 k h).2 i hi).2
    have hi8 := ((hs.2.2.2.1 k h).1.1 i hi).2.1
    apply hm a
    all_goals
      intro he
      have he := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c + 120 < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show c + 128 < 2 ^ 64 by omega)] at he
      unfold CellHits at hh
      rcases hd with hd | hd | hd | hd <;> omega
  have hf (k : Nat) (h : k ∈ [168, 176]) :
      htabFootprint post (memW s (c + k)) = htabFootprint s (memW s (c + k)) := by
    let t := memW s (c + k)
    have hh := (hs.2.2.2.1 k h).1.1 (t, 88) (by simp [t, htabFootprint])
    exact (htabFootprint_eq_of_hdr_unhit hh.2.1
      (Nat.le_trans hh.1.2 (by decide))
      (hu k h (t, 88) (by simp [t, htabFootprint]))).2
  refine ⟨⟨hp, ?_⟩, ?_, wordsOK_transfer hs.1.1 hp hs.2.2.1, ?_, ?_⟩
  · simpa only [ArenaOK, globN, hg] using hs.1.2
  · simpa only [Allocated, globN, hg] using hs.2.1
  · intro k h
    rw [hk k h]
    refine ⟨htabWF_congr_unhit hs.1.1 hp (hs.2.2.2.1 k h).1 (hu k h), ?_⟩
    rw [hf k h]
    intro i hi
    refine ⟨?_, ((hs.2.2.2.1 k h).2 i hi).2⟩
    simpa only [Allocated, globN, hg] using ((hs.2.2.2.1 k h).2 i hi).1
  · rw [hk 168 (by simp), hk 176 (by simp), hf 168 (by simp), hf 176 (by simp)]
    exact hs.2.2.2.2

/-- The guard ignores all globals except the three allocator pointers. -/
theorem rollback_globals {F : Type} {s post : PanSemStateFiniteExact 64 F} {c : Nat}
    (hs : RollbackReadyAt s c) (hp : GuestInv post)
    (hm : post.memory = s.memory)
    (hh : globN post "heap_ptr" = globN s "heap_ptr")
    (hf : globN post "frame_mem_ptr" = globN s "frame_mem_ptr")
    (hsc : globN post "scratch_ptr" = globN s "scratch_ptr") :
    RollbackReadyAt post c := by
  have hw : memW post = memW s := memW_congr hm
  have hfp (t : Nat) : htabFootprint post t = htabFootprint s t := by
    simp only [htabFootprint, hdr, hw]
  refine ⟨⟨hp, ?_⟩, ?_, wordsOK_transfer hs.1.1 hp hs.2.2.1, ?_, ?_⟩
  · simpa only [ArenaOK, hh, hf, hsc] using hs.1.2
  · simpa only [Allocated, hh, hsc] using hs.2.1
  · intro k hk
    rw [hw]
    refine ⟨htabWF_congr_unhit hs.1.1 hp (hs.2.2.2.1 k hk).1
      (fun _ _ a _ _ => congrFun hm a), ?_⟩
    rw [hfp]
    intro i hi
    refine ⟨?_, ((hs.2.2.2.1 k hk).2 i hi).2⟩
    simpa only [Allocated, hh, hsc] using ((hs.2.2.2.1 k hk).2 i hi).1
  · simpa only [hw, hfp] using hs.2.2.2.2


private def dropDecls : Nat → ProgHOL 64 → ProgHOL 64
  | 0, p => p
  | n + 1, .dec _ _ _ p => dropDecls n p
  | _, p => p

private def leftSeq : ProgHOL 64 → ProgHOL 64
  | .seq a _ => a
  | p => p

private def rightSeq : ProgHOL 64 → ProgHOL 64
  | .seq _ b => b
  | p => p

/-- Literal pieces of the installed body, with definitional decomposition. -/
def body : ProgHOL 64 := (sourceFunctionEntry Guest.Software.guestFn_finish_child).2.2.1
def core : ProgHOL 64 := dropDecls 11 body
def prelude : ProgHOL 64 := leftSeq core
def pop : ProgHOL 64 := rightSeq core
def branches : ProgHOL 64 := leftSeq (rightSeq (rightSeq pop))
def cleanup : ProgHOL 64 := rightSeq (rightSeq (rightSeq pop))

structure Calls : Prop where
  address_to_u256 : TerminatingFunBoundedOn GuestInv (ofString "address_to_u256") K.address_to_u256
  create_finish : TerminatingFunBoundedOn GuestInv (ofString "create_finish") K.create_finish
  credit_state_gas_refund : TerminatingFunBoundedOn GuestInv (ofString "credit_state_gas_refund") K.credit_state_gas_refund
  frame_halt : TerminatingFunBoundedOn GuestInv (ofString "frame_halt") K.frame_halt
  frame_mem_release : TerminatingFunBoundedOn GuestInv (ofString "frame_mem_release") K.frame_mem_release
  incorporate_child_on_error : TerminatingFunBoundedOn GuestInv (ofString "incorporate_child_on_error") K.incorporate_child_on_error
  incorporate_child_on_success : TerminatingFunBoundedOn GuestInv (ofString "incorporate_child_on_success") K.incorporate_child_on_success
  memcpy : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.memcpy
  min : TerminatingFunBoundedOn GuestInv (ofString "min") K.min
  pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.pc_add
  refill_frame_state_gas : TerminatingFunBoundedOn GuestInv (ofString "refill_frame_state_gas") K.refill_frame_state_gas
  rollback_child_access : TerminatingFunBoundedOn RollbackReady (ofString "rollback_child_access") K.rollback_child_access
  scratch_release : TerminatingFunBoundedOn GuestInv (ofString "scratch_release") K.scratch_release
  set_retdata : TerminatingFunBoundedOn GuestInv (ofString "set_retdata") K.set_retdata
  stack_push : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.stack_push
  state_restore : TerminatingFunBoundedOn GuestInv (ofString "state_restore") K.state_restore


theorem skip_bound : TerminatingProgBoundedOn GuestInv .skip 0 :=
  TerminatingProgBoundedOn.of_clock clock_skip
theorem return_bound (e : ExpHOL 64) : TerminatingProgBoundedOn GuestInv (.return e) 0 :=
  TerminatingProgBoundedOn.of_clock (fun s => clock_return s e)
theorem store_bound (a v : ExpHOL 64) : TerminatingProgBoundedOn GuestInv (.store a v) 0 :=
  TerminatingProgBoundedOn.of_clock (fun s => clock_store s a v)

open Lean Elab Tactic Meta in
private def findCalleeBound (fn : Expr) : TacticM Expr := do
  for d in ← getLCtx do
    let t := d.type
    if t.isAppOf ``TerminatingFunBoundedOn then
      if ← withReducible (isDefEq t.getAppArgs[1]! fn) then return d.toExpr
  throwError "missing callee bound for {fn}"

open Lean Elab Tactic Meta in
private partial def proveGuestBound (prog : Expr) : TacticM Expr := do
  let p ← whnf prog
  let a := p.getAppArgs
  match p.getAppFn.constName? with
  | some ``ProgHOL.seq =>
    mkAppM ``TerminatingProgBoundedOn.seq_guestInv #[← proveGuestBound a[2]!, ← proveGuestBound a[3]!]
  | some ``ProgHOL.ite =>
    mkAppOptM ``TerminatingProgBoundedOn.ite_on
      #[some (mkConst ``GuestInv), some a[2]!, none, none, none, none,
        some (← proveGuestBound a[3]!), some (← proveGuestBound a[4]!)]
  | some ``ProgHOL.dec =>
    mkAppM ``TerminatingProgBoundedOn.dec_on
      #[mkConst ``localsFree_guestInv, a[2]!, a[3]!, a[4]!, ← proveGuestBound a[5]!]
  | some ``ProgHOL.decCall =>
    mkAppM ``TerminatingProgBoundedOn.decCall_guestInv
      #[← findCalleeBound a[4]!, a[2]!, a[3]!, a[5]!, ← proveGuestBound a[6]!]
  | some ``ProgHOL.call => do
    let ret ← whnf a[2]!
    let pair ← whnf ret.getAppArgs[1]!
    let h ← whnf pair.getAppArgs[3]!
    let hf ← findCalleeBound a[3]!
    if h.isAppOf ``Option.none then
      mkAppM ``TerminatingProgBoundedOn.call_guestInv #[hf, pair.getAppArgs[2]!, a[4]!]
    else
      let hd ← whnf h.getAppArgs[1]!
      let hd2 ← whnf hd.getAppArgs[3]!
      mkAppM ``TerminatingProgBoundedOn.callHandle_guestInv
        #[hf, pair.getAppArgs[2]!, hd.getAppArgs[2]!, hd2.getAppArgs[2]!,
          ← proveGuestBound hd2.getAppArgs[3]!, a[4]!]
  | some ``ProgHOL.skip => pure (mkConst ``skip_bound)
  | some ``ProgHOL.return => mkAppM ``return_bound #[a[2]!]
  | some ``ProgHOL.store => mkAppM ``store_bound #[a[2]!, a[3]!]
  | _ => throwError "unsupported program: {p.getAppFn}"

open Lean Elab Tactic Meta in
elab "finish_child_guest_bound" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  unless target.isAppOf ``TerminatingProgBoundedOn do throwError "expected a guarded program bound"
  let proof ← proveGuestBound target.getAppArgs[1]!
  goal.assignIfDefEq proof
  replaceMainGoal []

theorem cleanup_bound (h : Calls) : TerminatingProgBoundedOn GuestInv cleanup
    ((K.scratch_release + 1) + (K.frame_mem_release + 1) + (K.pc_add + 1)) := by
  rcases h with ⟨ha, hc, hcr, hfh, hfm, he, hs, hm, hmin, hp, hr, hb, hsr, hsd, hsp, hst⟩
  apply TerminatingProgBoundedOn.mono_bound (b := _)
  · change TerminatingProgBoundedOn GuestInv (.seq _ (.seq _ (.seq _ (.return _)))) _
    finish_child_guest_bound
  · omega

theorem rollback_entry : CallEntryOn RollbackReady RollbackReady
    (ofString "rollback_child_access") [.var .local (ofString "child")] := by
  intro F s vals b ls ret hc hs ha hl
  have hx := callee_param_one s (ofString "rollback_child_access") (ofString "child") .one
    ((sourceFunctionEntry Guest.Software.guestFn_rollback_child_access).2.2.1)
    ((sourceFunctionEntry Guest.Software.guestFn_rollback_child_access).2.2.2)
    (by rw [hc]; exact lookup_rollback_child_access) vals b ls ret ha hl
  exact localsOnly_rollbackReady s ls (s.clock - 1)
    (fun n hn => by simp only [List.mem_singleton] at hn; subst n; exact hx) hs

def errorCost : Nat := (K.rollback_child_access + 1) + (K.incorporate_child_on_error + 1) +
  max (K.credit_state_gas_refund + 1) 0 + (K.set_retdata + 1) + (K.stack_push + 1)
def createSuccessCost : Nat := (K.incorporate_child_on_success + 1) + (K.set_retdata + 1) +
  (K.address_to_u256 + 1) + (K.stack_push + 1)
def callSuccessCost : Nat := (K.incorporate_child_on_success + 1) + (K.set_retdata + 1) +
  (K.stack_push + 1)
def branchCost : Nat := max (max errorCost createSuccessCost)
  (max errorCost callSuccessCost + (K.min + 1) + max (K.memcpy + 1) 0)

/-- After the prefix, only the first call of either error branch needs a guard. -/
theorem branches_bound (h : Calls) : TerminatingProgBoundedOn RollbackReady branches branchCost := by
  rcases h with ⟨ha, hc, hcr, hfh, hfm, he, hs, hm, hmin, hp, hr, hb, hsr, hsd, hsp, hst⟩
  apply TerminatingProgBoundedOn.mono_bound
  · change TerminatingProgBoundedOn RollbackReady (.ite _ (.dec _ _ _ (.ite _ _ _)) (.seq (.ite _ _ _) _)) _
    apply TerminatingProgBoundedOn.ite_on
    · apply TerminatingProgBoundedOn.dec_onLocals localsOnly_rollbackReady _ (by decide)
      apply TerminatingProgBoundedOn.ite_on
      · apply TerminatingProgBoundedOn.seq_guestInv_after
          (TerminatingProgBoundedOn.call_on hb _ _ rollback_entry) rollback_guest
        finish_child_guest_bound
      · refine @bound_mono RollbackReady GuestInv _
          ((K.incorporate_child_on_success + 1) + ((K.set_retdata + 1) +
            (K.address_to_u256 + (K.stack_push + 1) + 1))) ?_ @rollback_guest
        finish_child_guest_bound
    · apply TerminatingProgBoundedOn.seq_guestInv_after (hPG := rollback_guest)
      · apply TerminatingProgBoundedOn.ite_on
        · apply TerminatingProgBoundedOn.seq_guestInv_after
            (TerminatingProgBoundedOn.call_on hb _ _ rollback_entry) rollback_guest
          finish_child_guest_bound
        · refine @bound_mono RollbackReady GuestInv _
            ((K.incorporate_child_on_success + 1) + ((K.set_retdata + 1) +
              (K.stack_push + 1))) ?_ @rollback_guest
          finish_child_guest_bound
      · finish_child_guest_bound
  · unfold branchCost errorCost createSuccessCost callSuccessCost
    omega


def preludeCost : Nat := max (max
  ((K.create_finish + 1) + (K.state_restore + 1) + (K.refill_frame_state_gas + 1) +
    (K.frame_halt + 1)) (K.state_restore + 1)) 0

theorem prelude_bound (h : Calls) : TerminatingProgBoundedOn GuestInv prelude preludeCost := by
  rcases h with ⟨ha, hc, hcr, hfh, hfm, he, hs, hm, hmin, hp, hr, hb, hsr, hsd, hsp, hst⟩
  apply TerminatingProgBoundedOn.mono_bound
  · change TerminatingProgBoundedOn GuestInv (.ite _ (.dec _ _ _ (.ite _ (.dec _ _ _ _) _)) .skip) _
    finish_child_guest_bound
  · unfold preludeCost
    omega

theorem current_step_entry {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (ls : HolFiniteMapExact MlS (ValueHOL 64)) {gw : List String}
    (hs : Current s) (hq : EvmStep gw (callEntryStateHOLFinite s ls) post)
    (hev : ofString "ev" ∉ gw.map ofString) : Current { post with locals := s.locals } := by
  refine ⟨localsFree_evmInv post s.locals post.clock hq.1, ?_⟩
  change locN s "child" = globN post "ev"
  have hg : s.globals.lookup (ofString "ev") = post.globals.lookup (ofString "ev") := hq.2.2.1 _ hev
  rw [hs.2]
  simp only [globN, hg]

/-- Callees preserve the saved child across ordinary return. -/
theorem current_call {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {gw : List String} {fn : MlS} (h : EvmKeeps P gw fn)
    (hev : ofString "ev" ∉ gw.map ofString) (args : List (ExpHOL 64))
    (he : CallEntryOn Current P fn args) :
    Hoare Current (.call (some (none, none)) fn args) (fun r s => r = none → Current s) :=
  Hoare.call0 h he
    (fun _s ls _post v _ hs hq _ => current_step_entry ls hs (hq (Or.inl ⟨v, rfl⟩)) hev)
    (fun _ _ hn _ he => (hn he).elim)

theorem current_evm_entry (fn : MlS) (args : List (ExpHOL 64)) :
    CallEntryOn Current EvmInv fn args :=
  fun s _ _ ls _ _ hs _ _ => localsFree_evmInv s ls _ hs.1

theorem current_create_entry (args : List (ExpHOL 64)) :
    CallEntryOn Current (EvmAvoids createBuffers) (ofString "create_finish") args :=
  fun s _ _ ls _ _ hs _ _ => evm_createBuffers _ (localsFree_evmInv s ls _ hs.1)


/-- A usable rollback guard before the parent globals are installed. -/
def AtChild : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => RollbackReady s ∧ locN s "child" = globN s "ev"

def EmptyBad {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ¬ ∃ w : BitVec 64, s.globals.lookup (ofString "evm_empty") = some (.val (.word w))

def outputStore (off : Nat) (src : ExpHOL 64) : ProgHOL 64 :=
  .store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) src

def clearOutput : ProgHOL 64 :=
  .seq (outputStore 120 (.var .global (ofString "evm_empty")))
    (outputStore 128 (.const 0))

theorem global_word_of_pos {F : Type} (s : PanSemStateFiniteExact 64 F) (n : String)
    (h : 0 < globN s n) : ∃ w : BitVec 64,
      s.globals.lookup (ofString n) = some (.val (.word w)) := by
  rcases he : s.globals.lookup (ofString n) with _ | ⟨⟨w⟩⟩ | vs | ⟨nm, vs⟩
  · simp [globN, he] at h
  · exact ⟨w, rfl⟩
  · simp [globN, he] at h
  · simp [globN, he] at h

theorem store_output_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hs : AtChild s) (off : Nat) (hoff : off = 120 ∨ off = 128)
    (src : ExpHOL 64) (v : BitVec 64)
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) src =
      some (.val (.word v))) :
    (evaluateHOLFiniteState s (outputStore off src)).1 = none →
      AtChild (evaluateHOLFiniteState s (outputStore off src)).2 := by
  have hepos : 0 < globN s "ev" := by
    rw [← hs.2]
    rcases hs.1.2.1 with ha | ha
    · have : 0 < sourceBase := by decide
      have := ha.1
      omega
    · have := ha.1
      have := hs.1.1.2.2.2.1
      have := hs.1.1.2.2.2.2.1
      have : 0 < scratchStart := by decide
      omega
  obtain ⟨w, hw⟩ := global_word_of_pos s "ev" hepos
  have he : locN s "child" = w.toNat := by simpa only [globN, hw] using hs.2
  have hadd : w + BitVec.ofNat 64 off = BitVec.ofNat 64 (locN s "child" + off) := by
    simp only [he, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have had : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) =
        some (.val (.word (BitVec.ofNat 64 (locN s "child" + off)))) := by
    simp [evalHOLExact, evalListHOLExact, hw, wordOpHOL, wordOp, valueIsWord, valueWord, hadd]
  rw [outputStore, evaluateHOLFiniteState_store, had, hv]
  simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL]
  split_ifs with hd <;> simp only
  · intro _
    refine ⟨rollback_output_frame hs.1
      (guestInv_congr (s := s) rfl rfl rfl rfl hs.1.1.1) rfl ?_, hs.2⟩
    intro a h1 h2
    rcases hoff with rfl | rfl
    · exact if_neg h1
    · exact if_neg h2
  · intro h
    cases h

theorem store_metadata {F : Type} (s : PanSemStateFiniteExact 64 F) (a v : ExpHOL 64) :
    (evaluateHOLFiniteState s (.store a v)).2.globals = s.globals ∧
    (evaluateHOLFiniteState s (.store a v)).2.locals = s.locals := by
  rw [evaluateHOLFiniteState_store]
  constructor <;> (repeat' split) <;> rfl

/-- Non-word `evm_empty` is retained; the later one-word declaration rejects it. -/
theorem clearOutput_hoare : Hoare Current clearOutput
    (fun r s => r = none → GuestInv s ∧ (RollbackReady s ∨ EmptyBad s)) := by
  let W : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
    fun s => GuestInv s ∧ (AtChild s ∨ EmptyBad s)
  apply hoare_seq (Q := W)
  · refine ⟨fun s hc hs hn he => ?_⟩
    refine ⟨guestInv_evaluate s _ (current_guest s hs), ?_⟩
    by_cases hw : ∃ w : BitVec 64, s.globals.lookup (ofString "evm_empty") = some (.val (.word w))
    · obtain ⟨w, hw⟩ := hw
      exact Or.inl (store_output_word s ⟨current_rollback s hs, hs.2⟩ 120 (Or.inl rfl)
        _ w (by simpa only [evalHOLExact] using hw) he)
    · right
      unfold EmptyBad
      unfold outputStore
      rw [(store_metadata s _ _).1]
      exact hw
  · refine ⟨fun s hc hs hn he => ?_⟩
    refine ⟨guestInv_evaluate s _ hs.1, ?_⟩
    rcases hs.2 with hs | hs
    · left
      exact (store_output_word s hs 128 (Or.inr rfl) (.const 0) 0 rfl he).1
    · right
      unfold EmptyBad at hs ⊢
      unfold outputStore
      rw [(store_metadata s _ _).1]
      exact hs


def ReadyBad : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ (RollbackReady s ∨ EmptyBad s)

def Pending : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ (RollbackReady s ∨ (locN s "kind" = 2 ∧ EmptyBad s))

theorem hoare_post
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Q R : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    {p : ProgHOL 64} (h : Hoare P p Q)
    (hq : ∀ {F : Type} r (s : PanSemStateFiniteExact 64 F), Q r s → R r s) : Hoare P p R :=
  ⟨fun s hc hs hn => hq _ _ (h.run s hc hs hn)⟩

theorem readyBad_locals : PostLocalsOnly ["child"] (fun r s => r = none → ReadyBad s) := by
  intro F r s ls hl hs he
  obtain ⟨hg, hr | hb⟩ := hs he
  · exact ⟨guestInv_with_locals_clock s ls _ hg,
      Or.inl (localsOnly_rollbackReady s ls _ hl hr)⟩
  · exact ⟨guestInv_with_locals_clock s ls _ hg, Or.inr hb⟩

theorem current_dec {name : MlS} {shape : ShapeHOL} {init : ExpHOL 64} {p : ProgHOL 64}
    (hne : ofString "child" ≠ name)
    (h : Hoare Current p (fun r s => r = none → ReadyBad s)) :
    Hoare Current (.dec name shape init p) (fun r s => r = none → ReadyBad s) :=
  Hoare.dec (fun n hn => by simp only [List.mem_singleton] at hn; subst n; exact hne)
    (fun s v hs _ => current_locals.setVar
      (fun n hn => by simp only [List.mem_singleton] at hn; subst n; exact hne) v s hs)
    h readyBad_locals (fun _ _ h => by cases h)

theorem current_readyBad {F : Type} (s : PanSemStateFiniteExact 64 F) (h : Current s) :
    ReadyBad s := ⟨current_guest s h, Or.inl (current_rollback s h)⟩

structure Keeps : Prop where
  create_finish : EvmKeeps (EvmAvoids createBuffers)
    ["heap_ptr", "journal_n", "scratch_ptr"] (ofString "create_finish")
  frame_halt : EvmKeeps EvmInv [] (ofString "frame_halt")
  refill_frame_state_gas : EvmKeeps EvmInv [] (ofString "refill_frame_state_gas")
  state_restore : EvmKeeps EvmInv ["heap_ptr", "journal_n"] (ofString "state_restore")

def handler : ProgHOL 64 :=
  .seq (.call (some (none, none)) (ofString "state_restore") [.var .local (ofString "csnap")])
    (.seq (.call (some (none, none)) (ofString "refill_frame_state_gas") [])
      (.seq (.call (some (none, none)) (ofString "frame_halt") [.var .local (ofString "err")])
        clearOutput))

def createCall : ProgHOL 64 :=
  .call (some (none, some (ofString "EvmErr", ofString "err", handler)))
    (ofString "create_finish") [.var .local (ofString "msg"), .var .local (ofString "child")]

theorem handler_hoare (h : Keeps) : Hoare Current handler (fun r s => r = none → ReadyBad s) := by
  apply hoare_seq (current_call h.state_restore (by decide) _ (current_evm_entry _ _))
  apply hoare_seq (current_call h.refill_frame_state_gas (by simp) _ (current_evm_entry _ _))
  exact hoare_seq (current_call h.frame_halt (by simp) _ (current_evm_entry _ _)) clearOutput_hoare

theorem createCall_hoare (h : Keeps) : Hoare Current createCall (fun r s => r = none → ReadyBad s) := by
  refine Hoare.callH (Ph := Current) h.create_finish (current_create_entry _) ?_ ?_ (handler_hoare h) ?_
  · intro F s ls post v hc hs hq he
    exact current_readyBad _ (current_step_entry ls hs (hq (Or.inl ⟨v, rfl⟩)) (by decide))
  · intro F s ls post v hc hs hq
    exact current_locals.setVar (by decide) v _
      (current_step_entry ls hs (hq (Or.inr ⟨_, v, rfl, by decide⟩)) (by decide))
  · intro F r s hn _ he
    exact (hn he).elim

private def yesBranch : ProgHOL 64 → ProgHOL 64
  | .ite _ a _ => a
  | p => p

def createPrelude : ProgHOL 64 := yesBranch prelude

theorem createPrelude_hoare (h : Keeps) :
    Hoare Current createPrelude (fun r s => r = none → ReadyBad s) := by
  change Hoare Current (.dec _ _ _ (.ite _ (.dec _ _ _ createCall) _)) _
  apply current_dec (by decide)
  apply hoare_ite
  · exact current_dec (by decide) (createCall_hoare h)
  · exact hoare_post (current_call h.state_restore (by decide) _ (current_evm_entry _ _))
      (fun _ s hs he => current_readyBad s (hs he))

def kindIsCreate : ExpHOL 64 := .cmp .equal (.var .local (ofString "kind")) (.const 2)

theorem kind_true {F : Type} {s : PanSemStateFiniteExact 64 F} (h : CondTrue kindIsCreate s) :
    locN s "kind" = 2 := by
  obtain ⟨w, hw, hn⟩ := h
  obtain ⟨a, b, ha, hb, he⟩ := cond_local s .equal "kind" _ w hw
  cases evalAt_const s 2 _ hb
  rw [he] at hn
  simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hn
  by_cases hab : a = 2
  · subst a
    exact ha.symm
  · simp only [beq_iff_eq, if_neg hab] at hn
    exact (hn rfl).elim


theorem local_hoare_avoids (n : Nat) (p : ProgHOL 64)
    (hp : avoidsLocal (ofString "kind") p = true) :
    Hoare (fun s => locN s "kind" = n) p (fun r s => r = none → locN s "kind" = n) := by
  refine ⟨fun s hc hs hn he => ?_⟩
  have hl := evaluate_avoidsLocal_flowing (ofString "kind") p hp s (Or.inl he)
  simpa only [locN, hl] using hs

theorem local_hoare_dec (n : Nat) {name : MlS} {shape : ShapeHOL} {init : ExpHOL 64} {p : ProgHOL 64}
    (hne : ofString "kind" ≠ name)
    (h : Hoare (fun s => locN s "kind" = n) p (fun r s => r = none → locN s "kind" = n)) :
    Hoare (fun s => locN s "kind" = n) (.dec name shape init p)
      (fun r s => r = none → locN s "kind" = n) := by
  refine Hoare.dec (names := ["kind"])
    (fun k hk => by simp only [List.mem_singleton] at hk; subst k; exact hne) ?_ h ?_
    (fun _ _ he => by cases he)
  · intro F s v hs hv
    exact (locN_setVar_ne s "kind" name v hne).trans hs
  · intro F r s ls hl hs he
    exact (locN_congr s ls s.clock "kind" (hl "kind" (by simp))).trans (hs he)

theorem createCall_kind (h : Keeps) (n : Nat) :
    Hoare (fun s => locN s "kind" = n) createCall (fun r s => r = none → locN s "kind" = n) := by
  obtain ⟨ps, b, ret, hl, _⟩ := h.create_finish
  have ht : FunSpec (fun _ => True) (fun _ _ _ => True) (ofString "create_finish") :=
    ⟨ps, b, ret, hl, fun _ _ _ _ _ => trivial⟩
  refine Hoare.callH (Ph := fun s => locN s "kind" = n) ht
    (fun _ _ _ _ _ _ _ _ _ => trivial) ?_ ?_
    (local_hoare_avoids n handler (by decide)) ?_
  · intro F s ls post v hc hs hq he
    exact hs
  · intro F s ls post v hc hs hq
    exact (locN_setVar_ne _ "kind" (ofString "err") v (by decide)).trans hs
  · intro F r s hn hc he
    exact (hn he).elim

theorem createPrelude_kind (h : Keeps) (n : Nat) :
    Hoare (fun s => locN s "kind" = n) createPrelude (fun r s => r = none → locN s "kind" = n) := by
  change Hoare _ (.dec _ _ _ (.ite _ (.dec _ _ _ createCall) _)) _
  apply local_hoare_dec n (by decide)
  apply hoare_ite
  · exact local_hoare_dec n (by decide) (createCall_kind h n)
  · exact local_hoare_avoids n _ (by decide)

theorem prelude_hoare (h : Keeps) : Hoare Current prelude (fun r s => r = none → Pending s) := by
  change Hoare Current (.ite kindIsCreate createPrelude .skip) _
  apply Hoare.ite
  · refine ⟨fun s hc hs hn he => ?_⟩
    obtain ⟨hg, hr | hb⟩ := (createPrelude_hoare h).run s hc hs.1 hn he
    · exact ⟨hg, Or.inl hr⟩
    · have hk := (createPrelude_kind h 2).run s hc (kind_true hs.2) hn he
      exact ⟨hg, Or.inr ⟨hk, hb⟩⟩
  · exact Hoare.skip (fun s hs _ => ⟨current_guest s hs.1, Or.inl (current_rollback s hs.1)⟩)
  · intro F s hs he
    cases he


theorem branches_bad_clock {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hk : locN s "kind" = 2) (hb : EmptyBad s) :
    (evaluateHOLFiniteState s branches).2.clock = s.clock := by
  have hl : s.locals.lookup (ofString "kind") = some (.val (.word 2)) := by
    rcases he : s.locals.lookup (ofString "kind") with _ | ⟨⟨w⟩⟩ | vs | ⟨nm, vs⟩
    · simp [locN, he] at hk
    · have hw : w = 2 := BitVec.eq_of_toNat_eq (by simpa [locN, he] using hk)
      simp [hw]
    · simp [locN, he] at hk
    · simp [locN, he] at hk
  have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      kindIsCreate = some (.val (.word 1)) := by
    simp [kindIsCreate, evalHOLExact, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  change (evaluateHOLFiniteState s (.ite kindIsCreate
    (.dec (ofString "empty") .one (.var .global (ofString "evm_empty")) _) _)).2.clock = _
  rw [evaluateHOLFiniteState_ite, hcond]
  simp only [show (1 : BitVec 64) ≠ 0 by decide, ↓reduceIte]
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact]
  rcases he : s.globals.lookup (ofString "evm_empty") with _ | ⟨⟨w⟩⟩ | vs | ⟨nm, vs⟩
  · rfl
  · exact (hb ⟨w, he⟩).elim
  · simp only [shapeOfHOLExact, shapeEqHOL, Bool.false_eq_true, ↓reduceIte]
  · simp only [shapeOfHOLExact, shapeEqHOL, Bool.false_eq_true, ↓reduceIte]

theorem pending_branches_bound (h : Calls) : TerminatingProgBoundedOn Pending branches branchCost := by
  intro F s hc hs hn
  rcases hs.2 with hr | ⟨hk, hb⟩
  · exact branches_bound h s hc hr hn
  · have hh := branches_bad_clock s hk hb
    exact ⟨by omega, by omega⟩

theorem pending_guest {F : Type} (s : PanSemStateFiniteExact 64 F) (h : Pending s) :
    GuestInv s := h.1

theorem pending_assign (name : MlS) (src : ExpHOL 64)
    (hne : ∀ n ∈ (["heap_ptr", "frame_mem_ptr", "scratch_ptr", "evm_empty"] : List String),
      ofString n ≠ name) :
    Hoare Pending (.assign .global name src) (fun r s => r = none → Pending s) := by
  apply Hoare.assign
  · intro F s v hs hv he
    have hg : GuestInv (setKvarHOLFinite .global name v s) :=
      guestInv_congr (s := s) rfl rfl rfl rfl hs.1
    have hget (n : String) (hn : n ∈ (["heap_ptr", "frame_mem_ptr", "scratch_ptr", "evm_empty"] : List String)) :
        (setKvarHOLFinite .global name v s).globals.lookup (ofString n) = s.globals.lookup (ofString n) := by
      simp [setKvarHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.lookup_update,
        FUPDATE, Ne.symm (hne n hn)]
    have hgn (n : String) (hn : n ∈ (["heap_ptr", "frame_mem_ptr", "scratch_ptr", "evm_empty"] : List String)) :
        globN (setKvarHOLFinite .global name v s) n = globN s n := by
      simp only [globN, hget n hn]
    refine ⟨hg, ?_⟩
    rcases hs.2 with hr | ⟨hk, hb⟩
    · left
      exact rollback_globals hr hg rfl (hgn "heap_ptr" (by simp))
        (hgn "frame_mem_ptr" (by simp)) (hgn "scratch_ptr" (by simp))
    · right
      refine ⟨hk, ?_⟩
      unfold EmptyBad at hb ⊢
      rw [hget "evm_empty" (by simp)]
      exact hb
  · intro F s hs he
    cases he

def cleanupCost : Nat := (K.scratch_release + 1) + (K.frame_mem_release + 1) + (K.pc_add + 1)

theorem pop_bound (h : Calls) : TerminatingProgBoundedOn Pending pop (branchCost + cleanupCost) := by
  apply TerminatingProgBoundedOn.mono_bound
  · change TerminatingProgBoundedOn Pending (.seq (.assign .global (ofString "ev") _)
      (.seq (.assign .global (ofString "cur_cont") _) (.seq branches cleanup))) _
    apply seq_cut (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
      (pending_assign _ _ (by decide))
    apply seq_cut (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
      (pending_assign _ _ (by decide))
    exact TerminatingProgBoundedOn.seq_guestInv_after (pending_branches_bound h)
      pending_guest (cleanup_bound h)
  · unfold cleanupCost
    omega

theorem core_bound (h : Calls) (hk : Keeps) :
    TerminatingProgBoundedOn Current core (preludeCost + (branchCost + cleanupCost)) :=
  seq_cut (bound_mono (prelude_bound h) current_guest) (prelude_hoare hk) (pop_bound h)

theorem body_bound (h : Calls) (hk : Keeps) : TerminatingProgBoundedOn EvmInv body K.finish_child := by
  apply TerminatingProgBoundedOn.mono_bound (a := preludeCost + (branchCost + cleanupCost))
  · change TerminatingProgBoundedOn EvmInv (.dec (ofString "rec") .one _
      (.dec (ofString "child") .one (.var .global (ofString "ev")) _)) _
    apply TerminatingProgBoundedOn.dec_on localsFree_evmInv
    refine dec_cut _ _ _ (Q := Current) (k := preludeCost + (branchCost + cleanupCost)) ?_ ?_
    · intro F s v hs hv
      refine ⟨localsFree_evmInv s _ _ hs, ?_⟩
      simp only [evalHOLExact] at hv
      simp [locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, globN, hv]
    · iterate 9
        apply TerminatingProgBoundedOn.dec_onLocals current_locals _ (by decide)
      exact core_bound h hk
  · simp only [K.finish_child, preludeCost, branchCost, errorCost, createSuccessCost,
      callSuccessCost, cleanupCost, Nat.add_assoc, Nat.le_refl]

/-- Concrete body composition, using exactly the supplied callee bounds and EVM contracts. -/
theorem finish_child (h : Calls) (hk : Keeps) :
    TerminatingFunBoundedOn FinishReady (ofString "finish_child") K.finish_child :=
  ⟨_, _, _, lookup_finish_child, bound_mono (body_bound h hk) (fun _ hs => hs.1)⟩

end InitECandidate.Solver.Wave8GuestInv.FinishChild
