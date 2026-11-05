import InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec.Base
import InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.Common

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8Contracts.M23 (EvmStep EvmKeeps EvmAvoids GlobalsKept)
open InitECandidate.Solver.Wave8GuestInv.R11Shards

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem ro_is_zero_bytes :
    InitECandidate.Solver.Wave8Contracts.M15.ReadOnlyFn (ofString "is_zero_bytes") :=
  InitECandidate.Solver.Wave8Contracts.M15.readOnlyFn_of_guestAst
    19 (by rw [guestAst_len]; decide) Guest.Software.guestFn_is_zero_bytes rfl
    (fun _ => false) (fun _ h => by cases h) rfl

def precompileIndexCallees (f : MlS) : Bool :=
  f == ofString "is_zero_bytes"

theorem precompileIndexCallees_good :
    ∀ function, precompileIndexCallees function = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      InitECandidate.Solver.Wave8Contracts.M15.readOnlyProg precompileIndexCallees body = true := by
  intro function hfn values body callee rs hfound
  have heq : function = ofString "is_zero_bytes" := by
    simpa only [precompileIndexCallees, beq_iff_eq] using hfn
  subst function
  obtain ⟨params, rs', hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
  have hl := lookup_of_guestAst_getElem 19 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_is_zero_bytes) rfl
  change originalRuntimeCode.lookup (ofString "is_zero_bytes") = _ at hl
  rw [hl] at hinst
  have hbody := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
  rw [← hbody]
  rfl

theorem ro_precompile_index :
    InitECandidate.Solver.Wave8Contracts.M15.ReadOnlyFn (ofString "precompile_index") :=
  InitECandidate.Solver.Wave8Contracts.M15.readOnlyFn_of_guestAst
    822 (by rw [guestAst_len]; decide) Guest.Software.guestFn_precompile_index rfl
    precompileIndexCallees precompileIndexCallees_good rfl

theorem evmChainFrom_stable {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fuel e c : Nat) (h : (evmChainFrom s fuel e c).length < fuel) :
    evmChainFrom s (fuel + 1) e c = evmChainFrom s fuel e c := by
  induction fuel generalizing e c with
  | zero => simp at h
  | succ fuel ih =>
    by_cases hk : memW s (c + 16) = 0
    · simp [evmChainFrom, hk]
    · have ht : (evmChainFrom s fuel (memW s c) (memW s (c + 8))).length < fuel := by
        simpa only [evmChainFrom, if_neg hk, List.length_cons, Nat.add_lt_add_iff_right] using h
      have he := congrArg (List.cons (e, c))
        (ih (memW s c) (memW s (c + 8)) ht)
      simpa only [evmChainFrom, if_neg hk] using he

theorem evmChain_parent {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hkind : memW s (globN s "cur_cont" + 16) ≠ 0)
    (hlen : (evmChain s).length ≤ maxChain) :
    evmChainFrom s (maxChain + 1)
        (memW s (globN s "cur_cont")) (memW s (globN s "cur_cont" + 8)) =
      (evmChain s).tail := by
  have hcons : evmChain s = (globN s "ev", globN s "cur_cont") ::
      evmChainFrom s maxChain (memW s (globN s "cur_cont"))
        (memW s (globN s "cur_cont" + 8)) := by
    simp only [evmChain, evmChainFrom, if_neg hkind]
  rw [hcons] at hlen ⊢
  simp only [List.tail_cons]
  exact evmChainFrom_stable s _ _ _ (by simp only [List.length_cons] at hlen; omega)

theorem evmChain_pop_length {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hchain : evmChain post = (evmChain s).tail) :
    (evmChain post).length + 1 = (evmChain s).length := by
  have hcons : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl := by
    exact ⟨_, rfl⟩
  obtain ⟨tl, ht⟩ := hcons
  simp only [hchain, ht, List.tail_cons, List.length_cons]

theorem child_gas_refund_le (parentGas parentSpill childGas childSpill repay : Nat)
    (hrepay : repay ≤ parentSpill + childSpill) :
    parentGas + childGas + repay + (parentSpill + childSpill - repay) ≤
      childGas + childSpill + (parentGas + parentSpill) := by
  omega

theorem child_error_gas_refund_le (parentGas parentSpill childGas childSpill : Nat) :
    parentGas + childGas + parentSpill ≤
      childGas + childSpill + (parentGas + parentSpill) := by
  omega

theorem child_pop_gas_sum_le {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {child parent : Ivl} {ancestors : List Ivl}
    (hbefore : evmChain s = child :: parent :: ancestors)
    (hafter : evmChain post = parent :: ancestors)
    (hparent : memW post (parent.1 + 64) + memW post (parent.1 + 192) ≤
      memW s (child.1 + 64) + memW s (child.1 + 192) +
        (memW s (parent.1 + 64) + memW s (parent.1 + 192)))
    (hancestors : ∀ ec ∈ ancestors,
      memW post (ec.1 + 64) + memW post (ec.1 + 192) =
        memW s (ec.1 + 64) + memW s (ec.1 + 192)) :
    ((evmChain post).map fun ec =>
      memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum ≤
    ((evmChain s).map fun ec =>
      memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum := by
  have htail : (ancestors.map fun ec =>
      memW post (ec.1 + 64) + memW post (ec.1 + 192)) =
      ancestors.map (fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)) := by
    exact List.map_congr_left hancestors
  simp only [hbefore, hafter, List.map_cons, List.sum_cons, htail]
  omega

theorem evmPot_lt_of_child_pop {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv post)
    (hlen : (evmChain post).length + 1 = (evmChain s).length)
    (hgas : R11Shards.OpDispatchSpec.evmR post ≤ R11Shards.OpDispatchSpec.evmR s) :
    evmPot post < evmPot s := by
  have hFp : R11Shards.OpDispatchSpec.evmFp post <
      R11Shards.OpDispatchSpec.evmFp s := by
    unfold R11Shards.OpDispatchSpec.evmFp
    split <;> split <;> omega
  have hbound := R11Shards.OpDispatchSpec.evmPot_lt_bound post hInv hgas hFp
  have hge := R11Shards.OpDispatchSpec.evmPot_ge s
  omega

theorem store_cont_done_step {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s)
    (hrun : evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "cur_cont"), .const 32]) (.const 1)) =
        (none, post)) :
    EvmStep [] s post ∧ EvmDone post ∧
      OpDispatchSpec.evmR post ≤ OpDispatchSpec.evmR s := by
  obtain ⟨he_lt, hc_lt, _, ⟨ccw, hccw, hccn⟩, _⟩ := evm_head_globals hInv
  obtain ⟨w, hw, hp⟩ := store_global_off_word
    (gname := "cur_cont") (gbase := globN s "cur_cont") (off := 32)
    hccw hccn (by omega)
    (fun v hv => by simp [evalHOLExact] at hv; exact ⟨1, hv.symm⟩) hrun
  have hw1 : w = 1 := by simpa [evalHOLExact] using hw.symm
  have hdj : Disj (globN s "ev", 280) (globN s "cur_cont", 104) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hP, _⟩ := hInv
    have hfl := List.pairwise_flatten.mp hP
    have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
      simp [evmChain, evmChainFrom]
    have hpw := hfl.1 _ (List.mem_map_of_mem hhead)
    exact (List.pairwise_cons.mp (List.pairwise_append.mp hpw).1).1 _ (by simp)
  have hne : ∀ k, k + 8 ≤ 280 →
      globN s "ev" + k ≠ globN s "cur_cont" + 32 := by
    intro k hk
    unfold Disj at hdj
    rcases hdj with h | h | h | h <;> dsimp only at * <;> omega
  have hGp : GuestInv post := by
    rw [hp]
    exact guestInv_congr (s := s) rfl rfl rfl rfl hInv.1.1
  have hmem : ∀ x : BitVec 64,
      (∀ a ∈ headAllowedOffsets (globN s "ev") (globN s "cur_cont"),
        x ≠ BitVec.ofNat 64 a) → post.memory x = s.memory x := by
    intro x hx
    rw [hp]
    exact if_neg (hx _ (by simp [headAllowedOffsets]))
  have hgas : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) ≤
      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) := by
    rw [hp, memW_updW_ne s _ _ w (by omega) (by omega) (hne 64 (by omega)),
      memW_updW_ne s _ _ w (by omega) (by omega) (hne 192 (by omega))]
  obtain ⟨hi, hc, hg⟩ := evmInv_of_head_status_gas_update hInv hGp
    (by rw [hp]) (by rw [hp]) hmem hgas
  refine ⟨⟨hi, by simp [globN, hp], ?_, hc⟩, ?_, hg⟩
  · intro k hk
    rw [hp]
  · left
    have hcc : globN post "cur_cont" = globN s "cur_cont" := by simp [globN, hp]
    rw [hcc, hp, memW_updW_same, hw1]
    decide

theorem evmStep_trans {F : Type} {s mid post : PanSemStateFiniteExact 64 F}
    {gw : List String} (hfirst : EvmStep gw s mid) (hsecond : EvmStep gw mid post) :
    EvmStep gw s post :=
  ⟨hsecond.1, Nat.le_trans hfirst.2.1 hsecond.2.1,
    fun k hk => (hfirst.2.2.1 k hk).trans (hsecond.2.2.1 k hk),
    hsecond.2.2.2.trans hfirst.2.2.2⟩

theorem evmStep_locals_clock {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {gw : List String} (hstep : EvmStep gw s post)
    (ls lp : HolFiniteMapExact MlS (ValueHOL 64)) (ks kp : Nat) :
    EvmStep gw { s with locals := ls, clock := ks }
      { post with locals := lp, clock := kp } := by
  exact ⟨OpDispatchSpec.localsFree_evmInv post lp kp hstep.1, hstep.2.1,
    hstep.2.2.1, by
      rw [OpDispatchSpec.evmChain_congr (s := post)
          (t := { post with locals := lp, clock := kp }) rfl rfl,
        OpDispatchSpec.evmChain_congr (s := s)
          (t := { s with locals := ls, clock := ks }) rfl rfl]
      exact hstep.2.2.2⟩

theorem evmKeeps_of_readOnly {fname : MlS}
    (hro : InitECandidate.Solver.Wave8Contracts.M15.ReadOnlyFn fname) :
    EvmKeeps EvmInv [] fname := by
  obtain ⟨params, body, ret, hl, hr⟩ := hro
  refine ⟨params, body, ret, hl, ?_⟩
  intro F s hc hi he hn hs
  have hpost := hr s hc hi.1.1 he hn hs
  rw [hpost]
  exact evmStep_locals_clock ⟨hi, le_rfl, fun _ _ => rfl, rfl⟩ _ _ _ _

theorem ek_precompile_index : EvmKeeps EvmInv [] (ofString "precompile_index") :=
  evmKeeps_of_readOnly ro_precompile_index

theorem ek_is_zero_bytes : EvmKeeps EvmInv [] (ofString "is_zero_bytes") :=
  evmKeeps_of_readOnly ro_is_zero_bytes

theorem frame_start_tail_step {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hInv : EvmInv s) (done : BitVec 64)
    (hdone : s.locals.lookup (ofString "done") = some (.val (.word done)))
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hrun : evaluateHOLFiniteState s
      (.seq
        (.ite (.cmp .notEqual (.var .local (ofString "done")) (.const 0))
          (.store (.op .add [.var .global (ofString "cur_cont"), .const 32]) (.const 1))
          .skip)
        (.return (.const 0))) = (some (.returned v), post)) :
    EvmStep [] s post := by
  have hcmp : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notEqual (.var .local (ofString "done")) (.const 0)) =
      some (.val (.word (if done ≠ 0 then 1 else 0))) := by
    simp [evalHOLExact, hdone, Compiler.Encoders.Asm.wordCmpHOL]
  rw [evaluateHOLFiniteState_seq_line780] at hrun
  cases hi : evaluateHOLFiniteState s
      (.ite (.cmp .notEqual (.var .local (ofString "done")) (.const 0))
        (.store (.op .add [.var .global (ofString "cur_cont"), .const 32]) (.const 1))
        .skip) with
  | mk r mid =>
    rw [hi] at hrun
    cases r with
    | none =>
      have hmid : EvmStep [] s mid := by
        rw [evaluateHOLFiniteState_ite, hcmp] at hi
        by_cases hz : done = 0
        · simp only [hz, ne_eq, not_true_eq_false, ↓reduceIte] at hi
          rw [evaluateHOLFiniteState_skip] at hi
          have hm : s = mid := (Prod.mk.inj hi).2
          subst mid
          exact ⟨hInv, Nat.le_refl _, fun _ _ => rfl, rfl⟩
        · simp only [hz, ne_eq, not_false_eq_true, ↓reduceIte] at hi
          exact (store_cont_done_step hInv hi).1
      dsimp only at hrun
      rw [evaluateHOLFiniteState_return] at hrun
      dsimp only [evalHOLExact] at hrun
      have hshape : sizeOfShapeWithContextHOL mid.structs
          (shapeOfHOLExact (.val (.word (0 : BitVec 64)) : ValueHOL 64)) ≤ 32 := by
        simp [shapeOfHOLExact]
      rw [if_pos hshape] at hrun
      have hp : emptyLocalsHOLFinite mid = post := (Prod.mk.inj hrun).2
      rw [← hp]
      exact evmStep_locals_clock hmid s.locals HolFiniteMapExact.empty s.clock mid.clock
    | some r =>
      have hr : r = .returned v := Option.some.inj (Prod.mk.inj hrun).1
      subst r
      rw [evaluateHOLFiniteState_ite, hcmp] at hi
      by_cases hz : done = 0
      · simp only [hz, ne_eq, not_true_eq_false, ↓reduceIte] at hi
        rw [evaluateHOLFiniteState_skip] at hi
        cases hi
      · simp only [hz, ne_eq, not_false_eq_true, ↓reduceIte] at hi
        exact False.elim (store_res_not_resumes hi (Or.inl ⟨v, rfl⟩))

theorem store_ev_status_step {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s) (off : Nat) (hoff : off ∈ [120, 128, 160])
    (e : ExpHOL 64)
    (hword : ∀ v, @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) e = some v →
        ∃ w : BitVec 64, v = .val (.word w))
    (hrun : evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) e) =
        (none, post)) :
    EvmStep [] s post ∧ OpDispatchSpec.evmR post ≤ OpDispatchSpec.evmR s := by
  obtain ⟨he_lt, _, ⟨evw, hevw, hevn⟩, _, _⟩ := evm_head_globals hInv
  have hoffle : off ≤ 160 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff; omega
  obtain ⟨w, _, hp⟩ := store_global_off_word
    (gname := "ev") (gbase := globN s "ev") (off := off)
    hevw hevn (by omega) hword hrun
  have hGp : GuestInv post := by
    rw [hp]
    exact guestInv_congr (s := s) rfl rfl rfl rfl hInv.1.1
  have hmem : ∀ x : BitVec 64,
      (∀ a ∈ headAllowedOffsets (globN s "ev") (globN s "cur_cont"),
        x ≠ BitVec.ofNat 64 a) → post.memory x = s.memory x := by
    intro x hx
    rw [hp]
    apply if_neg
    apply hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl <;> simp [headAllowedOffsets]
  have hgas : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) ≤
      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) := by
    have ho64 : off ≠ 64 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff; omega
    rw [hp, memW_updW_ne s _ _ w (by omega) (by omega) (by omega),
      memW_updW_ne s _ _ w (by omega) (by omega) (by omega)]
  obtain ⟨hi, hc, hg⟩ := evmInv_of_head_status_gas_update hInv hGp
    (by rw [hp]) (by rw [hp]) hmem hgas
  exact ⟨⟨hi, by simp [globN, hp], fun _ _ => by rw [hp], hc⟩, hg⟩

theorem void_call_returned_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {fname : MlS} {args : List (ExpHOL 64)}
    (hcall : evaluateHOLFiniteState s (.call (some (none, none)) fname args) = (none, post)) :
    ∃ values body callee ret v cpost,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), cpost) ∧
      post = { cpost with locals := s.locals } := by
  rw [evaluateHOLFiniteState_call] at hcall
  revert hcall
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · simp
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, ret⟩
    · simp
    · dsimp only
      by_cases hz : s.clock = 0
      · simp [hz]
      · simp only [hz, ↓reduceIte]
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, cpost⟩
        rcases res with _ | r
        · simp
        · cases r with
          | returned v =>
            dsimp only; split
            · intro h; injection h with _ hp
              exact ⟨values, body, callee, ret, v, cpost, rfl, hl, hrun, hp.symm⟩
            · simp
          | _ => simp

theorem void_call_step {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {fname : MlS} {args : List (ExpHOL 64)} {gw : List String}
    (hcode : s.code = originalRuntimeCode) (hInv : EvmInv s)
    (hcallee : EvmKeeps EvmInv gw fname)
    (hcall : evaluateHOLFiniteState s (.call (some (none, none)) fname args) = (none, post)) :
    EvmStep gw s post := by
  obtain ⟨params, fbody, retSh, hlook, hspec⟩ := hcallee
  obtain ⟨values, body, callee, ret, v, cpost, _, hl, hrun, hp⟩ := void_call_returned_inv hcall
  have hb := lookupCodeHOLFinite_installed_body s.code.lookup fname params fbody body
    retSh ret values callee (by rw [hcode]; exact hlook) hl
  subst body
  have hi := OpDispatchSpec.localsFree_evmInv s callee (s.clock - 1) hInv
  have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fname vs =
      some (fbody, (callEntryStateHOLFinite s callee).locals, retSh) := by
    have hr := lookupCodeHOLFinite_installed_return s fname params fbody fbody
      retSh ret values callee (by rw [hcode]; exact hlook) hl
    subst ret
    exact ⟨values, by simpa only [hcode, callEntryStateHOLFinite] using hl⟩
  have hs := hspec (callEntryStateHOLFinite s callee) hcode hi hex
    (by rw [hrun]; simp)
    (by rw [hrun]; exact Or.inl ⟨v, rfl⟩)
  rw [hrun] at hs
  rw [hp]
  exact evmStep_locals_clock hs s.locals s.locals s.clock cpost.clock

def frameExceptionCallees (f : MlS) : Bool :=
  f == ofString "refill_frame_state_gas" || f == ofString "frame_halt"

theorem frameExceptionCallees_good :
    ∀ f, frameExceptionCallees f = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body, callee, rs) →
      StateRestoreEpilogue.noCatchableRaise frameExceptionCallees body = true := by
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
  simp only [frameExceptionCallees, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with rfl | rfl
  · rw [lookup_refill_frame_state_gas] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]
    rfl
  · rw [lookup_frame_halt] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]
    rfl

theorem frame_exception_no_catchable_raise {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode)
    (eid : MlS) (v : ValueHOL 64) (hne : eid ≠ ofString "TrapErr") :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_exception)).1 ≠
      some (.exception eid v) :=
  StateRestoreEpilogue.evaluate_noCatchableRaise frameExceptionCallees
    frameExceptionCallees_good (sourceFnBody Guest.Software.guestFn_frame_exception)
    rfl s hcode eid v hne

theorem void_call_ne_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname : MlS) (args : List (ExpHOL 64)) (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 ≠ some (.returned u) := by
  rw [evaluateHOLFiniteState_call]
  rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | _
  · simp
  · dsimp only
    rcases lookupCodeHOLFinite s.code.lookup fname _ with _ | ⟨_, _, _⟩
    · simp
    · dsimp only; split
      · simp
      · rcases evaluateHOLFiniteState _ _ with ⟨res, _⟩
        rcases res with _ | r
        · simp
        · cases r with
          | returned _ => dsimp only; split <;> simp
          | _ => simp

theorem store_ne_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (addr val : ExpHOL 64) (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.store addr val)).1 ≠ some (.returned u) :=
  fun h => store_res_not_resumes (by rw [Prod.ext_iff]; exact ⟨h, rfl⟩) (Or.inl ⟨u, rfl⟩)

theorem ite_ne_returned {F : Type} {s : PanSemStateFiniteExact 64 F}
    {c : ExpHOL 64} {y n : ProgHOL 64}
    (hy : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t y).1 ≠ some (.returned u))
    (hn : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t n).1 ≠ some (.returned u))
    (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.ite c y n)).1 ≠ some (.returned u) := by
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact hn s u
    · exact hy s u
  · simp

theorem seq_ne_returned {p1 p2 : ProgHOL 64}
    (h1 : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t p1).1 ≠ some (.returned u))
    (h2 : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t p2).1 ≠ some (.returned u))
    {F : Type} (s : PanSemStateFiniteExact 64 F) (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.seq p1 p2)).1 ≠ some (.returned u) := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases h : evaluateHOLFiniteState s p1 with ⟨r1, m⟩
  cases r1 with
  | none => dsimp only; exact h2 m u
  | some _ => dsimp only; exact fun hr => h1 s u (by rw [h]; exact hr)

theorem seq_returned_step {F : Type} {s : PanSemStateFiniteExact 64 F} {p1 p2 : ProgHOL 64}
    {v : ValueHOL 64}
    (h : (evaluateHOLFiniteState s (.seq p1 p2)).1 = some (.returned v))
    (hn1 : ∀ u, (evaluateHOLFiniteState s p1).1 ≠ some (.returned u)) :
    ∃ m, evaluateHOLFiniteState s p1 = (none, m) ∧
      m.code = s.code ∧
      evaluateHOLFiniteState m p2 = evaluateHOLFiniteState s (.seq p1 p2) := by
  have hseq := evaluateHOLFiniteState_seq_line780 s p1 p2
  rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, m⟩
  rw [hr1] at hseq
  cases r1 with
  | none =>
    have hm := (PanRunBounded.evaluateHOLFiniteState_metadata s p1).1
    rw [hr1] at hm
    exact ⟨m, rfl, hm, hseq.symm⟩
  | some r =>
    rw [hseq] at h; dsimp only at h
    injection h with hr; subst hr
    exact absurd (congrArg Prod.fst hr1) (hn1 v)

theorem halt_clear_output_step {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hcode : s.code = originalRuntimeCode) (hInv : EvmInv s)
    (hrun : evaluateHOLFiniteState s
      (.seq
        (.call (some (none, none)) (ofString "frame_halt") [.var .local (ofString "err")])
        (.seq
          (.store (.op .add [.var .global (ofString "ev"), .const 120])
            (.var .global (ofString "evm_empty")))
          (.store (.op .add [.var .global (ofString "ev"), .const 128]) (.const 0)))) =
        (none, post)) :
    EvmStep [] s post := by
  rw [evaluateHOLFiniteState_seq_line780] at hrun
  rcases hc : evaluateHOLFiniteState s
    (.call (some (none, none)) (ofString "frame_halt") [.var .local (ofString "err")]) with ⟨rc, m1⟩
  rw [hc] at hrun
  cases rc with
  | some _ => cases hrun
  | none =>
    dsimp only at hrun
    have hs1 : EvmStep [] s m1 := void_call_step hcode hInv ek_frame_halt_r11 hc
    rw [evaluateHOLFiniteState_seq_line780] at hrun
    rcases h120 : evaluateHOLFiniteState m1
      (.store (.op .add [.var .global (ofString "ev"), .const 120])
        (.var .global (ofString "evm_empty"))) with ⟨r120, m2⟩
    rw [h120] at hrun
    cases r120 with
    | some _ => cases hrun
    | none =>
      dsimp only at hrun
      obtain ⟨w_emp, hw_emp⟩ := hs1.1.1.2.2.2.2.2.2.2.2.2 "evm_empty" (by decide)
      have hs2 : EvmStep [] m1 m2 :=
        (store_ev_status_step hs1.1 120 (by simp) _
          (fun v0 hv0 => by
            change m1.globals.lookup (ofString "evm_empty") = some v0 at hv0
            rw [hw_emp] at hv0; injection hv0 with hv'; exact ⟨w_emp, hv'.symm⟩) h120).1
      have hs3 : EvmStep [] m2 post :=
        (store_ev_status_step hs2.1 128 (by simp) _
          (fun v0 hv0 => by simp [evalHOLExact] at hv0; exact ⟨0, hv0.symm⟩) hrun).1
      exact evmStep_trans hs1 (evmStep_trans hs2 hs3)

theorem ek_frame_exception :
    EvmKeeps EvmInv [] (ofString "frame_exception") := by
  refine ⟨[(ofString "err", .one)], sourceFnBody Guest.Software.guestFn_frame_exception, .one,
    lookup_frame_exception, ?_⟩
  intro F s hcode hInv hex _ hres
  obtain ⟨w_err, hw_err⟩ := one_word_param_of_lookup lookup_frame_exception hex
  rcases hres with ⟨v, hv⟩ | ⟨eid, v, he, hne⟩
  · rw [frame_exception_body_eq] at hv ⊢
    obtain ⟨m1, hc1, hcode1, hseq1⟩ := seq_returned_step hv (void_call_ne_returned s _ _)
    rw [← hseq1] at hv ⊢; clear hseq1
    have hs1 : EvmStep [] s m1 := void_call_step hcode hInv ek_refill_frame_state_gas_r11 hc1
    have herr1 : m1.locals.lookup (ofString "err") = some (.val (.word w_err)) := by
      obtain ⟨_, _, _, _, _, _, _, _, _, hm1⟩ := void_call_returned_inv hc1
      rw [hm1]; exact hw_err
    have hite_nr : ∀ u, (evaluateHOLFiniteState m1
        (.ite (.cmp .notEqual (.var .local (ofString "err")) (.const 1))
          (.seq
            (.call (some (none, none)) (ofString "frame_halt") [.var .local (ofString "err")])
            (.seq
              (.store (.op .add [.var .global (ofString "ev"), .const 120])
                (.var .global (ofString "evm_empty")))
              (.store (.op .add [.var .global (ofString "ev"), .const 128]) (.const 0))))
          (.store (.op .add [.var .global (ofString "ev"), .const 160])
            (.var .local (ofString "err"))))).1 ≠ some (.returned u) :=
      ite_ne_returned
        (seq_ne_returned (fun t u => void_call_ne_returned t _ _ u)
          (seq_ne_returned (fun t u => store_ne_returned t _ _ u)
            (fun t u => store_ne_returned t _ _ u)))
        (fun t u => store_ne_returned t _ _ u)
    obtain ⟨m2, hite, _, hseq2⟩ := seq_returned_step hv hite_nr
    rw [← hseq2] at hv ⊢; clear hseq2
    have hs2 : EvmStep [] m1 m2 := by
      rw [evaluateHOLFiniteState_ite] at hite
      have hcmp : @evalHOLExact 64 F _ m1.toExact (fun a => Classical.propDecidable (m1.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "err")) (.const 1)) =
          some (.val (.word (if w_err ≠ 1 then 1 else 0))) := by
        simp [evalHOLExact, herr1, Compiler.Encoders.Asm.wordCmpHOL]
      rw [hcmp] at hite; dsimp only at hite
      by_cases hw1 : w_err = 1
      · subst hw1
        simp only [ne_eq, not_true_eq_false, ↓reduceIte] at hite
        exact (store_ev_status_step hs1.1 160 (by simp) _
          (fun v0 hv0 => by
            change m1.locals.lookup (ofString "err") = some v0 at hv0
            rw [herr1] at hv0; injection hv0 with hv'; exact ⟨1, hv'.symm⟩) hite).1
      · have h10 : ((1 : BitVec 64) = 0) = False := by decide
        simp only [ne_eq, hw1, not_false_eq_true, ↓reduceIte, h10] at hite
        exact halt_clear_output_step (hcode1.trans hcode) hs1.1 hite
    obtain ⟨m3, hst3, _, hseq3⟩ := seq_returned_step hv (store_ne_returned m2 _ _)
    rw [← hseq3] at hv ⊢; clear hseq3
    have hs3 : EvmStep [] m2 m3 := (store_cont_done_step hs2.1 hst3).1
    rw [evaluateHOLFiniteState_return] at hv ⊢
    have hc0 : @evalHOLExact 64 F _ m3.toExact (fun a => Classical.propDecidable (m3.memaddrs a))
        (.const 0) = some (.val (.word 0)) := rfl
    rw [hc0] at hv ⊢; dsimp only at hv ⊢
    have hle32 : sizeOfShapeWithContextHOL m3.structs
        (shapeOfHOLExact (ValueHOL.val (HolWordLab.word (0 : BitVec 64)))) ≤ 32 := by
      simp [shapeOfHOLExact]
    rw [if_pos hle32]; dsimp only
    exact evmStep_locals_clock (evmStep_trans hs1 (evmStep_trans hs2 hs3))
      s.locals HolFiniteMapExact.empty s.clock m3.clock
  · exact False.elim (frame_exception_no_catchable_raise s hcode eid v hne he)

theorem lookup_frame_start :
    originalRuntimeCode.lookup (ofString "frame_start") =
      some ([], sourceFnBody Guest.Software.guestFn_frame_start, .one) :=
  lookup_of_guestAst_getElem 581 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_frame_start) rfl

def frameStartAvoids {F : Type} (s : PanSemStateFiniteExact 64 F) : List (Nat × Nat) :=
  [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
   (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
   (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
   (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
   (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
   (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
   (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96),
   (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40),
   (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128),
   (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128),
   (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
   (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64),
   (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52),
   (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)]

def frameStartGw : List String :=
  ["bn_expw", "bn_gamma", "heap_ptr", "journal_n", "scratch_ptr"]

theorem evmAvoids_frameStart_locals_clock {F : Type}
    (s : PanSemStateFiniteExact 64 F) (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (h : EvmAvoids frameStartAvoids s) :
    EvmAvoids frameStartAvoids { s with locals := L, clock := k } := by
  let s' : PanSemStateFiniteExact 64 F := { s with locals := L, clock := k }
  have hInv : EvmInv s := ⟨h.1, h.2.choose, h.2.choose_spec.1⟩
  have hInv' : EvmInv s' := OpDispatchSpec.localsFree_evmInv s L k hInv
  obtain ⟨S, hE, Nd, hT, hD⟩ := h.2
  have hf : ∀ (nodes : Nat) (Fr : List Nat) (head : Nat),
      FreeChain s' nodes head Fr ↔ FreeChain s nodes head Fr := by
    intro nodes Fr; induction Fr with
    | nil => intro _; exact Iff.rfl
    | cons _ rest ih => intro _; exact and_congr Iff.rfl (ih _)
  have hw : ∀ t, HtabWF s' t ↔ HtabWF s t := by
    intro t; simp only [HtabWF, hf]; exact Iff.rfl
  have ht : ∀ S0, TablesTyped s' S0 ↔ TablesTyped s S0 := by
    intro S0; simp only [TablesTyped, hw]; exact Iff.rfl
  have hwt : WorldTyped s' S ↔ WorldTyped s S := by
    simp only [WorldTyped, ht]; exact Iff.rfl
  have hch : evmChain s' = evmChain s := OpDispatchSpec.evmChain_congr rfl rfl
  have hE' : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s' S := by
    dsimp only [InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt] at hE ⊢
    simp only [s', FrameWF, MsgOwned, hwt, hch] at hE ⊢
    exact hE
  have hT' : TriesTypedWith s' S Nd := hT
  refine ⟨hInv'.1, S, hE', Nd, hT', ?_⟩
  rw [hch]
  exact hD

theorem evmStep_mono_gw {gw1 gw2 : List String} {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hsub : ∀ k : MlS, k ∉ gw2.map ofString → k ∉ gw1.map ofString)
    (hs : EvmStep gw1 s post) : EvmStep gw2 s post :=
  ⟨hs.1, hs.2.1, fun k hk => hs.2.2.1 k (hsub k hk), hs.2.2.2⟩

theorem frame_start_body_eq :
    sourceFnBody Guest.Software.guestFn_frame_start =
      .dec (ofString "err") .one (.const 0)
        (.dec (ofString "done") .one (.const 0)
          (.seq
            (.call (some (some (.local, ofString "done"),
              some (ofString "EvmErr", ofString "err",
                .call (some (none, none)) (ofString "frame_exception")
                  [.var .local (ofString "err")])))
              (ofString "frame_prologue") [])
            (.seq
              (.ite (.cmp .notEqual (.var .local (ofString "done")) (.const 0))
                (.store (.op .add [.var .global (ofString "cur_cont"), .const 32]) (.const 1))
                .skip)
              (.return (.const 0))))) := rfl

theorem dec_const_zero_unwrap {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : MlS) (body : ProgHOL 64) :
    (evaluateHOLFiniteState s (.dec nm .one (.const 0) body)).1 =
      (evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word 0)) s) body).1 ∧
    (evaluateHOLFiniteState s (.dec nm .one (.const 0) body)).2 =
      { (evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word 0)) s) body).2 with
        locals := (evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word 0)) s) body).2.locals.resVarEq
          (nm, s.locals.lookup nm) } := by
  rw [evaluateHOLFiniteState_dec_total]; dsimp only
  have he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.const 0) = some (.val (.word 0)) := rfl
  rw [he]; dsimp only
  have hsh : shapeEqHOL .one (shapeOfHOLExact (ValueHOL.val (HolWordLab.word (0 : BitVec 64)))) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  rw [if_pos hsh]; dsimp only
  exact ⟨rfl, rfl⟩

theorem seq_unwrap {F : Type} (s : PanSemStateFiniteExact 64 F) (p1 p2 : ProgHOL 64) :
    evaluateHOLFiniteState s (.seq p1 p2) =
      match (evaluateHOLFiniteState s p1).1 with
      | none => evaluateHOLFiniteState (evaluateHOLFiniteState s p1).2 p2
      | some val => (some val, (evaluateHOLFiniteState s p1).2) := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases evaluateHOLFiniteState s p1 with ⟨r, m⟩
  cases r <;> rfl

theorem ek_frame_start_of
    (hek_prologue : EvmKeeps (EvmAvoids frameStartAvoids) frameStartGw
      (ofString "frame_prologue")) :
    EvmKeeps
      (EvmAvoids (fun s =>
        [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
         (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
         (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
         (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
         (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
         (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
         (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96),
         (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40),
         (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128),
         (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128),
         (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
         (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64),
         (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52),
         (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)]))
      ["bn_expw", "bn_gamma", "heap_ptr", "journal_n", "scratch_ptr"]
      (ofString "frame_start") := by
  change EvmKeeps (EvmAvoids frameStartAvoids) frameStartGw (ofString "frame_start")
  obtain ⟨p_params, p_body, p_ret, hlook_p, hspec_p⟩ := hek_prologue
  refine ⟨[], sourceFnBody Guest.Software.guestFn_frame_start, .one, lookup_frame_start, ?_⟩
  intro F s hcode hAv _ hnt hres
  rw [frame_start_body_eq] at hnt hres ⊢
  let s1 := setVarHOLFinite (ofString "err") (.val (.word 0)) s
  let s2 := setVarHOLFinite (ofString "done") (.val (.word 0)) s1
  let pCall : ProgHOL 64 :=
    .call (some (some (.local, ofString "done"),
      some (ofString "EvmErr", ofString "err",
        .call (some (none, none)) (ofString "frame_exception")
          [.var .local (ofString "err")])))
      (ofString "frame_prologue") []
  let pTail : ProgHOL 64 :=
    .seq
      (.ite (.cmp .notEqual (.var .local (ofString "done")) (.const 0))
        (.store (.op .add [.var .global (ofString "cur_cont"), .const 32]) (.const 1))
        .skip)
      (.return (.const 0))
  have hd1 := dec_const_zero_unwrap s (ofString "err") (.dec (ofString "done") .one (.const 0) (.seq pCall pTail))
  have hd2 := dec_const_zero_unwrap s1 (ofString "done") (.seq pCall pTail)
  rw [hd1.1, hd2.1] at hnt hres
  rw [hd1.2, hd2.2]
  have hcode2 : s2.code = originalRuntimeCode := hcode
  have hInv : EvmInv s := ⟨hAv.1, hAv.2.choose, hAv.2.choose_spec.1⟩
  have hAv2 : EvmAvoids frameStartAvoids s2 :=
    evmAvoids_frameStart_locals_clock s s2.locals s.clock hAv
  suffices hbody_step : EvmStep frameStartGw s (evaluateHOLFiniteState s2 (.seq pCall pTail)).2 by
    exact evmStep_locals_clock hbody_step s.locals _ s.clock _
  have hsq := seq_unwrap s2 pCall pTail
  rw [hsq] at hnt hres ⊢
  rcases hpc : evaluateHOLFiniteState s2 pCall with ⟨rc, m⟩
  have hpc1 : (evaluateHOLFiniteState s2 pCall).1 = rc := congrArg Prod.fst hpc
  have hpc2 : (evaluateHOLFiniteState s2 pCall).2 = m := congrArg Prod.snd hpc
  rw [hpc1, hpc2] at hnt hres
  dsimp only at ⊢
  have hpc' := hpc
  dsimp only [pCall] at hpc'
  rw [evaluateHOLFiniteState_call] at hpc'
  have hargs : evalListHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a)) [] =
      some [] := rfl
  rw [hargs] at hpc'; dsimp only at hpc'
  rcases hl : lookupCodeHOLFinite s2.code.lookup (ofString "frame_prologue") [] with _ | ⟨body', callee, ret'⟩
  · rw [hl] at hpc'
    injection hpc' with hrc _
    subst hrc
    rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
  · rw [hl] at hpc'; dsimp only at hpc'
    have hbody_eq := lookupCodeHOLFinite_installed_body s2.code.lookup _ p_params p_body body'
      p_ret ret' [] callee (by rw [hcode2]; exact hlook_p) hl
    subst body'
    have hret_eq := lookupCodeHOLFinite_installed_return s2 _ p_params p_body p_body
      p_ret ret' [] callee (by rw [hcode2]; exact hlook_p) hl
    subst ret'
    by_cases hz : s2.clock = 0
    · rw [if_pos hz] at hpc'
      injection hpc' with hrc _
      subst hrc
      exact False.elim (hnt rfl)
    · rw [if_neg hz] at hpc'
      let entry := callEntryStateHOLFinite s2 callee
      have hAv_e : EvmAvoids frameStartAvoids entry :=
        evmAvoids_frameStart_locals_clock s2 callee (s2.clock - 1) hAv2
      have hex_e : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "frame_prologue") vs =
          some (p_body, entry.locals, p_ret) :=
        ⟨[], by simpa only [hcode2, entry, callEntryStateHOLFinite] using hl⟩
      rcases hrun_p : evaluateHOLFiniteState entry p_body with ⟨res_p, cpost⟩
      rw [hrun_p] at hpc'
      have hcode_cp : cpost.code = originalRuntimeCode := by
        have hm := (PanRunBounded.evaluateHOLFiniteState_metadata entry p_body).1
        rw [hrun_p] at hm; exact hm.trans hcode2
      cases res_p with
      | none =>
        dsimp only at hpc'
        injection hpc' with hrc _; subst hrc
        rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
      | some rp =>
        cases rp with
        | returned vp =>
          dsimp only at hpc'
          split at hpc'
          · rename_i hsh_ret
            split at hpc'
            · rename_i hvalid
              injection hpc' with hrc hm_eq
              subst hrc
              dsimp only at hnt hres ⊢
              have hvp_word : ∃ dw : BitVec 64, vp = .val (.word dw) := by
                rcases vp with ⟨⟨dw⟩⟩ | vs | ⟨nm, fs⟩
                · exact ⟨dw, rfl⟩
                · simp [isValidValueHOLExact, lookupKvarHOLExact,
                    s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    shapeOfHOLExact, shapeEqHOL] at hvalid
                · simp [isValidValueHOLExact, lookupKvarHOLExact,
                    s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    shapeOfHOLExact, shapeEqHOL] at hvalid
              obtain ⟨dw, rfl⟩ := hvp_word
              have hstep_cp : EvmStep frameStartGw entry cpost := by
                have h := hspec_p entry hcode2 hAv_e hex_e
                  (by dsimp only [entry]; rw [hrun_p]; simp)
                  (by dsimp only [entry]; rw [hrun_p]; exact Or.inl ⟨_, rfl⟩)
                dsimp only [entry] at h; rw [hrun_p] at h; exact h
              have hstep_m : EvmStep frameStartGw s m := by
                rw [← hm_eq]
                exact evmStep_locals_clock
                  (evmStep_trans (evmStep_locals_clock ⟨hInv, le_rfl, fun _ _ => rfl, rfl⟩ s.locals callee s.clock (s2.clock - 1)) hstep_cp)
                  s.locals _ s.clock cpost.clock
              have hdone_m : m.locals.lookup (ofString "done") = some (.val (.word dw)) := by
                rw [← hm_eq]
                simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              rcases ht : evaluateHOLFiniteState m pTail with ⟨rt, post⟩
              have ht1 : (evaluateHOLFiniteState m pTail).1 = rt := congrArg Prod.fst ht
              rw [ht1] at hres; dsimp only at ⊢
              rcases hres with ⟨vt, hvt⟩ | ⟨eid_t, vt, het, _⟩
              · subst hvt
                have htail := frame_start_tail_step m hstep_m.1 dw hdone_m vt post ht
                have htail' : EvmStep frameStartGw m post :=
                  evmStep_mono_gw (by intro k _; simp) htail
                exact evmStep_trans hstep_m htail'
              · dsimp only [pTail] at ht
                rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at ht
                have hcmp_m : @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a))
                    (.cmp .notEqual (.var .local (ofString "done")) (.const 0)) =
                    some (.val (.word (if dw ≠ 0 then 1 else 0))) := by
                  simp [evalHOLExact, hdone_m, Compiler.Encoders.Asm.wordCmpHOL]
                rw [hcmp_m] at ht; dsimp only at ht
                by_cases hdw : dw = 0
                · simp only [hdw, ne_eq, not_true_eq_false, ↓reduceIte, evaluateHOLFiniteState_skip,
                    evaluateHOLFiniteState_return] at ht
                  have hc0 : @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a))
                      (.const 0) = some (.val (.word 0)) := rfl
                  rw [hc0] at ht; dsimp only at ht
                  split at ht <;> (have hrt := congrArg Prod.fst ht; rw [het] at hrt; cases hrt)
                · have h10 : ((1 : BitVec 64) = 0) = False := by decide
                  simp only [ne_eq, hdw, not_false_eq_true, ↓reduceIte, h10] at ht
                  rcases hst_m : evaluateHOLFiniteState m _ with ⟨rst, ms⟩
                  rw [hst_m] at ht
                  cases rst with
                  | none =>
                    dsimp only at ht
                    rw [evaluateHOLFiniteState_return] at ht
                    have hc0 : @evalHOLExact 64 F _ ms.toExact (fun a => Classical.propDecidable (ms.memaddrs a))
                        (.const 0) = some (.val (.word 0)) := rfl
                    rw [hc0] at ht; dsimp only at ht
                    split at ht <;> (have hrt := congrArg Prod.fst ht; rw [het] at hrt; cases hrt)
                  | some r_s =>
                    dsimp only at ht
                    have hfirst : some r_s = rt := congrArg Prod.fst ht
                    rw [← hfirst] at het
                    injection het with hrs
                    subst hrs
                    exact False.elim (store_res_not_resumes hst_m (Or.inr ⟨eid_t, vt, rfl, ‹_›⟩))
            · injection hpc' with hrc _; subst hrc
              rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
          · injection hpc' with hrc _; subst hrc
            rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
        | exception exId exVal =>
          dsimp only at hpc'
          by_cases heid : exId = ofString "EvmErr"
          · subst exId
            rw [if_pos rfl] at hpc'
            have hne_trap : ofString "EvmErr" ≠ ofString "TrapErr" := by decide
            have hstep_cp : EvmStep frameStartGw entry cpost := by
              have h := hspec_p entry hcode2 hAv_e hex_e
                (by dsimp only [entry]; rw [hrun_p]; simp)
                (by dsimp only [entry]; rw [hrun_p]; exact Or.inr ⟨_, exVal, rfl, hne_trap⟩)
              dsimp only [entry] at h; rw [hrun_p] at h; exact h
            split at hpc'
            · split at hpc'
              · let hstate := setKvarHOLFinite .local (ofString "err") exVal { cpost with locals := s2.locals }
                have hstep_hs : EvmStep frameStartGw s hstate :=
                  evmStep_locals_clock
                    (evmStep_trans (evmStep_locals_clock ⟨hInv, le_rfl, fun _ _ => rfl, rfl⟩ s.locals callee s.clock (s2.clock - 1)) hstep_cp)
                    s.locals hstate.locals s.clock cpost.clock
                have hcode_hs : hstate.code = originalRuntimeCode := hcode_cp
                rcases rc with _ | r_h
                · have hh : evaluateHOLFiniteState hstate
                      (.call (some (none, none)) (ofString "frame_exception") [.var .local (ofString "err")]) =
                      (none, m) := hpc'
                  have hstep_fe : EvmStep [] hstate m :=
                    void_call_step hcode_hs hstep_hs.1 ek_frame_exception hh
                  have hstep_m : EvmStep frameStartGw s m :=
                    evmStep_trans hstep_hs (evmStep_mono_gw (by intro k _; simp) hstep_fe)
                  have hdone_m : m.locals.lookup (ofString "done") = some (.val (.word 0)) := by
                    obtain ⟨_, _, _, _, _, _, _, _, _, hm_eq⟩ := void_call_returned_inv hh
                    rw [hm_eq]
                    have hne_ed : ofString "err" ≠ ofString "done" := by decide
                    simp [hstate, setKvarHOLFinite, setVarHOLFinite, s2, s1,
                      HolFiniteMapExact.lookup_update, FUPDATE, hne_ed]
                  dsimp only at hres ⊢
                  rcases ht : evaluateHOLFiniteState m pTail with ⟨rt, post⟩
                  have ht1 : (evaluateHOLFiniteState m pTail).1 = rt := congrArg Prod.fst ht
                  rw [ht1] at hres; dsimp only at ⊢
                  rcases hres with ⟨vt, hvt⟩ | ⟨eid_t, vt, het, hne_t⟩
                  · subst hvt
                    have htail := frame_start_tail_step m hstep_m.1 0 hdone_m vt post ht
                    have htail' : EvmStep frameStartGw m post :=
                      evmStep_mono_gw (by intro k _; simp) htail
                    exact evmStep_trans hstep_m htail'
                  · dsimp only [pTail] at ht
                    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at ht
                    have hcmp0 : @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a))
                        (.cmp .notEqual (.var .local (ofString "done")) (.const 0)) =
                        some (.val (.word 0)) := by
                      simp [evalHOLExact, hdone_m, Compiler.Encoders.Asm.wordCmpHOL]
                    rw [hcmp0] at ht; dsimp only at ht
                    rw [if_pos rfl, evaluateHOLFiniteState_skip, evaluateHOLFiniteState_return] at ht
                    have hc0 : @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a))
                        (.const 0) = some (.val (.word 0)) := rfl
                    rw [hc0] at ht; dsimp only at ht
                    split at ht <;> (have hrt := congrArg Prod.fst ht; rw [het] at hrt; cases hrt)
                · have hh : evaluateHOLFiniteState hstate
                      (.call (some (none, none)) (ofString "frame_exception") [.var .local (ofString "err")]) =
                      (some r_h, m) := hpc'
                  dsimp only at hres ⊢
                  rcases hres with ⟨vt, hvt⟩ | ⟨eid_h, vh, heh, hne_h⟩
                  · cases hvt
                    exact False.elim (void_call_ne_returned hstate _ _ vt (congrArg Prod.fst hh))
                  · cases heh
                    rw [evaluateHOLFiniteState_call] at hh
                    rcases hef : evalListHOLFinite hstate (h := fun a => Classical.propDecidable (hstate.memaddrs a))
                        [.var .local (ofString "err")] with _ | fvals
                    · rw [hef] at hh; cases hh
                    · rw [hef] at hh; dsimp only at hh
                      rcases hfl : lookupCodeHOLFinite hstate.code.lookup (ofString "frame_exception") fvals with _ | ⟨fb, fcal, frs⟩
                      · rw [hfl] at hh; cases hh
                      · rw [hfl] at hh; dsimp only at hh
                        split at hh
                        · cases hh
                        · have hfb := lookupCodeHOLFinite_installed_body hstate.code.lookup _ _ _ fb _ frs fvals fcal
                            (by rw [hcode_hs]; exact lookup_frame_exception) hfl
                          subst fb
                          rcases hfe_run : evaluateHOLFiniteState (callEntryStateHOLFinite hstate fcal)
                              (sourceFnBody Guest.Software.guestFn_frame_exception) with ⟨rfe, fe_post⟩
                          rw [hfe_run] at hh
                          rcases rfe with _ | rfe'
                          · cases hh
                          · cases rfe' with
                            | returned _ => dsimp only at hh; split at hh <;> cases hh
                            | exception eid2 v2 =>
                              dsimp only at hh
                              injection hh with h1 _
                              have heq := Option.some.inj h1
                              cases heq
                              exact False.elim (frame_exception_no_catchable_raise
                                (callEntryStateHOLFinite hstate fcal) hcode_hs eid_h vh hne_h
                                (congrArg Prod.fst hfe_run))
                            | _ => cases hh
              · injection hpc' with hrc _; subst hrc
                rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
            · injection hpc' with hrc _; subst hrc
              rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
          · rw [if_neg heid] at hpc'
            injection hpc' with hrc hm_eq
            subst hrc
            dsimp only at hres ⊢
            rcases hres with ⟨_, h⟩ | ⟨eid_u, vu, heu, hne_u⟩
            · cases h
            · injection heu with h1; injection h1 with he1 hv1; subst eid_u vu
              have hstep_cp : EvmStep frameStartGw entry cpost := by
                have h := hspec_p entry hcode2 hAv_e hex_e
                  (by dsimp only [entry]; rw [hrun_p]; simp)
                  (by dsimp only [entry]; rw [hrun_p]; exact Or.inr ⟨exId, exVal, rfl, hne_u⟩)
                dsimp only [entry] at h; rw [hrun_p] at h; exact h
              rw [← hm_eq]
              exact evmStep_locals_clock
                (evmStep_trans (evmStep_locals_clock ⟨hInv, le_rfl, fun _ _ => rfl, rfl⟩ s.locals callee s.clock (s2.clock - 1)) hstep_cp)
                s.locals HolFiniteMapExact.empty s.clock cpost.clock
        | timeOut =>
          dsimp only at hpc'; injection hpc' with hrc _; subst hrc; exact False.elim (hnt rfl)
        | error | «break» | «continue» | finalFfi _ =>
          dsimp only at hpc'; injection hpc' with hrc _; subst hrc
          rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h

theorem release_body_returned_effect {F : Type} (s : PanSemStateFiniteExact 64 F)
    (g : MlS) (m v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hm : s.locals.lookup (ofString "m") = some m)
    (hrun : evaluateHOLFiniteState s
      (.seq (.assign .global g (.var .local (ofString "m"))) (.return (.const 0))) =
        (some (.returned v), post)) :
    post.globals = s.globals.update (g, m) ∧ post.memory = s.memory ∧
      post.code = s.code ∧ post.memaddrs = s.memaddrs := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hrun
  have he : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString "m")) = some m := hm
  rw [he] at hrun
  dsimp only at hrun
  by_cases hv : isValidValueHOLFinite s .global g m = true
  · rw [if_pos hv] at hrun
    dsimp only at hrun
    rw [evaluateHOLFiniteState_return] at hrun
    have hc0 : @evalHOLExact 64 F _ (setKvarHOLFinite .global g m s).toExact
        (fun a => Classical.propDecidable ((setKvarHOLFinite .global g m s).memaddrs a))
        (.const 0) = some (.val (.word 0)) := rfl
    rw [hc0] at hrun
    dsimp only at hrun
    split at hrun
    · injection hrun with _ hp
      subst post
      exact ⟨rfl, rfl, rfl, rfl⟩
    · cases hrun
  · rw [if_neg hv] at hrun
    cases hrun

theorem frame_mem_release_returned_effect {F : Type} (s : PanSemStateFiniteExact 64 F)
    (m v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hm : s.locals.lookup (ofString "m") = some m)
    (hrun : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_mem_release) =
      (some (.returned v), post)) :
    post.globals = s.globals.update (ofString "frame_mem_ptr", m) ∧
      post.memory = s.memory ∧ post.code = s.code ∧ post.memaddrs = s.memaddrs :=
  release_body_returned_effect s (ofString "frame_mem_ptr") m v post hm hrun

theorem scratch_release_returned_effect {F : Type} (s : PanSemStateFiniteExact 64 F)
    (m v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hm : s.locals.lookup (ofString "m") = some m)
    (hrun : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_scratch_release) =
      (some (.returned v), post)) :
    post.globals = s.globals.update (ofString "scratch_ptr", m) ∧
      post.memory = s.memory ∧ post.code = s.code ∧ post.memaddrs = s.memaddrs :=
  release_body_returned_effect s (ofString "scratch_ptr") m v post hm hrun

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
