import InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec.Base
import InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.Common
import InitECandidate.Solver.Wave8GuestInv.ContractParts.C00Defs
import InitECandidate.Solver.Wave8GuestInv.R11Shards.FrameException
import InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.TruncateSpec
import InitECandidate.Solver.Wave8GuestInv.R16Shards.HtabUnionIntoSpec
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.FrameBase
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.StackPush
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.StackPushInv
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.StateGasHelpers
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadDelHtabSet
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.AllocJournalStep
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M25.rt_alloc
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.RlpMemcpyLemmas
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.rv_min

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

def RollbackReadyAt {F : Type} (s : PanSemStateFiniteExact 64 F) (c : Nat) : Prop :=
  ArenaReady s ∧ Allocated s (c, 280) ∧ WordsOK s (c, 280) ∧
    (∀ k ∈ [168, 176],
      HtabWF s (memW s (c + k)) ∧
      ∀ i ∈ htabFootprint s (memW s (c + k)), Allocated s i ∧ Disj (c, 280) i) ∧
    (memW s (c + 168) = memW s (c + 176) ∨
      ∀ i ∈ htabFootprint s (memW s (c + 168)),
        ∀ j ∈ htabFootprint s (memW s (c + 176)), Disj i j)

def RollbackReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => RollbackReadyAt s (locN s "child")

theorem rollbackReadyAt_of_mem_evmChain {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : EvmInv s) {ec : Ivl} (hmem : ec ∈ evmChain s) :
    RollbackReadyAt s ec.1 := by
  obtain ⟨hA, S, hW, hrest⟩ := h
  obtain ⟨hT, -, -, -⟩ := hW
  obtain ⟨-, hTt, hTp, -⟩ := hT
  dsimp only at hrest
  obtain ⟨-, -, -, hWF, -, -, -, hdis, -⟩ := hrest
  have hF := hWF ec hmem
  dsimp only [FrameWF] at hF
  obtain ⟨hblk, -, -, -, -, -, -, -, h168, h176, -⟩ := hF
  have hrec := hblk (ec.1, 280) (by simp)
  have hd := hdis ec hmem (ec.1, 280) (by simp [frameObjects])
  refine ⟨hA, Or.inr hrec.1, hrec.2, ?_, ?_⟩
  · intro k hk
    have hS : memW s (ec.1 + k) ∈ S := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact h168
      · exact h176
    exact ⟨(hTt _ hS).1, fun i hi => ⟨((hTt _ hS).2 i hi).1, hd.1 _ hS i hi⟩⟩
  · by_cases heq : memW s (ec.1 + 168) = memW s (ec.1 + 176)
    · exact Or.inl heq
    · exact Or.inr (hTp _ h168 _ h176 heq)

theorem rollbackReadyAt_of_evmInv {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) :
    RollbackReadyAt s (globN s "ev") :=
  rollbackReadyAt_of_mem_evmChain s h (ec := (globN s "ev", globN s "cur_cont"))
    (by simp [evmChain, evmChainFrom])

def bufferRegion {F : Type} (s : PanSemStateFiniteExact 64 F) (gn : String × Nat) : Ivl :=
  (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)

theorem disj_flip {i j : Ivl} (h : Disj i j) : Disj j i := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

theorem worldTyped_iff_with {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) :
    WorldTyped s S ↔ ∃ Nd, InitECandidate.Solver.Wave8Contracts.M23.WorldTypedWith s S Nd := by
  simp only [WorldTyped, TriesTyped, InitECandidate.Solver.Wave8Contracts.M23.WorldTypedWith]
  exact ⟨fun ⟨h1, h2, h3, Nd, h4⟩ => ⟨Nd, h1, h2, h3, h4⟩,
         fun ⟨Nd, h1, h2, h3, h4⟩ => ⟨h1, h2, h3, Nd, h4⟩⟩

theorem bufferRegion_disj {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hW : InitECandidate.Solver.Wave8Contracts.M23.WorldTypedWith s S Nd)
    (gn : String × Nat) (hg : gn ∈ globalBuffers)
    (hu : gn.1 ∉ InitECandidate.Solver.Wave8Contracts.M23.typedRecords.map Prod.fst) :
    ∀ j ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Nd,
      Disj (bufferRegion s gn) j := by
  let buffers := globalBuffers.map (bufferRegion s)
  let rest := [(if globN s "journal_cap" = 0 then 0 else globN s "journal",
      32 * globN s "journal_cap")] ++ blockOutObjects s ++ balObjects s
  have hfixed : fixedObjects s = buffers ++ rest := by
    simp only [fixedObjects, buffers, rest, List.append_assoc]
    rfl
  have hpair := hW.2.2.1.2
  rw [hfixed] at hpair
  have hmem : bufferRegion s gn ∈ buffers := List.mem_map.mpr ⟨gn, hg, rfl⟩
  have hfixmem : bufferRegion s gn ∈ fixedObjects s := by
    rw [hfixed]; exact List.mem_append_left _ hmem
  have hcross := (List.pairwise_append.mp hpair).2.2
  have hnames : globalBuffers.Pairwise
      (fun a b => Disj (bufferRegion s a) (bufferRegion s b)) :=
    List.pairwise_map.mp (List.pairwise_append.mp hpair).1
  have : Std.Symm (fun a b : String × Nat => Disj (bufferRegion s a) (bufferRegion s b)) :=
    ⟨fun _ _ h => disj_flip h⟩
  intro j hj
  simp only [InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls, List.mem_append] at hj
  rcases hj with ((((ht | hr) | hjournal) | hbo) | hbal) | hn
  · obtain ⟨t, ht, hj⟩ := List.mem_flatMap.mp ht
    exact disj_flip (((hW.1.2.1 t ht).2 j hj).2 _ hfixmem)
  · obtain ⟨r, hrecord, heq⟩ := List.mem_map.mp hr
    rw [← heq]
    change Disj (bufferRegion s gn) (bufferRegion s r)
    have hrg : r ∈ globalBuffers :=
      (by decide : ∀ r ∈ InitECandidate.Solver.Wave8Contracts.M23.typedRecords,
        r ∈ globalBuffers) r hrecord
    have hne : gn ≠ r := by
      intro heq; apply hu; exact List.mem_map.mpr ⟨r, hrecord, congrArg Prod.fst heq.symm⟩
    exact hnames.forall hg hrg hne
  · exact hcross _ hmem _ (by simp only [rest, List.mem_append]; exact Or.inl (Or.inl hjournal))
  · exact hcross _ hmem _ (by simp only [rest, List.mem_append]; exact Or.inl (Or.inr hbo))
  · exact hcross _ hmem _ (by simp only [rest, List.mem_append]; exact Or.inr hbal)
  · exact disj_flip ((hW.2.2.2.2.1 j hn).2 _ hfixmem)

theorem bufferRegion_disj_le {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hW : InitECandidate.Solver.Wave8Contracts.M23.WorldTypedWith s S Nd)
    (gn : String × Nat) (hg : gn ∈ globalBuffers)
    (hu : gn.1 ∉ InitECandidate.Solver.Wave8Contracts.M23.typedRecords.map Prod.fst)
    (n : Nat) (hle : n ≤ gn.2) :
    ∀ j ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Nd,
      Disj (bufferRegion s (gn.1, n)) j := by
  intro j hj
  have h := bufferRegion_disj hW gn hg hu j hj
  by_cases hz : globN s gn.1 = 0
  · exact Or.inl (by simp [bufferRegion, hz])
  · simp only [bufferRegion, hz, ↓reduceIte] at h ⊢
    unfold Disj at h ⊢
    dsimp only at h ⊢
    omega

def createBuffers : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl :=
  fun s => [bufferRegion s ("keccak_pad", 136), bufferRegion s ("keccak_st", 200),
    bufferRegion s ("mpt_nib_scratch", 64), bufferRegion s ("sk_buf", 52)]

theorem create_buffer_part_disj {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hi : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (hw : InitECandidate.Solver.Wave8Contracts.M23.WorldTypedWith s S Nd)
    (gn : String × Nat) (hg : gn ∈ globalBuffers)
    (hu : gn.1 ∉ InitECandidate.Solver.Wave8Contracts.M23.typedRecords.map Prod.fst)
    (n : Nat) (hn : n ≤ gn.2) :
    ∀ j ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Nd ++
        ((evmChain s).map (frameObjects s)).flatten,
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
    have hd := disj_flip (((hi.2.2.2.2.2.2.2.2.1 ec hec j hj).2 _ hf))
    by_cases hz : globN s gn.1 = 0
    · exact Or.inl (by simp [bufferRegion, hz])
    · simp only [bufferRegion, hz, ↓reduceIte] at hd ⊢
      unfold Disj at hd ⊢
      dsimp only at hd ⊢
      omega

theorem evmAvoids_createBuffers_of_evmInv {F : Type}
    (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) :
    EvmAvoids createBuffers s := by
  obtain ⟨ha, S, hi⟩ := h
  obtain ⟨Nd, hw⟩ := (worldTyped_iff_with s S).mp hi.1
  refine ⟨ha, S, hi, Nd, hw.2.2.2, ?_⟩
  intro i hm
  simp only [createBuffers, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact create_buffer_part_disj hi hw ("keccak_pad", 136) (by decide) (by decide) 136 (by decide)
  · exact create_buffer_part_disj hi hw ("keccak_st", 200) (by decide) (by decide) 200 (by decide)
  · exact create_buffer_part_disj hi hw ("mpt_nib_scratch", 64) (by decide) (by decide) 64 (by decide)
  · exact create_buffer_part_disj hi hw ("sk_buf", 64) (by decide) (by decide) 52 (by decide)

theorem journalRole_not_frame_role {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat) :
    journalRole s t ∉ (["frame.del", "frame.addr", "frame.key"] : List String) := by
  unfold journalRole
  split
  · decide
  · split
    · decide
    · split
      · decide
      · split
        · decide
        · decide

theorem journalRole_ne_frame_del {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat) :
    journalRole s t ≠ "frame.del" :=
  fun h => journalRole_not_frame_role s t (by simp [h])

theorem mem_journalRoleSlots_role_ne_frame_del {F : Type} (s : PanSemStateFiniteExact 64 F)
    {a : Nat × String} (ha : a ∈ journalRoleSlots s) :
    a.2 ≠ "frame.del" := by
  unfold journalRoleSlots at ha
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp ha
  dsimp only at hi
  rcases List.mem_cons.mp hi with rfl | hrest
  · exact journalRole_ne_frame_del s _
  · split at hrest
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hrest
      subst hrest
      dsimp only
      decide
    · simp at hrest

theorem frame_del_not_in_journalRoleSlots {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S : List Nat} {ch : List Ivl} {ec : Ivl}
    (hRoles : RolesOK s S (worldRoleSlots s ++ frameRoleSlots s ch) (journalRoleSlots s))
    (hec : ec ∈ ch) :
    ∀ a ∈ journalRoleSlots s, a.1 ≠ memW s (ec.1 + 136) := by
  intro a ha heq
  have hfrs : (memW s (ec.1 + 136), "frame.del") ∈
      (worldRoleSlots s ++ frameRoleSlots s ch) ++ journalRoleSlots s := by
    apply List.mem_append_left
    apply List.mem_append_right
    unfold frameRoleSlots
    exact List.mem_flatMap.mpr ⟨ec, hec, by simp⟩
  have hrole := hRoles.2.2 a ha _ hfrs heq
  exact mem_journalRoleSlots_role_ne_frame_del s ha hrole

theorem frame_access_not_in_world_or_journal {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S : List Nat} {ch : List Ivl} {ec : Ivl} {k : Nat}
    (hRoles : RolesOK s S (worldRoleSlots s ++ frameRoleSlots s ch) (journalRoleSlots s))
    (hec : ec ∈ ch) (hk : k ∈ ([136, 168, 176] : List Nat)) :
    (∀ a ∈ worldRoleSlots s, a.1 ≠ memW s (ec.1 + k)) ∧
    (∀ a ∈ journalRoleSlots s, a.1 ≠ memW s (ec.1 + k)) := by
  have hrole_pair : ∃ r : String,
      (memW s (ec.1 + k), r) ∈ frameRoleSlots s ch ∧
      r ∈ (["frame.del", "frame.addr", "frame.key"] : List String) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · exact ⟨"frame.del", List.mem_flatMap.mpr ⟨ec, hec, by simp⟩, by simp⟩
    · exact ⟨"frame.addr", List.mem_flatMap.mpr ⟨ec, hec, by simp⟩, by simp⟩
    · exact ⟨"frame.key", List.mem_flatMap.mpr ⟨ec, hec, by simp⟩, by simp⟩
  obtain ⟨r, hfrs, hr_mem⟩ := hrole_pair
  constructor
  · intro a ha heq
    have hpw := (List.pairwise_append.mp hRoles.2.1).2.2 a ha (memW s (ec.1 + k), r) hfrs heq
    have hwr_role : a.2 ∉ (["frame.del", "frame.addr", "frame.key"] : List String) := by
      unfold worldRoleSlots at ha
      have ha' := (List.mem_filter.mp ha).1
      rcases List.mem_append.mp ha' with h1 | hbal
      · rcases List.mem_append.mp h1 with h2 | hts_n
        · rcases List.mem_append.mp h2 with h3 | hbs_n
          · rcases List.mem_append.mp h3 with h4 | hg
            · rcases List.mem_append.mp h4 with h5 | hts
              · rcases List.mem_append.mp h5 with hws | hbs
                · unfold recRoles at hws; split at hws
                  · simp at hws
                  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hws
                    dsimp only; fin_cases hx <;> decide
                · unfold recRoles at hbs; split at hbs
                  · simp at hbs
                  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hbs
                    dsimp only; fin_cases hx <;> decide
              · unfold recRoles at hts; split at hts
                · simp at hts
                · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hts
                  dsimp only; fin_cases hx <;> decide
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
              rcases hg with rfl | rfl | rfl <;> dsimp only <;> decide
          · unfold nestRoles at hbs_n; split at hbs_n
            · simp at hbs_n
            · split at hbs_n
              · simp at hbs_n
              · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hbs_n; dsimp only; decide
        · unfold nestRoles at hts_n; split at hts_n
          · simp at hts_n
          · split at hts_n
            · simp at hts_n
            · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hts_n; dsimp only; decide
      · obtain ⟨ad, _, had⟩ := List.mem_flatMap.mp hbal
        simp only [List.mem_cons, List.not_mem_nil, or_false] at had
        rcases had with rfl | rfl <;> dsimp only <;> decide
    exact hwr_role (hpw.1 ▸ hr_mem)
  · intro a ha heq
    have hfrs_all : (memW s (ec.1 + k), r) ∈
        (worldRoleSlots s ++ frameRoleSlots s ch) ++ journalRoleSlots s :=
      List.mem_append_left _ (List.mem_append_right _ hfrs)
    have hrole := hRoles.2.2 a ha _ hfrs_all heq
    have hjr_role : a.2 ∉ (["frame.del", "frame.addr", "frame.key"] : List String) := by
      unfold journalRoleSlots at ha
      obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp ha
      dsimp only at hi
      rcases List.mem_cons.mp hi with rfl | hrest
      · exact journalRole_not_frame_role s _
      · split at hrest
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hrest
          subst hrest; dsimp only; decide
        · simp at hrest
    exact hjr_role (hrole ▸ hr_mem)

def ChainLinks (m : Nat → Nat) : List Ivl → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => m (b.1 + 24) + m (b.1 + 40) = m (a.2 + 56) ∧ ChainLinks m (b :: rest)

def HeadMemChainWF {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  (∀ ec ∈ evmChain s, memW s (ec.1 + 32) % 32 = 0 ∧ memW s (ec.1 + 40) % 8 = 0) ∧
  memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = globN s "frame_mem_ptr" ∧
  ChainLinks (memW s) (evmChain s)

def FinishReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => EvmInv s ∧ EvmDone s ∧ memW s (globN s "cur_cont" + 16) ≠ 0

def EvmInvA : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => EvmInv s ∧ HeadMemChainWF s

def FinishReadyA : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => EvmInvA s ∧ EvmDone s ∧ memW s (globN s "cur_cont" + 16) ≠ 0

def FinishChildSpecU : Prop :=
  FunSpec FinishReady
    (fun s r post => ((∃ v, r = some (.returned v)) ∨ OpDispatchSpec.IsEvmErr r) →
      EvmInv post ∧ (evmChain post).length + 1 = (evmChain s).length ∧
        OpDispatchSpec.evmR post ≤ OpDispatchSpec.evmR s)
    (ofString "finish_child")

def FinishChildMemSpec : Prop :=
  FunSpec FinishReadyA
    (fun s r post => ((∃ v, r = some (.returned v)) ∨ OpDispatchSpec.IsEvmErr r) →
      evmChain post = (evmChain s).tail ∧
      (∀ ec ∈ evmChain post, memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
        memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧ memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧
        memW post (ec.2 + 56) = memW s (ec.2 + 56)) ∧
      globN post "ev" = memW s (globN s "cur_cont") ∧
      globN post "frame_mem_ptr" = memW s (globN s "cur_cont" + 56))
    (ofString "finish_child")

def ChainCellsKept (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (fname : MlS) : Prop :=
  FunSpec P (fun s r post => InitECandidate.Solver.Wave8Contracts.M23.Resumes r → ∀ ec ∈ evmChain s,
      memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧ memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧
      memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧ memW post (ec.2 + 56) = memW s (ec.2 + 56))
    fname

theorem evmChain_cons {F : Type} (s : PanSemStateFiniteExact 64 F) :
    evmChain s = (globN s "ev", globN s "cur_cont") ::
      (if memW s (globN s "cur_cont" + 16) = 0 then [] else
        evmChainFrom s maxChain (memW s (globN s "cur_cont"))
          (memW s (globN s "cur_cont" + 8))) := by
  simp only [evmChain, evmChainFrom]

theorem evmChain_cons_of_cont_ne_zero {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hne : memW s (globN s "cur_cont" + 16) ≠ 0) :
    evmChain s = (globN s "ev", globN s "cur_cont") ::
      evmChainFrom s maxChain (memW s (globN s "cur_cont"))
        (memW s (globN s "cur_cont" + 8)) := by
  rw [evmChain_cons, if_neg hne]

theorem evmChainFrom_succ_eq_of_closed {F : Type} {s : PanSemStateFiniteExact 64 F} :
    ∀ (fuel e c : Nat),
      (∃ ec ∈ (evmChainFrom s (fuel + 1) e c).getLast?, memW s (ec.2 + 16) = 0) →
      evmChainFrom s (fuel + 2) e c = evmChainFrom s (fuel + 1) e c := by
  intro fuel
  induction fuel with
  | zero =>
    intro e c ⟨ec, hec, hk0⟩
    by_cases h0 : memW s (c + 16) = 0
    · simp only [evmChainFrom, if_pos h0]
    · simp only [evmChainFrom, if_neg h0, List.getLast?_singleton, Option.mem_def,
        Option.some.injEq] at hec
      subst hec
      exact absurd hk0 h0
  | succ fuel ih =>
    intro e c ⟨ec, hec, hk0⟩
    by_cases h0 : memW s (c + 16) = 0
    · simp only [evmChainFrom, if_pos h0]
    · have h1 : evmChainFrom s (fuel + 1 + 1) e c =
          (e, c) :: evmChainFrom s (fuel + 1) (memW s c) (memW s (c + 8)) := by
        simp only [evmChainFrom, if_neg h0]
      have h2 : evmChainFrom s (fuel + 1 + 2) e c =
          (e, c) :: evmChainFrom s (fuel + 2) (memW s c) (memW s (c + 8)) := by
        simp only [evmChainFrom, if_neg h0]
      rw [h1] at hec
      have hne_tail : evmChainFrom s (fuel + 1) (memW s c) (memW s (c + 8)) ≠ [] := by
        rw [evmChainFrom]; simp
      rw [List.getLast?_cons_of_ne_nil hne_tail] at hec
      rw [h1, h2, ih (memW s c) (memW s (c + 8)) ⟨ec, hec, hk0⟩]

theorem evmChain_pop_eq_tail {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hne : memW s (globN s "cur_cont" + 16) ≠ 0)
    (hlast : ∃ ec ∈ (evmChain s).getLast?, memW s (ec.2 + 16) = 0)
    (hm : post.memory = s.memory)
    (hev : globN post "ev" = memW s (globN s "cur_cont"))
    (hcc : globN post "cur_cont" = memW s (globN s "cur_cont" + 8)) :
    evmChain post = (evmChain s).tail := by
  have hmc : maxChain = (maxChain - 1) + 1 := by decide
  have hfrom_congr : ∀ (fuel e c : Nat), evmChainFrom post fuel e c = evmChainFrom s fuel e c := by
    have hmw : ∀ a, memW post a = memW s a := fun a => by
      unfold memW
      change (match post.memory (BitVec.ofNat 64 a) with | .word v => v.toNat) =
        (match s.memory (BitVec.ofNat 64 a) with | .word v => v.toNat)
      rw [hm]
    intro fuel; induction fuel with
    | zero => intros; rfl
    | succ f ihf =>
      intro e c
      simp only [evmChainFrom, hmw, ihf]
  have hcons := evmChain_cons_of_cont_ne_zero hne
  rw [hcons, List.tail_cons]
  obtain ⟨ecL, hecL, hk0⟩ := hlast
  rw [hcons] at hecL
  have hne_tail : evmChainFrom s maxChain (memW s (globN s "cur_cont"))
      (memW s (globN s "cur_cont" + 8)) ≠ [] := by
    rw [hmc]; simp [evmChainFrom]
  rw [List.getLast?_cons_of_ne_nil hne_tail] at hecL
  unfold evmChain
  rw [hev, hcc, hfrom_congr]
  have hmc2 : maxChain + 1 = (maxChain - 1) + 2 := by decide
  rw [hmc2]
  conv_rhs => rw [hmc]
  exact evmChainFrom_succ_eq_of_closed (maxChain - 1) _ _ ⟨ecL, by rwa [← hmc], hk0⟩

theorem worldTyped_filter_del {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    {ch : List Ivl} {t0 : Nat}
    (hW : WorldTyped s S)
    (hDel0 : DelExclusive s S ch 0 t0)
    (hRoles : RolesOK s S (worldRoleSlots s ++ frameRoleSlots s ch) (journalRoleSlots s))
    (hch0 : 0 < ch.length)
    (ht0_eq : memW s ((ch[0]'hch0).1 + 136) = t0) :
    WorldTyped s (S.filter (· != t0)) := by
  set S' := S.filter (· != t0)
  have ht0_not_wr : ∀ a ∈ worldRoleSlots s, a.1 ≠ t0 := by
    have := (frame_access_not_in_world_or_journal hRoles (List.getElem_mem hch0) (by simp : 136 ∈ ([136, 168, 176] : List Nat))).1
    simpa [ht0_eq] using this
  have ht0_not_jr : ∀ a ∈ journalRoleSlots s, a.1 ≠ t0 := by
    have := (frame_access_not_in_world_or_journal hRoles (List.getElem_mem hch0) (by simp : 136 ∈ ([136, 168, 176] : List Nat))).2
    simpa [ht0_eq] using this
  have hmem_S' : ∀ u, u ∈ S' ↔ u ∈ S ∧ u ≠ t0 := by
    intro u; simp [S', bne_iff_ne]
  have hroot_S' : ∀ u, RootIn S u → u ≠ t0 → RootIn S' u := by
    intro u hru hne
    rcases hru with rfl | huS
    · exact Or.inl rfl
    · exact Or.inr ((hmem_S' u).mpr ⟨huS, hne⟩)
  obtain ⟨hT, hJ, hF, Nd, hTr⟩ := hW
  obtain ⟨hNodup, hTt, hTp, hws, hbs, hts, hg, hbs_nest, hts_nest, hbal, hbo, hRolesW⟩ := hT
  have hnot_wtr := hDel0.1
  have hwtr_ws : ∀ k ∈ wsTableSlots, globN s "ws" ≠ 0 → memW s (globN s "ws" + k) ≠ t0 := by
    intro k hk hnz heq
    apply hnot_wtr
    unfold worldTableRefs
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left
    unfold recordSlots; rw [if_neg hnz]
    exact List.mem_map.mpr ⟨k, hk, heq⟩
  have hwtr_bs : ∀ k ∈ bsTableSlots, globN s "bs" ≠ 0 → memW s (globN s "bs" + k) ≠ t0 := by
    intro k hk hnz heq
    apply hnot_wtr
    unfold worldTableRefs
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_right
    unfold recordSlots; rw [if_neg hnz]
    exact List.mem_map.mpr ⟨k, hk, heq⟩
  have hwtr_ts : ∀ k ∈ tsTableSlots, globN s "ts" ≠ 0 → memW s (globN s "ts" + k) ≠ t0 := by
    intro k hk hnz heq
    apply hnot_wtr
    unfold worldTableRefs
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    unfold recordSlots; rw [if_neg hnz]
    exact List.mem_map.mpr ⟨k, hk, heq⟩
  have hwtr_g : ∀ g ∈ globalTableRoots, globN s g ≠ t0 := by
    intro g hgi heq
    apply hnot_wtr
    unfold worldTableRefs
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_right
    exact List.mem_map.mpr ⟨g, hgi, heq⟩
  have hwtr_bs_nest : globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ∈ S →
      ∀ v ∈ htabValues s (memW s (globN s "bs" + 32)), v ≠ t0 := by
    intro hnz hin v hv heq
    apply hnot_wtr
    unfold worldTableRefs
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_right
    dsimp only; rw [if_pos ⟨hnz, hin⟩]; exact heq ▸ hv
  have hwtr_ts_nest : globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ∈ S →
      ∀ v ∈ htabValues s (memW s (globN s "ts" + 32)), v ≠ t0 := by
    intro hnz hin v hv heq
    apply hnot_wtr
    unfold worldTableRefs
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    dsimp only; rw [if_pos ⟨hnz, hin⟩]; exact heq ▸ hv
  have hwtr_bal : ∀ ad ∈ balRecords s, memW s ad ≠ t0 ∧ memW s (ad + 8) ≠ t0 := by
    intro ad had
    constructor <;> intro heq <;> apply hnot_wtr <;> unfold worldTableRefs <;>
      apply List.mem_append_left <;> apply List.mem_append_right
    · exact List.mem_flatMap.mpr ⟨ad, had, by simp [heq]⟩
    · exact List.mem_flatMap.mpr ⟨ad, had, by simp [heq]⟩
  have hwtr_j : ∀ k < globN s "journal_n", memW s (globN s "journal" + 32 * k) ≠ t0 := by
    intro k hk heq
    apply hnot_wtr
    unfold worldTableRefs
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, heq⟩
  refine ⟨?_, ?_, hF, Nd, ?_⟩
  · refine ⟨hNodup.filter _,
      fun t ht => hTt t ((hmem_S' t).mp ht).1,
      fun t ht u hu hne => hTp t ((hmem_S' t).mp ht).1 u ((hmem_S' u).mp hu).1 hne,
      fun k hk hnz => hroot_S' _ (hws k hk hnz) (hwtr_ws k hk hnz),
      fun k hk hnz => hroot_S' _ (hbs k hk hnz) (hwtr_bs k hk hnz),
      fun k hk hnz => hroot_S' _ (hts k hk hnz) (hwtr_ts k hk hnz),
      fun g hgi => hroot_S' _ (hg g hgi) (hwtr_g g hgi),
      fun hnz hin => ?_,
      fun hnz hin => ?_,
      fun ad had => ⟨(hmem_S' _).mpr ⟨(hbal ad had).1, (hwtr_bal ad had).1⟩,
        (hmem_S' _).mpr ⟨(hbal ad had).2.1, (hwtr_bal ad had).2⟩, (hbal ad had).2.2⟩,
      hbo, ?_⟩
    · have hinS := ((hmem_S' _).mp hin).1
      intro i hi
      have hri := hbs_nest hnz hinS i hi
      have hval_in : nodeF s (hdr s (memW s (globN s "bs" + 32)) 5)
          (memW s (hdr s (memW s (globN s "bs" + 32)) 6 + 8 * i)) 8 ∈
          htabValues s (memW s (globN s "bs" + 32)) := by
        unfold htabValues
        exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
      exact (hmem_S' _).mpr ⟨hri, hwtr_bs_nest hnz hinS _ hval_in⟩
    · have hinS := ((hmem_S' _).mp hin).1
      intro i hi
      have hri := hts_nest hnz hinS i hi
      have hval_in : nodeF s (hdr s (memW s (globN s "ts" + 32)) 5)
          (memW s (hdr s (memW s (globN s "ts" + 32)) 6 + 8 * i)) 8 ∈
          htabValues s (memW s (globN s "ts" + 32)) := by
        unfold htabValues
        exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
      exact (hmem_S' _).mpr ⟨hri, hwtr_ts_nest hnz hinS _ hval_in⟩
    · refine ⟨fun a ha => ?_, hRolesW.2⟩
      obtain ⟨haS, hkl⟩ := hRolesW.1 a ha
      have hane : a.1 ≠ t0 := by
        rcases List.mem_append.mp ha with hwr | hjr
        · exact ht0_not_wr a hwr
        · exact ht0_not_jr a hjr
      exact ⟨(hmem_S' a.1).mpr ⟨haS, hane⟩, hkl⟩
  · refine ⟨hJ.1, hJ.2.1, hJ.2.2.1, fun k hk => ?_⟩
    exact (hmem_S' _).mpr ⟨hJ.2.2.2 k hk, hwtr_j k hk⟩
  · refine ⟨hTr.1, fun o ho => ⟨fun t ht => (hTr.2.1 o ho).1 t ((hmem_S' t).mp ht).1,
      (hTr.2.1 o ho).2⟩, fun hnz => ⟨(hTr.2.2 hnz).1, fun hin => (hTr.2.2 hnz).2 ((hmem_S' _).mp hin).1⟩⟩

theorem worldTableRefs_filter_del_eq {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    {t0 : Nat} (hnot_wtr : t0 ∉ worldTableRefs s S) :
    worldTableRefs s (S.filter (· != t0)) = worldTableRefs s S := by
  have hbs32_ne : globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0 := by
    intro hnz heq; apply hnot_wtr
    unfold worldTableRefs
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_right
    unfold recordSlots; rw [if_neg hnz]
    exact List.mem_map.mpr ⟨32, by decide, heq⟩
  have hts32_ne : globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0 := by
    intro hnz heq; apply hnot_wtr
    unfold worldTableRefs
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    unfold recordSlots; rw [if_neg hnz]
    exact List.mem_map.mpr ⟨32, by decide, heq⟩
  unfold worldTableRefs
  dsimp only
  have hbs_iff : (globN s "bs" ≠ 0 ∧ memW s (globN s "bs" + 32) ∈ S.filter (· != t0)) ↔
      (globN s "bs" ≠ 0 ∧ memW s (globN s "bs" + 32) ∈ S) := by
    constructor
    · rintro ⟨hnz, h⟩; exact ⟨hnz, (List.mem_filter.mp h).1⟩
    · rintro ⟨hnz, h⟩
      exact ⟨hnz, List.mem_filter.mpr ⟨h, bne_iff_ne.mpr (hbs32_ne hnz)⟩⟩
  have hts_iff : (globN s "ts" ≠ 0 ∧ memW s (globN s "ts" + 32) ∈ S.filter (· != t0)) ↔
      (globN s "ts" ≠ 0 ∧ memW s (globN s "ts" + 32) ∈ S) := by
    constructor
    · rintro ⟨hnz, h⟩; exact ⟨hnz, (List.mem_filter.mp h).1⟩
    · rintro ⟨hnz, h⟩
      exact ⟨hnz, List.mem_filter.mpr ⟨h, bne_iff_ne.mpr (hts32_ne hnz)⟩⟩
  simp only [hbs_iff, hts_iff]

theorem evmInvAt_of_pop_globals {F : Type} {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hAs : ArenaReady s) (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (hne : memW s (globN s "cur_cont" + 16) ≠ 0)
    (hAp : ArenaReady post)
    (hm : post.memory = s.memory)
    (hdom : post.memaddrs = s.memaddrs)
    (hbe : post.be = s.be)
    (hev : globN post "ev" = memW s (globN s "cur_cont"))
    (hcc : globN post "cur_cont" = memW s (globN s "cur_cont" + 8))
    (hg : ∀ name : String,
      name ≠ "ev" → name ≠ "cur_cont" → globN post name = globN s name) :
    ∃ S' : List Nat,
      (∀ t ∈ S', t ∈ S) ∧
      ((S' = S ∧ ¬ DelExclusive s S (evmChain s) 0 (memW s (globN s "ev" + 136))) ∨
        (S' = S.filter (· != memW s (globN s "ev" + 136)) ∧
        DelExclusive s S (evmChain s) 0 (memW s (globN s "ev" + 136)))) ∧
      InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt post S' ∧
      evmChain post = (evmChain s).tail ∧
      OpDispatchSpec.evmR post + (memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192)) =
        OpDispatchSpec.evmR s := by
  have hmw : ∀ a, memW post a = memW s a := fun a => by
    unfold memW
    change (match post.memory (BitVec.ofNat 64 a) with | .word v => v.toNat) =
      (match s.memory (BitVec.ofNat 64 a) with | .word v => v.toNat)
    rw [hm]
  obtain ⟨hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, hAT, hMarks, hRoles, hGas⟩ := hInv
  have hch_post : evmChain post = (evmChain s).tail :=
    evmChain_pop_eq_tail hne hch_last hm hev hcc
  have hcons := evmChain_cons_of_cont_ne_zero hne
  set chTail := evmChainFrom s maxChain (memW s (globN s "cur_cont"))
    (memW s (globN s "cur_cont" + 8))
  have htail_eq : (evmChain s).tail = chTail := by rw [hcons]; rfl
  have htail_ne : (evmChain s).tail ≠ [] := by
    rw [htail_eq]; dsimp only [chTail]
    have hmc : maxChain = (maxChain - 1) + 1 := by decide
    rw [hmc]; simp [evmChainFrom]
  have hlen_cons : (evmChain s).length = (evmChain s).tail.length + 1 := by
    conv_lhs => rw [hcons]
    simp [← htail_eq]
  have h01 : 0 + 1 < (evmChain s).length := by
    have : 0 < (evmChain s).tail.length := List.length_pos_of_ne_nil htail_ne
    omega
  have hch0_eq : (evmChain s)[0]'(by omega) = (globN s "ev", globN s "cur_cont") := by
    simp [hcons]
  set t0 := memW s (globN s "ev" + 136)
  have ht0_ch0 : memW s (((evmChain s)[0]'(by omega)).1 + 136) = t0 := by rw [hch0_eq]
  open Classical in
  let S' : List Nat := if DelExclusive s S (evmChain s) 0 t0 then S.filter (· != t0) else S
  have hS'_sub : ∀ t ∈ S', t ∈ S := by
    intro t ht; dsimp only [S'] at ht; split at ht
    · exact (List.mem_filter.mp ht).1
    · exact ht
  have hS'_cases : (S' = S ∧ ¬ DelExclusive s S (evmChain s) 0 t0) ∨
      (S' = S.filter (· != t0) ∧ DelExclusive s S (evmChain s) 0 t0) := by
    dsimp only [S']; split
    · rename_i hD; exact Or.inr ⟨rfl, hD⟩
    · rename_i hnD; exact Or.inl ⟨rfl, hnD⟩
  have hW_S' : WorldTyped s S' := by
    rcases hS'_cases with ⟨hEq, _⟩ | ⟨hEq, hD0⟩
    · rw [hEq]; exact hW
    · rw [hEq]; exact worldTyped_filter_del hW hD0 hRoles (by omega) ht0_ch0
  have hwtr_S' : worldTableRefs s S' = worldTableRefs s S := by
    rcases hS'_cases with ⟨hEq, _⟩ | ⟨hEq, hD0⟩
    · rw [hEq]
    · rw [hEq]; exact worldTableRefs_filter_del_eq hD0.1
  have hframe_in_S' : ∀ ec ∈ (evmChain s).tail, ∀ k ∈ ([136, 168, 176] : List Nat),
      memW s (ec.1 + k) ∈ S' := by
    intro ec hec k hk
    have hinS : memW s (ec.1 + k) ∈ S := by
      have hFW := hFW_all ec (List.mem_of_mem_tail hec)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact hFW.2.2.2.2.2.2.2.1
      · exact hFW.2.2.2.2.2.2.2.2.1
      · exact hFW.2.2.2.2.2.2.2.2.2.1
    rcases hS'_cases with ⟨hEq, _⟩ | ⟨hEq, hD0⟩
    · rw [hEq]; exact hinS
    · rw [hEq]
      refine List.mem_filter.mpr ⟨hinS, bne_iff_ne.mpr ?_⟩
      intro heq
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hec
      have hj_s : j + 1 < (evmChain s).length := by omega
      have hget_j : (evmChain s)[j + 1] = ((evmChain s).tail)[j] := by simp [List.getElem_tail]
      have := (hD0.2 (j + 1) hj_s k hk (by rw [hget_j]; exact heq)).2
      omega
  have htail_sub : ∀ ec ∈ (evmChain s).tail, ec ∈ evmChain s :=
    fun _ h => List.mem_of_mem_tail h
  have hcg : ∀ g ∈ InitECandidate.Solver.Wave8Contracts.M23.coreWorldGlobals,
      globN post g = globN s g := by
    intro g hg_in
    apply hg g
    · intro h; subst h; simp [InitECandidate.Solver.Wave8Contracts.M23.coreWorldGlobals] at hg_in
    · intro h; subst h; simp [InitECandidate.Solver.Wave8Contracts.M23.coreWorldGlobals] at hg_in
  obtain ⟨Nd_w, hWT⟩ := (worldTyped_iff_with s S').mp hW_S'
  have hcell_w : InitECandidate.Solver.Wave8Contracts.M23.SameTypedCells s post S' Nd_w := by
    refine ⟨hbe, hdom, hAs.1.memaddrs, ?_, ?_, ?_⟩
    · intro a _; rw [hm]
    · intro a _ _ _; rw [hm]
    · intro b _ _; unfold memB; rw [hm, hbe]
  have hhh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by
    rw [hg "heap_ptr" (by decide) (by decide)]
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by
    rw [hg "scratch_ptr" (by decide) (by decide)]
  have hfeq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [InitECandidate.Solver.Wave8Contracts.M23.blockOutObjects_eq hAs.2 hWT.2.2.1 hcell_w
          (hg "bo" (by decide) (by decide)),
        InitECandidate.Solver.Wave8Contracts.M23.balObjects_eq hAs.2 hWT.1 hWT.2.2.1 hcell_w
          (hg "bal_accounts" (by decide) (by decide)),
        hg "journal" (by decide) (by decide),
        hg "journal_cap" (by decide) (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : gn.1 ≠ "ev" ∧ gn.1 ≠ "cur_cont" := by revert gn hgn; decide
    rw [hg gn.1 hne.1 hne.2]
  have hFT_post : FixedTyped post :=
    InitECandidate.Solver.Wave8Contracts.M23.fixedTyped_of_eq hAp hWT.2.2.1 hhh hsc hfeq
  obtain ⟨hWT_post, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.worldTypedWith_congr_w1
    hAs hAp hhh hsc hcg hcell_w hWT ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hW_post : WorldTyped post S' := (worldTyped_iff_with post S').mpr ⟨Nd_w, hWT_post⟩
  have hfp_eq : ∀ t, htabFootprint post t = htabFootprint s t := by
    intro t; unfold htabFootprint hdr; simp only [hmw]
  have hfo_eq : ∀ ec, frameObjects post ec = frameObjects s ec := by
    intro ec
    unfold frameObjects frameLogs frameRet frameLogObjects logOwnedIvls logRecordIvls
    simp only [hmw, hg "vm_system_address" (by decide) (by decide)]
  have hfs_eq : ∀ ec, frameScratch post ec = frameScratch s ec := by
    intro ec; unfold frameScratch; simp only [hmw]
  have hwok : ∀ {o : Ivl}, WordsOK s o → WordsOK post o := by
    intro o ⟨h1, h2, hk⟩
    refine ⟨h1, h2, fun k hklt => ?_⟩
    obtain ⟨w, hdom_k, hmem_k⟩ := hk k hklt
    exact ⟨w, by rwa [hdom], by rwa [hm]⟩
  have hwtr_post : worldTableRefs post S' = worldTableRefs s S' := by
    have hgtr : globalTableRoots.map (globN post) = globalTableRoots.map (globN s) := by
      apply List.map_congr_left
      intro g hgi
      have hne : g ≠ "ev" ∧ g ≠ "cur_cont" := by revert g hgi; decide
      exact hg g hne.1 hne.2
    unfold worldTableRefs recordSlots balRecords
    unfold htabValues hdr nodeF
    simp only [hmw, hgtr, hg "ws" (by decide) (by decide), hg "bs" (by decide) (by decide),
      hg "ts" (by decide) (by decide), hg "bal_accounts" (by decide) (by decide),
      hg "journal" (by decide) (by decide), hg "journal_n" (by decide) (by decide)]
  have hwr_post : worldRoleSlots post = worldRoleSlots s := by
    unfold worldRoleSlots recRoles nestRoles balRecords
    simp only [hmw, hg "ws" (by decide) (by decide), hg "bs" (by decide) (by decide),
      hg "ts" (by decide) (by decide), hg "bal_accounts" (by decide) (by decide),
      hg "bal_idx_accts" (by decide) (by decide), hg "bal_idx_stor" (by decide) (by decide)]
    unfold htabValues hdr nodeF
    simp only [hmw]
  have hjr_post : journalRoleSlots post = journalRoleSlots s := by
    unfold journalRoleSlots journalRole
    simp only [hmw, hg "journal_n" (by decide) (by decide), hg "journal" (by decide) (by decide),
      hg "ts" (by decide) (by decide)]
  have hfrs_post : frameRoleSlots post ((evmChain s).tail) = frameRoleSlots s ((evmChain s).tail) := by
    unfold frameRoleSlots; simp only [hmw]
  have hR_sum : OpDispatchSpec.evmR post +
      (memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192)) = OpDispatchSpec.evmR s := by
    unfold OpDispatchSpec.evmR
    rw [hch_post]
    conv_rhs => rw [hcons]
    simp only [List.map_cons, List.sum_cons, htail_eq, hmw]
    omega
  refine ⟨S', hS'_sub, hS'_cases, ⟨hW_post, ?_⟩, hch_post, hR_sum⟩
  dsimp only; rw [hch_post]
  refine ⟨htail_ne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcons, List.length_cons] at hch_len
    rw [htail_eq]; omega
  · obtain ⟨ecL, hecL, hk0⟩ := hch_last
    rw [hcons, List.getLast?_cons_of_ne_nil (htail_eq ▸ htail_ne)] at hecL
    exact ⟨ecL, by rwa [htail_eq], by rw [hmw]; exact hk0⟩
  · intro ec hec
    have hFW := hFW_all ec (htail_sub ec hec)
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, _, _, _, c11, c12, c13, c14, c15, c16, c17⟩ := hFW
    have c8' : memW s (ec.1 + 136) ∈ S' := hframe_in_S' ec hec 136 (by simp)
    have c9' : memW s (ec.1 + 168) ∈ S' := hframe_in_S' ec hec 168 (by simp)
    have c10' : memW s (ec.1 + 176) ∈ S' := hframe_in_S' ec hec 176 (by simp)
    unfold FrameWF; dsimp only
    simp only [hmw, hg "scratch_ptr" (by decide) (by decide),
      hg "frame_mem_ptr" (by decide) (by decide), hg "heap_ptr" (by decide) (by decide),
      hg "evm_empty" (by decide) (by decide)]
    have hfl_eq : frameLogs post ec = frameLogs s ec := by unfold frameLogs; simp [hmw]
    have hfr_eq : frameRet post ec = frameRet s ec := by unfold frameRet; simp [hmw]
    rw [hfl_eq, hfr_eq]
    refine ⟨fun i hi => ⟨(c1 i hi).1, hwok (c1 i hi).2⟩,
      c2, hwok c3,
      c4, c5, c6, c7, c8', c9', c10', c11, c12, c13,
      hwok c14, ?_, ?_, ?_⟩
    · rcases c15 with h0 | ⟨hin, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hin, hwok hw⟩
    · rcases c16 with hz | ⟨hw_l, hal_l, hlt28, hle_cap, hent⟩
      · exact Or.inl hz
      · right
        refine ⟨hwok hw_l,
          InitECandidate.Solver.Wave8Contracts.M23.allocated_mono hhh hsc hal_l,
          by simpa [hmw] using hlt28, by simpa [hmw] using hle_cap, fun i hi => ?_⟩
        rw [hmw] at hi
        obtain ⟨⟨w_i, hdom_i, hmem_i⟩, hle⟩ := hent i hi
        refine ⟨⟨w_i, by simpa [hmw] using (hdom ▸ hdom_i), by simpa [hmw] using (hm ▸ hmem_i)⟩, ?_⟩
        unfold LogEntryOK at hle ⊢
        simp only [hmw, hg "heap_ptr" (by decide) (by decide)]
        exact ⟨hwok hle.1, hle.2⟩
    · obtain ⟨hal_m, hw_m, hdt, hdf, hdfo, Nd_m, hTr_m, hdj_m⟩ := c17
      have hTr_m' : TriesTypedWith s S' Nd_m := by
        refine ⟨hTr_m.1, fun o ho => ⟨fun t ht => (hTr_m.2.1 o ho).1 t (hS'_sub t ht), (hTr_m.2.1 o ho).2⟩,
          fun hnz => ⟨(hTr_m.2.2 hnz).1, fun hin => (hTr_m.2.2 hnz).2 (hS'_sub _ hin)⟩⟩
      have hcell_m : InitECandidate.Solver.Wave8Contracts.M23.SameTypedCells s post S' Nd_m := by
        refine ⟨hbe, hdom, hAs.1.memaddrs, ?_, ?_, ?_⟩
        · intro a _; rw [hm]
        · intro a _ _ _; rw [hm]
        · intro b _ _; unfold memB; rw [hm, hbe]
      obtain ⟨hWT_m_post, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.worldTypedWith_congr_w1
        hAs hAp hhh hsc hcg hcell_m ⟨hW_S'.1, hW_S'.2.1, hW_S'.2.2.1, hTr_m'⟩
        ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
      refine ⟨InitECandidate.Solver.Wave8Contracts.M23.allocated_mono hhh hsc hal_m,
        hwok hw_m,
        fun t ht i hi => by rw [hfp_eq] at hi; exact hdt t (hS'_sub t ht) i hi,
        by rw [hfeq]; exact hdf,
        fun ec' hec' o ho => by
          rw [hch_post] at hec'; rw [hfo_eq] at ho
          exact hdfo ec' (htail_sub ec' hec') o ho,
        Nd_m, hWT_m_post.2.2.2, fun o ho j hj => ?_⟩
      rw [InitECandidate.Solver.Wave8Contracts.M23.nodeExtents_eq hTr_m'.1 hcell_m] at hj
      exact hdj_m o ho j hj
  · intro ec hec
    have hec_tail : ec ∈ (evmChain s).tail := List.mem_of_mem_tail hec
    unfold FrameRoom
    rw [hmw, hmw]
    exact hFR_all ec hec_tail
  · intro i hi
    have hi_s : (i + 1) + 1 < (evmChain s).length := by omega
    have hrw := hRW (i + 1) hi_s
    have hget0 : ((evmChain s).tail)[i] = (evmChain s)[i + 1] := by simp [List.getElem_tail]
    have hget1 : ((evmChain s).tail)[i + 1] = (evmChain s)[i + 2] := by simp [List.getElem_tail]
    simp only [hmw, hget0, hget1]
    exact hrw
  · rw [show ((evmChain s).tail.map (frameObjects post)) = ((evmChain s).tail.map (frameObjects s)) from
      List.map_congr_left (fun ec _ => hfo_eq ec)]
    conv at hFO_pw => rw [hcons, List.map_cons, List.flatten_cons]
    rw [htail_eq]
    exact (List.pairwise_append.mp hFO_pw).2.1
  · intro ec hec o ho
    rw [hfo_eq] at ho
    obtain ⟨hd1, hd2⟩ := hFO_disj ec (htail_sub ec hec) o ho
    exact ⟨fun t ht i hi => by rw [hfp_eq] at hi; exact hd1 t (hS'_sub t ht) i hi,
      fun j hj => by rw [hfeq] at hj; exact hd2 j hj⟩
  · obtain ⟨Nd_a, hTr_a, hdj_a⟩ := hAT
    have hTr_a' : TriesTypedWith s S' Nd_a := by
      refine ⟨hTr_a.1, fun o ho => ⟨fun t ht => (hTr_a.2.1 o ho).1 t (hS'_sub t ht), (hTr_a.2.1 o ho).2⟩,
        fun hnz => ⟨(hTr_a.2.2 hnz).1, fun hin => (hTr_a.2.2 hnz).2 (hS'_sub _ hin)⟩⟩
    have hcell_a : InitECandidate.Solver.Wave8Contracts.M23.SameTypedCells s post S' Nd_a := by
      refine ⟨hbe, hdom, hAs.1.memaddrs, ?_, ?_, ?_⟩
      · intro a _; rw [hm]
      · intro a _ _ _; rw [hm]
      · intro b _ _; unfold memB; rw [hm, hbe]
    obtain ⟨hWT_a_post, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.worldTypedWith_congr_w1
      hAs hAp hhh hsc hcg hcell_a ⟨hW_S'.1, hW_S'.2.1, hW_S'.2.2.1, hTr_a'⟩
      ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
    refine ⟨Nd_a, hWT_a_post.2.2.2, fun o ho j hj => ?_⟩
    rw [InitECandidate.Solver.Wave8Contracts.M23.nodeExtents_eq hTr_a'.1 hcell_a] at hj
    obtain ⟨os, hos, ho'⟩ := List.mem_flatten.mp ho
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.mp hos
    rw [hfo_eq] at ho'
    exact hdj_a o (List.mem_flatten.mpr ⟨frameObjects s ec,
      List.mem_map.mpr ⟨ec, htail_sub ec hec, rfl⟩, ho'⟩) j hj
  · intro i hi
    have hi_s : (i + 1) + 1 < (evmChain s).length := by omega
    have hM := hMarks (i + 1) hi_s
    have hget_i : ((evmChain s).tail)[i] = (evmChain s)[i + 1] := by simp [List.getElem_tail]
    dsimp only at hM ⊢
    simp only [hget_i, hmw, hfs_eq, hfeq]
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
    refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
    · intro j hj hij
      have hj_s : j + 1 < (evmChain s).length := by omega
      have hget_j : ((evmChain s).tail)[j] = (evmChain s)[j + 1] := by simp [List.getElem_tail]
      have hfl_j : frameLogs post (((evmChain s).tail)[j]) = frameLogs s ((evmChain s)[j + 1]) := by
        rw [hget_j]; unfold frameLogs; simp [hmw]
      rw [hfo_eq, hfl_j, hget_j]
      exact m5 (j + 1) hj_s (by omega)
    · intro t ht'
      have ht := hS'_sub t ht'
      rw [hfp_eq t]
      rcases m8 t ht with ⟨htake_in, hdelEx⟩ | hfp_in
      · have htake_split : ((evmChain s).take (i + 2)).map (fun ec => memW s (ec.1 + 136)) =
            t0 :: (((evmChain s).tail.take (i + 1)).map (fun ec => memW s (ec.1 + 136))) := by
          conv_lhs => rw [hcons, List.take_succ_cons, List.map_cons]
          simp [htail_eq, t0]
        rw [htake_split, List.mem_cons] at htake_in
        by_cases hmem_tail : t ∈ ((evmChain s).tail.take (i + 1)).map (fun ec => memW s (ec.1 + 136))
        · left
          refine ⟨hmem_tail, ?_⟩
          unfold DelExclusive
          rw [hwtr_post, hwtr_S']
          refine ⟨hdelEx.1, fun j hj k hk heq => ?_⟩
          rw [hmw] at heq
          have hj_s : j + 1 < (evmChain s).length := by omega
          have hget_j : (evmChain s)[j + 1] = ((evmChain s).tail)[j] := by simp [List.getElem_tail]
          obtain ⟨hk136, hjle⟩ := hdelEx.2 (j + 1) hj_s k hk (by rw [hget_j]; exact heq)
          exact ⟨hk136, by omega⟩
        · rcases htake_in with rfl | hmem_t
          · -- `t = t0` and `t0` is NOT in `(ch.tail.take (i + 1)).map (+136)`:
            -- By `hdelEx`, `t0` is `DelExclusive` at `i + 1`, and since `t0` is not in `1..i+1`,
            -- `t0` is `DelExclusive` at `0`! Wait: then `DelExclusive s S (evmChain s) 0 t0` holds,
            -- which contradicts `t0 ∈ S'`!
            have hD0 : DelExclusive s S (evmChain s) 0 t0 := by
              refine ⟨hdelEx.1, fun j hj k hk heq => ?_⟩
              obtain ⟨hk136, hjle⟩ := hdelEx.2 j hj k hk heq
              refine ⟨hk136, ?_⟩
              by_cases hj0 : j = 0
              · omega
              · exfalso; apply hmem_tail
                have hjm1 : j - 1 < i + 1 := by omega
                have hjm1_len : j - 1 < (evmChain s).tail.length := by omega
                have hget : ((evmChain s).tail)[j - 1] = (evmChain s)[j] := by
                  simp [List.getElem_tail, Nat.sub_add_cancel (Nat.pos_of_ne_zero hj0)]
                apply List.mem_map.mpr
                refine ⟨((evmChain s).tail)[j - 1], ?_, ?_⟩
                · rw [List.mem_take_iff_getElem]
                  exact ⟨j - 1, by omega, rfl⟩
                · rw [hget, ← hk136]; exact heq
            rcases hS'_cases with hEq | ⟨hEq, _⟩
            · have ht0_in : t0 ∈ S.filter (· != t0) := by
                have hEq' : S' = S.filter (· != t0) := if_pos hD0
                rw [← hEq']; exact ht'
              exact absurd rfl (bne_iff_ne.mp (List.mem_filter.mp ht0_in).2)
            · rw [hEq] at ht'
              exact absurd rfl (bne_iff_ne.mp (List.mem_filter.mp ht').2)
          · exact absurd hmem_t hmem_tail
      · exact Or.inr hfp_in
  · rw [hwr_post, hfrs_post, hjr_post]
    have hfrs_sub : ∀ a ∈ frameRoleSlots s ((evmChain s).tail), a ∈ frameRoleSlots s (evmChain s) := by
      intro a ha; unfold frameRoleSlots at ha ⊢
      obtain ⟨ec, hec, ha'⟩ := List.mem_flatMap.mp ha
      exact List.mem_flatMap.mpr ⟨ec, htail_sub ec hec, ha'⟩
    have hsl_sub : ∀ a ∈ worldRoleSlots s ++ frameRoleSlots s ((evmChain s).tail),
        a ∈ worldRoleSlots s ++ frameRoleSlots s (evmChain s) := by
      intro a ha
      rcases List.mem_append.mp ha with hwr | hfr
      · exact List.mem_append_left _ hwr
      · exact List.mem_append_right _ (hfrs_sub a hfr)
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨haS, hkl⟩ := hRoles.1 a (by
        rcases List.mem_append.mp ha with hsl | hjr
        · exact List.mem_append_left _ (hsl_sub a hsl)
        · exact List.mem_append_right _ hjr)
      have haS' : a.1 ∈ S' := by
        rcases List.mem_append.mp ha with hsl | hjr
        · rcases List.mem_append.mp hsl with hwr | hfr
          · exact (hW_S'.1.2.2.2.2.2.2.2.2.2.2.2.1 a (List.mem_append_left _ hwr)).1
          · unfold frameRoleSlots at hfr
            obtain ⟨ec, hec, ha'⟩ := List.mem_flatMap.mp hfr
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
            rcases ha' with rfl | rfl | rfl
            · exact hframe_in_S' ec hec 136 (by simp)
            · exact hframe_in_S' ec hec 168 (by simp)
            · exact hframe_in_S' ec hec 176 (by simp)
        · exact (hW_S'.1.2.2.2.2.2.2.2.2.2.2.2.1 a (List.mem_append_right _ hjr)).1
      have hhdr_eq : hdr post a.1 0 = hdr s a.1 0 := by unfold hdr; simp [hmw]
      exact ⟨haS', hhdr_eq.trans hkl⟩
    · have hpw_all := List.pairwise_append.mp hRoles.2.1
      have hpw_frs : (frameRoleSlots s ((evmChain s).tail)).Pairwise
          (fun a b => a.1 = b.1 → a.2 = b.2 ∧ a.2 ∈ sharedRoles) := by
        have hfrs_cons : frameRoleSlots s (evmChain s) =
            frameRoleSlots s [(globN s "ev", globN s "cur_cont")] ++
              frameRoleSlots s ((evmChain s).tail) := by
          unfold frameRoleSlots
          conv_lhs => rw [hcons, List.flatMap_cons]
          simp [htail_eq]
        have hpw2 := hpw_all.2.1
        rw [hfrs_cons] at hpw2
        exact (List.pairwise_append.mp hpw2).2.1
      exact List.pairwise_append.mpr ⟨hpw_all.1, hpw_frs,
        fun a ha b hb => hpw_all.2.2 a ha b (hfrs_sub b hb)⟩
    · intro a ha b hb
      exact hRoles.2.2 a ha b (by
        rcases List.mem_append.mp hb with hsl | hjr
        · exact List.mem_append_left _ (hsl_sub b hsl)
        · exact List.mem_append_right _ hjr)
  · have hsum_le : ((evmChain s).tail.map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum ≤
        ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum := by
      conv_rhs => rw [hcons, List.map_cons, List.sum_cons]
      simp only [htail_eq, hmw]
      omega
    omega

theorem chainLinks_tail (m : Nat → Nat) (a : Ivl) (rest : List Ivl)
    (h : ChainLinks m (a :: rest)) : ChainLinks m rest := by
  match rest, h with
  | [], _ => trivial
  | _ :: _, h => exact h.2

theorem chainLinks_transport (m m' : Nat → Nat) :
    ∀ l : List Ivl, (∀ ec ∈ l, m' (ec.1 + 24) = m (ec.1 + 24) ∧
      m' (ec.1 + 40) = m (ec.1 + 40) ∧ m' (ec.2 + 56) = m (ec.2 + 56)) →
      ChainLinks m l → ChainLinks m' l
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | a :: b :: rest, hm, hl => by
    refine ⟨?_, chainLinks_transport m m' (b :: rest)
      (fun ec hec => hm ec (List.mem_cons_of_mem _ hec)) hl.2⟩
    have ha := hm a List.mem_cons_self
    have hb := hm b (List.mem_cons_of_mem _ List.mem_cons_self)
    rw [hb.1, hb.2.1, ha.2.2]; exact hl.1

theorem headMemChainWF_pop {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hs : HeadMemChainWF s)
    (hk : memW s (globN s "cur_cont" + 16) ≠ 0)
    (hchain : evmChain post = (evmChain s).tail)
    (hmem : ∀ ec ∈ evmChain post, memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
      memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧ memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧
      memW post (ec.2 + 56) = memW s (ec.2 + 56))
    (hev : globN post "ev" = memW s (globN s "cur_cont"))
    (hfmp : globN post "frame_mem_ptr" = memW s (globN s "cur_cont" + 56)) :
    HeadMemChainWF post := by
  obtain ⟨hal, _, hlk⟩ := hs
  have hcs := evmChain_cons_of_cont_ne_zero hk
  have htail : (evmChain s).tail = evmChainFrom s maxChain (memW s (globN s "cur_cont"))
      (memW s (globN s "cur_cont" + 8)) := by rw [hcs]; rfl
  rw [htail] at hchain
  refine ⟨?_, ?_, ?_⟩
  · intro ec hec
    have hm := hmem ec hec
    rw [hchain] at hec
    have := hal ec (by rw [hcs]; exact List.mem_cons_of_mem _ hec)
    rw [hm.2.1, hm.2.2.1]; exact this
  · have hhd : (globN post "ev", globN post "cur_cont") ∈ evmChain post := by
      simp [evmChain, evmChainFrom]
    have hm := hmem _ hhd
    rw [hm.1, hm.2.2.1, hfmp, hev]
    have hmc : maxChain = (maxChain - 1) + 1 := by decide
    rw [hcs, hmc] at hlk
    simp only [evmChainFrom] at hlk
    exact hlk.1
  · rw [hcs] at hlk
    have h1 := chainLinks_tail _ _ _ hlk
    rw [← hchain] at h1
    exact chainLinks_transport (memW s) (memW post) _
      (fun ec hec => ⟨(hmem ec hec).1, (hmem ec hec).2.2.1, (hmem ec hec).2.2.2⟩) h1

structure ReleaseReadyAt {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (cm cmm : Nat) : Prop where
  cm_le : cm ≤ scratchEnd
  cmm_ge : scratchStart ≤ cmm
  cmm_le_cm : cmm ≤ cm
  cm_al : cm % 8 = 0
  cmm_al : cmm % 8 = 0
  frame_scr : ∀ ec ∈ evmChain s, ∀ o ∈ frameScratch s ec, Inside o cm scratchEnd
  frame_mem : ∀ ec ∈ evmChain s, Inside (memW s (ec.1 + 24), memW s (ec.1 + 40)) scratchStart cmm
  frame_logs : ∀ ec ∈ evmChain s,
    Inside (frameLogs s ec) sourceBase (globN s "heap_ptr") ∨ Inside (frameLogs s ec) cm scratchEnd
  frame_msg : ∀ ec ∈ evmChain s,
    Inside (memW s (ec.1 + 112), 176) sourceBase (globN s "heap_ptr") ∨
      Inside (memW s (ec.1 + 112), 176) cm scratchEnd
  htab_in : ∀ t ∈ S, ∀ o ∈ htabFootprint s t,
    Inside o sourceBase (globN s "heap_ptr") ∨ Inside o cm scratchEnd
  fixed_in : ∀ o ∈ fixedObjects s,
    o.2 = 0 ∨ Inside o sourceBase (globN s "heap_ptr") ∨ Inside o cm scratchEnd

theorem releaseReadyAt_of_pop {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S S' : List Nat}
    (hAs : ArenaReady s)
    (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (hne : memW s (globN s "cur_cont" + 16) ≠ 0)
    (hm : post.memory = s.memory)
    (hg : ∀ name : String,
      name ≠ "ev" → name ≠ "cur_cont" → globN post name = globN s name)
    (hch_post : evmChain post = (evmChain s).tail)
    (hS'_sub : ∀ t ∈ S', t ∈ S)
    (hS'_cases : (S' = S ∧ ¬ DelExclusive s S (evmChain s) 0 (memW s (globN s "ev" + 136))) ∨
      (S' = S.filter (· != memW s (globN s "ev" + 136)) ∧
      DelExclusive s S (evmChain s) 0 (memW s (globN s "ev" + 136)))) :
    ReleaseReadyAt post S' (memW s (globN s "cur_cont" + 48))
      (memW s (globN s "cur_cont" + 56)) := by
  have hmw : ∀ a, memW post a = memW s a := fun a => by
    unfold memW
    change (match post.memory (BitVec.ofNat 64 a) with | .word v => v.toNat) =
      (match s.memory (BitVec.ofNat 64 a) with | .word v => v.toNat)
    rw [hm]
  obtain ⟨hW, _, _, _, hFW_all, _, _, _, _, _, hMarks, _, _⟩ := hInv
  have hcons := evmChain_cons_of_cont_ne_zero hne
  have htail_ne : (evmChain s).tail ≠ [] := by
    rw [hcons]
    have hmc : maxChain = (maxChain - 1) + 1 := by decide
    dsimp only [List.tail]; rw [hmc]; simp [evmChainFrom]
  have h01 : 0 + 1 < (evmChain s).length := by
    have hpos : 0 < (evmChain s).tail.length := List.length_pos_of_ne_nil htail_ne
    have hlen_cons : (evmChain s).length = (evmChain s).tail.length + 1 := by
      conv_lhs => rw [hcons]
      conv_rhs => rw [hcons]
      rfl
    omega
  have hch0_eq : (evmChain s)[0]'(by omega) = (globN s "ev", globN s "cur_cont") := by
    simp [hcons]
  have hM0 := hMarks 0 h01
  dsimp only at hM0
  rw [hch0_eq] at hM0
  dsimp only at hM0
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM0
  have he0_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    rw [hcons]; exact List.mem_cons_self
  have hFW0 := hFW_all _ he0_mem
  have he0_scr := (hFW0.1 (globN s "ev", 280) (by simp)).1
  have he0_fmem := hFW0.2.1
  have he0_le_cm : globN s "ev" + 280 ≤ memW s (globN s "cur_cont" + 48) :=
    m6 (globN s "ev", 280) (by simp [frameScratch])
  have hcmm_le_cm : memW s (globN s "cur_cont" + 56) ≤ memW s (globN s "cur_cont" + 48) := by
    have hfmp_le_sc : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hAs.2.2.2.2.1
    have h24_le_fmp : memW s (globN s "ev" + 24) ≤ globN s "frame_mem_ptr" := by
      dsimp only [Inside] at he0_fmem; omega
    have hsc_le_e0 : globN s "scratch_ptr" ≤ globN s "ev" := he0_scr.1
    omega
  have hhp_eq : globN post "heap_ptr" = globN s "heap_ptr" :=
    hg "heap_ptr" (by decide) (by decide)
  have hfs_eq : ∀ ec, frameScratch post ec = frameScratch s ec := by
    intro ec; unfold frameScratch; simp only [hmw]
  have hfl_eq : ∀ ec, frameLogs post ec = frameLogs s ec := by
    intro ec; unfold frameLogs; simp only [hmw]
  have hfp_eq : ∀ t, htabFootprint post t = htabFootprint s t := by
    intro t; unfold htabFootprint hdr; simp only [hmw]
  have hfix_eq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects blockOutObjects balObjects balRecords lstObjects htabValues hdr nodeF
    simp only [hmw, hg "bo" (by decide) (by decide), hg "bal_accounts" (by decide) (by decide),
      hg "journal" (by decide) (by decide), hg "journal_cap" (by decide) (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne_gn : gn.1 ≠ "ev" ∧ gn.1 ≠ "cur_cont" := by revert gn hgn; decide
    rw [hg gn.1 hne_gn.1 hne_gn.2]
  have htail_j : ∀ ec ∈ (evmChain s).tail, ∃ (j : Nat) (hj : j < (evmChain s).length),
      0 < j ∧ (evmChain s)[j] = ec := by
    intro ec hec
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hec
    have hk1 : k + 1 < (evmChain s).length := by
      rw [hcons] at hk ⊢; simp at hk ⊢; omega
    exact ⟨k + 1, hk1, by omega, by simp [List.getElem_tail]⟩
  have hgap : heapLimit ≤ globN s "scratch_ptr" := by
    have h1 := hAs.2.2.2.1
    have h2 := hAs.2.2.2.2.1
    rw [InitECandidate.Solver.Wave8Contracts.M23.heapLimit_val,
        InitECandidate.Solver.Wave8Contracts.M23.scratchStart_val] at *
    omega
  refine ⟨m1, m2, hcmm_le_cm, m3, m4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ec hec o ho
    rw [hch_post] at hec; rw [hfs_eq] at ho
    obtain ⟨j, hj, hj0, rfl⟩ := htail_j ec hec
    exact (m5 j hj hj0).1 o ho
  · intro ec hec
    rw [hch_post] at hec
    obtain ⟨j, hj, hj0, rfl⟩ := htail_j ec hec
    have hfo3 : (frameObjects s (evmChain s)[j])[3]! =
        (memW s ((evmChain s)[j].1 + 24), memW s ((evmChain s)[j].1 + 40)) := by
      simp [frameObjects]
    have hin := (m5 j hj hj0).2.1
    rw [hfo3] at hin
    simpa [hmw] using hin
  · intro ec hec
    rw [hch_post] at hec; rw [hfl_eq, hhp_eq]
    obtain ⟨j, hj, hj0, rfl⟩ := htail_j ec hec
    have hFWj := hFW_all _ (List.getElem_mem hj)
    rcases (m5 j hj hj0).2.2.1 with h_hl | h_cm
    · rcases hFWj.2.2.2.2.2.2.2.2.2.2.2.2.1 with h_hp | h_sc
      · exact Or.inl h_hp
      · exfalso
        have hpos : 0 < (frameLogs s (evmChain s)[j]).2 := by
          unfold frameLogs; dsimp only; have := hFWj.2.2.2.2.2.2.2.2.2.2.1; omega
        dsimp only [Inside] at h_hl h_sc
        omega
    · exact Or.inr h_cm
  · intro ec hec
    rw [hch_post] at hec; rw [hmw, hhp_eq]
    obtain ⟨j, hj, hj0, rfl⟩ := htail_j ec hec
    have hFWj := hFW_all _ (List.getElem_mem hj)
    rcases (m5 j hj hj0).2.2.2 with h_hl | h_cm
    · rcases hFWj.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with h_hp | h_sc
      · exact Or.inl h_hp
      · exfalso
        dsimp only [Inside] at h_hl h_sc
        omega
    · exact Or.inr h_cm
  · intro t ht' o ho
    rw [hfp_eq] at ho; rw [hhp_eq]
    have ht : t ∈ S := hS'_sub t ht'
    have hfp_alloc : Allocated s o := ((hW.1.2.1 t ht).2 o ho).1
    have hpos_o : 0 < o.2 := by
      unfold htabFootprint at ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      have hWFt := (hW.1.2.1 t ht).1
      have hk1 : 1 ≤ hdr s t 0 := hWFt.2.2.1
      have hstr : hdr s t 1 = (hdr s t 0 + 7) / 8 * 8 := hWFt.2.2.2.2.1
      have hstr_pos : 1 ≤ hdr s t 1 := by rw [hstr]; omega
      have hnc : 2 ≤ hdr s t 10 := hWFt.2.2.2.2.2.1
      rcases ho with rfl | rfl | rfl | rfl
      · dsimp only; omega
      · dsimp only; exact Nat.mul_pos (by omega) hstr_pos
      · dsimp only; omega
      · dsimp only; omega
    rcases m8 t ht with ⟨htake, hD0⟩ | hloc
    · exfalso
      have htake0 : ((evmChain s).take 1).map (fun ec => memW s (ec.1 + 136)) =
          [memW s (globN s "ev" + 136)] := by
        rw [hcons]; simp
      rw [htake0, List.mem_singleton] at htake
      subst htake
      rcases hS'_cases with ⟨_, hnD⟩ | ⟨hEq, _⟩
      · exact hnD hD0
      · rw [hEq] at ht'
        exact absurd rfl (bne_iff_ne.mp (List.mem_filter.mp ht').2)
    · rcases hloc o ho with h_hl | h_cm
      · rcases hfp_alloc with h_hp | h_sc
        · exact Or.inl h_hp
        · exfalso
          dsimp only [Inside] at h_hl h_sc
          omega
      · exact Or.inr h_cm
  · intro o ho
    rw [hfix_eq] at ho
    rw [hhp_eq]
    rcases m9 o ho with hz | h_hl | h_cm
    · exact Or.inl hz
    · by_cases hz : o.2 = 0
      · exact Or.inl hz
      · rcases hW.2.2.1.1 o ho with hz' | ⟨hal, _⟩
        · exact Or.inl hz'
        · rcases hal with h_hp | h_sc
          · exact Or.inr (Or.inl h_hp)
          · exfalso
            dsimp only [Inside] at h_hl h_sc
            omega
    · exact Or.inr (Or.inr h_cm)

theorem worldTypedWith_release_marks {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {cm cmm : Nat}
    (hAs : ArenaReady s) (_hAp : ArenaReady post)
    (hWT : InitECandidate.Solver.Wave8Contracts.M23.WorldTypedWith s S Nd)
    (hRel : ReleaseReadyAt s S cm cmm)
    (hm : post.memory = s.memory)
    (hdom : post.memaddrs = s.memaddrs)
    (hbe : post.be = s.be)
    (hsp : globN post "scratch_ptr" = cm)
    (_hfmp : globN post "frame_mem_ptr" = cmm)
    (hg : ∀ name : String,
      ofString name ≠ ofString "scratch_ptr" → ofString name ≠ ofString "frame_mem_ptr" →
      globN post name = globN s name) :
    InitECandidate.Solver.Wave8Contracts.M23.WorldTypedWith post S Nd := by
  have hmw : ∀ a, memW post a = memW s a := fun a => by
    unfold memW
    change (match post.memory (BitVec.ofNat 64 a) with | .word v => v.toNat) =
      (match s.memory (BitVec.ofNat 64 a) with | .word v => v.toNat)
    rw [hm]
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  have hcell : InitECandidate.Solver.Wave8Contracts.M23.SameTypedCells s post S Nd := by
    refine ⟨hbe, hdom, hAs.1.memaddrs, ?_, ?_, ?_⟩
    · intro a _; rw [hm]
    · intro a _ _ _; rw [hm]
    · intro b _ _; unfold memB; rw [hm, hbe]
  have hcg : ∀ g ∈ InitECandidate.Solver.Wave8Contracts.M23.coreWorldGlobals,
      globN post g = globN s g := by
    intro g hg_in
    have hne : ofString g ≠ ofString "scratch_ptr" ∧ ofString g ≠ ofString "frame_mem_ptr" := by
      revert g hg_in; decide
    exact hg g hne.1 hne.2
  have hhp : globN post "heap_ptr" = globN s "heap_ptr" :=
    hg "heap_ptr" (by decide) (by decide)
  have hfp_eq : ∀ t, htabFootprint post t = htabFootprint s t := by
    intro t; unfold htabFootprint hdr; simp only [hmw]
  have hfix_eq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects blockOutObjects balObjects balRecords lstObjects htabValues hdr nodeF
    simp only [hmw, hg "bo" (by decide) (by decide), hg "bal_accounts" (by decide) (by decide),
      hg "journal" (by decide) (by decide), hg "journal_cap" (by decide) (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne_gn : ofString gn.1 ≠ ofString "scratch_ptr" ∧ ofString gn.1 ≠ ofString "frame_mem_ptr" := by
      revert gn hgn; decide
    rw [hg gn.1 hne_gn.1 hne_gn.2]
  have hne_eq := InitECandidate.Solver.Wave8Contracts.M23.nodeExtents_eq hTr.1 hcell
  have hwrs_eq := InitECandidate.Solver.Wave8Contracts.M23.worldRoleSlots_eq hAs.2 hT hF hcell hcg
  have hjrs_eq := InitECandidate.Solver.Wave8Contracts.M23.journalRoleSlots_eq hAs.2 hJ hF hcell hcg
  have hbrec_eq : balRecords post = balRecords s := by
    unfold balRecords hdr nodeF
    simp only [hmw, hg "bal_accounts" (by decide) (by decide)]
  have hhl_gap : heapLimit ≤ globN s "scratch_ptr" := by
    have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
    rw [InitECandidate.Solver.Wave8Contracts.M23.heapLimit_val,
        InitECandidate.Solver.Wave8Contracts.M23.scratchStart_val] at *
    omega
  have halloc_heap : ∀ i : Ivl, 0 < i.2 → Inside i sourceBase heapLimit → Allocated s i →
      Allocated post i := by
    intro i hpos hin hal
    rcases hal with h_hp | h_sc
    · left; rw [hhp]; exact h_hp
    · exfalso; dsimp only [Inside] at hin h_sc; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨hnd, htwf, htpw, hws, hbs, hts, hgr, hbs32, hts32, hbal_ok, hbo_ok, hroles⟩ := hT
    refine ⟨hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      have hW := (htwf t ht).1
      rw [hfp_eq t, hfix_eq]
      refine ⟨InitECandidate.Solver.Wave8Contracts.M23.htabWF_congr hcell ht hW, fun i hi => ?_⟩
      refine ⟨?_, ((htwf t ht).2 i hi).2⟩
      unfold Allocated
      rw [hhp, hsp]
      exact hRel.htab_in t ht i hi
    · intro t ht u hu htu i hi j hj
      rw [hfp_eq t] at hi; rw [hfp_eq u] at hj
      exact htpw t ht u hu htu i hi j hj
    · intro k hk hnz
      rw [hg "ws" (by decide) (by decide)] at hnz ⊢
      rw [hmw]; exact hws k hk hnz
    · intro k hk hnz
      rw [hg "bs" (by decide) (by decide)] at hnz ⊢
      rw [hmw]; exact hbs k hk hnz
    · intro k hk hnz
      rw [hg "ts" (by decide) (by decide)] at hnz ⊢
      rw [hmw]; exact hts k hk hnz
    · intro g hg_mem
      have hne_g : ofString g ≠ ofString "scratch_ptr" ∧ ofString g ≠ ofString "frame_mem_ptr" := by
        revert g hg_mem; decide
      rw [hg g hne_g.1 hne_g.2]; exact hgr g hg_mem
    · intro hnz hmem
      rw [hg "bs" (by decide) (by decide)] at hnz hmem ⊢
      rw [hmw] at hmem ⊢
      exact InitECandidate.Solver.Wave8Contracts.M23.htabValuesIn_congr
        hcell hmem (htwf _ hmem).1 (fun _ h => h) (hbs32 hnz hmem)
    · intro hnz hmem
      rw [hg "ts" (by decide) (by decide)] at hnz hmem ⊢
      rw [hmw] at hmem ⊢
      exact InitECandidate.Solver.Wave8Contracts.M23.htabValuesIn_congr
        hcell hmem (htwf _ hmem).1 (fun _ h => h) (hts32 hnz hmem)
    · rw [hbrec_eq]
      intro ad had
      obtain ⟨c1, c2, c3, c4⟩ := hbal_ok ad had
      simp only [hmw]
      refine ⟨c1, c2, ?_, ?_⟩
      · intro k hk
        have hck := c3 k hk
        unfold LstOK at hck ⊢; simp only [hmw]; exact hck
      · have hv_eq : htabValues post (memW s ad) = htabValues s (memW s ad) := by
          unfold htabValues hdr nodeF; simp only [hmw]
        rw [hv_eq]
        intro l hl
        have hcl := c4 l hl
        unfold LstOK at hcl ⊢; simp only [hmw]; exact hcl
    · rw [hg "bo" (by decide) (by decide)]
      intro hnz k hk hp0
      rw [hmw] at hp0 ⊢
      have hbo := hbo_ok hnz k hk hp0
      unfold LstOK at hbo ⊢; simp only [hmw]; exact hbo
    · unfold RolesOK at hroles ⊢
      rw [hwrs_eq, hjrs_eq]
      refine ⟨fun a ha => ?_, hroles.2⟩
      obtain ⟨haS, hkl⟩ := hroles.1 a ha
      unfold hdr; rw [hmw]; exact ⟨haS, hkl⟩
  · obtain ⟨hj1, hj2, hj3, hj4⟩ := hJ
    unfold JournalTyped
    rw [hg "journal_n" (by decide) (by decide), hg "journal_cap" (by decide) (by decide),
        hg "journal" (by decide) (by decide)]
    refine ⟨hj1, hj2, ?_, fun i hi => by rw [hmw]; exact hj4 i hi⟩
    by_cases hjc0 : globN s "journal_cap" = 0
    · exact Or.inl hjc0
    · rcases hj3 with hz | ⟨_, hw⟩
      · exact Or.inl hz
      · right
        have hj_fix : (globN s "journal", 32 * globN s "journal_cap") ∈ fixedObjects s := by
          unfold fixedObjects
          apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
          simp [hjc0]
        have hal_post : Allocated post (globN s "journal", 32 * globN s "journal_cap") := by
          unfold Allocated; rw [hhp, hsp]
          rcases hRel.fixed_in _ hj_fix with hz | h_hp | h_cm
          · dsimp only at hz; omega
          · exact Or.inl h_hp
          · exact Or.inr h_cm
        exact ⟨hal_post, (R14Shards.OpHandlersA.wordsOK_congr_dom hdom).mpr hw⟩
  · unfold FixedTyped
    rw [hfix_eq]
    refine ⟨fun i hi => ?_, hF.2⟩
    rcases hF.1 i hi with h0 | ⟨_, hw⟩
    · exact Or.inl h0
    · rcases hRel.fixed_in i hi with h0 | h_hp | h_cm
      · exact Or.inl h0
      · exact Or.inr ⟨Or.inl (by rw [hhp]; exact h_hp),
          (R14Shards.OpHandlersA.wordsOK_congr_dom hdom).mpr hw⟩
      · exact Or.inr ⟨Or.inr (by rw [hsp]; exact h_cm),
          (R14Shards.OpHandlersA.wordsOK_congr_dom hdom).mpr hw⟩
  · obtain ⟨hNH, hndisj, hws_tr⟩ := hTr
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨fun n hn => ?_, fun n hn m hm hne => ?_⟩
      · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hNH.1 n hn
        have hni : nodeIvl post n = nodeIvl s n := by unfold nodeIvl; simp [hmw]
        have hns_pos : 0 < (nodeIvl s n).2 := by
          unfold nodeIvl nodeSize; dsimp only; split <;> [omega; split <;> [omega; split <;> omega]]
        rw [hmw, hni]
        refine ⟨h1, halloc_heap _ hns_pos h3 h2, h3,
          (R14Shards.OpHandlersA.wordsOK_congr_dom hdom).mpr h4,
          fun hk2 => by rw [hmw]; exact h5 hk2,
          fun hk3 i hi => by rw [hmw]; exact h6 hk3 i hi,
          fun h12 => ?_,
          by rw [hmw]; exact h8,
          fun hk1 => by rw [hmw]; exact h9 hk1,
          fun hk3 => by rw [hmw]; exact h10 hk3⟩
        rw [hmw, hmw]
        by_cases hlen0 : memW s (n + 40) = 0
        · exact Or.inl hlen0
        · rcases h7 h12 with hz | ⟨hnib, hal, hin, hdisj⟩
          · exact Or.inl hz
          · right
            have hnib' : NibblesOK post (memW s (n + 32)) (memW s (n + 40)) := by
              unfold NibblesOK at hnib ⊢; intro k hk; unfold memB at hnib ⊢; rw [hm, hbe]; exact hnib k hk
            refine ⟨hnib', halloc_heap _ (Nat.pos_of_ne_zero hlen0) hin hal, hin, fun m hm => ?_⟩
            have hni_m : nodeIvl post m = nodeIvl s m := by unfold nodeIvl; simp [hmw]
            rw [hni_m]; exact hdisj m hm
      · have hni_n : nodeIvl post n = nodeIvl s n := by unfold nodeIvl; simp [hmw]
        have hni_m : nodeIvl post m = nodeIvl s m := by unfold nodeIvl; simp [hmw]
        rw [hni_n, hni_m]; exact hNH.2 n hn m hm hne
    · rw [hne_eq, hfix_eq]
      intro o ho
      exact ⟨fun t ht i hi => by rw [hfp_eq t] at hi; exact (hndisj o ho).1 t ht i hi,
        (hndisj o ho).2⟩
    · rw [hg "ws" (by decide) (by decide)]
      intro hws_nz
      unfold hdr nodeF
      simp only [hmw]
      exact hws_tr hws_nz

theorem evmInvAt_of_release_marks {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S : List Nat} {cm cmm : Nat}
    (hAs : ArenaReady s)
    (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (hRel : ReleaseReadyAt s S cm cmm)
    (hAp_guest : GuestInv post)
    (hm : post.memory = s.memory)
    (hdom : post.memaddrs = s.memaddrs)
    (hbe : post.be = s.be)
    (hsp : globN post "scratch_ptr" = cm)
    (hfmp : globN post "frame_mem_ptr" = cmm)
    (hg : ∀ name : String,
      ofString name ≠ ofString "scratch_ptr" → ofString name ≠ ofString "frame_mem_ptr" →
      globN post name = globN s name)
    (hGW : GlobalsWord post) :
    ArenaReady post ∧
    InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt post S ∧
    evmChain post = evmChain s ∧
    OpDispatchSpec.evmR post = OpDispatchSpec.evmR s := by
  have hmw : ∀ a, memW post a = memW s a := fun a => by
    unfold memW
    change (match post.memory (BitVec.ofNat 64 a) with | .word v => v.toNat) =
      (match s.memory (BitVec.ofNat 64 a) with | .word v => v.toNat)
    rw [hm]
  have hhp : globN post "heap_ptr" = globN s "heap_ptr" :=
    hg "heap_ptr" (by decide) (by decide)
  have hAp : ArenaReady post := by
    refine ⟨hAp_guest, ?_⟩
    unfold ArenaOK
    rw [hhp, hfmp, hsp]
    exact ⟨hAs.2.1, hAs.2.2.1, hRel.cmm_ge, hRel.cmm_le_cm, hRel.cm_le,
      hAs.2.2.2.2.2.2.1, hRel.cmm_al, hRel.cm_al, hGW⟩
  obtain ⟨hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, hAT, hMarks, hRoles, hGas⟩ := hInv
  have hch_eq : evmChain post = evmChain s := by
    have hev := hg "ev" (by decide) (by decide)
    have hcc := hg "cur_cont" (by decide) (by decide)
    unfold evmChain
    rw [hev, hcc]
    have hfrom : ∀ fuel e c, evmChainFrom post fuel e c = evmChainFrom s fuel e c := by
      intro fuel; induction fuel with
      | zero => simp [evmChainFrom]
      | succ f ih =>
        intro e c; simp only [evmChainFrom, hmw]
        split
        · rfl
        · rw [ih]
    exact hfrom _ _ _
  have hR_eq : OpDispatchSpec.evmR post = OpDispatchSpec.evmR s :=
    R14Shards.OpHandlersA.evmR_eq_of_chain_and_words hch_eq
      (fun _ _ => ⟨hmw _, hmw _⟩)
  obtain ⟨Nd_w, hTr_w⟩ := hW.2.2.2
  have hWT_w := worldTypedWith_release_marks hAs hAp ⟨hW.1, hW.2.1, hW.2.2.1, hTr_w⟩
    hRel hm hdom hbe hsp hfmp hg
  have hW_post : WorldTyped post S :=
    ⟨hWT_w.1, hWT_w.2.1, hWT_w.2.2.1, Nd_w, hWT_w.2.2.2⟩
  have hfo_eq : ∀ ec, frameObjects post ec = frameObjects s ec := by
    intro ec
    unfold frameObjects frameLogs frameRet frameLogObjects logOwnedIvls logRecordIvls
    simp only [hmw, hg "vm_system_address" (by decide) (by decide)]
  have hfs_eq : ∀ ec, frameScratch post ec = frameScratch s ec := by
    intro ec; unfold frameScratch; simp only [hmw]
  have hfl_eq : ∀ ec, frameLogs post ec = frameLogs s ec := by
    intro ec; unfold frameLogs; simp only [hmw]
  have hfr_eq : ∀ ec, frameRet post ec = frameRet s ec := by
    intro ec; unfold frameRet; simp only [hmw]
  have hfp_eq : ∀ t, htabFootprint post t = htabFootprint s t := by
    intro t; unfold htabFootprint hdr; simp only [hmw]
  have hfix_eq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects blockOutObjects balObjects balRecords lstObjects htabValues hdr nodeF
    simp only [hmw, hg "bo" (by decide) (by decide), hg "bal_accounts" (by decide) (by decide),
      hg "journal" (by decide) (by decide), hg "journal_cap" (by decide) (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne_gn : ofString gn.1 ≠ ofString "scratch_ptr" ∧ ofString gn.1 ≠ ofString "frame_mem_ptr" := by
      revert gn hgn; decide
    rw [hg gn.1 hne_gn.1 hne_gn.2]
  refine ⟨hAp, ⟨hW_post, ?_⟩, hch_eq, hR_eq⟩
  dsimp only
  rw [hch_eq]
  refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨ec, hec, hk0⟩ := hch_last
    exact ⟨ec, hec, by rw [hmw]; exact hk0⟩
  · intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17⟩ := hFW
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      simp only [hmw] at hi
      have hfs_mem : i ∈ frameScratch s ec := by simpa [frameScratch] using hi
      rw [hsp]
      exact ⟨hRel.frame_scr ec hec i hfs_mem,
        (R14Shards.OpHandlersA.wordsOK_congr_dom hdom).mpr (f1 i hi).2⟩
    · rw [hmw, hmw, hfmp]; exact hRel.frame_mem ec hec
    · rw [hmw, hmw]; exact (R14Shards.OpHandlersA.wordsOK_congr_dom hdom).mpr f3
    · rw [hmw]; exact f4
    · rw [hmw, hmw]; exact f5
    · rw [hmw]; exact f6
    · rw [hmw, hmw]; exact f7
    · rw [hmw]; exact f8
    · rw [hmw]; exact f9
    · rw [hmw]; exact f10
    · simp only [hmw]; exact f11
    · simp only [hmw]; exact f12
    · rw [hfl_eq, hhp, hsp]; exact hRel.frame_logs ec hec
    · rw [hfl_eq]; exact (R14Shards.OpHandlersA.wordsOK_congr_dom hdom).mpr f14
    · rw [hmw, hmw, hg "evm_empty" (by decide) (by decide), hfr_eq, hhp]
      rcases f15 with h0 | ⟨hin, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hin, (R14Shards.OpHandlersA.wordsOK_congr_dom hdom).mpr hw⟩
    · rw [hmw]
      rcases f16 with hz | ⟨lw, lal, lcnt, lcap, lent⟩
      · exact Or.inl hz
      · right
        have hl_scr : (memW s (ec.1 + 88), 24) ∈ frameScratch s ec := by simp [frameScratch]
        have hl_al : Allocated post (memW s (ec.1 + 88), 24) := by
          right; rw [hsp]; exact hRel.frame_scr ec hec _ hl_scr
        refine ⟨(R14Shards.OpHandlersA.wordsOK_congr_dom hdom).mpr lw, hl_al,
          by rw [hmw]; exact lcnt, by rw [hmw, hmw]; exact lcap, ?_⟩
        intro idx hidx; rw [hmw] at hidx
        obtain ⟨hwa, hle⟩ := lent idx hidx
        rw [hmw]
        refine ⟨(R14Shards.OpHandlersA.wordAt_congr_dom hdom).mpr hwa, ?_⟩
        unfold LogEntryOK at hle ⊢
        simp only [hmw, hhp]
        exact ⟨(R14Shards.OpHandlersA.wordsOK_congr_dom hdom).mpr hle.1, hle.2⟩
    · rw [hmw]
      obtain ⟨_, mw, mht, mfx, mfo, Nd_m, hTr_m, mdj_m⟩ := f17
      have hWT_m := worldTypedWith_release_marks hAs hAp ⟨hW.1, hW.2.1, hW.2.2.1, hTr_m⟩
        hRel hm hdom hbe hsp hfmp hg
      have hm_al : Allocated post (memW s (ec.1 + 112), 176) := by
        unfold Allocated; rw [hhp, hsp]; exact hRel.frame_msg ec hec
      refine ⟨hm_al, (R14Shards.OpHandlersA.wordsOK_congr_dom hdom).mpr mw,
        fun t ht i hi => by rw [hfp_eq t] at hi; exact mht t ht i hi,
        fun j hj => by rw [hfix_eq] at hj; exact mfx j hj,
        fun ec' hec' o ho => by rw [hch_eq] at hec'; rw [hfo_eq] at ho; exact mfo ec' hec' o ho,
        Nd_m, hWT_m.2.2.2, fun o ho j hj => ?_⟩
      have hne_m : nodeExtents post Nd_m = nodeExtents s Nd_m := by
        unfold nodeExtents nodeIvl nodePath; simp only [hmw]
      rw [hne_m] at hj
      exact mdj_m o ho j hj
  · intro ec hec; unfold FrameRoom; simp only [hmw]; exact hFR_all ec hec
  · intro i hi; simp only [hmw]; exact hRW i hi
  · have hmap_eq : (evmChain s).map (frameObjects post) = (evmChain s).map (frameObjects s) := by
      apply List.map_congr_left; intro ec _; exact hfo_eq ec
    rw [hmap_eq]; exact hFO_pw
  · intro ec hec o ho
    rw [hfo_eq] at ho; rw [hfix_eq]
    exact ⟨fun t ht i hi => by rw [hfp_eq t] at hi; exact (hFO_disj ec hec o ho).1 t ht i hi,
      (hFO_disj ec hec o ho).2⟩
  · obtain ⟨Nd_a, hTr_a, hdj_a⟩ := hAT
    have hWT_a := worldTypedWith_release_marks hAs hAp ⟨hW.1, hW.2.1, hW.2.2.1, hTr_a⟩
      hRel hm hdom hbe hsp hfmp hg
    have hmap_eq : (evmChain s).map (frameObjects post) = (evmChain s).map (frameObjects s) := by
      apply List.map_congr_left; intro ec _; exact hfo_eq ec
    have hne_a : nodeExtents post Nd_a = nodeExtents s Nd_a := by
      unfold nodeExtents nodeIvl nodePath; simp only [hmw]
    rw [hmap_eq]
    refine ⟨Nd_a, hWT_a.2.2.2, fun o ho j hj => ?_⟩
    rw [hne_a] at hj; exact hdj_a o ho j hj
  · have hwtr_eq : worldTableRefs post S = worldTableRefs s S := by
      unfold worldTableRefs recordSlots balRecords htabValues hdr nodeF
      simp only [hmw, hg "ws" (by decide) (by decide), hg "bs" (by decide) (by decide),
        hg "ts" (by decide) (by decide), hg "bal_accounts" (by decide) (by decide),
        hg "journal_n" (by decide) (by decide), hg "journal" (by decide) (by decide)]
      have hgtr : globalTableRoots.map (globN post) = globalTableRoots.map (globN s) := by
        apply List.map_congr_left; intro g hg_in
        have hne : ofString g ≠ ofString "scratch_ptr" ∧ ofString g ≠ ofString "frame_mem_ptr" := by
          revert g hg_in; decide
        exact hg g hne.1 hne.2
      rw [hgtr]
    intro i hi
    have hM := hMarks i hi
    dsimp only at hM ⊢
    simp only [hmw, hfs_eq, hfo_eq, hfl_eq, hfp_eq, hfix_eq]
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
    refine ⟨m1, m2, m3, m4, m5, m6, m7, fun t ht => ?_, m9⟩
    have hdel_iff : DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
      unfold DelExclusive; rw [hwtr_eq]; simp only [hmw]
    rw [hdel_iff]; exact m8 t ht
  · have hcell_w : InitECandidate.Solver.Wave8Contracts.M23.SameTypedCells s post S Nd_w := by
      refine ⟨hbe, hdom, hAs.1.memaddrs, ?_, ?_, ?_⟩
      · intro a _; rw [hm]
      · intro a _ _ _; rw [hm]
      · intro b _ _; unfold memB; rw [hm, hbe]
    have hcg : ∀ g ∈ InitECandidate.Solver.Wave8Contracts.M23.coreWorldGlobals,
        globN post g = globN s g := by
      intro g hg_in
      have hne : ofString g ≠ ofString "scratch_ptr" ∧ ofString g ≠ ofString "frame_mem_ptr" := by
        revert g hg_in; decide
      exact hg g hne.1 hne.2
    have hwrs_eq := InitECandidate.Solver.Wave8Contracts.M23.worldRoleSlots_eq hAs.2 hW.1 hW.2.2.1 hcell_w hcg
    have hjrs_eq := InitECandidate.Solver.Wave8Contracts.M23.journalRoleSlots_eq hAs.2 hW.2.1 hW.2.2.1 hcell_w hcg
    have hfrs_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
      unfold frameRoleSlots; simp only [hmw]
    rw [hwrs_eq, hfrs_eq, hjrs_eq]
    unfold RolesOK at hRoles ⊢
    refine ⟨fun a ha => ?_, hRoles.2⟩
    obtain ⟨haS, hkl⟩ := hRoles.1 a ha
    unfold hdr; rw [hmw]; exact ⟨haS, hkl⟩
  · simp only [hmw]; exact hGas

theorem releaseReadyAt_lc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (ck : Nat) (S : List Nat) (cm cmm : Nat) :
    ReleaseReadyAt { s with locals := L, clock := ck } S cm cmm ↔
      ReleaseReadyAt s S cm cmm := by
  have hm : ({ s with locals := L, clock := ck } : PanSemStateFiniteExact 64 F).memory = s.memory := rfl
  have hg : ({ s with locals := L, clock := ck } : PanSemStateFiniteExact 64 F).globals = s.globals := rfl
  have hmw : ∀ a, memW { s with locals := L, clock := ck } a = memW s a := fun a => by
    unfold memW; dsimp only
  have hgn : ∀ k, globN { s with locals := L, clock := ck } k = globN s k := fun k => by
    unfold globN; dsimp only
  have hch : evmChain { s with locals := L, clock := ck } = evmChain s :=
    OpDispatchSpec.evmChain_congr hm hg
  have hfs : ∀ ec, frameScratch { s with locals := L, clock := ck } ec = frameScratch s ec := fun ec => by
    unfold frameScratch; simp only [hmw]
  have hfl : ∀ ec, frameLogs { s with locals := L, clock := ck } ec = frameLogs s ec := fun ec => by
    unfold frameLogs; simp only [hmw]
  have hfp : ∀ t, htabFootprint { s with locals := L, clock := ck } t = htabFootprint s t := fun t => by
    unfold htabFootprint hdr; simp only [hmw]
  have hfix : fixedObjects { s with locals := L, clock := ck } = fixedObjects s := by
    unfold fixedObjects blockOutObjects balObjects balRecords lstObjects htabValues hdr nodeF
    simp only [hmw, hgn]
  constructor
  · intro h
    refine ⟨h.cm_le, h.cmm_ge, h.cmm_le_cm, h.cm_al, h.cmm_al, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ec hec o ho
      exact h.frame_scr ec (by rwa [hch]) o (by rwa [hfs])
    · intro ec hec
      simpa only [hmw] using h.frame_mem ec (by rwa [hch])
    · intro ec hec
      simpa only [hfl, hgn] using h.frame_logs ec (by rwa [hch])
    · intro ec hec
      simpa only [hmw, hgn] using h.frame_msg ec (by rwa [hch])
    · intro t ht o ho
      simpa only [hgn] using h.htab_in t ht o (by rwa [hfp])
    · intro o ho
      simpa only [hgn] using h.fixed_in o (by rwa [hfix])
  · intro h
    refine ⟨h.cm_le, h.cmm_ge, h.cmm_le_cm, h.cm_al, h.cmm_al, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ec hec o ho
      exact h.frame_scr ec (by rwa [← hch]) o (by rwa [← hfs])
    · intro ec hec
      simpa only [hmw] using h.frame_mem ec (by rwa [← hch])
    · intro ec hec
      simpa only [hfl, hgn] using h.frame_logs ec (by rwa [← hch])
    · intro ec hec
      simpa only [hmw, hgn] using h.frame_msg ec (by rwa [← hch])
    · intro t ht o ho
      simpa only [hgn] using h.htab_in t ht o (by rwa [← hfp])
    · intro o ho
      simpa only [hgn] using h.fixed_in o (by rwa [← hfix])

theorem releaseReadyAt_transport {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S : List Nat} {cm cmm : Nat}
    (hRel : ReleaseReadyAt s S cm cmm)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hch : evmChain post = evmChain s)
    (hfs : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec)
    (hmem24_40 : ∀ ec ∈ evmChain s,
      memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧ memW post (ec.1 + 40) = memW s (ec.1 + 40))
    (hlogs : ∀ ec ∈ evmChain s,
      frameLogs post ec = frameLogs s ec ∨ Inside (frameLogs post ec) sourceBase (globN post "heap_ptr"))
    (h112 : ∀ ec ∈ evmChain s, memW post (ec.1 + 112) = memW s (ec.1 + 112))
    (hhtab : ∀ t ∈ S, htabFootprint post t = htabFootprint s t ∨
      ∀ o ∈ htabFootprint post t,
        (∃ j ∈ htabFootprint s t, Inside o j.1 (j.1 + j.2)) ∨
          Inside o sourceBase (globN post "heap_ptr"))
    (hfix : fixedObjects post = fixedObjects s) :
    ReleaseReadyAt post S cm cmm := by
  refine ⟨hRel.cm_le, hRel.cmm_ge, hRel.cmm_le_cm, hRel.cm_al, hRel.cmm_al,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ec hec o ho
    rw [hch] at hec; rw [hfs ec hec] at ho
    exact hRel.frame_scr ec hec o ho
  · intro ec hec
    rw [hch] at hec
    rw [(hmem24_40 ec hec).1, (hmem24_40 ec hec).2]
    exact hRel.frame_mem ec hec
  · intro ec hec
    rw [hch] at hec
    rcases hlogs ec hec with hfl_eq | hin_post
    · rw [hfl_eq]
      rcases hRel.frame_logs ec hec with ⟨h1, h2⟩ | hscr
      · exact Or.inl ⟨h1, le_trans h2 hhp⟩
      · exact Or.inr hscr
    · exact Or.inl hin_post
  · intro ec hec
    rw [hch] at hec; rw [h112 ec hec]
    rcases hRel.frame_msg ec hec with ⟨h1, h2⟩ | hscr
    · exact Or.inl ⟨h1, le_trans h2 hhp⟩
    · exact Or.inr hscr
  · intro t ht o ho
    rcases hhtab t ht with hfp_eq | hgrow
    · rw [hfp_eq] at ho
      rcases hRel.htab_in t ht o ho with ⟨h1, h2⟩ | hscr
      · exact Or.inl ⟨h1, le_trans h2 hhp⟩
      · exact Or.inr hscr
    · rcases hgrow o ho with ⟨j, hj, hin_j⟩ | hin_hp
      · rcases hRel.htab_in t ht j hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨le_trans h1 hin_j.1, le_trans hin_j.2 (le_trans h2 hhp)⟩
        · exact Or.inr ⟨le_trans h1 hin_j.1, le_trans hin_j.2 h2⟩
      · exact Or.inl hin_hp
  · intro o ho
    rw [hfix] at ho
    rcases hRel.fixed_in o ho with h0 | ⟨h1, h2⟩ | hscr
    · exact Or.inl h0
    · exact Or.inr (Or.inl ⟨h1, le_trans h2 hhp⟩)
    · exact Or.inr (Or.inr hscr)

theorem lookup_scratch_release :
    originalRuntimeCode.lookup (ofString "scratch_release") =
      some ([(ofString "m", .one)], sourceFnBody Guest.Software.guestFn_scratch_release, .one) :=
  lookup_of_guestAst_getElem 15 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_scratch_release) rfl

theorem lookup_frame_mem_release :
    originalRuntimeCode.lookup (ofString "frame_mem_release") =
      some ([(ofString "m", .one)], sourceFnBody Guest.Software.guestFn_frame_mem_release, .one) :=
  lookup_of_guestAst_getElem 12 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_frame_mem_release) rfl

theorem scratch_release_call_exact {F : Type}
    (st : PanSemStateFiniteExact 64 F) (mExp : ExpHOL 64) (mw : BitVec 64)
    (hcode : st.code = originalRuntimeCode)
    (hm : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) mExp =
      some (.val (.word mw)))
    (hsp_ex : ∃ spw : BitVec 64, st.globals.lookup (ofString "scratch_ptr") = some (.val (.word spw))) :
    st.clock = 0 ∨
    ∃ ck, evaluateHOLFiniteState st (.call (some (none, none)) (ofString "scratch_release") [mExp]) =
      (none, { st with
        globals := st.globals.update (ofString "scratch_ptr", .val (.word mw))
        clock := ck }) := by
  by_cases hz : st.clock = 0
  · exact Or.inl hz
  · right
    obtain ⟨spw, hsp⟩ := hsp_ex
    rw [evaluateHOLFiniteState_call]
    have hargs : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a)) [mExp] =
        some [.val (.word mw)] := by
      simp [evalListHOLFinite, evalListHOLExact, hm]
    have hl := pan_one_word_lookup st.code.lookup (ofString "scratch_release") (ofString "m")
      (sourceFnBody Guest.Software.guestFn_scratch_release) mw (by rw [hcode]; exact lookup_scratch_release)
    rw [hargs]; dsimp only; rw [hl]; dsimp only; rw [if_neg hz]
    let entry := callEntryStateHOLFinite st (HolFiniteMapExact.empty.update (ofString "m", .val (.word mw)))
    have hb : sourceFnBody Guest.Software.guestFn_scratch_release =
        .seq (.assign .global (ofString "scratch_ptr") (.var .local (ofString "m"))) (.return (.const 0)) := rfl
    have hev_b : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_scratch_release) =
        (some (.returned (.val (.word 0))),
          emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word mw)) entry)) := by
      rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
      have hm_ent : entry.locals.lookup (ofString "m") = some (.val (.word mw)) := by
        simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hsp_ent : entry.globals.lookup (ofString "scratch_ptr") = some (.val (.word spw)) := hsp
      simp [evalHOLExact, hm_ent, isValidValueHOLFinite, lookupKvarHOLFinite,
        hsp_ent, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
        evaluateHOLFiniteState_return]
    have hev_b' : evaluateHOLFiniteState
        (callEntryStateHOLFinite st (HolFiniteMapExact.empty.update (ofString "m", .val (.word mw))))
        (sourceFnBody Guest.Software.guestFn_scratch_release) =
        (some (.returned (.val (.word 0))),
          emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word mw)) entry)) := hev_b
    rw [hev_b']; dsimp only
    have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hsh]
    exact ⟨st.clock - 1, rfl⟩

theorem frame_mem_release_call_exact {F : Type}
    (st : PanSemStateFiniteExact 64 F) (mExp : ExpHOL 64) (mw : BitVec 64)
    (hcode : st.code = originalRuntimeCode)
    (hm : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) mExp =
      some (.val (.word mw)))
    (hfmp_ex : ∃ fmpw : BitVec 64, st.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fmpw))) :
    st.clock = 0 ∨
    ∃ ck, evaluateHOLFiniteState st (.call (some (none, none)) (ofString "frame_mem_release") [mExp]) =
      (none, { st with
        globals := st.globals.update (ofString "frame_mem_ptr", .val (.word mw))
        clock := ck }) := by
  by_cases hz : st.clock = 0
  · exact Or.inl hz
  · right
    obtain ⟨fmpw, hfmp⟩ := hfmp_ex
    rw [evaluateHOLFiniteState_call]
    have hargs : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a)) [mExp] =
        some [.val (.word mw)] := by
      simp [evalListHOLFinite, evalListHOLExact, hm]
    have hl := pan_one_word_lookup st.code.lookup (ofString "frame_mem_release") (ofString "m")
      (sourceFnBody Guest.Software.guestFn_frame_mem_release) mw (by rw [hcode]; exact lookup_frame_mem_release)
    rw [hargs]; dsimp only; rw [hl]; dsimp only; rw [if_neg hz]
    let entry := callEntryStateHOLFinite st (HolFiniteMapExact.empty.update (ofString "m", .val (.word mw)))
    have hb : sourceFnBody Guest.Software.guestFn_frame_mem_release =
        .seq (.assign .global (ofString "frame_mem_ptr") (.var .local (ofString "m"))) (.return (.const 0)) := rfl
    have hev_b : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_frame_mem_release) =
        (some (.returned (.val (.word 0))),
          emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "frame_mem_ptr") (.val (.word mw)) entry)) := by
      rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
      have hm_ent : entry.locals.lookup (ofString "m") = some (.val (.word mw)) := by
        simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hfmp_ent : entry.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fmpw)) := hfmp
      simp [evalHOLExact, hm_ent, isValidValueHOLFinite, lookupKvarHOLFinite,
        hfmp_ent, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
        evaluateHOLFiniteState_return]
    have hev_b' : evaluateHOLFiniteState
        (callEntryStateHOLFinite st (HolFiniteMapExact.empty.update (ofString "m", .val (.word mw))))
        (sourceFnBody Guest.Software.guestFn_frame_mem_release) =
        (some (.returned (.val (.word 0))),
          emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "frame_mem_ptr") (.val (.word mw)) entry)) := hev_b
    rw [hev_b']; dsimp only
    have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hsh]
    exact ⟨st.clock - 1, rfl⟩

theorem release_pair_step {F : Type}
    (st : PanSemStateFiniteExact 64 F) (cmExp cmmExp : ExpHOL 64)
    (cmw cmmw : BitVec 64) {S : List Nat} {cont : ProgHOL 64}
    (hAs : ArenaReady st)
    (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt st S)
    (hRel : ReleaseReadyAt st S cmw.toNat cmmw.toNat)
    (hcm : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) cmExp =
      some (.val (.word cmw)))
    (hcmm : ∀ g' ck', @evalHOLExact 64 F _
      ({ st with globals := g', clock := ck' } : PanSemStateFiniteExact 64 F).toExact
      (fun a => Classical.propDecidable (st.memaddrs a)) cmmExp = some (.val (.word cmmw)))
    (hnt : (evaluateHOLFiniteState st
      (.seq (.call (some (none, none)) (ofString "scratch_release") [cmExp])
        (.seq (.call (some (none, none)) (ofString "frame_mem_release") [cmmExp]) cont))).1 ≠ some .timeOut) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState st
        (.seq (.call (some (none, none)) (ofString "scratch_release") [cmExp])
          (.seq (.call (some (none, none)) (ofString "frame_mem_release") [cmmExp]) cont)) =
        evaluateHOLFiniteState mid cont ∧
      mid.locals = st.locals ∧
      mid.memory = st.memory ∧
      mid.memaddrs = st.memaddrs ∧
      mid.be = st.be ∧
      globN mid "scratch_ptr" = cmw.toNat ∧
      globN mid "frame_mem_ptr" = cmmw.toNat ∧
      (∀ k : MlS,
        k ≠ ofString "scratch_ptr" → k ≠ ofString "frame_mem_ptr" →
        mid.globals.lookup k = st.globals.lookup k) ∧
      ArenaReady mid ∧
      InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt mid S ∧
      evmChain mid = evmChain st ∧
      OpDispatchSpec.evmR mid = OpDispatchSpec.evmR st ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut := by
  obtain ⟨_, fp_w, sp_w, _, _, hfp_lk, _, hsp_lk, _⟩ :=
    InitECandidate.Solver.Wave8Contracts.M26.arenaOK_globals st hAs.2
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases scratch_release_call_exact st cmExp cmw hAs.1.code hcm ⟨sp_w, hsp_lk⟩ with hz1 | ⟨ck1, hsr⟩
  · exfalso
    rw [evaluateHOLFiniteState_call] at hnt
    have hargs : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a)) [cmExp] =
        some [.val (.word cmw)] := by simp [evalListHOLFinite, evalListHOLExact, hcm]
    have hl := pan_one_word_lookup st.code.lookup (ofString "scratch_release") (ofString "m")
      (sourceFnBody Guest.Software.guestFn_scratch_release) cmw (by rw [hAs.1.code]; exact lookup_scratch_release)
    rw [hargs] at hnt; dsimp only at hnt; rw [hl] at hnt; dsimp only at hnt
    rw [if_pos hz1] at hnt; exact hnt rfl
  · rw [hsr] at hnt ⊢; dsimp only at hnt ⊢
    set st1 : PanSemStateFiniteExact 64 F :=
      { st with globals := st.globals.update (ofString "scratch_ptr", .val (.word cmw)), clock := ck1 }
    have hfp_lk1 : st1.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fp_w)) := by
      simp [st1, HolFiniteMapExact.lookup_update, FUPDATE, hfp_lk,
        show ofString "scratch_ptr" ≠ ofString "frame_mem_ptr" by decide]
    have hcmm1 : @evalHOLExact 64 F _ st1.toExact (fun a => Classical.propDecidable (st1.memaddrs a)) cmmExp =
        some (.val (.word cmmw)) := hcmm _ _
    rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
    rcases frame_mem_release_call_exact st1 cmmExp cmmw hAs.1.code hcmm1 ⟨fp_w, hfp_lk1⟩ with hz2 | ⟨ck2, hfmr⟩
    · exfalso
      rw [evaluateHOLFiniteState_call] at hnt
      have hargs : evalListHOLFinite st1 (h := fun a => Classical.propDecidable (st1.memaddrs a)) [cmmExp] =
          some [.val (.word cmmw)] := by simp [evalListHOLFinite, evalListHOLExact, hcmm1]
      have hl := pan_one_word_lookup st1.code.lookup (ofString "frame_mem_release") (ofString "m")
        (sourceFnBody Guest.Software.guestFn_frame_mem_release) cmmw (by rw [hAs.1.code]; exact lookup_frame_mem_release)
      rw [hargs] at hnt; dsimp only at hnt; rw [hl] at hnt; dsimp only at hnt
      rw [if_pos hz2] at hnt; exact hnt rfl
    · rw [hfmr] at hnt ⊢; dsimp only at hnt ⊢
      let mid : PanSemStateFiniteExact 64 F :=
        { st1 with globals := st1.globals.update (ofString "frame_mem_ptr", .val (.word cmmw)), clock := ck2 }
      have hGp : GuestInv mid := guestInv_congr (s := st) rfl rfl rfl rfl hAs.1
      have hsp_mid : globN mid "scratch_ptr" = cmw.toNat := by
        simp [mid, st1, globN, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "frame_mem_ptr" ≠ ofString "scratch_ptr" by decide]
      have hfmp_mid : globN mid "frame_mem_ptr" = cmmw.toNat := by
        simp [mid, globN, HolFiniteMapExact.lookup_update, FUPDATE]
      have hg_kept : ∀ k : MlS,
          k ≠ ofString "scratch_ptr" → k ≠ ofString "frame_mem_ptr" →
          mid.globals.lookup k = st.globals.lookup k := by
        intro k h1 h2
        simp [mid, st1, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm h2, Ne.symm h1]
      have hg_mid : ∀ name : String,
          ofString name ≠ ofString "scratch_ptr" → ofString name ≠ ofString "frame_mem_ptr" →
          globN mid name = globN st name := by
        intro name h1 h2
        unfold globN; rw [hg_kept (ofString name) h1 h2]
      have hGW1 : GlobalsWord st1 :=
        globalsWord_update (ofString "scratch_ptr") cmw rfl hAs.2.2.2.2.2.2.2.2.2
      have hGW2 : GlobalsWord mid :=
        globalsWord_update (ofString "frame_mem_ptr") cmmw rfl hGW1
      obtain ⟨hAmid, hInvmid, hchmid, hRmid⟩ :=
        evmInvAt_of_release_marks hAs hInv hRel hGp rfl rfl rfl hsp_mid hfmp_mid hg_mid hGW2
      exact ⟨mid, rfl, rfl, rfl, rfl, rfl, hsp_mid, hfmp_mid, hg_kept, hAmid, hInvmid, hchmid, hRmid, hnt⟩

def ChainCellsAgree {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ ec ∈ evmChain s,
    memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
    memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧
    memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧
    memW post (ec.2 + 56) = memW s (ec.2 + 56)

structure CreateFinishSpecs : Prop where
  ek_create_finish : EvmKeeps (EvmAvoids createBuffers)
    ["heap_ptr", "journal_n", "scratch_ptr"] (ofString "create_finish")
  gas_mark_cells_create_finish :
    FunSpec (EvmAvoids createBuffers)
      (fun s r post => InitECandidate.Solver.Wave8Contracts.M23.Resumes r →
        OpDispatchSpec.evmR post ≤ OpDispatchSpec.evmR s ∧
        memW post (globN s "cur_cont" + 48) = memW s (globN s "cur_cont" + 48) ∧
        ChainCellsAgree s post)
      (ofString "create_finish")

theorem chainCellsAgree_refl {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ChainCellsAgree s s :=
  fun _ _ => ⟨rfl, rfl, rfl, rfl⟩

theorem chainCellsAgree_trans {F : Type} {s mid post : PanSemStateFiniteExact 64 F}
    (h1 : ChainCellsAgree s mid) (hch : evmChain mid = evmChain s)
    (h2 : ChainCellsAgree mid post) : ChainCellsAgree s post := by
  intro ec hec
  obtain ⟨a1, b1, c1, d1⟩ := h1 ec hec
  obtain ⟨a2, b2, c2, d2⟩ := h2 ec (hch.symm ▸ hec)
  exact ⟨a2.trans a1, b2.trans b1, c2.trans c1, d2.trans d1⟩

theorem chainCellsAgree_of_memory_eq {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hm : post.memory = s.memory) : ChainCellsAgree s post := by
  intro ec _
  have hw : ∀ a, memW post a = memW s a := by
    intro a
    unfold memW
    rw [hm]
  exact ⟨hw _, hw _, hw _, hw _⟩

theorem create_finish_specs_of (h : CreateFinishSpecs) :
    FunSpec (EvmAvoids createBuffers)
      (fun s r post => InitECandidate.Solver.Wave8Contracts.M23.Resumes r →
        InitECandidate.Solver.Wave8Contracts.M23.EvmStep
          ["heap_ptr", "journal_n", "scratch_ptr"] s post ∧
        OpDispatchSpec.evmR post ≤ OpDispatchSpec.evmR s ∧
        memW post (globN s "cur_cont" + 48) = memW s (globN s "cur_cont" + 48) ∧
        ChainCellsAgree s post)
      (ofString "create_finish") := by
  obtain ⟨ps, body, rt, hl, hk⟩ := h.ek_create_finish
  obtain ⟨ps', body', rt', hl', hc⟩ := h.gas_mark_cells_create_finish
  have heq := hl.symm.trans hl'
  simp only [Option.some.injEq, Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  refine ⟨_, _, _, hl, ?_⟩
  intro F s hcode hP hex hnt hr
  exact ⟨hk s hcode hP hex hnt hr, hc s hcode hP hex hnt hr⟩

theorem finish_child_pop_invariants {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hAs : ArenaReady s)
    (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (hne : memW s (globN s "cur_cont" + 16) ≠ 0)
    (hAp : ArenaReady post)
    (hm : post.memory = s.memory)
    (hdom : post.memaddrs = s.memaddrs)
    (hbe : post.be = s.be)
    (hev : globN post "ev" = memW s (globN s "cur_cont"))
    (hcc : globN post "cur_cont" = memW s (globN s "cur_cont" + 8))
    (hg : ∀ name : String,
      name ≠ "ev" → name ≠ "cur_cont" → globN post name = globN s name) :
    ∃ S' : List Nat,
      (∀ t ∈ S', t ∈ S) ∧
      InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt post S' ∧
      ReleaseReadyAt post S' (memW s (globN s "cur_cont" + 48))
        (memW s (globN s "cur_cont" + 56)) ∧
      evmChain post = (evmChain s).tail ∧
      (evmChain post).length + 1 = (evmChain s).length ∧
      OpDispatchSpec.evmR post +
        (memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192)) =
        OpDispatchSpec.evmR s ∧
      (∀ ec ∈ evmChain post,
        memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
        memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧
        memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧
        memW post (ec.2 + 56) = memW s (ec.2 + 56)) := by
  obtain ⟨S', hsub, hcases, hIp, hch, hR⟩ :=
    evmInvAt_of_pop_globals hAs hInv hne hAp hm hdom hbe hev hcc hg
  have hRel := releaseReadyAt_of_pop hAs hInv hne hm hg hch hsub hcases
  have hlen : (evmChain post).length + 1 = (evmChain s).length := by
    rw [hch, evmChain_cons_of_cont_ne_zero hne]
    simp
  have hcells := chainCellsAgree_of_memory_eq hm
  refine ⟨S', hsub, hIp, hRel, hch, hlen, hR, ?_⟩
  intro ec hec
  exact hcells ec (List.mem_of_mem_tail (hch ▸ hec))

theorem chainCellsAgree_of_frame_unhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (hInv : EvmInv s)
    (hu : ∀ ec ∈ evmChain s,
      InitECandidate.Solver.Wave8GuestInv.R16Shards.IvlUnhit s post (ec.1, 280) ∧
      InitECandidate.Solver.Wave8GuestInv.R16Shards.IvlUnhit s post (ec.2, 104)) :
    ChainCellsAgree s post := by
  intro ec hec
  have hFW := hInv.2.choose_spec.2.2.2.2.1 ec hec
  obtain ⟨he, hc, _, _⟩ :=
    InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hInv.1.2 hFW
  have he8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
  have hc8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
  obtain ⟨hue, huc⟩ := hu ec hec
  exact ⟨InitECandidate.Solver.Wave8GuestInv.R16Shards.memW_eq_of_ivlUnhit hue (by omega) he ⟨by omega, by omega⟩,
    InitECandidate.Solver.Wave8GuestInv.R16Shards.memW_eq_of_ivlUnhit hue (by omega) he ⟨by omega, by omega⟩,
    InitECandidate.Solver.Wave8GuestInv.R16Shards.memW_eq_of_ivlUnhit hue (by omega) he ⟨by omega, by omega⟩,
    InitECandidate.Solver.Wave8GuestInv.R16Shards.memW_eq_of_ivlUnhit huc (by omega) hc ⟨by omega, by omega⟩⟩

theorem state_restore_finish_cells {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode)
    (hInv : EvmInv s) (v : ValueHOL 64)
    (hv : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_state_restore)).1 =
      some (.returned v)) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_state_restore)).2
    EvmInv post ∧
    globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    InitECandidate.Solver.Wave8Contracts.M23.GlobalsKept ["heap_ptr", "journal_n"] s post ∧
    evmChain post = evmChain s ∧
    OpDispatchSpec.evmR post = OpDispatchSpec.evmR s ∧
    memW post (globN s "cur_cont" + 48) = memW s (globN s "cur_cont" + 48) ∧
    ChainCellsAgree s post := by
  obtain ⟨hIp, hhp, hg, hch, hR, hu⟩ :=
    InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue.state_restore_body_spec
      s hcode hInv v hv
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    rw [evmChain_cons]
    exact List.mem_cons_self
  have hFW := hInv.2.choose_spec.2.2.2.2.1 _ hhead
  have hc := (InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hInv.1.2 hFW).2.1
  have hc8 : globN s "cur_cont" % 8 = 0 :=
    (hFW.1 (globN s "cur_cont", 104) (by simp)).2.1
  exact ⟨hIp, hhp, hg, hch, hR,
    InitECandidate.Solver.Wave8GuestInv.R16Shards.memW_eq_of_ivlUnhit (hu _ hhead).2 (by omega) hc ⟨by omega, by omega⟩,
    chainCellsAgree_of_frame_unhit hInv hu⟩

theorem chainCellsAgree_and_mark_of_headAllowed {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (hInv : EvmInv s)
    (hmem_out : ∀ x : BitVec 64,
      (∀ addr ∈ headAllowedOffsets (globN s "ev") (globN s "cur_cont"),
        x ≠ BitVec.ofNat 64 addr) →
      post.memory x = s.memory x) :
    memW post (globN s "cur_cont" + 48) = memW s (globN s "cur_cont" + 48) ∧
    ChainCellsAgree s post := by
  set e0 := globN s "ev"
  set c0 := globN s "cur_cont"
  have hhead : (e0, c0) ∈ evmChain s := by
    rw [evmChain_cons]; exact List.mem_cons_self
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead
  obtain ⟨he0_lt, hc0_lt, _, _⟩ :=
    InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hInv.1.2 hFW0
  have hall_lt : ∀ addr ∈ headAllowedOffsets e0 c0, addr < 2 ^ 64 := by
    intro addr haddr
    simp only [headAllowedOffsets, List.mem_cons, List.not_mem_nil, or_false] at haddr
    rcases haddr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hmemW_ne : ∀ a : Nat, a < 2 ^ 64 →
      (∀ addr ∈ headAllowedOffsets e0 c0, a ≠ addr) → memW post a = memW s a := by
    intro a hlt hne
    unfold memW
    rw [hmem_out (BitVec.ofNat 64 a)]
    intro addr haddr heq
    have := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (hall_lt addr haddr)] at this
    exact hne addr haddr this
  have hdisj_not_in : ∀ {a base sz : Nat},
      Disj (e0, 280) (base, sz) → Disj (c0, 104) (base, sz) →
      base ≤ a → a + 8 ≤ base + sz →
      ∀ addr ∈ headAllowedOffsets e0 c0, a ≠ addr := by
    intro a base sz hde hdc hlo hhi addr haddr heq
    unfold Disj at hde hdc; dsimp only at hde hdc
    simp only [headAllowedOffsets, List.mem_cons, List.not_mem_nil, or_false] at haddr
    rcases haddr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rcases hde with h | h | h | h <;> omega
    · rcases hde with h | h | h | h <;> omega
    · rcases hde with h | h | h | h <;> omega
    · rcases hde with h | h | h | h <;> omega
    · rcases hde with h | h | h | h <;> omega
    · rcases hde with h | h | h | h <;> omega
    · rcases hde with h | h | h | h <;> omega
    · rcases hde with h | h | h | h <;> omega
    · rcases hde with h | h | h | h <;> omega
    · rcases hde with h | h | h | h <;> omega
    · rcases hdc with h | h | h | h <;> omega
  have hFO_pw := hInv.2.choose_spec.2.2.2.2.2.2.2.1
  have hcons : ∃ chTail, evmChain s = (e0, c0) :: chTail := by
    rw [evmChain_cons]; exact ⟨_, rfl⟩
  obtain ⟨chTail, hch_eq⟩ := hcons
  have hpw0 : (frameObjects s (e0, c0)).Pairwise Disj ∧
      (∀ o1 ∈ frameObjects s (e0, c0),
        ∀ ec ∈ chTail, ∀ o2 ∈ frameObjects s ec, Disj o1 o2) := by
    have hpw := hFO_pw
    rw [hch_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
    refine ⟨hpw.1, fun o1 ho1 ec hec o2 ho2 => hpw.2.2 o1 ho1 o2 ?_⟩
    exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, hec, rfl⟩, ho2⟩
  have hde_c0 : Disj (e0, 280) (c0, 104) := by
    have hp := hpw0.1
    unfold frameObjects at hp
    exact (List.pairwise_cons.mp (List.pairwise_append.mp hp).1).1 _ (by simp)
  have hc0_48 : memW post (c0 + 48) = memW s (c0 + 48) := by
    apply hmemW_ne (c0 + 48) (by omega)
    intro addr haddr heq
    simp only [headAllowedOffsets, List.mem_cons, List.not_mem_nil, or_false] at haddr
    rcases haddr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · unfold Disj at hde_c0; dsimp only at hde_c0; rcases hde_c0 with h | h | h | h <;> omega
    · unfold Disj at hde_c0; dsimp only at hde_c0; rcases hde_c0 with h | h | h | h <;> omega
    · unfold Disj at hde_c0; dsimp only at hde_c0; rcases hde_c0 with h | h | h | h <;> omega
    · unfold Disj at hde_c0; dsimp only at hde_c0; rcases hde_c0 with h | h | h | h <;> omega
    · unfold Disj at hde_c0; dsimp only at hde_c0; rcases hde_c0 with h | h | h | h <;> omega
    · unfold Disj at hde_c0; dsimp only at hde_c0; rcases hde_c0 with h | h | h | h <;> omega
    · unfold Disj at hde_c0; dsimp only at hde_c0; rcases hde_c0 with h | h | h | h <;> omega
    · unfold Disj at hde_c0; dsimp only at hde_c0; rcases hde_c0 with h | h | h | h <;> omega
    · unfold Disj at hde_c0; dsimp only at hde_c0; rcases hde_c0 with h | h | h | h <;> omega
    · unfold Disj at hde_c0; dsimp only at hde_c0; rcases hde_c0 with h | h | h | h <;> omega
    · omega
  refine ⟨hc0_48, ?_⟩
  intro ec hec
  have hFW := hInv.2.choose_spec.2.2.2.2.1 ec hec
  obtain ⟨he_lt, hc_lt, _, _⟩ :=
    InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hInv.1.2 hFW
  rw [hch_eq] at hec
  rcases List.mem_cons.mp hec with rfl | htail
  · have he_off : ∀ off : Nat, off ∈ ([24, 32, 40] : List Nat) →
        memW post (e0 + off) = memW s (e0 + off) := by
      intro off hoff
      have hoff_lt : off + 8 ≤ 280 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
        rcases hoff with rfl | rfl | rfl <;> omega
      apply hmemW_ne (e0 + off) (by omega)
      intro addr haddr heq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      simp only [headAllowedOffsets, List.mem_cons, List.not_mem_nil, or_false] at haddr
      rcases haddr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rcases hoff with rfl | rfl | rfl <;> omega
      · rcases hoff with rfl | rfl | rfl <;> omega
      · rcases hoff with rfl | rfl | rfl <;> omega
      · rcases hoff with rfl | rfl | rfl <;> omega
      · rcases hoff with rfl | rfl | rfl <;> omega
      · rcases hoff with rfl | rfl | rfl <;> omega
      · rcases hoff with rfl | rfl | rfl <;> omega
      · rcases hoff with rfl | rfl | rfl <;> omega
      · rcases hoff with rfl | rfl | rfl <;> omega
      · rcases hoff with rfl | rfl | rfl <;> omega
      · unfold Disj at hde_c0; dsimp only at hde_c0; rcases hde_c0 with h | h | h | h <;> omega
    have hc0_56 : memW post (c0 + 56) = memW s (c0 + 56) := by
      apply hmemW_ne (c0 + 56) (by omega)
      intro addr haddr heq
      simp only [headAllowedOffsets, List.mem_cons, List.not_mem_nil, or_false] at haddr
      rcases haddr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · unfold Disj at hde_c0; dsimp only at hde_c0; rcases hde_c0 with h | h | h | h <;> omega
      · unfold Disj at hde_c0; dsimp only at hde_c0; rcases hde_c0 with h | h | h | h <;> omega
      · unfold Disj at hde_c0; dsimp only at hde_c0; rcases hde_c0 with h | h | h | h <;> omega
      · unfold Disj at hde_c0; dsimp only at hde_c0; rcases hde_c0 with h | h | h | h <;> omega
      · unfold Disj at hde_c0; dsimp only at hde_c0; rcases hde_c0 with h | h | h | h <;> omega
      · unfold Disj at hde_c0; dsimp only at hde_c0; rcases hde_c0 with h | h | h | h <;> omega
      · unfold Disj at hde_c0; dsimp only at hde_c0; rcases hde_c0 with h | h | h | h <;> omega
      · unfold Disj at hde_c0; dsimp only at hde_c0; rcases hde_c0 with h | h | h | h <;> omega
      · unfold Disj at hde_c0; dsimp only at hde_c0; rcases hde_c0 with h | h | h | h <;> omega
      · unfold Disj at hde_c0; dsimp only at hde_c0; rcases hde_c0 with h | h | h | h <;> omega
      · omega
    exact ⟨he_off 24 (by simp), he_off 32 (by simp), he_off 40 (by simp), hc0_56⟩
  · have hde_ec1 : Disj (e0, 280) (ec.1, 280) :=
      hpw0.2 _ (by simp [frameObjects]) ec htail _ (by simp [frameObjects])
    have hdc_ec1 : Disj (c0, 104) (ec.1, 280) :=
      hpw0.2 _ (by simp [frameObjects]) ec htail _ (by simp [frameObjects])
    have hde_ec2 : Disj (e0, 280) (ec.2, 104) :=
      hpw0.2 _ (by simp [frameObjects]) ec htail _ (by simp [frameObjects])
    have hdc_ec2 : Disj (c0, 104) (ec.2, 104) :=
      hpw0.2 _ (by simp [frameObjects]) ec htail _ (by simp [frameObjects])
    exact ⟨hmemW_ne (ec.1 + 24) (by omega) (hdisj_not_in hde_ec1 hdc_ec1 (by omega) (by omega)),
      hmemW_ne (ec.1 + 32) (by omega) (hdisj_not_in hde_ec1 hdc_ec1 (by omega) (by omega)),
      hmemW_ne (ec.1 + 40) (by omega) (hdisj_not_in hde_ec1 hdc_ec1 (by omega) (by omega)),
      hmemW_ne (ec.2 + 56) (by omega) (hdisj_not_in hde_ec2 hdc_ec2 (by omega) (by omega))⟩

private theorem store_res_not_resumes_r11 {F : Type}
    {t post : PanSemStateFiniteExact 64 F} {dst src : ExpHOL 64} {r : PanSemResultExact 64}
    (h : evaluateHOLFiniteState t (.store dst src) = (some r, post)) :
    ¬ ResumesR11 (some r) := by
  rw [evaluateHOLFiniteState_store] at h
  revert h
  split
  · split
    · split
      · simp
      · intro h; injection h with hr _; injection hr with hr'; subst hr'
        rintro (⟨_, hc⟩ | ⟨_, _, hc, _⟩) <;> cases hc
    · intro h; injection h with hr _; injection hr with hr'; subst hr'
      rintro (⟨_, hc⟩ | ⟨_, _, hc, _⟩) <;> cases hc
  · intro h; injection h with hr _; injection hr with hr'; subst hr'
    rintro (⟨_, hc⟩ | ⟨_, _, hc, _⟩) <;> cases hc

theorem refill_memory_frame {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s)
    (hres : ResumesR11
      (evaluateHOLFiniteState s
        (sourceFnBody Guest.Software.guestFn_refill_frame_state_gas)).1) :
    ∀ x : BitVec 64,
      (∀ addr ∈ headAllowedOffsets (globN s "ev") (globN s "cur_cont"),
        x ≠ BitVec.ofNat 64 addr) →
      (evaluateHOLFiniteState s
        (sourceFnBody Guest.Software.guestFn_refill_frame_state_gas)).2.memory x = s.memory x := by
  obtain ⟨he_lt, _, ⟨evw, hevw_lk, hevw_nat⟩, _, _⟩ := evm_head_globals hInv
  rw [refill_body_eq, evaluateHOLFiniteState_dec_total] at hres ⊢
  dsimp only at hres ⊢
  revert hres
  rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ev"), .const 112])) with _ | msgVal
  · dsimp only; intro hres
    rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
  · dsimp only
    by_cases hsh_msg : shapeEqHOL .one (shapeOfHOLExact msgVal) = true
    · rw [if_pos hsh_msg]; dsimp only; intro hres x hx
      let s0 := setVarHOLFinite (ofString "msg") msgVal s
      let body0 : ProgHOL 64 :=
        .seq
          (.store (.op .add [.var .global (ofString "ev"), .const 64])
            (.op .add
              [.load .one (.op .add [.var .global (ofString "ev"), .const 64]),
               .load .one (.op .add [.var .global (ofString "ev"), .const 192])]))
          (.seq
            (.store (.op .add [.var .global (ofString "ev"), .const 72])
              (.load .one (.op .add [.var .local (ofString "msg"), .const 48])))
            (.seq
              (.store (.op .add [.var .global (ofString "ev"), .const 192]) (.const 0))
              (.return (.const 0))))
      change ResumesR11 (evaluateHOLFiniteState s0 body0).1 at hres
      change (evaluateHOLFiniteState s0 body0).2.memory x = s.memory x
      dsimp only [body0] at hres ⊢
      rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
      cases h1 : evaluateHOLFiniteState s0
          (.store (.op .add [.var .global (ofString "ev"), .const 64])
            (.op .add
              [.load .one (.op .add [.var .global (ofString "ev"), .const 64]),
               .load .one (.op .add [.var .global (ofString "ev"), .const 192])])) with
      | mk r1 s1 =>
        rw [h1] at hres; dsimp only at hres ⊢
        rcases r1 with _ | res1
        · obtain ⟨w1, _, hs1_eq⟩ :=
            InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.store_global_off_word
              (t := s0) (post := s1) (gname := "ev") (gbase := globN s "ev") (off := 64)
              hevw_lk hevw_nat (by omega)
              (fun v hv => by
                simp only [evalHOLExact, wordOpHOL] at hv; revert hv
                rcases @evalListHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a)) _ with _ | vs
                · simp
                · dsimp only; split
                  · simp only [Option.map]
                    rcases wordOp .add (vs.map valueWord) with _ | w
                    · simp
                    · intro hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
                  · simp) h1
          rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
          cases h2 : evaluateHOLFiniteState s1
              (.store (.op .add [.var .global (ofString "ev"), .const 72])
                (.load .one (.op .add [.var .local (ofString "msg"), .const 48]))) with
          | mk r2 s2 =>
            rw [h2] at hres; dsimp only at hres ⊢
            rcases r2 with _ | res2
            · obtain ⟨w2, _, hs2_eq⟩ :=
                InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.store_global_off_word
                  (t := s1) (post := s2) (gname := "ev") (gbase := globN s "ev") (off := 72)
                  (by rw [hs1_eq]; exact hevw_lk) hevw_nat (by omega)
                  (fun v hv => by
                    have hml_word : ∀ (addr : BitVec 64) dom (dec : DecidablePred dom),
                        @memLoadHOLExact 64 _ .one addr dom dec s1.memory s1.structs = some v →
                        ∃ w : BitVec 64, v = .val (.word w) := by
                      intro addr dom dec hml
                      unfold memLoadHOLExact at hml
                      by_cases hd : dom addr
                      · rw [if_pos hd] at hml; injection hml with hv'
                        cases hm : s1.memory addr with
                        | word w => rw [hm] at hv'; exact ⟨w, hv'.symm⟩
                      · rw [if_neg hd] at hml; cases hml
                    unfold evalHOLExact at hv; revert hv
                    split
                    · split
                      · rename_i addr _; exact hml_word addr _ _
                      · simp
                    · simp) h2
              rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
              cases h3 : evaluateHOLFiniteState s2
                  (.store (.op .add [.var .global (ofString "ev"), .const 192]) (.const 0)) with
              | mk r3 s3 =>
                rw [h3] at hres; dsimp only at hres ⊢
                rcases r3 with _ | res3
                · obtain ⟨w3, _, hs3_eq⟩ :=
                    InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.store_global_off_word
                      (t := s2) (post := s3) (gname := "ev") (gbase := globN s "ev") (off := 192)
                      (by rw [hs2_eq, hs1_eq]; exact hevw_lk) hevw_nat (by omega)
                      (fun v hv => by injection hv with hv'; exact ⟨0, hv'.symm⟩) h3
                  rw [evaluateHOLFiniteState_return]
                  dsimp only [evalHOLExact]
                  have hle32 : sizeOfShapeWithContextHOL s3.structs
                      (shapeOfHOLExact (ValueHOL.val (HolWordLab.word (0 : BitVec 64)))) ≤ 32 := by
                    simp [shapeOfHOLExact]
                  rw [if_pos hle32]
                  change s3.memory x = s.memory x
                  rw [hs3_eq, hs2_eq, hs1_eq]
                  have hn192 : x ≠ BitVec.ofNat 64 (globN s "ev" + 192) :=
                    hx _ (by simp [headAllowedOffsets])
                  have hn72 : x ≠ BitVec.ofNat 64 (globN s "ev" + 72) :=
                    hx _ (by simp [headAllowedOffsets])
                  have hn64 : x ≠ BitVec.ofNat 64 (globN s "ev" + 64) :=
                    hx _ (by simp [headAllowedOffsets])
                  simp [InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.updW,
                    hn192, hn72, hn64, s0, setVarHOLFinite]
                · exact absurd hres (store_res_not_resumes_r11 h3)
            · exact absurd hres (store_res_not_resumes_r11 h2)
        · exact absurd hres (store_res_not_resumes_r11 h1)
    · rw [if_neg hsh_msg]; dsimp only; intro hres
      rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h

theorem frame_halt_memory_frame {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s) {w_err : BitVec 64}
    (hw_err : s.locals.lookup (ofString "err") = some (.val (.word w_err)))
    (hres : ResumesR11
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_halt)).1) :
    ∀ x : BitVec 64,
      (∀ addr ∈ headAllowedOffsets (globN s "ev") (globN s "cur_cont"),
        x ≠ BitVec.ofNat 64 addr) →
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_halt)).2.memory x =
        s.memory x := by
  obtain ⟨he_lt, _, ⟨evw, hevw_lk, hevw_nat⟩, _, _⟩ := evm_head_globals hInv
  rw [frame_halt_body_eq, evaluateHOLFiniteState_seq_line780] at hres ⊢
  intro x hx
  cases h1 : evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "ev"), .const 184])
        (.op .add
          [.load .one (.op .add [.var .global (ofString "ev"), .const 184]),
           .load .one (.op .add [.var .global (ofString "ev"), .const 64])])) with
  | mk r1 s1 =>
    rw [h1] at hres; dsimp only at hres ⊢
    rcases r1 with _ | res1
    · obtain ⟨w1, _, hs1_eq⟩ :=
        InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.store_global_off_word
          (t := s) (post := s1) (gname := "ev") (gbase := globN s "ev") (off := 184)
          hevw_lk hevw_nat (by omega)
          (fun v hv => by
            simp only [evalHOLExact, wordOpHOL] at hv; revert hv
            rcases @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) _ with _ | vs
            · simp
            · dsimp only; split
              · simp only [Option.map]
                rcases wordOp .add (vs.map valueWord) with _ | w
                · simp
                · intro hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
              · simp) h1
      rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
      cases h2 : evaluateHOLFiniteState s1
          (.store (.op .add [.var .global (ofString "ev"), .const 64]) (.const 0)) with
      | mk r2 s2 =>
        rw [h2] at hres; dsimp only at hres ⊢
        rcases r2 with _ | res2
        · obtain ⟨w2, _, hs2_eq⟩ :=
            InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.store_global_off_word
              (t := s1) (post := s2) (gname := "ev") (gbase := globN s "ev") (off := 64)
              (by rw [hs1_eq]; exact hevw_lk) hevw_nat (by omega)
              (fun v hv => by injection hv with hv'; exact ⟨0, hv'.symm⟩) h2
          rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
          cases h3 : evaluateHOLFiniteState s2
              (.store (.op .add [.var .global (ofString "ev"), .const 160])
                (.var .local (ofString "err"))) with
          | mk r3 s3 =>
            rw [h3] at hres; dsimp only at hres ⊢
            rcases r3 with _ | res3
            · obtain ⟨w3, _, hs3_eq⟩ :=
                InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.store_global_off_word
                  (t := s2) (post := s3) (gname := "ev") (gbase := globN s "ev") (off := 160)
                  (by rw [hs2_eq, hs1_eq]; exact hevw_lk) hevw_nat (by omega)
                  (fun v hv => by
                    change s2.locals.lookup (ofString "err") = some v at hv
                    rw [hs2_eq, hs1_eq] at hv; dsimp only at hv; rw [hw_err] at hv
                    injection hv with hv'; exact ⟨w_err, hv'.symm⟩) h3
              rw [evaluateHOLFiniteState_return]
              dsimp only [evalHOLExact]
              have hle32 : sizeOfShapeWithContextHOL s3.structs
                  (shapeOfHOLExact (ValueHOL.val (HolWordLab.word (0 : BitVec 64)))) ≤ 32 := by
                simp [shapeOfHOLExact]
              rw [if_pos hle32]
              change s3.memory x = s.memory x
              rw [hs3_eq, hs2_eq, hs1_eq]
              have hn160 : x ≠ BitVec.ofNat 64 (globN s "ev" + 160) :=
                hx _ (by simp [headAllowedOffsets])
              have hn64 : x ≠ BitVec.ofNat 64 (globN s "ev" + 64) :=
                hx _ (by simp [headAllowedOffsets])
              have hn184 : x ≠ BitVec.ofNat 64 (globN s "ev" + 184) :=
                hx _ (by simp [headAllowedOffsets])
              simp [InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.updW,
                hn160, hn64, hn184]
            · exact absurd hres (store_res_not_resumes_r11 h3)
        · exact absurd hres (store_res_not_resumes_r11 h2)
    · exact absurd hres (store_res_not_resumes_r11 h1)

def FinishPost {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (r : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 F) : Prop :=
  ((∃ v, r = some (.returned v)) ∨ OpDispatchSpec.IsEvmErr r) →
    EvmInv post ∧
    (evmChain post).length + 1 = (evmChain s0).length ∧
    OpDispatchSpec.evmR post ≤ OpDispatchSpec.evmR s0 ∧
    evmChain post = (evmChain s0).tail ∧
    (∀ ec ∈ evmChain post,
      memW post (ec.1 + 24) = memW s0 (ec.1 + 24) ∧
      memW post (ec.1 + 32) = memW s0 (ec.1 + 32) ∧
      memW post (ec.1 + 40) = memW s0 (ec.1 + 40) ∧
      memW post (ec.2 + 56) = memW s0 (ec.2 + 56)) ∧
    globN post "ev" = memW s0 (globN s0 "cur_cont") ∧
    globN post "frame_mem_ptr" = memW s0 (globN s0 "cur_cont" + 56)

theorem finishPost_vacuous {F : Type} {s0 post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)}
    (h1 : ∀ v, r ≠ some (.returned v)) (h2 : ¬ OpDispatchSpec.IsEvmErr r) :
    FinishPost s0 r post := by
  rintro (⟨v, hv⟩ | he)
  · exact absurd hv (h1 v)
  · exact absurd he h2

theorem finishPost_congr_lc {F : Type} {s0 p1 p2 : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)}
    (hm : p1.memory = p2.memory) (hg : p1.globals = p2.globals)
    (hd : p1.memaddrs = p2.memaddrs) (hb : p1.be = p2.be)
    (hsh : p1.shMemaddrs = p2.shMemaddrs) (_hst : p1.structs = p2.structs)
    (_hes : p1.eshapes = p2.eshapes) (hc : p1.code = p2.code)
    (hba : p1.baseAddr = p2.baseAddr) (_hta : p1.topAddr = p2.topAddr)
    (h : FinishPost s0 r p1) : FinishPost s0 r p2 := by
  intro hr
  obtain ⟨hInv, hlen, hR, hch, hcells, hev, hfmp⟩ := h hr
  have hmw : ∀ a, memW p2 a = memW p1 a := by
    intro a; unfold memW; rw [hm]
  have hgn : ∀ nm, globN p2 nm = globN p1 nm := by
    intro nm; unfold globN; rw [hg]
  have hch_eq : evmChain p2 = evmChain p1 := by
    have : ∀ (fuel e c : Nat), evmChainFrom p2 fuel e c = evmChainFrom p1 fuel e c := by
      intro fuel; induction fuel with
      | zero => intros; rfl
      | succ fuel ih =>
        intro e c; simp only [evmChainFrom, hmw]; split
        · rfl
        · rw [ih]
    unfold evmChain; rw [hgn, hgn, this]
  have hInv2 : EvmInv p2 := by
    have hGp : GuestInv p2 := guestInv_congr (s := p1) hc.symm hd.symm hsh.symm hba.symm hInv.1.1
    exact (evmInv_of_head_status_gas_update hInv hGp hg.symm hb.symm
      (fun x _ => by rw [← hm]) (by rw [hmw, hmw])).1
  refine ⟨hInv2, by rw [hch_eq]; exact hlen, ?_, by rw [hch_eq]; exact hch, ?_,
    by rw [hgn]; exact hev, by rw [hgn]; exact hfmp⟩
  · unfold OpDispatchSpec.evmR at hR ⊢
    rw [hch_eq]
    have hmap : ((evmChain p1).map fun ec => memW p2 (ec.1 + 64) + memW p2 (ec.1 + 192)) =
        ((evmChain p1).map fun ec => memW p1 (ec.1 + 64) + memW p1 (ec.1 + 192)) := by
      apply List.map_congr_left; intro ec _; rw [hmw, hmw]
    rw [hmap]; exact hR
  · intro ec hec; rw [hch_eq] at hec
    rw [hmw, hmw, hmw, hmw]; exact hcells ec hec

theorem lookup_finish_child :
    originalRuntimeCode.lookup (ofString "finish_child") =
      some ([], sourceFnBody Guest.Software.guestFn_finish_child, .one) :=
  lookup_of_guestAst_getElem 583 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_finish_child) rfl

def fcDropDecls : Nat → ProgHOL 64 → ProgHOL 64
  | 0, p => p
  | n + 1, .dec _ _ _ p => fcDropDecls n p
  | _, p => p

def fcLeftSeq : ProgHOL 64 → ProgHOL 64
  | .seq a _ => a
  | p => p

def fcRightSeq : ProgHOL 64 → ProgHOL 64
  | .seq _ b => b
  | p => p

def fcBody : ProgHOL 64 := sourceFnBody Guest.Software.guestFn_finish_child
def fcCore : ProgHOL 64 := fcDropDecls 11 fcBody
def fcPrelude : ProgHOL 64 := fcLeftSeq fcCore
def fcAfterPrelude : ProgHOL 64 := fcRightSeq fcCore
def fcBranches : ProgHOL 64 := fcLeftSeq (fcRightSeq (fcRightSeq fcAfterPrelude))
def fcCleanup : ProgHOL 64 := fcRightSeq (fcRightSeq (fcRightSeq fcAfterPrelude))

theorem fcCore_eq : fcCore = .seq fcPrelude fcAfterPrelude := rfl

theorem fcAfterPrelude_eq :
    fcAfterPrelude =
      .seq (.assign .global (ofString "ev") (.var .local (ofString "parent")))
        (.seq (.assign .global (ofString "cur_cont")
            (.load .one (.op .add [.var .local (ofString "rec"), .const 8#64])))
          (.seq fcBranches fcCleanup)) := rfl

theorem fcCleanup_eq :
    fcCleanup =
      .seq (.call (some (none, none)) (ofString "scratch_release")
          [.var .local (ofString "child_mark")])
        (.seq (.call (some (none, none)) (ofString "frame_mem_release")
            [.var .local (ofString "child_mem_mark")])
          (.seq (.call (some (none, none)) (ofString "pc_add") [.const 1#64])
            (.return (.const 0#64)))) := rfl

structure FcEntryLocals {F : Type} (s0 s : PanSemStateFiniteExact 64 F) : Prop where
  rec_lk : s.locals.lookup (ofString "rec") =
    some (.val (.word (BitVec.ofNat 64 (globN s0 "cur_cont"))))
  child_lk : s.locals.lookup (ofString "child") =
    some (.val (.word (BitVec.ofNat 64 (globN s0 "ev"))))
  parent_lk : s.locals.lookup (ofString "parent") =
    some (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont")))))
  kind_lk : s.locals.lookup (ofString "kind") =
    some (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 16)))))
  msg_lk : s.locals.lookup (ofString "msg") =
    some (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 40)))))
  nac_lk : s.locals.lookup (ofString "new_account_charged") =
    some (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 64)))))
  cm_lk : s.locals.lookup (ofString "child_mark") =
    some (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 48)))))
  cmm_lk : s.locals.lookup (ofString "child_mem_mark") =
    some (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 56)))))
  os_lk : s.locals.lookup (ofString "out_start") =
    some (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 72)))))
  osz_lk : s.locals.lookup (ofString "out_size") =
    some (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 80)))))
  ca_lk : s.locals.lookup (ofString "contract_address") =
    some (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 88)))))

theorem fcEntryLocals_congr_locals {F : Type} {s0 s1 s2 : PanSemStateFiniteExact 64 F}
    (hl : s2.locals = s1.locals) (h : FcEntryLocals s0 s1) : FcEntryLocals s0 s2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rw [hl]; assumption)

private theorem eval_load_local_off {F : Type} (s : PanSemStateFiniteExact 64 F)
    {lname : String} {base sz off : Nat}
    (hlk : s.locals.lookup (ofString lname) = some (.val (.word (BitVec.ofNat 64 base))))
    (_hdom : s.memaddrs = ordinaryDomain)
    (hwok : WordsOK s (base, sz))
    (hbnd : base + sz ≤ 2 ^ 64)
    (hoff : off + 8 ≤ sz) (hoff8 : off % 8 = 0) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .local (ofString lname), .const (BitVec.ofNat 64 off)])) =
      some (.val (.word (BitVec.ofNat 64 (memW s (base + off))))) := by
  have hadd_eq : BitVec.ofNat 64 base + BitVec.ofNat 64 off = BitVec.ofNat 64 (base + off) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show base < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show off < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show base + off < 2 ^ 64 by omega)]
  have hwa : WordAt s (base + off) := hwok.2.2 (off / 8) (by omega)
    |> fun h => by rwa [show base + 8 * (off / 8) = base + off by omega] at h
  obtain ⟨w, hmem_dom, hmem_eq⟩ := hwa
  have hadd0 : BitVec.ofNat 64 base + (BitVec.ofNat 64 off + (0 : BitVec 64)) =
      BitVec.ofNat 64 (base + off) := by
    change BitVec.ofNat 64 base + (BitVec.ofNat 64 off + 0#64) = _
    rw [BitVec.add_zero, hadd_eq]
  simp only [evalHOLExact, evalListHOLExact, hlk, isWfShapeExactHOL, memLoadHOLExact, ↓reduceIte,
    valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr,
    Bool.and_self]
  rw [hadd0]
  simp only [hmem_dom, ↓reduceIte, hmem_eq, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
  unfold memW
  rw [hmem_eq]; simp

theorem finish_child_decls_step {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (hInv : EvmInv s0)
    (hCore : ∀ (s1 : PanSemStateFiniteExact 64 F),
      s1.memory = s0.memory → s1.globals = s0.globals →
      s1.memaddrs = s0.memaddrs → s1.be = s0.be →
      s1.shMemaddrs = s0.shMemaddrs → s1.structs = s0.structs →
      s1.eshapes = s0.eshapes → s1.code = s0.code →
      s1.baseAddr = s0.baseAddr → s1.topAddr = s0.topAddr →
      s1.clock = s0.clock →
      FcEntryLocals s0 s1 →
      (evaluateHOLFiniteState s1 fcCore).1 ≠ some .timeOut →
      FinishPost s0 (evaluateHOLFiniteState s1 fcCore).1
        (evaluateHOLFiniteState s1 fcCore).2)
    (hnt : (evaluateHOLFiniteState s0 fcBody).1 ≠ some .timeOut) :
    FinishPost s0 (evaluateHOLFiniteState s0 fcBody).1
      (evaluateHOLFiniteState s0 fcBody).2 := by
  have hhead : (globN s0 "ev", globN s0 "cur_cont") ∈ evmChain s0 := by
    rw [evmChain_cons]; exact List.mem_cons_self
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead
  obtain ⟨he0_lt, hc0_lt, _, _⟩ :=
    InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hInv.1.2 hFW0
  have hc0_wok : WordsOK s0 (globN s0 "cur_cont", 104) :=
    (hFW0.1 (globN s0 "cur_cont", 104) (by simp)).2
  obtain ⟨w_cc, hw_cc⟩ := hInv.1.2.2.2.2.2.2.2.2.2 "cur_cont" (by decide)
  obtain ⟨w_ev, hw_ev⟩ := hInv.1.2.2.2.2.2.2.2.2.2 "ev" (by decide)
  have hw_cc_eq : w_cc = BitVec.ofNat 64 (globN s0 "cur_cont") := by
    apply BitVec.eq_of_toNat_eq
    unfold GlobalWord at hw_cc
    have hgn : globN s0 "cur_cont" = w_cc.toNat := by simp [globN, hw_cc]
    rw [BitVec.toNat_ofNat, hgn, Nat.mod_eq_of_lt w_cc.isLt]
  have hw_ev_eq : w_ev = BitVec.ofNat 64 (globN s0 "ev") := by
    apply BitVec.eq_of_toNat_eq
    unfold GlobalWord at hw_ev
    have hgn : globN s0 "ev" = w_ev.toNat := by simp [globN, hw_ev]
    rw [BitVec.toNat_ofNat, hgn, Nat.mod_eq_of_lt w_ev.isLt]
  subst hw_cc_eq hw_ev_eq
  unfold GlobalWord at hw_cc hw_ev
  have hdec_step : ∀ {t : PanSemStateFiniteExact 64 F} (nm : MlS) (e : ExpHOL 64)
      (w : BitVec 64) (p : ProgHOL 64),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e =
        some (.val (.word w)) →
      ((evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) t) p).1 ≠ some .timeOut →
        FinishPost s0
          (evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) t) p).1
          (evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) t) p).2) →
      (evaluateHOLFiniteState t (.dec nm .one e p)).1 ≠ some .timeOut →
      FinishPost s0
        (evaluateHOLFiniteState t (.dec nm .one e p)).1
        (evaluateHOLFiniteState t (.dec nm .one e p)).2 := by
    intro t nm e w p hev hcont hnt_dec
    rw [evaluateHOLFiniteState_dec_total] at hnt_dec ⊢
    dsimp only at hnt_dec ⊢
    rw [hev] at hnt_dec ⊢
    dsimp only at hnt_dec ⊢
    split at hnt_dec
    · rename_i hcond
      rw [if_pos hcond]; dsimp only
      have hres := hcont hnt_dec
      exact finishPost_congr_lc
        (p1 := (evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) t) p).2)
        (p2 := { (evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) t) p).2 with
          locals := (evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) t) p).2.locals.resVarEq
            (nm, t.locals.lookup nm) })
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hres
    · rename_i hcond
      rw [if_neg hcond]; dsimp only
      exact finishPost_vacuous (r := some .error) (by simp) (by simp [OpDispatchSpec.IsEvmErr])
  change (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_finish_child)).1 ≠
      some .timeOut at hnt
  change FinishPost s0 (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_finish_child)).1
    (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_finish_child)).2
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_finish_child,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural] at hnt ⊢
  -- Step 1: rec
  have he1 : @evalHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
      (.var .global (ofString "cur_cont")) =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "cur_cont")))) := by
    simp [evalHOLExact, hw_cc]
  refine hdec_step _ _ _ _ he1 (fun hnt1 => ?_) hnt
  set d1 := setVarHOLFinite (ofString "rec") (.val (.word (BitVec.ofNat 64 (globN s0 "cur_cont")))) s0
  -- Step 2: child
  have he2 : @evalHOLExact 64 F _ d1.toExact (fun a => Classical.propDecidable (d1.memaddrs a))
      (.var .global (ofString "ev")) =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "ev")))) := by
    simp [evalHOLExact, d1, setVarHOLFinite, hw_ev]
  refine hdec_step _ _ _ _ he2 (fun hnt2 => ?_) hnt1
  set d2 := setVarHOLFinite (ofString "child") (.val (.word (BitVec.ofNat 64 (globN s0 "ev")))) d1
  have hd2_rec : d2.locals.lookup (ofString "rec") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "cur_cont")))) := by
    have hne : ofString "child" ≠ ofString "rec" := by decide
    simp [d2, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
  -- Step 3: parent (rec + 0)
  have he3 := eval_load_local_off d2 hd2_rec hInv.1.1.memaddrs hc0_wok (by omega) (off := 0) (by omega) (by omega)
  simp only [Nat.add_zero] at he3
  refine hdec_step _ _ _ _ he3 (fun hnt3 => ?_) hnt2
  set d3 := setVarHOLFinite (ofString "parent") (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont"))))) d2
  have hd3_rec : d3.locals.lookup (ofString "rec") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "cur_cont")))) := by
    have hne : ofString "parent" ≠ ofString "rec" := by decide
    simp [d3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hd2_rec]
  -- Step 4: kind (rec + 16)
  have he4 := eval_load_local_off d3 hd3_rec hInv.1.1.memaddrs hc0_wok (by omega) (off := 16) (by omega) (by omega)
  refine hdec_step _ _ _ _ he4 (fun hnt4 => ?_) hnt3
  set d4 := setVarHOLFinite (ofString "kind") (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 16))))) d3
  have hd4_rec : d4.locals.lookup (ofString "rec") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "cur_cont")))) := by
    have hne : ofString "kind" ≠ ofString "rec" := by decide
    simp [d4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hd3_rec]
  -- Step 5: msg (rec + 40)
  have he5 := eval_load_local_off d4 hd4_rec hInv.1.1.memaddrs hc0_wok (by omega) (off := 40) (by omega) (by omega)
  refine hdec_step _ _ _ _ he5 (fun hnt5 => ?_) hnt4
  set d5 := setVarHOLFinite (ofString "msg") (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 40))))) d4
  have hd5_rec : d5.locals.lookup (ofString "rec") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "cur_cont")))) := by
    have hne : ofString "msg" ≠ ofString "rec" := by decide
    simp [d5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hd4_rec]
  -- Step 6: new_account_charged (rec + 64)
  have he6 := eval_load_local_off d5 hd5_rec hInv.1.1.memaddrs hc0_wok (by omega) (off := 64) (by omega) (by omega)
  refine hdec_step _ _ _ _ he6 (fun hnt6 => ?_) hnt5
  set d6 := setVarHOLFinite (ofString "new_account_charged") (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 64))))) d5
  have hd6_rec : d6.locals.lookup (ofString "rec") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "cur_cont")))) := by
    have hne : ofString "new_account_charged" ≠ ofString "rec" := by decide
    simp [d6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hd5_rec]
  -- Step 7: child_mark (rec + 48)
  have he7 := eval_load_local_off d6 hd6_rec hInv.1.1.memaddrs hc0_wok (by omega) (off := 48) (by omega) (by omega)
  refine hdec_step _ _ _ _ he7 (fun hnt7 => ?_) hnt6
  set d7 := setVarHOLFinite (ofString "child_mark") (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 48))))) d6
  have hd7_rec : d7.locals.lookup (ofString "rec") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "cur_cont")))) := by
    have hne : ofString "child_mark" ≠ ofString "rec" := by decide
    simp [d7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hd6_rec]
  -- Step 8: child_mem_mark (rec + 56)
  have he8 := eval_load_local_off d7 hd7_rec hInv.1.1.memaddrs hc0_wok (by omega) (off := 56) (by omega) (by omega)
  refine hdec_step _ _ _ _ he8 (fun hnt8 => ?_) hnt7
  set d8 := setVarHOLFinite (ofString "child_mem_mark") (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 56))))) d7
  have hd8_rec : d8.locals.lookup (ofString "rec") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "cur_cont")))) := by
    have hne : ofString "child_mem_mark" ≠ ofString "rec" := by decide
    simp [d8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hd7_rec]
  -- Step 9: out_start (rec + 72)
  have he9 := eval_load_local_off d8 hd8_rec hInv.1.1.memaddrs hc0_wok (by omega) (off := 72) (by omega) (by omega)
  refine hdec_step _ _ _ _ he9 (fun hnt9 => ?_) hnt8
  set d9 := setVarHOLFinite (ofString "out_start") (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 72))))) d8
  have hd9_rec : d9.locals.lookup (ofString "rec") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "cur_cont")))) := by
    have hne : ofString "out_start" ≠ ofString "rec" := by decide
    simp [d9, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hd8_rec]
  -- Step 10: out_size (rec + 80)
  have he10 := eval_load_local_off d9 hd9_rec hInv.1.1.memaddrs hc0_wok (by omega) (off := 80) (by omega) (by omega)
  refine hdec_step _ _ _ _ he10 (fun hnt10 => ?_) hnt9
  set d10 := setVarHOLFinite (ofString "out_size") (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 80))))) d9
  have hd10_rec : d10.locals.lookup (ofString "rec") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "cur_cont")))) := by
    have hne : ofString "out_size" ≠ ofString "rec" := by decide
    simp [d10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hd9_rec]
  -- Step 11: contract_address (rec + 88)
  have he11 := eval_load_local_off d10 hd10_rec hInv.1.1.memaddrs hc0_wok (by omega) (off := 88) (by omega) (by omega)
  refine hdec_step _ _ _ _ he11 (fun hnt11 => ?_) hnt10
  set d11 := setVarHOLFinite (ofString "contract_address") (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 88))))) d10
  have hd11_locs : FcEntryLocals s0 d11 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      simp only [d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, setVarHOLFinite,
        HolFiniteMapExact.lookup_update, FUPDATE]
      repeat (rw [if_neg (by decide)])
      try simp
  exact hCore d11 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hd11_locs hnt11

theorem seq_finishPost {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {p1 p2 : ProgHOL 64}
    (hnret1 : ∀ u, (evaluateHOLFiniteState s p1).1 ≠ some (.returned u))
    (h1 : (evaluateHOLFiniteState s p1).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState s p1).1 = none →
        (evaluateHOLFiniteState (evaluateHOLFiniteState s p1).2 p2).1 ≠ some .timeOut →
        FinishPost s0
          (evaluateHOLFiniteState (evaluateHOLFiniteState s p1).2 p2).1
          (evaluateHOLFiniteState (evaluateHOLFiniteState s p1).2 p2).2) ∧
      (OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState s p1).1 →
        FinishPost s0 (evaluateHOLFiniteState s p1).1 (evaluateHOLFiniteState s p1).2))
    (hnt : (evaluateHOLFiniteState s (.seq p1 p2)).1 ≠ some .timeOut) :
    FinishPost s0 (evaluateHOLFiniteState s (.seq p1 p2)).1
      (evaluateHOLFiniteState s (.seq p1 p2)).2 := by
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  cases hr1 : evaluateHOLFiniteState s p1 with
  | mk r1 m =>
    rw [hr1] at hnt
    dsimp only at hnt ⊢
    cases r1 with
    | none =>
      dsimp only at hnt ⊢
      obtain ⟨hnone, _⟩ := h1 (by rw [hr1]; simp)
      rw [hr1] at hnone
      exact hnone rfl hnt
    | some r =>
      dsimp only at hnt ⊢
      by_cases herr : OpDispatchSpec.IsEvmErr (some r)
      · obtain ⟨_, he⟩ := h1 (by rw [hr1]; exact hnt)
        rw [hr1] at he
        exact he herr
      · refine finishPost_vacuous (fun u hu => ?_) herr
        exact hnret1 u (by rw [hr1]; exact hu)

theorem call0_ne_returned_fc {F : Type} (s : PanSemStateFiniteExact 64 F) (fn : MlS)
    (args : List (ExpHOL 64)) (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).1 ≠ some (.returned u) := by
  rw [evaluateHOLFiniteState_call]
  rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | _
  · simp
  · dsimp only
    rcases lookupCodeHOLFinite s.code.lookup fn _ with _ | ⟨_, _, _⟩
    · simp
    · dsimp only; split
      · simp
      · rcases evaluateHOLFiniteState _ _ with ⟨res, _⟩
        rcases res with _ | r
        · simp
        · cases r with
          | returned _ => dsimp only; split <;> simp
          | _ => simp

theorem callHandle_ne_returned_fc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (exn var : MlS) (handler : ProgHOL 64) (fn : MlS) (args : List (ExpHOL 64))
    (hh : ∀ (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t handler).1 ≠ some (.returned u))
    (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (none, some (exn, var, handler))) fn args)).1 ≠
      some (.returned u) := by
  rw [evaluateHOLFiniteState_call]
  rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | _
  · simp
  · dsimp only
    rcases lookupCodeHOLFinite s.code.lookup fn _ with _ | ⟨_, _, _⟩
    · simp
    · dsimp only; split
      · simp
      · rcases evaluateHOLFiniteState _ _ with ⟨res, cpost⟩
        rcases res with _ | r
        · simp
        · cases r with
          | returned _ => dsimp only; split <;> simp
          | exception eid ev =>
            dsimp only; split
            · rcases s.eshapes.lookup eid with _ | sh
              · simp
              · dsimp only; split
                · exact hh _ u
                · simp
            · simp
          | _ => simp

theorem store_ne_returned_fc {F : Type} (s : PanSemStateFiniteExact 64 F) (d e : ExpHOL 64)
    (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.store d e)).1 ≠ some (.returned u) := by
  rw [evaluateHOLFiniteState_store]
  split
  · split
    · split <;> simp
    · simp
  · simp

theorem assign_ne_returned_fc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (vk : VarKind) (nm : MlS) (e : ExpHOL 64) (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.assign vk nm e)).1 ≠ some (.returned u) := by
  rw [evaluateHOLFiniteState_assign]
  split
  · simp
  · split <;> simp

theorem skip_ne_returned_fc {F : Type} (s : PanSemStateFiniteExact 64 F) (u : ValueHOL 64) :
    (evaluateHOLFiniteState s .skip).1 ≠ some (.returned u) := by
  rw [evaluateHOLFiniteState_skip]; simp

theorem seq_ne_returned_fc {p1 p2 : ProgHOL 64}
    (h1 : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t p1).1 ≠ some (.returned u))
    (h2 : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t p2).1 ≠ some (.returned u))
    {F : Type} (s : PanSemStateFiniteExact 64 F) (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.seq p1 p2)).1 ≠ some (.returned u) := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases h : evaluateHOLFiniteState s p1 with ⟨r1, m⟩
  cases r1 with
  | none => exact h2 m u
  | some r =>
    dsimp only; intro hr
    exact h1 s u (by rw [h]; exact hr)

theorem ite_ne_returned_fc {c : ExpHOL 64} {y n : ProgHOL 64}
    (hy : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t y).1 ≠ some (.returned u))
    (hn : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t n).1 ≠ some (.returned u))
    {F : Type} (s : PanSemStateFiniteExact 64 F) (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.ite c y n)).1 ≠ some (.returned u) := by
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact hn s u
    · exact hy s u
  · simp

theorem dec_ne_returned_fc {nm : MlS} {sh : ShapeHOL} {e : ExpHOL 64} {p : ProgHOL 64}
    (hp : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t p).1 ≠ some (.returned u))
    {F : Type} (s : PanSemStateFiniteExact 64 F) (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.dec nm sh e p)).1 ≠ some (.returned u) := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · simp
  · split
    · dsimp only; exact hp _ u
    · simp

theorem decCall_ne_returned_fc {nm : MlS} {sh : ShapeHOL} {fn : MlS} {args : List (ExpHOL 64)}
    {p : ProgHOL 64}
    (hp : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t p).1 ≠ some (.returned u))
    {F : Type} (s : PanSemStateFiniteExact 64 F) (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.decCall nm sh fn args p)).1 ≠ some (.returned u) := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | _
  · simp
  · dsimp only
    rcases lookupCodeHOLFinite s.code.lookup fn _ with _ | ⟨_, _, _⟩
    · simp
    · dsimp only; split
      · simp
      · rcases evaluateHOLFiniteState _ _ with ⟨res, _⟩
        rcases res with _ | r
        · simp
        · cases r with
          | returned _ =>
            dsimp only; split
            · dsimp only; exact hp _ u
            · simp
          | _ => simp

theorem call0_outcome_fc {F : Type} {s : PanSemStateFiniteExact 64 F}
    {fname : MlS} {args : List (ExpHOL 64)}
    (_hnt : (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 ≠ some .timeOut) :
    (∀ u, (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 ≠ some (.returned u)) ∧
    (((evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = none →
      ∃ values body callee ret v cpost,
        evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
        lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) ∧
        evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), cpost) ∧
        (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).2 =
          { cpost with locals := s.locals }) ∧
     (OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 →
      ∃ values body callee ret v cpost,
        evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
        lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) ∧
        evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
          (some (.exception (ofString "EvmErr") v), cpost) ∧
        (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).2 =
          emptyLocalsHOLFinite cpost)) := by
  refine ⟨call0_ne_returned_fc s fname args, ?_, ?_⟩
  · rw [evaluateHOLFiniteState_call]
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
              · intro _; exact ⟨values, body, callee, ret, v, cpost, rfl, hl, hrun, rfl⟩
              · simp
            | _ => simp
  · rw [evaluateHOLFiniteState_call]
    rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
    · simp [OpDispatchSpec.IsEvmErr]
    · dsimp only
      rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, ret⟩
      · simp [OpDispatchSpec.IsEvmErr]
      · dsimp only
        by_cases hz : s.clock = 0
        · simp [hz, OpDispatchSpec.IsEvmErr]
        · simp only [hz, ↓reduceIte]
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, cpost⟩
          rcases res with _ | r
          · simp [OpDispatchSpec.IsEvmErr]
          · cases r with
            | returned _ =>
              dsimp only; split <;> simp [OpDispatchSpec.IsEvmErr]
            | exception eid v =>
              dsimp only
              rintro ⟨v', hv'⟩
              injection hv' with hr'
              injection hr' with heid hv_eq
              subst heid hv_eq
              exact ⟨values, body, callee, ret, v, cpost, rfl, hl, hrun, rfl⟩
            | _ => simp [OpDispatchSpec.IsEvmErr]

def fcCreateErrHandler : ProgHOL 64 :=
  .seq (.call (some (none, none)) (ofString "state_restore") [.var .local (ofString "csnap")])
    (.seq (.call (some (none, none)) (ofString "refill_frame_state_gas") [])
      (.seq (.call (some (none, none)) (ofString "frame_halt") [.var .local (ofString "err")])
        (.seq (.store (.op .add [.var .global (ofString "ev"), .const 120#64])
            (.var .global (ofString "evm_empty")))
          (.store (.op .add [.var .global (ofString "ev"), .const 128#64])
            (.const 0#64)))))

theorem fcCreateErrHandler_ne_returned {F : Type} (t : PanSemStateFiniteExact 64 F)
    (u : ValueHOL 64) :
    (evaluateHOLFiniteState t fcCreateErrHandler).1 ≠ some (.returned u) := by
  unfold fcCreateErrHandler
  exact seq_ne_returned_fc (fun s v => call0_ne_returned_fc s _ _ v)
    (seq_ne_returned_fc (fun s v => call0_ne_returned_fc s _ _ v)
      (seq_ne_returned_fc (fun s v => call0_ne_returned_fc s _ _ v)
        (seq_ne_returned_fc (fun s v => store_ne_returned_fc s _ _ v)
          (fun s v => store_ne_returned_fc s _ _ v)))) t u

theorem fcPrelude_eq :
    fcPrelude =
      .ite (.cmp .equal (.var .local (ofString "kind")) (.const 2#64))
        (.dec (ofString "csnap") .one
          (.load .one (.op .add [.var .local (ofString "rec"), .const 96#64]))
          (.ite (.cmp .equal
              (.load .one (.op .add [.var .local (ofString "child"), .const 160#64]))
              (.const 0#64))
            (.dec (ofString "err") .one (.const 0#64)
              (.call (some (none, some (ofString "EvmErr", ofString "err", fcCreateErrHandler)))
                (ofString "create_finish")
                [.var .local (ofString "msg"), .var .local (ofString "child")]))
            (.call (some (none, none)) (ofString "state_restore")
              [.var .local (ofString "csnap")])))
        .skip := rfl

theorem fcPrelude_ne_returned {F : Type} (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64) :
    (evaluateHOLFiniteState t fcPrelude).1 ≠ some (.returned u) := by
  rw [fcPrelude_eq]
  exact ite_ne_returned_fc
    (dec_ne_returned_fc
      (ite_ne_returned_fc
        (dec_ne_returned_fc
          (fun s v => callHandle_ne_returned_fc s _ _ _ _ _ fcCreateErrHandler_ne_returned v))
        (fun s v => call0_ne_returned_fc s _ _ v)))
    (fun s v => skip_ne_returned_fc s v) t u

structure PreludeRel {F : Type} (s0 post : PanSemStateFiniteExact 64 F) : Prop where
  inv : EvmInv post
  chain_eq : evmChain post = evmChain s0
  r_le : OpDispatchSpec.evmR post ≤ OpDispatchSpec.evmR s0
  mark_eq : memW post (globN s0 "cur_cont" + 48) = memW s0 (globN s0 "cur_cont" + 48)
  cells : ChainCellsAgree s0 post
  out_eq : memW s0 (globN s0 "cur_cont" + 16) ≠ 2 →
    memW post (globN s0 "cur_cont" + 72) = memW s0 (globN s0 "cur_cont" + 72) ∧
    memW post (globN s0 "cur_cont" + 80) = memW s0 (globN s0 "cur_cont" + 80)
  locals_ok : FcEntryLocals s0 post

theorem evmChain_lc_fc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    evmChain { s with locals := L, clock := k } = evmChain s := by
  have hcf : ∀ (fuel e c : Nat),
      evmChainFrom { s with locals := L, clock := k } fuel e c = evmChainFrom s fuel e c := by
    intro fuel; induction fuel with
    | zero => intros; rfl
    | succ fuel ih => intros; simp only [evmChainFrom, ih]; rfl
  exact hcf _ _ _

theorem evmR_lc_fc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    OpDispatchSpec.evmR { s with locals := L, clock := k } = OpDispatchSpec.evmR s := by
  unfold OpDispatchSpec.evmR; rw [evmChain_lc_fc s L k]; rfl

theorem preludeRel_refl {F : Type} {s0 s1 : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s0) (hm : s1.memory = s0.memory) (hg : s1.globals = s0.globals)
    (hd : s1.memaddrs = s0.memaddrs) (hb : s1.be = s0.be)
    (hsh : s1.shMemaddrs = s0.shMemaddrs) (hc : s1.code = s0.code)
    (hba : s1.baseAddr = s0.baseAddr) (hlocs : FcEntryLocals s0 s1) :
    PreludeRel s0 s1 := by
  have hmw : ∀ a, memW s1 a = memW s0 a := fun a => by unfold memW; rw [hm]
  have hGp : GuestInv s1 := guestInv_congr (s := s0) hc hd hsh hba hInv.1.1
  obtain ⟨hInv1, hch1, hR1⟩ :=
    evmInv_of_head_status_gas_update hInv hGp hg hb (fun _ _ => by rw [hm]) (by rw [hmw, hmw])
  exact ⟨hInv1, hch1, hR1, hmw _, chainCellsAgree_of_memory_eq hm,
    fun _ => ⟨hmw _, hmw _⟩, hlocs⟩

theorem call_state_restore_step {F : Type} {s : PanSemStateFiniteExact 64 F}
    {args : List (ExpHOL 64)}
    (hInv : EvmInv s)
    (hnt : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "state_restore") args)).1 ≠
      some .timeOut) :
    ((evaluateHOLFiniteState s (.call (some (none, none)) (ofString "state_restore") args)).1 = none →
      let post := (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "state_restore") args)).2
      EvmInv post ∧
      evmChain post = evmChain s ∧
      OpDispatchSpec.evmR post = OpDispatchSpec.evmR s ∧
      memW post (globN s "cur_cont" + 48) = memW s (globN s "cur_cont" + 48) ∧
      ChainCellsAgree s post ∧
      (∀ ec ∈ evmChain s,
        InitECandidate.Solver.Wave8GuestInv.R16Shards.IvlUnhit s post (ec.1, 280) ∧
        InitECandidate.Solver.Wave8GuestInv.R16Shards.IvlUnhit s post (ec.2, 104)) ∧
      post.locals = s.locals) ∧
    ¬ OpDispatchSpec.IsEvmErr
      (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "state_restore") args)).1 := by
  have hcode : s.code = originalRuntimeCode := hInv.1.1.code
  obtain ⟨_, hnone, herr⟩ := call0_outcome_fc (s := s) (fname := ofString "state_restore") (args := args) hnt
  constructor
  · intro hn
    obtain ⟨vals, body, cal, ret, rv, cpost, _, hl, hrun, hpost_eq⟩ := hnone hn
    have hcode_lk : s.code.lookup (ofString "state_restore") =
        some ([(ofString "snap", .one)], sourceFnBody Guest.Software.guestFn_state_restore, .one) := by
      rw [hcode]
      exact InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue.lookup_state_restore
    have hbody : body = sourceFnBody Guest.Software.guestFn_state_restore :=
      lookupCodeHOLFinite_installed_body s.code.lookup _ _ _ _ _ _ _ _ hcode_lk hl
    subst hbody
    have hInv_ce : EvmInv (callEntryStateHOLFinite s cal) :=
      OpDispatchSpec.localsFree_evmInv s cal (s.clock - 1) hInv
    obtain ⟨hIp, _, _, hch_cp, hR_cp, hu_cp⟩ :=
      InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue.state_restore_body_spec
        (callEntryStateHOLFinite s cal) hcode hInv_ce rv (by rw [hrun])
    obtain ⟨_, _, _, _, _, hmark_cp, hcells_cp⟩ :=
      state_restore_finish_cells (callEntryStateHOLFinite s cal) hcode hInv_ce rv (by rw [hrun])
    have hcpost_eq : (evaluateHOLFiniteState (callEntryStateHOLFinite s cal)
        (sourceFnBody Guest.Software.guestFn_state_restore)).2 = cpost := by rw [hrun]
    rw [hcpost_eq] at hIp hch_cp hR_cp hu_cp hmark_cp hcells_cp
    dsimp only
    rw [hpost_eq]
    have hInv_p : EvmInv { cpost with locals := s.locals } :=
      OpDispatchSpec.localsFree_evmInv cpost s.locals cpost.clock hIp
    have hch_ce : evmChain (callEntryStateHOLFinite s cal) = evmChain s :=
      evmChain_lc_fc s cal (s.clock - 1)
    have hR_ce : OpDispatchSpec.evmR (callEntryStateHOLFinite s cal) = OpDispatchSpec.evmR s :=
      evmR_lc_fc s cal (s.clock - 1)
    have hch_p : evmChain { cpost with locals := s.locals } = evmChain s :=
      (evmChain_lc_fc cpost s.locals cpost.clock).trans (hch_cp.trans hch_ce)
    have hR_p : OpDispatchSpec.evmR { cpost with locals := s.locals } = OpDispatchSpec.evmR s :=
      (evmR_lc_fc cpost s.locals cpost.clock).trans (hR_cp.trans hR_ce)
    have hcells_p : ChainCellsAgree s { cpost with locals := s.locals } := by
      intro ec hec
      exact hcells_cp ec (hch_ce.symm ▸ hec)
    have hu_p : ∀ ec ∈ evmChain s,
        InitECandidate.Solver.Wave8GuestInv.R16Shards.IvlUnhit s { cpost with locals := s.locals } (ec.1, 280) ∧
        InitECandidate.Solver.Wave8GuestInv.R16Shards.IvlUnhit s { cpost with locals := s.locals } (ec.2, 104) := by
      intro ec hec
      exact hu_cp ec (hch_ce.symm ▸ hec)
    exact ⟨hInv_p, hch_p, hR_p, hmark_cp, hcells_p, hu_p, rfl⟩
  · intro he
    obtain ⟨vals, body, cal, ret, rv, cpost, _, hl, hrun, _⟩ := herr he
    have hcode_lk : s.code.lookup (ofString "state_restore") =
        some ([(ofString "snap", .one)], sourceFnBody Guest.Software.guestFn_state_restore, .one) := by
      rw [hcode]
      exact InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue.lookup_state_restore
    have hbody : body = sourceFnBody Guest.Software.guestFn_state_restore :=
      lookupCodeHOLFinite_installed_body s.code.lookup _ _ _ _ _ _ _ _ hcode_lk hl
    subst hbody
    exact InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue.evaluate_noCatchableRaise
      InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue.htabMutCallees
      InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue.htabMutCallees_good
      (sourceFnBody Guest.Software.guestFn_state_restore) rfl
      (callEntryStateHOLFinite s cal) hcode
      (ofString "EvmErr") rv (by decide) (by rw [hrun])

theorem cur_cont_unhit_keeps_fields {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s)
    (hu : InitECandidate.Solver.Wave8GuestInv.R16Shards.IvlUnhit s post (globN s "cur_cont", 104)) :
    memW post (globN s "cur_cont" + 16) = memW s (globN s "cur_cont" + 16) ∧
    memW post (globN s "cur_cont" + 48) = memW s (globN s "cur_cont" + 48) ∧
    memW post (globN s "cur_cont" + 64) = memW s (globN s "cur_cont" + 64) ∧
    memW post (globN s "cur_cont" + 88) = memW s (globN s "cur_cont" + 88) := by
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    rw [evmChain_cons]; exact List.mem_cons_self
  have hFW := hInv.2.choose_spec.2.2.2.2.1 _ hhead
  have hc := (InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hInv.1.2 hFW).2.1
  have hc8 : globN s "cur_cont" % 8 = 0 := (hFW.1 (globN s "cur_cont", 104) (by simp)).2.1
  exact ⟨InitECandidate.Solver.Wave8GuestInv.R16Shards.memW_eq_of_ivlUnhit hu (by omega) hc ⟨by omega, by omega⟩,
    InitECandidate.Solver.Wave8GuestInv.R16Shards.memW_eq_of_ivlUnhit hu (by omega) hc ⟨by omega, by omega⟩,
    InitECandidate.Solver.Wave8GuestInv.R16Shards.memW_eq_of_ivlUnhit hu (by omega) hc ⟨by omega, by omega⟩,
    InitECandidate.Solver.Wave8GuestInv.R16Shards.memW_eq_of_ivlUnhit hu (by omega) hc ⟨by omega, by omega⟩⟩

theorem headAllowed_keeps_cur_cont_fields {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s)
    (hmem_out : ∀ x : BitVec 64,
      (∀ addr ∈ headAllowedOffsets (globN s "ev") (globN s "cur_cont"),
        x ≠ BitVec.ofNat 64 addr) →
      post.memory x = s.memory x) :
    memW post (globN s "cur_cont" + 16) = memW s (globN s "cur_cont" + 16) ∧
    memW post (globN s "cur_cont" + 48) = memW s (globN s "cur_cont" + 48) ∧
    memW post (globN s "cur_cont" + 64) = memW s (globN s "cur_cont" + 64) ∧
    memW post (globN s "cur_cont" + 88) = memW s (globN s "cur_cont" + 88) ∧
    ChainCellsAgree s post := by
  obtain ⟨hmark, hcells⟩ := chainCellsAgree_and_mark_of_headAllowed hInv hmem_out
  set e0 := globN s "ev"
  set c0 := globN s "cur_cont"
  have hhead : (e0, c0) ∈ evmChain s := by rw [evmChain_cons]; exact List.mem_cons_self
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead
  obtain ⟨he0_lt, hc0_lt, _, _⟩ :=
    InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hInv.1.2 hFW0
  have hdisj : Disj (e0, 280) (c0, 104) := by
    have hfl := List.pairwise_flatten.mp hInv.2.choose_spec.2.2.2.2.2.2.2.1
    have hp0 := hfl.1 _ (List.mem_map_of_mem hhead)
    exact (List.pairwise_cons.mp (List.pairwise_append.mp hp0).1).1 _ (by simp)
  have hall_lt : ∀ addr ∈ headAllowedOffsets e0 c0, addr < 2 ^ 64 := by
    intro addr haddr
    simp only [headAllowedOffsets, List.mem_cons, List.not_mem_nil, or_false] at haddr
    rcases haddr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hmw : ∀ off : Nat, off < 104 → off ≠ 32 → memW post (c0 + off) = memW s (c0 + off) := by
    intro off hoff hne32
    unfold memW
    rw [hmem_out (BitVec.ofNat 64 (c0 + off))]
    intro addr haddr heq
    have hnat := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (hall_lt addr haddr)] at hnat
    simp only [headAllowedOffsets, List.mem_cons, List.not_mem_nil, or_false] at haddr
    unfold Disj at hdisj; dsimp only at hdisj
    rcases haddr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (rcases hdisj with h | h | h | h <;> omega)
  exact ⟨hmw 16 (by omega) (by omega), hmark, hmw 64 (by omega) (by omega),
    hmw 88 (by omega) (by omega), hcells⟩

theorem fcCreateErrHandler_step {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s) {w_err : BitVec 64}
    (_hw_err : s.locals.lookup (ofString "err") = some (.val (.word w_err)))
    (hnt : (evaluateHOLFiniteState s fcCreateErrHandler).1 ≠ some .timeOut) :
    ((evaluateHOLFiniteState s fcCreateErrHandler).1 = none →
      let post := (evaluateHOLFiniteState s fcCreateErrHandler).2
      EvmInv post ∧
      evmChain post = evmChain s ∧
      OpDispatchSpec.evmR post ≤ OpDispatchSpec.evmR s ∧
      memW post (globN s "cur_cont" + 16) = memW s (globN s "cur_cont" + 16) ∧
      memW post (globN s "cur_cont" + 48) = memW s (globN s "cur_cont" + 48) ∧
      memW post (globN s "cur_cont" + 64) = memW s (globN s "cur_cont" + 64) ∧
      memW post (globN s "cur_cont" + 88) = memW s (globN s "cur_cont" + 88) ∧
      ChainCellsAgree s post ∧
      post.locals = s.locals) ∧
    ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState s fcCreateErrHandler).1 := by
  unfold fcCreateErrHandler at hnt ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  cases hr1 : evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "state_restore") [.var .local (ofString "csnap")]) with
  | mk r1 s1 =>
    rw [hr1] at hnt; dsimp only at hnt ⊢
    obtain ⟨hsr_none, hsr_noerr⟩ :=
      call_state_restore_step (s := s) (args := [.var .local (ofString "csnap")]) hInv
        (by rw [hr1]; intro ht; cases r1 <;> simp at ht; subst ht; exact hnt rfl)
    rw [hr1] at hsr_none hsr_noerr
    rcases r1 with _ | res1
    · dsimp only at hnt hsr_none ⊢
      obtain ⟨hInv1, hch1, hR1, hmark1, hcells1, hu1, hloc1⟩ := hsr_none rfl
      have hhead_s : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
        rw [evmChain_cons]; exact List.mem_cons_self
      obtain ⟨hk1, _, hnac1, hca1⟩ := cur_cont_unhit_keeps_fields hInv (hu1 _ hhead_s).2
      have hcc1 : globN s1 "cur_cont" = globN s "cur_cont" := by
        have hhead1 : (evmChain s1).head? = (evmChain s).head? := congrArg List.head? hch1
        rw [evmChain_cons, evmChain_cons] at hhead1
        simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at hhead1
        exact hhead1.2
      -- Step 2: refill_frame_state_gas
      rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
      cases hr2 : evaluateHOLFiniteState s1
          (.call (some (none, none)) (ofString "refill_frame_state_gas") []) with
      | mk r2 s2 =>
        rw [hr2] at hnt; dsimp only at hnt ⊢
        obtain ⟨_, hr2_none, hr2_err⟩ :=
          call0_outcome_fc (s := s1) (fname := ofString "refill_frame_state_gas") (args := [])
            (by rw [hr2]; intro ht; cases r2 <;> simp at ht; subst ht; exact hnt rfl)
        rw [hr2] at hr2_none hr2_err
        rcases r2 with _ | res2
        · dsimp only at hnt hr2_none ⊢
          obtain ⟨vals2, body2, cal2, ret2, rv2, cpost2, _, hl2, hrun2, hs2_eq⟩ := hr2_none rfl
          have hcode1 : s1.code = originalRuntimeCode := hInv1.1.1.code
          have hcode_lk2 : s1.code.lookup (ofString "refill_frame_state_gas") =
              some ([], sourceFnBody Guest.Software.guestFn_refill_frame_state_gas, .one) := by
            rw [hcode1]; exact lookup_refill_frame_state_gas
          have hbody2 : body2 = sourceFnBody Guest.Software.guestFn_refill_frame_state_gas :=
            lookupCodeHOLFinite_installed_body s1.code.lookup _ _ _ _ _ _ _ _ hcode_lk2 hl2
          subst hbody2
          have hInv_ce2 : EvmInv (callEntryStateHOLFinite s1 cal2) :=
            OpDispatchSpec.localsFree_evmInv s1 cal2 (s1.clock - 1) hInv1
          have hres2 : ResumesR11 (evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal2)
              (sourceFnBody Guest.Software.guestFn_refill_frame_state_gas)).1 := by
            rw [hrun2]; exact Or.inl ⟨rv2, rfl⟩
          obtain ⟨hInv_cp2, hglob_cp2, hch_cp2, hR_cp2⟩ := refill_exec_step hInv_ce2 hres2
          have hmem_cp2 := refill_memory_frame hInv_ce2 hres2
          have hcpost2_eq : (evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal2)
              (sourceFnBody Guest.Software.guestFn_refill_frame_state_gas)).2 = cpost2 := by rw [hrun2]
          rw [hcpost2_eq] at hInv_cp2 hglob_cp2 hch_cp2 hR_cp2 hmem_cp2
          have hInv2 : EvmInv s2 := by
            rw [hs2_eq]; exact OpDispatchSpec.localsFree_evmInv cpost2 s1.locals cpost2.clock hInv_cp2
          have hglob2 : s2.globals = s1.globals := by rw [hs2_eq]; exact hglob_cp2
          have hloc2 : s2.locals = s.locals := by rw [hs2_eq]; exact hloc1
          have hch2 : evmChain s2 = evmChain s1 := by
            rw [hs2_eq]
            exact (evmChain_lc_fc cpost2 s1.locals cpost2.clock).trans
              (hch_cp2.trans (evmChain_lc_fc s1 cal2 (s1.clock - 1)))
          have hR2 : OpDispatchSpec.evmR s2 ≤ OpDispatchSpec.evmR s1 := by
            rw [hs2_eq]
            have h1 : OpDispatchSpec.evmR { cpost2 with locals := s1.locals } = OpDispatchSpec.evmR cpost2 :=
              evmR_lc_fc cpost2 s1.locals cpost2.clock
            have h2 : OpDispatchSpec.evmR (callEntryStateHOLFinite s1 cal2) = OpDispatchSpec.evmR s1 :=
              evmR_lc_fc s1 cal2 (s1.clock - 1)
            have hrr : OpDispatchSpec.evmR cpost2 ≤ OpDispatchSpec.evmR (callEntryStateHOLFinite s1 cal2) := hR_cp2
            omega
          obtain ⟨hk2, hmark2, hnac2, hca2, hcells2⟩ :=
            headAllowed_keeps_cur_cont_fields (s := s1) (post := s2) hInv1
              (fun x hx => by rw [hs2_eq]; exact hmem_cp2 x hx)
          -- Step 3: frame_halt [err]
          rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
          cases hr3 : evaluateHOLFiniteState s2
              (.call (some (none, none)) (ofString "frame_halt") [.var .local (ofString "err")]) with
          | mk r3 s3 =>
            rw [hr3] at hnt; dsimp only at hnt ⊢
            obtain ⟨_, hr3_none, hr3_err⟩ :=
              call0_outcome_fc (s := s2) (fname := ofString "frame_halt")
                (args := [.var .local (ofString "err")])
                (by rw [hr3]; intro ht; cases r3 <;> simp at ht; subst ht; exact hnt rfl)
            rw [hr3] at hr3_none hr3_err
            rcases r3 with _ | res3
            · dsimp only at hnt hr3_none ⊢
              obtain ⟨vals3, body3, cal3, ret3, rv3, cpost3, _, hl3, hrun3, hs3_eq⟩ := hr3_none rfl
              have hcode2 : s2.code = originalRuntimeCode := hInv2.1.1.code
              have hcode_lk3 : s2.code.lookup (ofString "frame_halt") =
                  some ([(ofString "err", .one)], sourceFnBody Guest.Software.guestFn_frame_halt, .one) := by
                rw [hcode2]; exact lookup_frame_halt
              have hbody3 : body3 = sourceFnBody Guest.Software.guestFn_frame_halt :=
                lookupCodeHOLFinite_installed_body s2.code.lookup _ _ _ _ _ _ _ _ hcode_lk3 hl3
              subst hbody3
              have hret3 : ret3 = .one := by
                have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
                  s2.code.lookup (ofString "frame_halt") vals3
                  (sourceFnBody Guest.Software.guestFn_frame_halt) cal3 ret3 hl3
                simp only [Flapjack.lookupCodeHOLExact, hcode_lk3] at hx
                split at hx
                · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
                · cases hx
              subst hret3
              obtain ⟨w_ce_err, hw_ce_err⟩ := one_word_param_of_lookup lookup_frame_halt
                ⟨vals3, by rwa [hcode2] at hl3⟩
              have hInv_ce3 : EvmInv (callEntryStateHOLFinite s2 cal3) :=
                OpDispatchSpec.localsFree_evmInv s2 cal3 (s2.clock - 1) hInv2
              have hres3 : ResumesR11 (evaluateHOLFiniteState (callEntryStateHOLFinite s2 cal3)
                  (sourceFnBody Guest.Software.guestFn_frame_halt)).1 := by
                rw [hrun3]; exact Or.inl ⟨rv3, rfl⟩
              obtain ⟨hInv_cp3, hglob_cp3, hch_cp3, hR_cp3⟩ :=
                frame_halt_exec_step hInv_ce3 hw_ce_err hres3
              have hmem_cp3 := frame_halt_memory_frame hInv_ce3 hw_ce_err hres3
              have hcpost3_eq : (evaluateHOLFiniteState (callEntryStateHOLFinite s2 cal3)
                  (sourceFnBody Guest.Software.guestFn_frame_halt)).2 = cpost3 := by rw [hrun3]
              rw [hcpost3_eq] at hInv_cp3 hglob_cp3 hch_cp3 hR_cp3 hmem_cp3
              have hInv3 : EvmInv s3 := by
                rw [hs3_eq]; exact OpDispatchSpec.localsFree_evmInv cpost3 s2.locals cpost3.clock hInv_cp3
              have hglob3 : s3.globals = s2.globals := by rw [hs3_eq]; exact hglob_cp3
              have hloc3 : s3.locals = s.locals := by rw [hs3_eq]; exact hloc2
              have hch3 : evmChain s3 = evmChain s2 := by
                rw [hs3_eq]
                exact (evmChain_lc_fc cpost3 s2.locals cpost3.clock).trans
                  (hch_cp3.trans (evmChain_lc_fc s2 cal3 (s2.clock - 1)))
              have hR3 : OpDispatchSpec.evmR s3 ≤ OpDispatchSpec.evmR s2 := by
                rw [hs3_eq]
                have h1 : OpDispatchSpec.evmR { cpost3 with locals := s2.locals } = OpDispatchSpec.evmR cpost3 :=
                  evmR_lc_fc cpost3 s2.locals cpost3.clock
                have h2 : OpDispatchSpec.evmR (callEntryStateHOLFinite s2 cal3) = OpDispatchSpec.evmR s2 :=
                  evmR_lc_fc s2 cal3 (s2.clock - 1)
                have hrr : OpDispatchSpec.evmR cpost3 ≤ OpDispatchSpec.evmR (callEntryStateHOLFinite s2 cal3) := hR_cp3
                omega
              obtain ⟨hk3, hmark3, hnac3, hca3, hcells3⟩ :=
                headAllowed_keeps_cur_cont_fields (s := s2) (post := s3) hInv2
                  (fun x hx => by rw [hs3_eq]; exact hmem_cp3 x hx)
              -- Step 4 & 5: store(ev+120, evm_empty); store(ev+128, 0)
              rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
              cases hr4 : evaluateHOLFiniteState s3
                  (.store (.op .add [.var .global (ofString "ev"), .const 120#64])
                    (.var .global (ofString "evm_empty"))) with
              | mk r4 s4 =>
                rw [hr4] at hnt; dsimp only at hnt ⊢
                rcases r4 with _ | res4
                · dsimp only at hnt ⊢
                  cases hr5 : evaluateHOLFiniteState s4
                      (.store (.op .add [.var .global (ofString "ev"), .const 128#64])
                        (.const 0#64)) with
                  | mk r5 s5 =>
                    rw [hr5] at hnt; dsimp only at hnt ⊢
                    rcases r5 with _ | res5
                    · obtain ⟨he_lt3, _, ⟨evw3, hevw3_lk, hevw3_nat⟩, _, _⟩ := evm_head_globals hInv3
                      obtain ⟨w_emp3, hw_emp3⟩ := hInv3.1.2.2.2.2.2.2.2.2.2 "evm_empty" (by decide)
                      obtain ⟨w120, _, hs4_eq⟩ :=
                        InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.store_global_off_word
                          (t := s3) (post := s4) (gname := "ev") (gbase := globN s3 "ev") (off := 120)
                          hevw3_lk hevw3_nat (by omega)
                          (fun v0 hv0 => by
                            change s3.globals.lookup (ofString "evm_empty") = some v0 at hv0
                            unfold GlobalWord at hw_emp3
                            rw [hw_emp3] at hv0; injection hv0 with hv'; exact ⟨w_emp3, hv'.symm⟩) hr4
                      obtain ⟨w128, _, hs5_eq⟩ :=
                        InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.store_global_off_word
                          (t := s4) (post := s5) (gname := "ev") (gbase := globN s3 "ev") (off := 128)
                          (by rw [hs4_eq]; exact hevw3_lk) hevw3_nat (by omega)
                          (fun v0 hv0 => by simp [evalHOLExact] at hv0; exact ⟨0, hv0.symm⟩) hr5
                      have hGp5 : GuestInv s5 := by
                        rw [hs5_eq, hs4_eq]; exact guestInv_congr (s := s3) rfl rfl rfl rfl hInv3.1.1
                      have hglob5 : s5.globals = s3.globals := by rw [hs5_eq, hs4_eq]
                      have hbe5 : s5.be = s3.be := by rw [hs5_eq, hs4_eq]
                      have hloc5 : s5.locals = s.locals := by rw [hs5_eq, hs4_eq]; exact hloc3
                      have hmem5 : ∀ x : BitVec 64,
                          (∀ addr ∈ headAllowedOffsets (globN s3 "ev") (globN s3 "cur_cont"),
                            x ≠ BitVec.ofNat 64 addr) →
                          s5.memory x = s3.memory x := by
                        intro x hx
                        rw [hs5_eq, hs4_eq]
                        have hn120 : x ≠ BitVec.ofNat 64 (globN s3 "ev" + 120) := hx _ (by simp [headAllowedOffsets])
                        have hn128 : x ≠ BitVec.ofNat 64 (globN s3 "ev" + 128) := hx _ (by simp [headAllowedOffsets])
                        simp [InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.updW, hn120, hn128]
                      have hgas5 : memW s5 (globN s3 "ev" + 64) + memW s5 (globN s3 "ev" + 192) ≤
                          memW s3 (globN s3 "ev" + 64) + memW s3 (globN s3 "ev" + 192) := by
                        rw [hs5_eq,
                          InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.memW_updW_ne s4 _ _ w128 (by omega) (by omega) (by omega),
                          InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.memW_updW_ne s4 _ _ w128 (by omega) (by omega) (by omega),
                          hs4_eq,
                          InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.memW_updW_ne s3 _ _ w120 (by omega) (by omega) (by omega),
                          InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.memW_updW_ne s3 _ _ w120 (by omega) (by omega) (by omega)]
                      obtain ⟨hInv5, hch5, hR5⟩ :=
                        evmInv_of_head_status_gas_update hInv3 hGp5 hglob5 hbe5 hmem5 hgas5
                      obtain ⟨hk5, hmark5, hnac5, hca5, hcells5⟩ :=
                        headAllowed_keeps_cur_cont_fields (s := s3) (post := s5) hInv3 hmem5
                      have hcc2 : globN s2 "cur_cont" = globN s1 "cur_cont" := by simp [globN, hglob2]
                      have hcc3 : globN s3 "cur_cont" = globN s2 "cur_cont" := by simp [globN, hglob3]
                      rw [hcc3, hcc2, hcc1] at hk5 hmark5 hnac5 hca5
                      rw [hcc2, hcc1] at hk3 hmark3 hnac3 hca3
                      rw [hcc1] at hk2 hmark2 hnac2 hca2
                      have hR5' : OpDispatchSpec.evmR s5 ≤ OpDispatchSpec.evmR s3 := hR5
                      refine ⟨fun _ => ⟨hInv5,
                        hch5.trans (hch3.trans (hch2.trans hch1)),
                        by omega,
                        hk5.trans (hk3.trans (hk2.trans hk1)),
                        hmark5.trans (hmark3.trans (hmark2.trans hmark1)),
                        hnac5.trans (hnac3.trans (hnac2.trans hnac1)),
                        hca5.trans (hca3.trans (hca2.trans hca1)),
                        chainCellsAgree_trans
                          (chainCellsAgree_trans (chainCellsAgree_trans hcells1 hch1 hcells2)
                            (hch2.trans hch1) hcells3)
                          (hch3.trans (hch2.trans hch1)) hcells5,
                        hloc5⟩, by simp [OpDispatchSpec.IsEvmErr]⟩
                    · refine ⟨(fun h => by cases h), ?_⟩
                      rintro ⟨v, hv⟩
                      exact store_res_not_resumes_r11 hr5 (Or.inr ⟨ofString "EvmErr", v, hv, by decide⟩)
                · dsimp only
                  refine ⟨(fun h => by cases h), ?_⟩
                  rintro ⟨v, hv⟩
                  exact store_res_not_resumes_r11 hr4 (Or.inr ⟨ofString "EvmErr", v, hv, by decide⟩)
            · dsimp only
              refine ⟨(fun h => by cases h), ?_⟩
              intro herr3
              obtain ⟨vals3, body3, cal3, ret3, rv3, cpost3, _, hl3, hrun3, _⟩ := hr3_err herr3
              have hcode2 : s2.code = originalRuntimeCode := hInv2.1.1.code
              have hcode_lk3 : s2.code.lookup (ofString "frame_halt") =
                  some ([(ofString "err", .one)], sourceFnBody Guest.Software.guestFn_frame_halt, .one) := by
                rw [hcode2]; exact lookup_frame_halt
              have hbody3 : body3 = sourceFnBody Guest.Software.guestFn_frame_halt :=
                lookupCodeHOLFinite_installed_body s2.code.lookup _ _ _ _ _ _ _ _ hcode_lk3 hl3
              subst hbody3
              exact InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue.evaluate_noCatchableRaise
                (fun _ => false) (fun _ h => by cases h)
                (sourceFnBody Guest.Software.guestFn_frame_halt) rfl
                (callEntryStateHOLFinite s2 cal3) hcode2
                (ofString "EvmErr") rv3 (by decide) (by rw [hrun3])
        · dsimp only
          refine ⟨(fun h => by cases h), ?_⟩
          intro herr2
          obtain ⟨vals2, body2, cal2, ret2, rv2, cpost2, _, hl2, hrun2, _⟩ := hr2_err herr2
          have hcode1 : s1.code = originalRuntimeCode := hInv1.1.1.code
          have hcode_lk2 : s1.code.lookup (ofString "refill_frame_state_gas") =
              some ([], sourceFnBody Guest.Software.guestFn_refill_frame_state_gas, .one) := by
            rw [hcode1]; exact lookup_refill_frame_state_gas
          have hbody2 : body2 = sourceFnBody Guest.Software.guestFn_refill_frame_state_gas :=
            lookupCodeHOLFinite_installed_body s1.code.lookup _ _ _ _ _ _ _ _ hcode_lk2 hl2
          subst hbody2
          exact InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue.evaluate_noCatchableRaise
            (fun _ => false) (fun _ h => by cases h)
            (sourceFnBody Guest.Software.guestFn_refill_frame_state_gas) rfl
            (callEntryStateHOLFinite s1 cal2) hcode1
            (ofString "EvmErr") rv2 (by decide) (by rw [hrun2])
    · dsimp only
      exact ⟨(fun h => by cases h), hsr_noerr⟩

theorem fcEntryLocals_resVarEq {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {nm : MlS} {saved : Option (ValueHOL 64)}
    (h1 : ofString "rec" ≠ nm) (h2 : ofString "child" ≠ nm) (h3 : ofString "parent" ≠ nm)
    (h4 : ofString "kind" ≠ nm) (h5 : ofString "msg" ≠ nm)
    (h6 : ofString "new_account_charged" ≠ nm) (h7 : ofString "child_mark" ≠ nm)
    (h8 : ofString "child_mem_mark" ≠ nm) (h9 : ofString "out_start" ≠ nm)
    (h10 : ofString "out_size" ≠ nm) (h11 : ofString "contract_address" ≠ nm)
    (h : FcEntryLocals s0 s) :
    FcEntryLocals s0 { s with locals := s.locals.resVarEq (nm, saved) } := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only; rw [PanRunBounded.resVarEq_lookup, if_neg h1]; exact r1
  · dsimp only; rw [PanRunBounded.resVarEq_lookup, if_neg h2]; exact r2
  · dsimp only; rw [PanRunBounded.resVarEq_lookup, if_neg h3]; exact r3
  · dsimp only; rw [PanRunBounded.resVarEq_lookup, if_neg h4]; exact r4
  · dsimp only; rw [PanRunBounded.resVarEq_lookup, if_neg h5]; exact r5
  · dsimp only; rw [PanRunBounded.resVarEq_lookup, if_neg h6]; exact r6
  · dsimp only; rw [PanRunBounded.resVarEq_lookup, if_neg h7]; exact r7
  · dsimp only; rw [PanRunBounded.resVarEq_lookup, if_neg h8]; exact r8
  · dsimp only; rw [PanRunBounded.resVarEq_lookup, if_neg h9]; exact r9
  · dsimp only; rw [PanRunBounded.resVarEq_lookup, if_neg h10]; exact r10
  · dsimp only; rw [PanRunBounded.resVarEq_lookup, if_neg h11]; exact r11

theorem fcEntryLocals_setVar {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {nm : MlS} {v : ValueHOL 64}
    (h1 : nm ≠ ofString "rec") (h2 : nm ≠ ofString "child") (h3 : nm ≠ ofString "parent")
    (h4 : nm ≠ ofString "kind") (h5 : nm ≠ ofString "msg")
    (h6 : nm ≠ ofString "new_account_charged") (h7 : nm ≠ ofString "child_mark")
    (h8 : nm ≠ ofString "child_mem_mark") (h9 : nm ≠ ofString "out_start")
    (h10 : nm ≠ ofString "out_size") (h11 : nm ≠ ofString "contract_address")
    (h : FcEntryLocals s0 s) :
    FcEntryLocals s0 (setVarHOLFinite nm v s) := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]; split
     · rename_i heq; have heq' := beq_iff_eq.mp heq
       first | exact absurd heq' h1 | exact absurd heq' h2 | exact absurd heq' h3 |
         exact absurd heq' h4 | exact absurd heq' h5 | exact absurd heq' h6 |
         exact absurd heq' h7 | exact absurd heq' h8 | exact absurd heq' h9 |
         exact absurd heq' h10 | exact absurd heq' h11
     · assumption)

private theorem ev_word_of_valid_err {F : Type}
    {s : PanSemStateFiniteExact 64 F} {ev : ValueHOL 64}
    (herr_lk : s.locals.lookup (ofString "err") = some (.val (.word 0#64)))
    (hv2 : isValidValueHOLExact s.toExact .local (ofString "err") ev = true) :
    ∃ w_ev : BitVec 64, ev = .val (.word w_ev) := by
  simp only [isValidValueHOLExact, lookupKvarHOLExact, herr_lk, shapeOfHOLExact] at hv2
  cases ev with
  | val v0 =>
    cases v0 with
    | word w => exact ⟨w, rfl⟩
  | rStruct _ => simp [shapeOfHOLExact, shapeEqHOL] at hv2
  | nStruct _ _ => simp [shapeOfHOLExact, shapeEqHOL] at hv2

theorem callHandle0_outcome_fc {F : Type} {s : PanSemStateFiniteExact 64 F}
    {exn var : MlS} {handler : ProgHOL 64} {fname : MlS} {args : List (ExpHOL 64)}
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, some (exn, var, handler))) fname args)).1 ≠ some .timeOut) :
    let run := evaluateHOLFiniteState s
      (.call (some (none, some (exn, var, handler))) fname args)
    (run.1 = none →
      (∃ values body callee ret rv cpost,
        evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
        lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) ∧
        evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned rv), cpost) ∧
        run.2 = { cpost with locals := s.locals }) ∨
      (∃ values body callee ret ev cpost,
        evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
        lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) ∧
        evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
          (some (.exception exn ev), cpost) ∧
        isValidValueHOLExact s.toExact .local var ev = true ∧
        let resumed := setVarHOLFinite var ev { cpost with locals := s.locals }
        (evaluateHOLFiniteState resumed handler).1 = none ∧
        run.2 = (evaluateHOLFiniteState resumed handler).2)) ∧
    (OpDispatchSpec.IsEvmErr run.1 →
      (exn ≠ ofString "EvmErr" ∧
        ∃ values body callee ret ev cpost,
          evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
          lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) ∧
          evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
            (some (.exception (ofString "EvmErr") ev), cpost) ∧
          run.2 = emptyLocalsHOLFinite cpost) ∨
      (∃ values body callee ret ev cpost,
        evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
        lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) ∧
        evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
          (some (.exception exn ev), cpost) ∧
        isValidValueHOLExact s.toExact .local var ev = true ∧
        let resumed := setVarHOLFinite var ev { cpost with locals := s.locals }
        (evaluateHOLFiniteState resumed handler).1 ≠ some .timeOut ∧
        OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState resumed handler).1 ∧
        run.2 = (evaluateHOLFiniteState resumed handler).2)) := by
  dsimp only
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · exact ⟨(fun h => by cases h), by simp [OpDispatchSpec.IsEvmErr]⟩
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, ret⟩
    · exact ⟨(fun h => by cases h), by simp [OpDispatchSpec.IsEvmErr]⟩
    · simp only [hl] at hnt ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, cpost⟩
        simp only [hrun] at hnt ⊢
        rcases res with _ | r
        · exact ⟨(fun h => by cases h), by simp [OpDispatchSpec.IsEvmErr]⟩
        · cases r with
          | timeOut => simp at hnt
          | returned rv =>
            dsimp only at hnt ⊢
            split
            · exact ⟨fun _ => Or.inl ⟨values, body, callee, ret, rv, cpost, rfl, hl, hrun, rfl⟩,
                by simp [OpDispatchSpec.IsEvmErr]⟩
            · exact ⟨(fun h => by cases h), by simp [OpDispatchSpec.IsEvmErr]⟩
          | exception eid ev =>
            dsimp only at hnt ⊢
            by_cases hid : eid = exn
            · subst hid
              simp only [↓reduceIte] at hnt ⊢
              rcases hsh : s.eshapes.lookup eid with _ | esh
              · exact ⟨(fun h => by cases h), by simp [OpDispatchSpec.IsEvmErr]⟩
              · simp only [hsh] at hnt ⊢
                by_cases hv : (shapeEqHOL (shapeOfHOLExact ev) esh &&
                    isValidValueHOLExact s.toExact .local var ev) = true
                · simp only [hv, ↓reduceIte] at hnt ⊢
                  have hv2 : isValidValueHOLExact s.toExact .local var ev = true :=
                    ((Bool.and_eq_true _ _).mp hv).2
                  exact ⟨fun hn => Or.inr ⟨values, body, callee, ret, ev, cpost, rfl, hl, hrun, hv2, hn, rfl⟩,
                    fun he => Or.inr ⟨values, body, callee, ret, ev, cpost, rfl, hl, hrun, hv2, hnt, he, rfl⟩⟩
                · simp only [hv, Bool.false_eq_true, ↓reduceIte]
                  exact ⟨(fun h => by cases h), by simp [OpDispatchSpec.IsEvmErr]⟩
            · simp only [hid, ↓reduceIte]
              refine ⟨(fun h => by cases h), ?_⟩
              rintro ⟨v', hv'⟩
              injection hv' with hr'
              injection hr' with heid hv_eq
              subst heid hv_eq
              exact Or.inl ⟨fun h => hid h.symm,
                values, body, callee, ret, ev, cpost, rfl, hl, hrun, rfl⟩
          | _ =>
            dsimp only
            exact ⟨(fun h => by cases h), by simp [OpDispatchSpec.IsEvmErr]⟩

theorem call_create_finish_handled_step (hCF : CreateFinishSpecs) {F : Type}
    {s0 s_er : PanSemStateFiniteExact 64 F}
    {handler : ProgHOL 64}
    (hh_step : ∀ {s : PanSemStateFiniteExact 64 F} {w_err : BitVec 64},
      EvmInv s →
      s.locals.lookup (ofString "err") = some (.val (.word w_err)) →
      (evaluateHOLFiniteState s handler).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState s handler).1 = none →
        let post := (evaluateHOLFiniteState s handler).2
        EvmInv post ∧
        evmChain post = evmChain s ∧
        OpDispatchSpec.evmR post ≤ OpDispatchSpec.evmR s ∧
        memW post (globN s "cur_cont" + 16) = memW s (globN s "cur_cont" + 16) ∧
        memW post (globN s "cur_cont" + 48) = memW s (globN s "cur_cont" + 48) ∧
        memW post (globN s "cur_cont" + 64) = memW s (globN s "cur_cont" + 64) ∧
        memW post (globN s "cur_cont" + 88) = memW s (globN s "cur_cont" + 88) ∧
        ChainCellsAgree s post ∧
        post.locals = s.locals) ∧
      ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState s handler).1)
    (hInv_er : EvmInv s_er)
    (hch_er : evmChain s_er = evmChain s0)
    (hR_er : OpDispatchSpec.evmR s_er ≤ OpDispatchSpec.evmR s0)
    (hmark_er : memW s_er (globN s0 "cur_cont" + 48) = memW s0 (globN s0 "cur_cont" + 48))
    (hcells_er : ChainCellsAgree s0 s_er)
    (hlocs_er : FcEntryLocals s0 s_er)
    (herr_lk : s_er.locals.lookup (ofString "err") = some (.val (.word 0#64)))
    (hkind_val : memW s0 (globN s0 "cur_cont" + 16) = 2)
    (hnt : (evaluateHOLFiniteState s_er
      (.call (some (none, some (ofString "EvmErr", ofString "err", handler)))
        (ofString "create_finish")
        [.var .local (ofString "msg"), .var .local (ofString "child")])).1 ≠ some .timeOut) :
    let run := evaluateHOLFiniteState s_er
      (.call (some (none, some (ofString "EvmErr", ofString "err", handler)))
        (ofString "create_finish")
        [.var .local (ofString "msg"), .var .local (ofString "child")])
    (run.1 = none → PreludeRel s0 run.2) ∧
    (OpDispatchSpec.IsEvmErr run.1 →
      EvmInv run.2 ∧ evmChain run.2 = evmChain s0 ∧
      OpDispatchSpec.evmR run.2 ≤ OpDispatchSpec.evmR s0 ∧
      ChainCellsAgree s0 run.2) := by
  have hcc_er : globN s_er "cur_cont" = globN s0 "cur_cont" := by
    have hhead : (evmChain s_er).head? = (evmChain s0).head? := congrArg List.head? hch_er
    rw [evmChain_cons, evmChain_cons] at hhead
    simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at hhead
    exact hhead.2
  obtain ⟨cf_params, cf_body, cf_ret, hcf_lk, hcf_spec⟩ := create_finish_specs_of hCF
  have hcode_er : s_er.code = originalRuntimeCode := hInv_er.1.1.code
  have hcallee_post : ∀ values body callee ret res cpost,
      lookupCodeHOLFinite s_er.code.lookup (ofString "create_finish") values =
        some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s_er callee) body = (res, cpost) →
      res ≠ some .timeOut →
      InitECandidate.Solver.Wave8Contracts.M23.Resumes res →
      EvmInv cpost ∧ evmChain cpost = evmChain s0 ∧
      OpDispatchSpec.evmR cpost ≤ OpDispatchSpec.evmR s0 ∧
      memW cpost (globN s0 "cur_cont" + 48) = memW s0 (globN s0 "cur_cont" + 48) ∧
      ChainCellsAgree s0 cpost := by
    intro values body callee ret res cpost hl hrun hsafe hres
    have hcf_lk' : s_er.code.lookup (ofString "create_finish") =
        some (cf_params, cf_body, cf_ret) := by rw [hcode_er]; exact hcf_lk
    have hbody_eq : body = cf_body :=
      lookupCodeHOLFinite_installed_body s_er.code.lookup _ _ _ _ _ _ _ _ hcf_lk' hl
    have hret_eq : ret = cf_ret := by
      have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
        s_er.code.lookup (ofString "create_finish") values body callee ret hl
      simp only [Flapjack.lookupCodeHOLExact, hcf_lk'] at hx
      split at hx
      · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
      · cases hx
    have hInv_ce : EvmInv (callEntryStateHOLFinite s_er callee) :=
      OpDispatchSpec.localsFree_evmInv s_er callee (s_er.clock - 1) hInv_er
    have hAv_ce : EvmAvoids createBuffers (callEntryStateHOLFinite s_er callee) :=
      evmAvoids_createBuffers_of_evmInv _ hInv_ce
    have hex_ce : ∃ vals, lookupCodeHOLFinite originalRuntimeCode.lookup
        (ofString "create_finish") vals =
          some (cf_body, (callEntryStateHOLFinite s_er callee).locals, cf_ret) :=
      ⟨values, by rw [← hcode_er, ← hbody_eq, ← hret_eq]; exact hl⟩
    have hrun_cf : evaluateHOLFiniteState (callEntryStateHOLFinite s_er callee) cf_body = (res, cpost) := by
      rw [← hbody_eq]; exact hrun
    have hsp := hcf_spec (callEntryStateHOLFinite s_er callee) hcode_er hAv_ce hex_ce
      (by rw [hrun_cf]; exact hsafe) (by rw [hrun_cf]; exact hres)
    rw [hrun_cf] at hsp
    dsimp only at hsp
    obtain ⟨⟨hIp, _, _, hch_cp⟩, hR_cp, hmark_cp, hcells_cp⟩ := hsp
    have hch_ce : evmChain (callEntryStateHOLFinite s_er callee) = evmChain s_er :=
      evmChain_lc_fc s_er callee (s_er.clock - 1)
    have hR_ce : OpDispatchSpec.evmR (callEntryStateHOLFinite s_er callee) = OpDispatchSpec.evmR s_er :=
      evmR_lc_fc s_er callee (s_er.clock - 1)
    rw [show globN (callEntryStateHOLFinite s_er callee) "cur_cont" = globN s0 "cur_cont" from hcc_er] at hmark_cp
    exact ⟨hIp, hch_cp.trans (hch_ce.trans hch_er), by omega, hmark_cp.trans hmark_er,
      chainCellsAgree_trans hcells_er hch_er (fun ec hec => hcells_cp ec (hch_ce.symm ▸ hec))⟩
  obtain ⟨hout_none, hout_err⟩ := callHandle0_outcome_fc hnt
  dsimp only at hout_none hout_err ⊢
  constructor
  · intro hn
    rcases hout_none hn with
      ⟨values, body, callee, ret, rv, cpost, _, hl, hrun, hp_eq⟩ |
      ⟨values, body, callee, ret, ev, cpost, _, hl, hrun, hv2, hh_hn, hp_eq⟩
    · obtain ⟨hIp, hch_cp, hR_cp, hmark_cp, hcells_cp⟩ :=
        hcallee_post values body callee ret (some (.returned rv)) cpost hl hrun
          (by simp) (Or.inl ⟨rv, rfl⟩)
      rw [hp_eq]
      let p_ret := { cpost with locals := s_er.locals }
      have hInv_ret : EvmInv p_ret :=
        OpDispatchSpec.localsFree_evmInv cpost s_er.locals cpost.clock hIp
      have hch_ret : evmChain p_ret = evmChain s0 :=
        (evmChain_lc_fc cpost s_er.locals cpost.clock).trans hch_cp
      have hR_ret : OpDispatchSpec.evmR p_ret ≤ OpDispatchSpec.evmR s0 := by
        have h1 : OpDispatchSpec.evmR p_ret = OpDispatchSpec.evmR cpost :=
          evmR_lc_fc cpost s_er.locals cpost.clock
        omega
      have hlocs_ret : FcEntryLocals s0 p_ret :=
        fcEntryLocals_congr_locals (s1 := s_er) (s2 := p_ret) rfl hlocs_er
      exact ⟨hInv_ret, hch_ret, hR_ret, hmark_cp, hcells_cp,
        fun hne => absurd hkind_val hne, hlocs_ret⟩
    · obtain ⟨w_ev, rfl⟩ := ev_word_of_valid_err herr_lk hv2
      obtain ⟨hIp, hch_cp, hR_cp, hmark_cp, hcells_cp⟩ :=
        hcallee_post values body callee ret (some (.exception (ofString "EvmErr") (.val (.word w_ev))))
          cpost hl hrun (by simp)
          (Or.inr ⟨ofString "EvmErr", .val (.word w_ev), rfl, by decide⟩)
      set hst := setVarHOLFinite (ofString "err") (.val (.word w_ev))
        { cpost with locals := s_er.locals }
      have hInv_hst : EvmInv hst :=
        OpDispatchSpec.localsFree_evmInv cpost hst.locals cpost.clock hIp
      have hw_err_hst : hst.locals.lookup (ofString "err") = some (.val (.word w_ev)) := by
        simp [hst, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hnt_h : (evaluateHOLFiniteState hst handler).1 ≠ some .timeOut := by
        rw [hh_hn]; simp
      obtain ⟨hh_none, _⟩ := hh_step hInv_hst hw_err_hst hnt_h
      obtain ⟨hInv_hp, hch_hp, hR_hp, _, hmark_hp, _, _, hcells_hp, hloc_hp⟩ := hh_none hh_hn
      have hch_hst : evmChain hst = evmChain s0 :=
        (evmChain_lc_fc cpost hst.locals cpost.clock).trans hch_cp
      have hR_hst : OpDispatchSpec.evmR hst = OpDispatchSpec.evmR cpost :=
        evmR_lc_fc cpost hst.locals cpost.clock
      have hcc_hst : globN hst "cur_cont" = globN s0 "cur_cont" := by
        have hhead : (evmChain hst).head? = (evmChain s0).head? := congrArg List.head? hch_hst
        rw [evmChain_cons, evmChain_cons] at hhead
        simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at hhead
        exact hhead.2
      rw [hcc_hst] at hmark_hp
      have hlocs_hst : FcEntryLocals s0 hst :=
        fcEntryLocals_setVar (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (fcEntryLocals_congr_locals (s1 := s_er) (s2 := { cpost with locals := s_er.locals }) rfl hlocs_er)
      have hlocs_hp : FcEntryLocals s0 (evaluateHOLFiniteState hst handler).2 :=
        fcEntryLocals_congr_locals hloc_hp hlocs_hst
      have hcells_hst_ph : ChainCellsAgree cpost (evaluateHOLFiniteState hst handler).2 := by
        intro ec hec
        have hch_eq : evmChain hst = evmChain cpost := evmChain_lc_fc cpost hst.locals cpost.clock
        exact hcells_hp ec (hch_eq.symm ▸ hec)
      rw [hp_eq]
      exact ⟨hInv_hp, hch_hp.trans hch_hst, by omega, hmark_hp.trans hmark_cp,
        chainCellsAgree_trans hcells_cp hch_cp hcells_hst_ph,
        fun hne => absurd hkind_val hne, hlocs_hp⟩
  · intro herr
    rcases hout_err herr with ⟨hne, _⟩ | ⟨values, body, callee, ret, ev, cpost, _, hl, hrun, hv2, hnt_h, he_h, _⟩
    · exact absurd rfl hne
    · obtain ⟨w_ev, rfl⟩ := ev_word_of_valid_err herr_lk hv2
      obtain ⟨hIp, _, _, _, _⟩ :=
        hcallee_post values body callee ret (some (.exception (ofString "EvmErr") (.val (.word w_ev))))
          cpost hl hrun (by simp)
          (Or.inr ⟨ofString "EvmErr", .val (.word w_ev), rfl, by decide⟩)
      set hst := setVarHOLFinite (ofString "err") (.val (.word w_ev))
        { cpost with locals := s_er.locals }
      have hInv_hst : EvmInv hst :=
        OpDispatchSpec.localsFree_evmInv cpost hst.locals cpost.clock hIp
      have hw_err_hst : hst.locals.lookup (ofString "err") = some (.val (.word w_ev)) := by
        simp [hst, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      obtain ⟨_, hh_noerr⟩ := hh_step hInv_hst hw_err_hst hnt_h
      exact False.elim (hh_noerr he_h)

theorem prelude_dec_word_step {F : Type}
    {s0 t : PanSemStateFiniteExact 64 F}
    {nm : MlS} {e : ExpHOL 64} {w : BitVec 64} {p : ProgHOL 64}
    (h1 : ofString "rec" ≠ nm) (h2 : ofString "child" ≠ nm) (h3 : ofString "parent" ≠ nm)
    (h4 : ofString "kind" ≠ nm) (h5 : ofString "msg" ≠ nm)
    (h6 : ofString "new_account_charged" ≠ nm) (h7 : ofString "child_mark" ≠ nm)
    (h8 : ofString "child_mem_mark" ≠ nm) (h9 : ofString "out_start" ≠ nm)
    (h10 : ofString "out_size" ≠ nm) (h11 : ofString "contract_address" ≠ nm)
    (hev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e =
      some (.val (.word w)))
    (hnt : (evaluateHOLFiniteState t (.dec nm .one e p)).1 ≠ some .timeOut)
    (hbody : (evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) t) p).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) t) p).1 = none →
        PreludeRel s0 (evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) t) p).2) ∧
      (OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) t) p).1 →
        EvmInv (evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) t) p).2 ∧
        evmChain (evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) t) p).2 = evmChain s0 ∧
        OpDispatchSpec.evmR (evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) t) p).2 ≤
          OpDispatchSpec.evmR s0 ∧
        ChainCellsAgree s0 (evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) t) p).2)) :
    ((evaluateHOLFiniteState t (.dec nm .one e p)).1 = none →
      PreludeRel s0 (evaluateHOLFiniteState t (.dec nm .one e p)).2) ∧
    (OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState t (.dec nm .one e p)).1 →
      EvmInv (evaluateHOLFiniteState t (.dec nm .one e p)).2 ∧
      evmChain (evaluateHOLFiniteState t (.dec nm .one e p)).2 = evmChain s0 ∧
      OpDispatchSpec.evmR (evaluateHOLFiniteState t (.dec nm .one e p)).2 ≤
        OpDispatchSpec.evmR s0 ∧
      ChainCellsAgree s0 (evaluateHOLFiniteState t (.dec nm .one e p)).2) := by
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  rw [hev] at hnt ⊢
  dsimp only at hnt ⊢
  have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  rw [if_pos hsh] at hnt ⊢
  dsimp only at hnt ⊢
  obtain ⟨hb_none, hb_err⟩ := hbody hnt
  set p_in := (evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) t) p).2
  let L_out := HolFiniteMapExact.resVarEq p_in.locals (nm, t.locals.lookup nm)
  let p_out : PanSemStateFiniteExact 64 F := { p_in with locals := L_out }
  have hp_mem : p_out.memory = p_in.memory := rfl
  have hp_glob : p_out.globals = p_in.globals := rfl
  have hch_po : evmChain p_out = evmChain p_in :=
    OpDispatchSpec.evmChain_congr hp_mem hp_glob
  have hR_po : OpDispatchSpec.evmR p_out = OpDispatchSpec.evmR p_in :=
    R14Shards.OpHandlersA.evmR_eq_of_chain_and_words hch_po
      (fun _ _ => ⟨rfl, rfl⟩)
  constructor
  · intro hn
    obtain ⟨hIp, hchp, hRp, hmarkp, hcellsp, houtp, hlocsp⟩ := hb_none hn
    have hInv_out : EvmInv p_out := OpDispatchSpec.localsFree_evmInv p_in L_out p_in.clock hIp
    have hlocs_out : FcEntryLocals s0 p_out :=
      fcEntryLocals_resVarEq h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hlocsp
    exact ⟨hInv_out, hch_po.trans hchp, hR_po.le.trans hRp, hmarkp, hcellsp, houtp, hlocs_out⟩
  · intro herr
    obtain ⟨hIp, hchp, hRp, hcellsp⟩ := hb_err herr
    have hInv_out : EvmInv p_out := OpDispatchSpec.localsFree_evmInv p_in L_out p_in.clock hIp
    exact ⟨hInv_out, hch_po.trans hchp, hR_po.le.trans hRp, hcellsp⟩

private theorem eval_cmp_equal_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e1 e2 : ExpHOL 64) (w1 w2 : BitVec 64)
    (h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 =
      some (.val (.word w1)))
    (h2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 =
      some (.val (.word w2))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal e1 e2) =
      some (.val (.word (if w1 = w2 then 1#64 else 0#64))) := by
  simp only [evalHOLExact, h1, h2, Compiler.Encoders.Asm.wordCmpHOL]
  by_cases h : w1 = w2 <;> simp [h]

theorem fcPrelude_kind2_csnap_step (hCF : CreateFinishSpecs) {F : Type}
    {s0 s1 s_cs : PanSemStateFiniteExact 64 F}
    (_hInv1 : EvmInv s1)
    (hch1 : evmChain s1 = evmChain s0)
    (hR1 : OpDispatchSpec.evmR s1 ≤ OpDispatchSpec.evmR s0)
    (hmark1 : memW s1 (globN s0 "cur_cont" + 48) = memW s0 (globN s0 "cur_cont" + 48))
    (hcells1 : ChainCellsAgree s0 s1)
    (hcc1 : globN s1 "cur_cont" = globN s0 "cur_cont" ∧ globN s1 "ev" = globN s0 "ev")
    (he1_lt : globN s1 "ev" + 280 ≤ 2 ^ 64)
    (he1_wok : WordsOK s1 (globN s1 "ev", 280))
    (hkind_val : memW s0 (globN s0 "cur_cont" + 16) = 2)
    (hs_cs : s_cs.memory = s1.memory ∧ s_cs.globals = s1.globals ∧
      s_cs.memaddrs = s1.memaddrs ∧ s_cs.be = s1.be ∧ s_cs.shMemaddrs = s1.shMemaddrs ∧
      s_cs.structs = s1.structs ∧ s_cs.eshapes = s1.eshapes ∧ s_cs.code = s1.code ∧
      s_cs.baseAddr = s1.baseAddr ∧ s_cs.topAddr = s1.topAddr ∧ s_cs.ffi = s1.ffi)
    (hInv_cs : EvmInv s_cs)
    (hlocs_cs : FcEntryLocals s0 s_cs)
    (hnt_cs : (evaluateHOLFiniteState s_cs
      (.ite
        (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 160#64])) (.const 0#64))
        (.dec (ofString "err") .one (.const 0#64)
          (.call (some (none, some (ofString "EvmErr", ofString "err", fcCreateErrHandler)))
            (ofString "create_finish") [.var .local (ofString "msg"), .var .local (ofString "child")]))
        (.call (some (none, none)) (ofString "state_restore") [.var .local (ofString "csnap")]))).1 ≠ some .timeOut) :
    let run := evaluateHOLFiniteState s_cs
      (.ite
        (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 160#64])) (.const 0#64))
        (.dec (ofString "err") .one (.const 0#64)
          (.call (some (none, some (ofString "EvmErr", ofString "err", fcCreateErrHandler)))
            (ofString "create_finish") [.var .local (ofString "msg"), .var .local (ofString "child")]))
        (.call (some (none, none)) (ofString "state_restore") [.var .local (ofString "csnap")]))
    (run.1 = none → PreludeRel s0 run.2) ∧
    (OpDispatchSpec.IsEvmErr run.1 →
      EvmInv run.2 ∧ evmChain run.2 = evmChain s0 ∧
      OpDispatchSpec.evmR run.2 ≤ OpDispatchSpec.evmR s0 ∧
      ChainCellsAgree s0 run.2) := by
  dsimp only
  have hchild_cs : s_cs.locals.lookup (ofString "child") =
      some (.val (.word (BitVec.ofNat 64 (globN s1 "ev")))) := by
    rw [hcc1.2]; exact hlocs_cs.child_lk
  have he1_cs_wok : WordsOK s_cs (globN s1 "ev", 280) := by
    refine ⟨he1_wok.1, he1_wok.2.1, fun k hk => ?_⟩
    obtain ⟨w, hd, hm⟩ := he1_wok.2.2 k hk
    exact ⟨w, hs_cs.2.2.1 ▸ hd, hs_cs.1 ▸ hm⟩
  have hmemw_cs : ∀ a, memW s_cs a = memW s1 a := fun a => by unfold memW; rw [hs_cs.1]
  have hld160 : @evalHOLExact 64 F _ s_cs.toExact (fun a => Classical.propDecidable (s_cs.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "child"), .const 160#64])) =
      some (.val (.word (BitVec.ofNat 64 (memW s1 (globN s1 "ev" + 160))))) := by
    rw [← hmemw_cs (globN s1 "ev" + 160)]
    exact eval_load_local_off s_cs hchild_cs hInv_cs.1.1.memaddrs he1_cs_wok he1_lt
      (off := 160) (by omega) (by omega)
  have hcmp160 : @evalHOLExact 64 F _ s_cs.toExact (fun a => Classical.propDecidable (s_cs.memaddrs a))
      (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 160#64])) (.const 0#64)) =
      some (.val (.word (if BitVec.ofNat 64 (memW s1 (globN s1 "ev" + 160)) = 0#64
        then 1#64 else 0#64))) :=
    eval_cmp_equal_word s_cs _ _ _ _ hld160 rfl
  rw [evaluateHOLFiniteState_ite, hcmp160] at hnt_cs ⊢
  dsimp only at hnt_cs ⊢
  by_cases hst0 : BitVec.ofNat 64 (memW s1 (globN s1 "ev" + 160)) = 0#64
  · -- child status == 0: dec "err" := 0; call create_finish with handler fcCreateErrHandler
    have hc1_ne0 : (if BitVec.ofNat 64 (memW s1 (globN s1 "ev" + 160)) = 0#64
        then (1#64 : BitVec 64) else 0#64) ≠ 0 := by simp [hst0]
    rw [if_neg hc1_ne0] at hnt_cs ⊢
    have he_err0 : @evalHOLExact 64 F _ s_cs.toExact (fun a => Classical.propDecidable (s_cs.memaddrs a))
        (.const 0#64) = some (.val (.word 0#64)) := rfl
    refine prelude_dec_word_step (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      he_err0 hnt_cs (fun hnt_er => ?_)
    let s_er := setVarHOLFinite (ofString "err") (.val (.word 0#64)) s_cs
    have her_mem : s_er.memory = s1.memory := hs_cs.1
    have her_glob : s_er.globals = s1.globals := hs_cs.2.1
    have hInv_er : EvmInv s_er := OpDispatchSpec.localsFree_evmInv s_cs s_er.locals s_cs.clock hInv_cs
    have hch_er : evmChain s_er = evmChain s0 :=
      (OpDispatchSpec.evmChain_congr her_mem her_glob).trans hch1
    have hR_er : OpDispatchSpec.evmR s_er ≤ OpDispatchSpec.evmR s0 := by
      have h1' : OpDispatchSpec.evmR s_er = OpDispatchSpec.evmR s1 :=
        R14Shards.OpHandlersA.evmR_eq_of_chain_and_words
          (OpDispatchSpec.evmChain_congr her_mem her_glob)
          (fun _ _ => ⟨by unfold memW; rw [her_mem], by unfold memW; rw [her_mem]⟩)
      exact h1'.le.trans hR1
    have hmark_er : memW s_er (globN s0 "cur_cont" + 48) = memW s0 (globN s0 "cur_cont" + 48) :=
      (by unfold memW; rw [her_mem] : memW s_er _ = memW s1 _).trans hmark1
    have hcells_er : ChainCellsAgree s0 s_er :=
      chainCellsAgree_trans hcells1 hch1 (chainCellsAgree_of_memory_eq her_mem)
    have hlocs_er : FcEntryLocals s0 s_er :=
      fcEntryLocals_setVar (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hlocs_cs
    have herr_lk : s_er.locals.lookup (ofString "err") = some (.val (.word 0#64)) := by
      simp [s_er, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    exact call_create_finish_handled_step hCF
      (fun {t w_err} hI hw hnt_h => fcCreateErrHandler_step (s := t) (w_err := w_err) hI hw hnt_h)
      hInv_er hch_er hR_er hmark_er hcells_er hlocs_er herr_lk hkind_val hnt_er
  · -- child status != 0: call state_restore(csnap)
    have hc0 : (if BitVec.ofNat 64 (memW s1 (globN s1 "ev" + 160)) = 0#64
        then (1#64 : BitVec 64) else 0#64) = 0 := by simp [hst0]
    rw [if_pos hc0] at hnt_cs ⊢
    obtain ⟨hsr_none, hsr_noerr⟩ :=
      call_state_restore_step (s := s_cs) (args := [.var .local (ofString "csnap")]) hInv_cs hnt_cs
    dsimp only at hsr_none
    constructor
    · intro hn
      obtain ⟨hIp, hchp, hRp, hmarkp, hcellsp, _, hlocp⟩ := hsr_none hn
      have hch_ec : evmChain s_cs = evmChain s1 :=
        OpDispatchSpec.evmChain_congr hs_cs.1 hs_cs.2.1
      have hR_ec : OpDispatchSpec.evmR s_cs = OpDispatchSpec.evmR s1 :=
        R14Shards.OpHandlersA.evmR_eq_of_chain_and_words hch_ec
          (fun _ _ => ⟨hmemw_cs _, hmemw_cs _⟩)
      have hcc_cs : globN s_cs "cur_cont" = globN s0 "cur_cont" := by
        have hg_cs : globN s_cs "cur_cont" = globN s1 "cur_cont" := by
          unfold globN; rw [hs_cs.2.1]
        exact hg_cs.trans hcc1.1
      have hmark_fin : memW (evaluateHOLFiniteState s_cs
          (.call (some (none, none)) (ofString "state_restore") [.var .local (ofString "csnap")])).2
          (globN s0 "cur_cont" + 48) = memW s0 (globN s0 "cur_cont" + 48) := by
        rw [hcc_cs] at hmarkp
        exact hmarkp.trans ((hmemw_cs _).trans hmark1)
      have hcells_s1_p : ChainCellsAgree s1 (evaluateHOLFiniteState s_cs
          (.call (some (none, none)) (ofString "state_restore") [.var .local (ofString "csnap")])).2 :=
        fun ec hec => by
          have hc := hcellsp ec (hch_ec.symm ▸ hec)
          exact ⟨hc.1.trans (hmemw_cs _), hc.2.1.trans (hmemw_cs _),
            hc.2.2.1.trans (hmemw_cs _), hc.2.2.2.trans (hmemw_cs _)⟩
      have hcells_fin : ChainCellsAgree s0 (evaluateHOLFiniteState s_cs
          (.call (some (none, none)) (ofString "state_restore") [.var .local (ofString "csnap")])).2 :=
        chainCellsAgree_trans hcells1 hch1 hcells_s1_p
      have hR_fin : OpDispatchSpec.evmR (evaluateHOLFiniteState s_cs
          (.call (some (none, none)) (ofString "state_restore") [.var .local (ofString "csnap")])).2 ≤
          OpDispatchSpec.evmR s0 :=
        hRp.le.trans (hR_ec.le.trans hR1)
      exact ⟨hIp, hchp.trans (hch_ec.trans hch1), hR_fin, hmark_fin, hcells_fin,
        fun hne => absurd hkind_val hne, fcEntryLocals_congr_locals hlocp hlocs_cs⟩
    · intro herr
      exact False.elim (hsr_noerr herr)

theorem fcPrelude_step (hCF : CreateFinishSpecs) {F : Type}
    {s0 s1 : PanSemStateFiniteExact 64 F}
    (hRel0 : PreludeRel s0 s1)
    (hnt : (evaluateHOLFiniteState s1 fcPrelude).1 ≠ some .timeOut) :
    ((evaluateHOLFiniteState s1 fcPrelude).1 = none →
      PreludeRel s0 (evaluateHOLFiniteState s1 fcPrelude).2) ∧
    (OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState s1 fcPrelude).1 →
      EvmInv (evaluateHOLFiniteState s1 fcPrelude).2 ∧
      evmChain (evaluateHOLFiniteState s1 fcPrelude).2 = evmChain s0 ∧
      OpDispatchSpec.evmR (evaluateHOLFiniteState s1 fcPrelude).2 ≤ OpDispatchSpec.evmR s0 ∧
      ChainCellsAgree s0 (evaluateHOLFiniteState s1 fcPrelude).2) := by
  have hInv1 := hRel0.inv
  have hch1 := hRel0.chain_eq
  have hR1 := hRel0.r_le
  have hmark1 := hRel0.mark_eq
  have hcells1 := hRel0.cells
  have hlocs1 := hRel0.locals_ok
  have hcc1 : globN s1 "cur_cont" = globN s0 "cur_cont" ∧ globN s1 "ev" = globN s0 "ev" := by
    have hhead : (evmChain s1).head? = (evmChain s0).head? := congrArg List.head? hch1
    rw [evmChain_cons, evmChain_cons] at hhead
    simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at hhead
    exact ⟨hhead.2, hhead.1⟩
  have hhead1 : (globN s1 "ev", globN s1 "cur_cont") ∈ evmChain s1 := by
    rw [evmChain_cons]; exact List.mem_cons_self
  have hFW1 := hInv1.2.choose_spec.2.2.2.2.1 _ hhead1
  obtain ⟨he1_lt, hc1_lt, _, _⟩ :=
    InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hInv1.1.2 hFW1
  have hc1_wok : WordsOK s1 (globN s1 "cur_cont", 104) :=
    (hFW1.1 (globN s1 "cur_cont", 104) (by simp)).2
  have he1_wok : WordsOK s1 (globN s1 "ev", 280) :=
    (hFW1.1 (globN s1 "ev", 280) (by simp)).2
  rw [fcPrelude_eq, evaluateHOLFiniteState_ite] at hnt ⊢
  have hcmp_kind : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.cmp .equal (.var .local (ofString "kind")) (.const 2#64)) =
      some (.val (.word (if BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 16)) = 2#64
        then 1 else 0))) := by
    simp [evalHOLExact, hlocs1.kind_lk, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp_kind] at hnt ⊢
  dsimp only at hnt ⊢
  by_cases hkind2 : BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 16)) = 2#64
  · -- kind == 2
    have hkind_val : memW s0 (globN s0 "cur_cont" + 16) = 2 := by
      have hInv0_or : memW s0 (globN s0 "cur_cont" + 16) < 2 ^ 64 := by
        unfold memW; split
        · rename_i w _; exact w.isLt
      have hnat := congrArg BitVec.toNat hkind2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hInv0_or] at hnat
      exact hnat
    have h1_ne0 : (if BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 16)) = 2#64
        then (1 : BitVec 64) else 0) ≠ 0 := by simp [hkind2]
    rw [if_neg h1_ne0] at hnt ⊢
    have hrec1 : s1.locals.lookup (ofString "rec") =
        some (.val (.word (BitVec.ofNat 64 (globN s1 "cur_cont")))) := by
      rw [hcc1.1]; exact hlocs1.rec_lk
    have he_csnap := eval_load_local_off s1 hrec1 hInv1.1.1.memaddrs hc1_wok (by omega)
      (off := 96) (by omega) (by omega)
    refine prelude_dec_word_step (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      he_csnap hnt (fun hnt_cs => ?_)
    let s_cs := setVarHOLFinite (ofString "csnap")
      (.val (.word (BitVec.ofNat 64 (memW s1 (globN s1 "cur_cont" + 96))))) s1
    have hInv_cs : EvmInv s_cs := OpDispatchSpec.localsFree_evmInv s1 s_cs.locals s1.clock hInv1
    have hlocs_cs : FcEntryLocals s0 s_cs :=
      fcEntryLocals_setVar (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hlocs1
    exact fcPrelude_kind2_csnap_step hCF hInv1 hch1 hR1 hmark1 hcells1 hcc1 he1_lt he1_wok hkind_val
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hInv_cs hlocs_cs hnt_cs
  · -- kind != 2: .skip
    have h0 : (if BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 16)) = 2#64
        then (1 : BitVec 64) else 0) = 0 := by simp [hkind2]
    rw [if_pos h0, evaluateHOLFiniteState_skip]
    exact ⟨fun _ => hRel0, by simp [OpDispatchSpec.IsEvmErr]⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
