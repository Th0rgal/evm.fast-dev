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

theorem pc_add_call_step {F : Type}
    (st : PanSemStateFiniteExact 64 F) (nExp : ExpHOL 64) (nw : BitVec 64)
    (hInv : EvmInv st)
    (hn : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) nExp =
      some (.val (.word nw)))
    (hnt : (evaluateHOLFiniteState st (.call (some (none, none)) (ofString "pc_add") [nExp])).1 ≠
      some .timeOut) :
    ((evaluateHOLFiniteState st (.call (some (none, none)) (ofString "pc_add") [nExp])).1 = none →
      let post := (evaluateHOLFiniteState st (.call (some (none, none)) (ofString "pc_add") [nExp])).2
      EvmInv post ∧
      post.globals = st.globals ∧
      evmChain post = evmChain st ∧
      OpDispatchSpec.evmR post = OpDispatchSpec.evmR st ∧
      ChainCellsAgree st post ∧
      post.locals = st.locals) ∧
    ¬ OpDispatchSpec.IsEvmErr
      (evaluateHOLFiniteState st (.call (some (none, none)) (ofString "pc_add") [nExp])).1 := by
  have hcode : st.code = originalRuntimeCode := hInv.1.1.code
  have hargs : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a)) [nExp] =
      some [.val (.word nw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hn]
  have hl := pan_one_word_lookup st.code.lookup (ofString "pc_add") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_pc_add) nw (by rw [hcode]; exact R14Shards.OpHandlersA.lookup_pc_add)
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  rw [hargs] at hnt ⊢; dsimp only at hnt ⊢
  rw [hl] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hz : st.clock = 0
  · rw [if_pos hz] at hnt; exact absurd rfl hnt
  · rw [if_neg hz] at hnt ⊢
    let entry := callEntryStateHOLFinite st (HolFiniteMapExact.empty.update (ofString "n", .val (.word nw)))
    have hInv_ent : EvmInv entry :=
      OpDispatchSpec.localsFree_evmInv st entry.locals entry.clock hInv
    have hhead_mem : (globN entry "ev", globN entry "cur_cont") ∈ evmChain entry := by
      simp [evmChain, evmChainFrom]
    have hFW0 := hInv_ent.2.choose_spec.2.2.2.2.1 _ hhead_mem
    have hb_ev := (InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hInv_ent.1.2 hFW0).1
    dsimp only at hb_ev
    have hev_pos : 0 < globN entry "ev" := by
      have hin := (hFW0.1 (globN entry "ev", 280) (by simp)).1.1
      have h1 := hInv_ent.1.2.2.2.1; have h2 := hInv_ent.1.2.2.2.2.1
      rw [R11Shards.scratchStart_val] at h1; dsimp only at hin; omega
    obtain ⟨evw, hevw, hevw_nat⟩ :=
      InitECandidate.Solver.Wave8Contracts.M23.global_word_of_pos entry "ev" hev_pos
    have hbody : sourceFnBody Guest.Software.guestFn_pc_add =
        .seq
          (.store (.op .add [.var .global (ofString "ev"), .const 0])
            (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 0]), .var .local (ofString "n")]))
          (.return (.const 0)) := rfl
    have hev_b : ∃ cpost : PanSemStateFiniteExact 64 F,
        evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_pc_add) =
          (some (.returned (.val (.word 0))), cpost) ∧
        EvmInv cpost ∧
        cpost.globals = entry.globals ∧
        evmChain cpost = evmChain entry ∧
        OpDispatchSpec.evmR cpost = OpDispatchSpec.evmR entry ∧
        (∀ x : BitVec 64,
          (∀ off ∈ R14Shards.OpHandlersA.nonStructFrameOffs, x ≠ BitVec.ofNat 64 (globN entry "ev" + off)) →
          cpost.memory x = entry.memory x) := by
      rw [hbody, evaluateHOLFiniteState_seq_line780]
      have hwa0 : WordAt entry (globN entry "ev") :=
        (hFW0.1 (globN entry "ev", 280) (by simp)).2.2.2 0 (by omega)
          |> fun h => by rwa [show globN entry "ev" + 8 * 0 = globN entry "ev" by omega] at h
      obtain ⟨pcw, hdom0, hmem0⟩ := hwa0
      have hev_bv : evw + 0#64 = BitVec.ofNat 64 (globN entry "ev") := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.add_zero, hevw_nat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show globN entry "ev" < 2 ^ 64 by omega)]
      have hn_ent : entry.locals.lookup (ofString "n") = some (.val (.word nw)) := by
        simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hst_exact : evaluateHOLFiniteState entry
          (.store (.op .add [.var .global (ofString "ev"), .const 0])
            (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 0]), .var .local (ofString "n")])) =
          (none, { entry with memory := R14Shards.OpHandlersA.updW entry.memory (BitVec.ofNat 64 (globN entry "ev")) (pcw + nw) }) := by
        rw [evaluateHOLFiniteState_store]
        have hdst : @evalHOLExact 64 F _ entry.toExact (fun a => Classical.propDecidable (entry.memaddrs a))
            (.op .add [.var .global (ofString "ev"), .const 0]) =
            some (.val (.word (BitVec.ofNat 64 (globN entry "ev")))) := by
          simp only [evalHOLExact, evalListHOLExact, hevw, valueIsWord, valueWord, wordOpHOL, wordOp,
            List.all, List.map, Option.map, List.foldr, Bool.and_self]
          change some (ValueHOL.val (HolWordLab.word (evw + (0#64 + 0#64)))) = _
          rw [BitVec.add_zero, hev_bv]
        have hval : @evalHOLExact 64 F _ entry.toExact (fun a => Classical.propDecidable (entry.memaddrs a))
            (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 0]), .var .local (ofString "n")]) =
            some (.val (.word (pcw + nw))) := by
          simp only [evalHOLExact, evalListHOLExact, isWfShapeExactHOL, hevw, hn_ent, valueIsWord, valueWord,
            wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr, Bool.and_self, ↓reduceIte]
          have hml : @memLoadHOLExact 64 _ .one (evw + (0#64 + 0#64)) entry.memaddrs
              (fun a => Classical.propDecidable (entry.memaddrs a)) entry.memory entry.structs =
              some (.val (.word pcw)) := by
            rw [BitVec.add_zero, hev_bv]
            simp [memLoadHOLExact, hdom0, hmem0]
          erw [hml]
          simp [valueIsWord, valueWord]
        rw [hdst, hval]; dsimp only
        unfold flattenHOL panMemStoresHOL panMemStoreHOL
        simp only [hdom0, ↓reduceIte, panMemStoresHOL]
        rfl
      rw [hst_exact]; dsimp only
      let s1 : PanSemStateFiniteExact 64 F :=
        { entry with memory := R14Shards.OpHandlersA.updW entry.memory (BitVec.ofNat 64 (globN entry "ev")) (pcw + nw) }
      rw [evaluateHOLFiniteState_return]; dsimp only [evalHOLExact]
      have hsz0 : sizeOfShapeWithContextHOL s1.structs
          (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
        simp [shapeOfHOLExact]
      rw [if_pos hsz0]
      let cpost := emptyLocalsHOLFinite s1
      have hGp : GuestInv cpost := guestInv_congr (s := entry)
        rfl rfl rfl rfl hInv_ent.1.1
      have hglob_p : cpost.globals = entry.globals := rfl
      have hbe_p : cpost.be = entry.be := rfl
      have hmem_out : ∀ x : BitVec 64,
          (∀ off ∈ R14Shards.OpHandlersA.nonStructFrameOffs, x ≠ BitVec.ofNat 64 (globN entry "ev" + off)) →
          cpost.memory x = entry.memory x := by
        intro x hx
        change R14Shards.OpHandlersA.updW entry.memory (BitVec.ofNat 64 (globN entry "ev")) (pcw + nw) x =
          entry.memory x
        dsimp only [R14Shards.OpHandlersA.updW]
        have hn0 : x ≠ BitVec.ofNat 64 (globN entry "ev") := by
          simpa using hx 0 (by simp [R14Shards.OpHandlersA.nonStructFrameOffs])
        rw [if_neg hn0]
      obtain ⟨hInv_p, hch_p, hR_p⟩ :=
        R14Shards.OpHandlersA.evmInv_of_head_nonstruct hInv_ent hGp hglob_p hbe_p hmem_out
      exact ⟨cpost, rfl, hInv_p, hglob_p, hch_p, hR_p, hmem_out⟩
    obtain ⟨cpost, hrun, hInv_cp, hglob_cp, hch_cp, hR_cp, hmem_out⟩ := hev_b
    change evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_pc_add) = _ at hrun
    rw [hrun] at hnt ⊢; dsimp only at hnt ⊢
    have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hsh] at hnt ⊢
    let resSt : PanSemStateFiniteExact 64 F := { cpost with locals := st.locals }
    have hInv_res : EvmInv resSt :=
      OpDispatchSpec.localsFree_evmInv cpost st.locals cpost.clock hInv_cp
    have hglob_res : resSt.globals = st.globals := hglob_cp
    have hch_res : evmChain resSt = evmChain st := by
      have h1 : evmChain resSt = evmChain cpost := OpDispatchSpec.evmChain_congr rfl rfl
      have h2 : evmChain entry = evmChain st := OpDispatchSpec.evmChain_congr rfl rfl
      exact h1.trans (hch_cp.trans h2)
    have hR_res : OpDispatchSpec.evmR resSt = OpDispatchSpec.evmR st := by
      have h1 : OpDispatchSpec.evmR resSt = OpDispatchSpec.evmR cpost :=
        R14Shards.OpHandlersA.evmR_eq_of_chain_and_words (OpDispatchSpec.evmChain_congr rfl rfl)
          (fun _ _ => ⟨rfl, rfl⟩)
      have h2 : OpDispatchSpec.evmR entry = OpDispatchSpec.evmR st :=
        R14Shards.OpHandlersA.evmR_eq_of_chain_and_words (OpDispatchSpec.evmChain_congr rfl rfl)
          (fun _ _ => ⟨rfl, rfl⟩)
      exact h1.trans (hR_cp.trans h2)
    have hcells_res : ChainCellsAgree st resSt := by
      have hFO_pw := hInv.2.choose_spec.2.2.2.2.2.2.2.1
      have hcons : ∃ chTail, evmChain st = (globN st "ev", globN st "cur_cont") :: chTail := by
        rw [evmChain_cons]; exact ⟨_, rfl⟩
      obtain ⟨chTail, hch_st_eq⟩ := hcons
      have hpw0 : (frameObjects st (globN st "ev", globN st "cur_cont")).Pairwise Disj ∧
          (∀ o1 ∈ frameObjects st (globN st "ev", globN st "cur_cont"),
            ∀ ec ∈ chTail, ∀ o2 ∈ frameObjects st ec, Disj o1 o2) := by
        have hpw := hFO_pw
        rw [hch_st_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
        refine ⟨hpw.1, fun o1 ho1 ec hec o2 ho2 => hpw.2.2 o1 ho1 o2 ?_⟩
        exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, hec, rfl⟩, ho2⟩
      have hde_c0 : Disj (globN st "ev", 280) (globN st "cur_cont", 104) := by
        have hp := hpw0.1
        unfold frameObjects at hp
        exact (List.pairwise_cons.mp (List.pairwise_append.mp hp).1).1 _ (by simp)
      have hoff_lt280 : ∀ off ∈ R14Shards.OpHandlersA.nonStructFrameOffs, off + 8 ≤ 280 := by
        intro off hoff; revert off hoff; decide
      have hev_ent : globN entry "ev" = globN st "ev" := rfl
      have hmem_ec : ∀ a : Nat, a < 2 ^ 64 →
          (∀ off ∈ R14Shards.OpHandlersA.nonStructFrameOffs, a ≠ globN st "ev" + off) →
          memW resSt a = memW st a := by
        intro a ha hne
        unfold memW
        have hx : resSt.memory (BitVec.ofNat 64 a) = st.memory (BitVec.ofNat 64 a) := by
          apply hmem_out
          intro off hoff heq
          have hn_eq := congrArg BitVec.toNat heq
          have hlt_off := hoff_lt280 off hoff
          have hb_off : globN entry "ev" + off < 2 ^ 64 := by omega
          rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb_off, hev_ent] at hn_eq
          exact hne off hoff hn_eq
        rw [hx]
      intro ec hec
      have hFW := hInv.2.choose_spec.2.2.2.2.1 ec hec
      obtain ⟨he_lt, hc_lt, _, _⟩ :=
        InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hInv.1.2 hFW
      rw [hch_st_eq] at hec
      rcases List.mem_cons.mp hec with rfl | htail
      · have hnot_head : ∀ aoff : Nat, aoff ∈ ([24, 32, 40] : List Nat) →
            ∀ off ∈ R14Shards.OpHandlersA.nonStructFrameOffs,
            globN st "ev" + aoff ≠ globN st "ev" + off := by
          have hne_pair : ∀ aoff ∈ ([24, 32, 40] : List Nat),
              ∀ off ∈ R14Shards.OpHandlersA.nonStructFrameOffs, aoff ≠ off := by decide
          intro aoff haoff off hoff heq
          have := hne_pair aoff haoff off hoff
          omega
        have hnot_c0 : ∀ off ∈ R14Shards.OpHandlersA.nonStructFrameOffs,
            globN st "cur_cont" + 56 ≠ globN st "ev" + off := by
          intro off hoff heq
          have hlt_off := hoff_lt280 off hoff
          unfold Disj at hde_c0; dsimp only at hde_c0
          rcases hde_c0 with h | h | h | h <;> omega
        exact ⟨hmem_ec _ (by omega) (hnot_head 24 (by simp)),
          hmem_ec _ (by omega) (hnot_head 32 (by simp)),
          hmem_ec _ (by omega) (hnot_head 40 (by simp)),
          hmem_ec _ (by omega) hnot_c0⟩
      · have hdj_e : Disj (globN st "ev", 280) (ec.1, 280) :=
          hpw0.2 _ (by simp [frameObjects]) ec htail _ (by simp [frameObjects])
        have hdj_c : Disj (globN st "ev", 280) (ec.2, 104) :=
          hpw0.2 _ (by simp [frameObjects]) ec htail _ (by simp [frameObjects])
        have hnot_tail_e : ∀ aoff : Nat, aoff + 8 ≤ 280 →
            ∀ off ∈ R14Shards.OpHandlersA.nonStructFrameOffs,
            ec.1 + aoff ≠ globN st "ev" + off := by
          intro aoff haoff off hoff heq
          have hlt_off := hoff_lt280 off hoff
          unfold Disj at hdj_e; dsimp only at hdj_e
          rcases hdj_e with h | h | h | h <;> omega
        have hnot_tail_c : ∀ off ∈ R14Shards.OpHandlersA.nonStructFrameOffs,
            ec.2 + 56 ≠ globN st "ev" + off := by
          intro off hoff heq
          have hlt_off := hoff_lt280 off hoff
          unfold Disj at hdj_c; dsimp only at hdj_c
          rcases hdj_c with h | h | h | h <;> omega
        exact ⟨hmem_ec _ (by omega) (hnot_tail_e 24 (by omega)),
          hmem_ec _ (by omega) (hnot_tail_e 32 (by omega)),
          hmem_ec _ (by omega) (hnot_tail_e 40 (by omega)),
          hmem_ec _ (by omega) hnot_tail_c⟩
    exact ⟨fun _ => ⟨hInv_res, hglob_res, hch_res, hR_res, hcells_res, rfl⟩,
      by simp [OpDispatchSpec.IsEvmErr]⟩

theorem fcCleanup_step {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hAs : ArenaReady st)
    (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt st S)
    (hRel : ReleaseReadyAt st S
      (memW s0 (globN s0 "cur_cont" + 48))
      (memW s0 (globN s0 "cur_cont" + 56)))
    (hlocs : FcEntryLocals s0 st)
    (hch : evmChain st = (evmChain s0).tail)
    (hlen : (evmChain st).length + 1 = (evmChain s0).length)
    (hR : OpDispatchSpec.evmR st ≤ OpDispatchSpec.evmR s0)
    (hcells : ∀ ec ∈ evmChain st,
      memW st (ec.1 + 24) = memW s0 (ec.1 + 24) ∧
      memW st (ec.1 + 32) = memW s0 (ec.1 + 32) ∧
      memW st (ec.1 + 40) = memW s0 (ec.1 + 40) ∧
      memW st (ec.2 + 56) = memW s0 (ec.2 + 56))
    (hev : globN st "ev" = memW s0 (globN s0 "cur_cont"))
    (hnt : (evaluateHOLFiniteState st fcCleanup).1 ≠ some .timeOut) :
    FinishPost s0 (evaluateHOLFiniteState st fcCleanup).1
      (evaluateHOLFiniteState st fcCleanup).2 := by
  rw [fcCleanup_eq] at hnt ⊢
  set cmw : BitVec 64 := BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 48))
  set cmmw : BitVec 64 := BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 56))
  have hcm_lt : memW s0 (globN s0 "cur_cont" + 48) < 2 ^ 64 := by
    unfold memW; split; rename_i w _; exact w.isLt
  have hcmm_lt : memW s0 (globN s0 "cur_cont" + 56) < 2 ^ 64 := by
    unfold memW; split; rename_i w _; exact w.isLt
  have hcm_nat : cmw.toNat = memW s0 (globN s0 "cur_cont" + 48) := by
    dsimp only [cmw]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcm_lt]
  have hcmm_nat : cmmw.toNat = memW s0 (globN s0 "cur_cont" + 56) := by
    dsimp only [cmmw]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcmm_lt]
  have hRel_bv : ReleaseReadyAt st S cmw.toNat cmmw.toNat := by
    rw [hcm_nat, hcmm_nat]; exact hRel
  have hcm_eval : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
      (.var .local (ofString "child_mark")) = some (.val (.word cmw)) := by
    simp [evalHOLExact, hlocs.cm_lk, cmw]
  have hcmm_eval : ∀ g' ck', @evalHOLExact 64 F _
      ({ st with globals := g', clock := ck' } : PanSemStateFiniteExact 64 F).toExact
      (fun a => Classical.propDecidable (st.memaddrs a))
      (.var .local (ofString "child_mem_mark")) = some (.val (.word cmmw)) := by
    intro g' ck'; simp [evalHOLExact, hlocs.cmm_lk, cmmw]
  obtain ⟨mid, heq_mid, hloc_mid, hmem_mid, hdom_mid, hbe_mid,
      hsp_mid, hfmp_mid, hg_kept, hAmid, hInvmid, hch_mid, hR_mid, hnt_mid⟩ :=
    release_pair_step st (.var .local (ofString "child_mark"))
      (.var .local (ofString "child_mem_mark")) cmw cmmw
      hAs hInv hRel_bv hcm_eval hcmm_eval hnt
  rw [heq_mid]
  have hInv_mid_full : EvmInv mid := ⟨hAmid, S, hInvmid⟩
  have hev_mid : globN mid "ev" = memW s0 (globN s0 "cur_cont") := by
    have : globN mid "ev" = globN st "ev" := by
      unfold globN; rw [hg_kept (ofString "ev") (by decide) (by decide)]
    exact this.trans hev
  refine seq_finishPost (fun u => call0_ne_returned_fc mid _ _ u) (fun hnt_pc => ?_) hnt_mid
  obtain ⟨hpc_none, hpc_noerr⟩ :=
    pc_add_call_step mid (.const 1#64) 1#64 hInv_mid_full (by simp [evalHOLExact]) hnt_pc
  dsimp only at hpc_none
  refine ⟨fun hnone hnt_ret => ?_, fun herr => False.elim (hpc_noerr herr)⟩
  obtain ⟨hInv_pc, hglob_pc, hch_pc, hR_pc, hcells_pc, _⟩ := hpc_none hnone
  let s_pc := (evaluateHOLFiniteState mid (.call (some (none, none)) (ofString "pc_add") [.const 1#64])).2
  rw [evaluateHOLFiniteState_return]
  dsimp only [evalHOLExact]
  have hsz0 : sizeOfShapeWithContextHOL s_pc.structs
      (shapeOfHOLExact (.val (.word (0#64 : BitVec 64)))) ≤ 32 := by
    simp [shapeOfHOLExact]
  rw [if_pos hsz0]
  dsimp only
  apply finishPost_congr_lc (p1 := s_pc) (p2 := s_pc.emptyLocalsHOLFinite)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  intro _
  have hch_spc : evmChain s_pc = (evmChain s0).tail :=
    hch_pc.trans (hch_mid.trans hch)
  have hlen_spc : (evmChain s_pc).length + 1 = (evmChain s0).length := by
    rw [hch_pc, hch_mid]; exact hlen
  have hR_spc : OpDispatchSpec.evmR s_pc ≤ OpDispatchSpec.evmR s0 := by
    rw [hR_pc, hR_mid]; exact hR
  have hev_spc : globN s_pc "ev" = memW s0 (globN s0 "cur_cont") := by
    have : globN s_pc "ev" = globN mid "ev" := by unfold globN; rw [hglob_pc]
    exact this.trans hev_mid
  have hfmp_spc : globN s_pc "frame_mem_ptr" = memW s0 (globN s0 "cur_cont" + 56) := by
    have : globN s_pc "frame_mem_ptr" = globN mid "frame_mem_ptr" := by unfold globN; rw [hglob_pc]
    exact this.trans (hfmp_mid.trans hcmm_nat)
  have hcells_spc : ∀ ec ∈ evmChain s_pc,
      memW s_pc (ec.1 + 24) = memW s0 (ec.1 + 24) ∧
      memW s_pc (ec.1 + 32) = memW s0 (ec.1 + 32) ∧
      memW s_pc (ec.1 + 40) = memW s0 (ec.1 + 40) ∧
      memW s_pc (ec.2 + 56) = memW s0 (ec.2 + 56) := by
    intro ec hec
    have hec_mid : ec ∈ evmChain mid := hch_pc ▸ hec
    have hec_st : ec ∈ evmChain st := hch_mid ▸ hec_mid
    obtain ⟨a1, b1, c1, d1⟩ := hcells_pc ec hec_mid
    have hmw_mid : ∀ a, memW mid a = memW st a := fun a => by unfold memW; rw [hmem_mid]
    obtain ⟨a0, b0, c0, d0⟩ := hcells ec hec_st
    exact ⟨a1.trans ((hmw_mid _).trans a0), b1.trans ((hmw_mid _).trans b0),
      c1.trans ((hmw_mid _).trans c0), d1.trans ((hmw_mid _).trans d0)⟩
  exact ⟨hInv_pc, hlen_spc, hR_spc, hch_spc, hcells_spc, hev_spc, hfmp_spc⟩

structure FcBranchState {F : Type} (s0 st : PanSemStateFiniteExact 64 F)
    (S : List Nat) : Prop where
  arena : ArenaReady st
  inv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt st S
  release : ReleaseReadyAt st S (memW s0 (globN s0 "cur_cont" + 48))
    (memW s0 (globN s0 "cur_cont" + 56))
  locals_ok : FcEntryLocals s0 st
  chain_eq : evmChain st = (evmChain s0).tail
  length_eq : (evmChain st).length + 1 = (evmChain s0).length
  r_le : OpDispatchSpec.evmR st ≤ OpDispatchSpec.evmR s0
  cells : ∀ ec ∈ evmChain st,
    memW st (ec.1 + 24) = memW s0 (ec.1 + 24) ∧
    memW st (ec.1 + 32) = memW s0 (ec.1 + 32) ∧
    memW st (ec.1 + 40) = memW s0 (ec.1 + 40) ∧
    memW st (ec.2 + 56) = memW s0 (ec.2 + 56)
  ev_eq : globN st "ev" = memW s0 (globN s0 "cur_cont")

theorem fcBranchState_cleanup {F : Type} {s0 st : PanSemStateFiniteExact 64 F}
    {S : List Nat} (h : FcBranchState s0 st S)
    (hnt : (evaluateHOLFiniteState st fcCleanup).1 ≠ some .timeOut) :
    FinishPost s0 (evaluateHOLFiniteState st fcCleanup).1
      (evaluateHOLFiniteState st fcCleanup).2 :=
  fcCleanup_step h.arena h.inv h.release h.locals_ok h.chain_eq h.length_eq
    h.r_le h.cells h.ev_eq hnt

theorem preludeRel_pop_invariants {F : Type}
    {s0 s post : PanSemStateFiniteExact 64 F} (h : PreludeRel s0 s)
    (hne : memW s (globN s "cur_cont" + 16) ≠ 0)
    (hAp : ArenaReady post) (hm : post.memory = s.memory)
    (hd : post.memaddrs = s.memaddrs) (hb : post.be = s.be)
    (hev : globN post "ev" = memW s (globN s "cur_cont"))
    (hcc : globN post "cur_cont" = memW s (globN s "cur_cont" + 8))
    (hg : ∀ name : String, name ≠ "ev" → name ≠ "cur_cont" →
      globN post name = globN s name)
    (hl : post.locals = s.locals)
    (hparent : memW s (globN s "cur_cont") = memW s0 (globN s0 "cur_cont")) :
    ∃ S, FcBranchState s0 post S := by
  have hhead := congrArg List.head? h.chain_eq
  rw [evmChain_cons, evmChain_cons] at hhead
  simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at hhead
  have hcur : globN s "cur_cont" = globN s0 "cur_cont" := hhead.2
  have hmem : (globN s0 "ev", globN s0 "cur_cont") ∈ evmChain s0 := by
    rw [evmChain_cons]; exact List.mem_cons_self
  have hcm : memW s (globN s "cur_cont" + 48) =
      memW s0 (globN s0 "cur_cont" + 48) := by
    rw [hcur]; exact h.mark_eq
  have hcmm : memW s (globN s "cur_cont" + 56) =
      memW s0 (globN s0 "cur_cont" + 56) := by
    rw [hcur]; exact (h.cells _ hmem).2.2.2
  obtain ⟨S, hI⟩ := h.inv.2
  obtain ⟨S', _, hIp, hRel, hch, hlen, hR, hcells⟩ :=
    finish_child_pop_invariants h.inv.1 hI hne hAp hm hd hb hev hcc hg
  refine ⟨S', hAp, hIp, ?_, fcEntryLocals_congr_locals hl h.locals_ok,
    hch.trans (congrArg List.tail h.chain_eq), ?_, ?_, ?_, hev.trans hparent⟩
  · rw [hcm, hcmm] at hRel
    exact hRel
  · rw [h.chain_eq] at hlen
    exact hlen
  · have := h.r_le
    omega
  · intro ec hec
    have hec_s : ec ∈ evmChain s := List.mem_of_mem_tail (hch ▸ hec)
    have hec_0 : ec ∈ evmChain s0 := h.chain_eq ▸ hec_s
    obtain ⟨a, b, c, d⟩ := hcells ec hec
    obtain ⟨a0, b0, c0, d0⟩ := h.cells ec hec_0
    exact ⟨a.trans a0, b.trans b0, c.trans c0, d.trans d0⟩

theorem fcBranchState_congr_locals_clock {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F} {S : List Nat}
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (ck : Nat)
    (h : FcBranchState s0 st S)
    (hL : FcEntryLocals s0 { st with locals := L, clock := ck }) :
    FcBranchState s0 { st with locals := L, clock := ck } S := by
  let st' : PanSemStateFiniteExact 64 F := { st with locals := L, clock := ck }
  have hch' : evmChain st' = evmChain st := evmChain_lc_fc st L ck
  have hR' : OpDispatchSpec.evmR st' = OpDispatchSpec.evmR st := evmR_lc_fc st L ck
  have hA' : ArenaReady st' := ⟨guestInv_congr (s := st) rfl rfl rfl rfl h.arena.1,
    arenaOK_congr rfl h.arena.2⟩
  have hf : ∀ (nodes : Nat) (Fr : List Nat) (head : Nat),
      FreeChain st' nodes head Fr ↔ FreeChain st nodes head Fr := by
    intro nodes Fr; induction Fr with
    | nil => intro _; exact Iff.rfl
    | cons _ rest ih => intro _; exact and_congr Iff.rfl (ih _)
  have hw : ∀ t, HtabWF st' t ↔ HtabWF st t := by
    intro t; simp only [HtabWF, hf]; exact Iff.rfl
  have ht : ∀ S0, TablesTyped st' S0 ↔ TablesTyped st S0 := by
    intro S0; simp only [TablesTyped, hw]; exact Iff.rfl
  have hwt : WorldTyped st' S ↔ WorldTyped st S := by
    simp only [WorldTyped, ht]; exact Iff.rfl
  have hInv' : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt st' S := by
    have hE := h.inv
    dsimp only [InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt] at hE ⊢
    simp only [st', FrameWF, MsgOwned, hwt, hch'] at hE ⊢
    exact hE
  have hRel' : ReleaseReadyAt st' S (memW s0 (globN s0 "cur_cont" + 48))
      (memW s0 (globN s0 "cur_cont" + 56)) :=
    (releaseReadyAt_lc st L ck S _ _).mpr h.release
  exact ⟨hA', hInv', hRel', hL, hch'.trans h.chain_eq,
    by rw [hch']; exact h.length_eq, by rw [hR']; exact h.r_le,
    fun ec hec => h.cells ec (hch' ▸ hec), h.ev_eq⟩

def headSimpleOffs : List Nat :=
  [0, 16, 48, 56, 64, 72, 80, 96, 104, 152, 160, 184, 192, 200, 208, 224, 240, 248, 256, 264, 272]

theorem evmInvAt_of_head_simple {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hAs : ArenaReady s)
    (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (hGp : GuestInv post)
    (hglob : post.globals = s.globals)
    (hbe : post.be = s.be)
    (hmem_out : ∀ x : BitVec 64,
      (∀ off ∈ headSimpleOffs, x ≠ BitVec.ofNat 64 (globN s "ev" + off)) →
      post.memory x = s.memory x)
    (hsp_le : memW post (globN s "ev" + 16) ≤ memW s (globN s "ev" + 232))
    (hgas_le : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) +
      (((evmChain s).tail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) + 1 < 2 ^ 64) :
    ArenaReady post ∧
    InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt post S ∧
    evmChain post = evmChain s ∧
    fixedObjects post = fixedObjects s ∧
    (∀ t ∈ S, htabFootprint post t = htabFootprint s t) ∧
    (∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec ∧
      frameScratch post ec = frameScratch s ec ∧
      frameLogs post ec = frameLogs s ec ∧
      memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
      memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧
      memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧
      memW post (ec.1 + 112) = memW s (ec.1 + 112) ∧
      memW post (ec.2 + 56) = memW s (ec.2 + 56)) ∧
    OpDispatchSpec.evmR post =
      memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) +
        (((evmChain s).tail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) := by
  obtain ⟨hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, hAT, hMarks, hRoles, _⟩ := hInv
  obtain ⟨Nd_at, hTr_at, hAT_at⟩ := hAT
  have hWT : InitECandidate.Solver.Wave8Contracts.M23.WorldTypedWith s S Nd_at :=
    ⟨hW.1, hW.2.1, hW.2.2.1, hTr_at⟩
  set e0 := globN s "ev"
  set c0 := globN s "cur_cont"
  have hch_cons : ∃ tl, evmChain s = (e0, c0) :: tl := ⟨_, rfl⟩
  obtain ⟨chTail, hch_eq⟩ := hch_cons
  have hhead_mem : (e0, c0) ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_self
  have hhead_FW := hFW_all _ hhead_mem
  obtain ⟨hb1, _, _, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hAs.2 hhead_FW
  dsimp only at hb1
  have he0_8 : e0 % 8 = 0 := (hhead_FW.1 (e0, 280) (by simp)).2.1
  have hdom_eq : post.memaddrs = s.memaddrs := hGp.memaddrs.trans hAs.1.memaddrs.symm
  have hoff_props : ∀ off ∈ headSimpleOffs,
      off + 8 ≤ 280 ∧ off % 8 = 0 ∧ s.memaddrs (BitVec.ofNat 64 (e0 + off)) := by
    intro off hoff
    have hdiv : off + 8 ≤ 280 ∧ off % 8 = 0 ∧ off / 8 < 280 / 8 ∧ 8 * (off / 8) = off := by
      revert off hoff; decide
    obtain ⟨_, hdom, _⟩ := (hhead_FW.1 (e0, 280) (by simp)).2.2.2 (off / 8) hdiv.2.2.1
    exact ⟨hdiv.1, hdiv.2.1, by simpa [hdiv.2.2.2] using hdom⟩
  have heff : InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect s post [(e0, 280)] := by
    refine ⟨hGp.code.trans hAs.1.code.symm, hdom_eq,
      hGp.shMemaddrs.trans hAs.1.shMemaddrs.symm,
      hGp.baseAddr.trans hAs.1.baseAddr.symm, hbe, hglob, ?_, ?_, ?_⟩
    · intro a hna
      apply hmem_out a
      intro off hoff rfl
      exact hna (hoff_props off hoff).2.2
    · intro a ha
      apply hmem_out a
      intro off hoff rfl
      have hp := hoff_props off hoff
      have htn : (BitVec.ofNat 64 (e0 + off)).toNat = e0 + off := Nat.mod_eq_of_lt (by omega)
      exact ha (e0, 280) (by simp) ⟨by rw [htn]; omega, by rw [htn]; omega⟩
    · intro b hb hno
      unfold memB
      have hal_b : (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := by
        rw [panByteAlign_toNat64,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
      rw [hmem_out (panByteAlignHOL (BitVec.ofNat 64 b)), hbe]
      intro off hoff heq
      have hp := hoff_props off hoff
      have htn : (BitVec.ofNat 64 (e0 + off)).toNat = e0 + off := Nat.mod_eq_of_lt (by omega)
      have := congrArg BitVec.toNat heq
      rw [hal_b, htn] at this
      exact hno (e0, 280) (by simp) ⟨by dsimp only; omega, by dsimp only; omega⟩
  have hRl8_e0 : ∀ x ∈ ([(e0, 280)] : List Ivl), x.1 % 8 = 0 := by
    intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact he0_8
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, hglob]
  have hApost : ArenaReady post := ⟨hGp, arenaOK_congr hglob hAs.2⟩
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq]
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq]
  have hrec_fo : (e0, 280) ∈ frameObjects s (e0, c0) := by simp [frameObjects]
  have hrec_disj_wti : ∀ i ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Nd_at,
      i.2 = 0 ∨ Disj (e0, 280) i := by
    intro i hi
    unfold InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls at hi
    simp only [List.mem_append] at hi
    rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
      exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).1 t ht i hfp)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
      exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _
        (InitECandidate.Solver.Wave8Contracts.M23.typedRec_in_fixedObjects s hr))
    · simp only [List.mem_singleton] at h3; subst h3
      have hfix_j : (if globN s "journal_cap" = 0 then 0 else globN s "journal",
          32 * globN s "journal_cap") ∈ fixedObjects s := by
        unfold fixedObjects
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
      exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ hfix_j)
    · exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _
        (InitECandidate.Solver.Wave8Contracts.M23.blockOut_in_fixedObjects h4))
    · exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _
        (InitECandidate.Solver.Wave8Contracts.M23.bal_in_fixedObjects h5))
    · exact Or.inr (hAT_at _ (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨_, hhead_mem, rfl⟩, hrec_fo⟩) i h6)
  have hcell : InitECandidate.Solver.Wave8Contracts.M23.SameTypedCells s post S Nd_at :=
    InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect.sameTypedCells
      (Rl := []) (extra := [(e0, 280)]) hAs.1.memaddrs hWT
      (fun _ h => by simp at h)
      (fun x hx => by simp at hx; subst hx; exact hrec_disj_wti)
      (by simpa using heff)
  have hfeq := InitECandidate.Solver.Wave8Contracts.M23.fixedObjects_eq_of_nonHeapGlobalsKept
    hAs.2 hWT.1 hWT.2.2.1 hcell (fun name _ _ _ => by rw [hglob])
  have hFT_post := InitECandidate.Solver.Wave8Contracts.M23.fixedTyped_of_eq hApost hWT.2.2.1 hh hsc hfeq
  obtain ⟨hWT_post, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.worldTypedWith_congr_w1 hAs hApost hh hsc
    (fun g _ => hglob_eq g) hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hW_post : WorldTyped post S :=
    ⟨hWT_post.1, hWT_post.2.1, hWT_post.2.2.1, Nd_at, hWT_post.2.2.2⟩
  have hmemW_ne : ∀ a : Nat, a < 2 ^ 64 →
      (∀ off ∈ headSimpleOffs, a ≠ e0 + off) → memW post a = memW s a := by
    intro a ha hne
    unfold memW
    rw [hmem_out (BitVec.ofNat 64 a)]
    intro off hoff heq
    have hp := hoff_props off hoff
    have := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega)] at this
    exact hne off hoff this
  have hpw_head_tail :
      (frameObjects s (e0, c0)).Pairwise Disj ∧
      (∀ o1 ∈ frameObjects s (e0, c0),
        ∀ ec ∈ chTail, ∀ o2 ∈ frameObjects s ec, Disj o1 o2) := by
    have hpw := hFO_pw
    rw [hch_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
    refine ⟨hpw.1, fun o1 ho1 ec hec o2 ho2 => hpw.2.2 o1 ho1 o2 ?_⟩
    exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, hec, rfl⟩, ho2⟩
  have hhead_disj_rest : ∀ o ∈ ((c0, 104) :: (memW s (e0 + 8), 32 * memW s (e0 + 232)) ::
      (memW s (e0 + 24), memW s (e0 + 40)) :: (memW s (e0 + 88), 24) ::
      frameLogs s (e0, c0) :: frameRet s (e0, c0) :: frameLogObjects s (e0, c0)),
      Disj (e0, 280) o := by
    have hpw0 := hpw_head_tail.1
    unfold frameObjects at hpw0
    exact (List.pairwise_cons.1 hpw0).1
  have hdisj_e0_nonrec : ∀ ec ∈ evmChain s,
      Disj (e0, 280) (ec.2, 104) ∧
      Disj (e0, 280) (memW s (ec.1 + 88), 24) ∧
      Disj (e0, 280) (frameLogs s ec) ∧
      (∀ i < memW s (memW s (ec.1 + 88) + 8),
        Disj (e0, 280) (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40)) := by
    intro ec hec
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · refine ⟨hhead_disj_rest _ (by simp), hhead_disj_rest _ (by simp),
        hhead_disj_rest _ (by simp), fun i hi => hhead_disj_rest _ ?_⟩
      simp only [List.mem_cons]
      right; right; right; right; right; right
      unfold frameLogObjects; dsimp only
      exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by
        unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
    · refine ⟨hpw_head_tail.2 _ hrec_fo ec htail _ (by simp [frameObjects]),
        hpw_head_tail.2 _ hrec_fo ec htail _ (by simp [frameObjects]),
        hpw_head_tail.2 _ hrec_fo ec htail _ (by simp [frameObjects]),
        fun i hi => hpw_head_tail.2 _ hrec_fo ec htail _ ?_⟩
      unfold frameObjects; apply List.mem_append_right
      unfold frameLogObjects; dsimp only
      exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by
        unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
  have htail_rec_eq : ∀ ec ∈ chTail, ∀ k, k + 8 ≤ 280 → memW post (ec.1 + k) = memW s (ec.1 + k) := by
    intro ec htail k hk
    have hFW := hFW_all ec (by rw [hch_eq]; exact List.mem_cons_of_mem _ htail)
    obtain ⟨hb_e, _, _, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hAs.2 hFW
    apply hmemW_ne (ec.1 + k) (by omega)
    intro off hoff heq
    have hp := hoff_props off hoff
    have hd := hpw_head_tail.2 (e0, 280) hrec_fo ec htail (ec.1, 280) (by simp [frameObjects])
    rcases hd with h0 | h0 | h1 | h2 <;> dsimp only at * <;> omega
  have hrec_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k ∉ headSimpleOffs → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨hb_e, hb_c, hb_88, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hAs.2 hFW
    have hc8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
    have h88_8 : (memW s (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2.1
    obtain ⟨hd_c, hd_88, _, _⟩ := hdisj_e0_nonrec ec hec
    refine ⟨?_,
      fun k hk hk8 => R14Shards.OpHandlersA.memW_eq_of_disj_eff heff hRl8_e0 hb_c hc8 hk8 hk
        (fun x hx => by simp at hx; subst hx; exact hd_c),
      fun k hk hk8 => R14Shards.OpHandlersA.memW_eq_of_disj_eff heff hRl8_e0 hb_88 h88_8 hk8 hk
        (fun x hx => by simp at hx; subst hx; exact hd_88)⟩
    intro k hk hknot
    apply hmemW_ne (ec.1 + k) (by omega)
    intro off hoff heq
    have hp := hoff_props off hoff
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · have : k = off := by dsimp only at heq; omega
      exact hknot (this ▸ hoff)
    · have hd := hpw_head_tail.2 (e0, 280) hrec_fo ec htail (ec.1, 280) (by simp [frameObjects])
      rcases hd with h0 | h0 | h1 | h2 <;> dsimp only at * <;> omega
  have hchain_aux : ∀ (fuel e c : Nat),
      (∀ ec ∈ evmChainFrom s fuel e c, ec ∈ evmChain s) →
      evmChainFrom post fuel e c = evmChainFrom s fuel e c := by
    intro fuel; induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro e c hsub
      have hec : (e, c) ∈ evmChain s := hsub (e, c) (by simp [evmChainFrom])
      obtain ⟨_, hc_eq, _⟩ := hrec_eq (e, c) hec
      have hc16 := hc_eq 16 (by omega) (by omega)
      have hc0 : memW post c = memW s c := by simpa using hc_eq 0 (by omega) (by omega)
      have hc8 := hc_eq 8 (by omega) (by omega)
      simp only [evmChainFrom, hc16, hc0, hc8]
      split
      · rfl
      · rename_i hne16
        rw [ih]; intro ec' hec'; exact hsub ec' (by simp [evmChainFrom, hne16, hec'])
  have hchain_eq : evmChain post = evmChain s := by
    unfold evmChain; rw [hglob_eq "ev", hglob_eq "cur_cont"]
    exact hchain_aux _ _ _ (fun _ h => h)
  have hframeLogs_eq : ∀ ec ∈ evmChain s, frameLogs post ec = frameLogs s ec := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    unfold frameLogs
    rw [he_eq 88 (by omega) (by decide),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega)]
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameRet
    rw [he_eq 216 (by omega) (by decide), he_eq 144 (by omega) (by decide)]
  have hlogs_congr : ∀ ec ∈ evmChain s,
      frameLogObjects post ec = frameLogObjects s ec ∧ LogsListOK post (memW post (ec.1 + 88)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨_, _, _, hfob⟩ := InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hAs.2 hFW
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    obtain ⟨_, _, hd_fl, hd_lr⟩ := hdisj_e0_nonrec ec hec
    have hl0 : memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) := by
      simpa using h88_eq 0 (by omega) (by omega)
    have hl8 : memW post (memW s (ec.1 + 88) + 8) = memW s (memW s (ec.1 + 88) + 8) :=
      h88_eq 8 (by omega) (by omega)
    have hl16 : memW post (memW s (ec.1 + 88) + 16) = memW s (memW s (ec.1 + 88) + 16) :=
      h88_eq 16 (by omega) (by omega)
    have harr_eq : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
        memW post (memW s (memW s (ec.1 + 88)) + 8 * i) = memW s (memW s (memW s (ec.1 + 88)) + 8 * i) := by
      intro i hi
      have hfl_in : frameLogs s ec ∈ frameObjects s ec := by simp [frameObjects]
      have hlen_le : memW s (memW s (ec.1 + 88) + 8) ≤ memW s (memW s (ec.1 + 88) + 16) :=
        hFW.2.2.2.2.2.2.2.2.2.2.2.1
      have hfl_b : (frameLogs s ec).1 + (frameLogs s ec).2 ≤ 2 ^ 64 := by
        rcases hfob _ hfl_in with h0 | hb
        · unfold frameLogs at h0; dsimp only at h0; omega
        · exact hb
      have hfl_8 : (memW s (memW s (ec.1 + 88))) % 8 = 0 := hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
      exact R14Shards.OpHandlersA.memW_eq_of_disj_eff heff hRl8_e0 hfl_b hfl_8 (by omega)
        (by unfold frameLogs; dsimp only; omega)
        (fun x hx => by simp at hx; subst hx; exact hd_fl)
    have hlr_eq : ∀ i (hi : i < memW s (memW s (ec.1 + 88) + 8)) off, off + 8 ≤ 40 → off % 8 = 0 →
        memW post (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + off) =
          memW s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + off) := by
      intro i hi off hoff hoff8
      have hlr_in : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40) ∈ frameObjects s ec := by
        unfold frameObjects; apply List.mem_append_right
        unfold frameLogObjects; dsimp only
        exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by
          unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
      have hlr_b : memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + 40 ≤ 2 ^ 64 := by
        rcases hfob _ hlr_in with h0 | hb
        · dsimp only at h0; omega
        · exact hb
      have hlr_8 : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) % 8 = 0 := by
        rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
        · have he88_in := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1.1
          have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
          rw [R11Shards.scratchStart_val] at h1; dsimp only at he88_in; omega
        · exact (hent i hi).2.1.1
      exact R14Shards.OpHandlersA.memW_eq_of_disj_eff heff hRl8_e0 hlr_b hlr_8 hoff8 hoff
        (fun x hx => by simp at hx; subst hx; exact hd_lr i hi)
    refine ⟨?_, ?_⟩
    · unfold frameLogObjects; dsimp only
      rw [he_eq 88 (by omega) (by decide), hl8]
      apply List.flatMap_congr; intro i hi; rw [List.mem_range] at hi
      rw [hl0, harr_eq i hi]
      have r0 := hlr_eq i hi 0 (by omega) (by omega)
      have r8 := hlr_eq i hi 8 (by omega) (by omega)
      have r16 := hlr_eq i hi 16 (by omega) (by omega)
      have r24 := hlr_eq i hi 24 (by omega) (by omega)
      have r32 := hlr_eq i hi 32 (by omega) (by omega)
      simp only [Nat.add_zero] at r0
      unfold logOwnedIvls logRecordIvls
      rw [r0, r8, r16, r24, r32, hglob_eq "vm_system_address"]
    · rw [he_eq 88 (by omega) (by decide)]
      rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨hw_l, hal_l, hlt28, hle_cap, hent⟩
      · exact Or.inl hz
      · right
        refine ⟨(R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 hw_l,
          InitECandidate.Solver.Wave8Contracts.M23.allocated_mono hh hsc hal_l,
          by rw [hl8]; exact hlt28, by rw [hl8, hl16]; exact hle_cap, fun i hi => ?_⟩
        rw [hl8] at hi; rw [hl0]
        obtain ⟨hwa, hle⟩ := hent i hi
        refine ⟨(R14Shards.OpHandlersA.wordAt_congr_dom hdom_eq).2 hwa, ?_⟩
        rw [harr_eq i hi]
        have r0 := hlr_eq i hi 0 (by omega) (by omega)
        have r8 := hlr_eq i hi 8 (by omega) (by omega)
        have r16 := hlr_eq i hi 16 (by omega) (by omega)
        have r24 := hlr_eq i hi 24 (by omega) (by omega)
        have r32 := hlr_eq i hi 32 (by omega) (by omega)
        simp only [Nat.add_zero] at r0
        unfold LogEntryOK at hle ⊢
        rw [r0, r8, r16, r24, r32, hglob_eq "heap_ptr"]
        exact ⟨(R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 hle.1, hle.2⟩
  have hframeObjects_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameObjects
    rw [he_eq 8 (by omega) (by decide), he_eq 232 (by omega) (by decide),
        he_eq 24 (by omega) (by decide), he_eq 40 (by omega) (by decide),
        he_eq 88 (by omega) (by decide),
        hframeLogs_eq ec hec, hframeRet_eq ec hec, (hlogs_congr ec hec).1]
  have hframeScratch_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega) (by decide), he_eq 232 (by omega) (by decide),
        he_eq 88 (by omega) (by decide)]
  have hmap_fo_eq : (evmChain s).map (frameObjects post) = (evmChain s).map (frameObjects s) :=
    List.map_congr_left hframeObjects_eq
  have hframeRoleSlots_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots; apply List.flatMap_congr; intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    rw [he_eq 136 (by omega) (by decide), he_eq 168 (by omega) (by decide),
        he_eq 176 (by omega) (by decide)]
  have hfp_eq_all : ∀ t ∈ S, htabFootprint post t = htabFootprint s t :=
    fun t ht => InitECandidate.Solver.Wave8Contracts.M23.htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1
  have htail_eq_s : (evmChain s).tail = chTail := by rw [hch_eq]; rfl
  have htail_sum_eq :
      (chTail.map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)) =
        (chTail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)) := by
    apply List.map_congr_left; intro ec htail
    rw [htail_rec_eq ec htail 64 (by omega), htail_rec_eq ec htail 192 (by omega)]
  have hR_val : OpDispatchSpec.evmR post =
      memW post (e0 + 64) + memW post (e0 + 192) +
        (((evmChain s).tail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) := by
    unfold OpDispatchSpec.evmR
    rw [hchain_eq, hch_eq, List.map_cons, List.sum_cons, htail_sum_eq, List.tail_cons]
  refine ⟨hApost, ?_, hchain_eq, hfeq, hfp_eq_all, ?_, hR_val⟩
  · unfold InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt
    refine ⟨hW_post, ?_⟩
    dsimp only; rw [hchain_eq]
    refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨ec, hec, hk0⟩ := hch_last
      have hec_mem := List.mem_of_mem_getLast? hec
      exact ⟨ec, hec, by rw [(hrec_eq ec hec_mem).2.1 16 (by omega) (by omega)]; exact hk0⟩
    · intro ec hec
      obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, _, c17⟩ := hFW_all ec hec
      have hlo_ok := (hlogs_congr ec hec).2
      have hmsg_ok : MsgOwned post S (memW post (ec.1 + 112)) := by
        rw [he_eq 112 (by omega) (by decide)]
        obtain ⟨hal_m, hw_m, hdt, hdf, hdfo, Nd_m, hTr_m, hdj_m⟩ := c17
        obtain ⟨hTr_int, hsub_int⟩ := R11Shards.triesTypedWith_inter hTr_at hTr_m
        set Ndi := Nd_at.filter (fun n => decide (n ∈ Nd_m))
        have hcell_i : InitECandidate.Solver.Wave8Contracts.M23.SameTypedCells s post S Ndi := by
          have hwti_sub : ∀ i ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Ndi,
              i ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Nd_at := by
            intro i hi; unfold InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls at hi ⊢
            rcases List.mem_append.1 hi with hpre | hne
            · exact List.mem_append_left _ hpre
            · apply List.mem_append_right; unfold nodeExtents at hne ⊢
              obtain ⟨n, hn, hnx⟩ := List.mem_flatMap.1 hne
              exact List.mem_flatMap.2 ⟨n, (List.mem_filter.1 hn).1, hnx⟩
          refine ⟨hcell.1, hcell.2.1, hcell.2.2.1, hcell.2.2.2.1,
            fun a ha ha8 ⟨i, hi, h1, h2⟩ => hcell.2.2.2.2.1 a ha ha8 ⟨i, hwti_sub i hi, h1, h2⟩,
            fun b hb ⟨i, hi, h1, h2⟩ => hcell.2.2.2.2.2 b hb ⟨i, hwti_sub i hi, h1, h2⟩⟩
        obtain ⟨hWT_i_post, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.worldTypedWith_congr_w1 hAs hApost hh hsc
          (fun g _ => hglob_eq g) hcell_i ⟨hWT.1, hWT.2.1, hWT.2.2.1, hTr_int⟩
          ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
        refine ⟨InitECandidate.Solver.Wave8Contracts.M23.allocated_mono hh hsc hal_m,
          (R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 hw_m,
          fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact hdt t ht i hi,
          by rw [hfeq]; exact hdf,
          by rw [hchain_eq]; intro ec' hec' o ho; rw [hframeObjects_eq ec' hec'] at ho; exact hdfo ec' hec' o ho,
          Ndi, hWT_i_post.2.2.2, fun o ho j hj => ?_⟩
        rw [InitECandidate.Solver.Wave8Contracts.M23.nodeExtents_eq hTr_int.1 hcell_i] at hj
        exact hdj_m o ho j (hsub_int j hj).2
      have hc5' : memW post (ec.1 + 16) ≤ memW post (ec.1 + 232) := by
        rw [he_eq 232 (by omega) (by decide)]
        have hec' := hec
        rw [hch_eq, List.mem_cons] at hec'
        rcases hec' with rfl | htail
        · exact hsp_le
        · rw [htail_rec_eq ec htail 16 (by omega)]; exact c5
      unfold FrameWF; dsimp only
      rw [he_eq 8 (by omega) (by decide), he_eq 232 (by omega) (by decide),
          he_eq 88 (by omega) (by decide), he_eq 24 (by omega) (by decide),
          he_eq 40 (by omega) (by decide),
          he_eq 32 (by omega) (by decide), he_eq 136 (by omega) (by decide),
          he_eq 168 (by omega) (by decide), he_eq 176 (by omega) (by decide),
          h88_eq 16 (by omega) (by omega), h88_eq 8 (by omega) (by omega),
          hframeLogs_eq ec hec,
          he_eq 216 (by omega) (by decide), he_eq 144 (by omega) (by decide),
          hframeRet_eq ec hec,
          hglob_eq "scratch_ptr", hglob_eq "frame_mem_ptr", hglob_eq "heap_ptr", hglob_eq "evm_empty"]
      rw [he_eq 88 (by omega) (by decide)] at hlo_ok
      have hc5_rw : memW post (ec.1 + 16) ≤ memW s (ec.1 + 232) := by
        simpa [he_eq 232 (by omega) (by decide)] using hc5'
      refine ⟨fun i hi => ⟨(c1 i hi).1, (R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 (c1 i hi).2⟩,
        c2, (R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 c3, c4, hc5_rw, c6, c7, c8, c9, c10, c11, c12,
        c13, (R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 c14, ?_, hlo_ok, hmsg_ok⟩
      rcases c15 with h0 | ⟨hin, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hin, (R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 hw⟩
    · intro ec hec
      have hec_tail : ec ∈ chTail := by rwa [htail_eq_s] at hec
      unfold FrameRoom
      rw [htail_rec_eq ec hec_tail 16 (by omega),
          htail_rec_eq ec hec_tail 232 (by omega)]
      exact hFR_all ec hec
    · intro i hi
      have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
      have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
      rw [(hrec_eq _ hi0).2.1 80 (by omega) (by omega),
          (hrec_eq _ hi0).2.1 72 (by omega) (by omega),
          (hrec_eq _ hi1).1 40 (by omega) (by decide)]
      exact hRW i hi
    · rw [hmap_fo_eq]; exact hFO_pw
    · intro ec hec o ho
      rw [hframeObjects_eq ec hec] at ho; rw [hfeq]
      exact ⟨fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact (hFO_disj ec hec o ho).1 t ht i hi,
        (hFO_disj ec hec o ho).2⟩
    · rw [hmap_fo_eq]
      refine ⟨Nd_at, hWT_post.2.2.2, fun o ho j hj => ?_⟩
      rw [InitECandidate.Solver.Wave8Contracts.M23.nodeExtents_eq hTr_at.1 hcell] at hj
      exact hAT_at o ho j hj
    · have hworldRefs_eq : worldTableRefs post S = worldTableRefs s S := by
        unfold worldTableRefs recordSlots
        rw [hglob_eq "ws", hglob_eq "bs", hglob_eq "ts",
            show globalTableRoots.map (globN post) = globalTableRoots.map (globN s) by
              simp only [globalTableRoots, List.map, hglob_eq],
            InitECandidate.Solver.Wave8Contracts.M23.balRecords_eq hWT.1 hcell (hglob_eq "bal_accounts"),
            hglob_eq "journal_n", hglob_eq "journal"]
        have hws_sl : (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW post (globN s "ws" + k)) =
            (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW s (globN s "ws" + k)) := by
          split; · rfl
          rename_i hnz; apply List.map_congr_left; intro k hk
          exact InitECandidate.Solver.Wave8Contracts.M23.memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 40) (by decide) hnz
            (by simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl <;> omega)
        have hbs_sl : (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW post (globN s "bs" + k)) =
            (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW s (globN s "bs" + k)) := by
          split; · rfl
          rename_i hnz; apply List.map_congr_left; intro k hk
          exact InitECandidate.Solver.Wave8Contracts.M23.memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz
            (by simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
        have hts_sl : (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW post (globN s "ts" + k)) =
            (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW s (globN s "ts" + k)) := by
          split; · rfl
          rename_i hnz; apply List.map_congr_left; intro k hk
          exact InitECandidate.Solver.Wave8Contracts.M23.memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz
            (by simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
        have hnest_bs : (if globN s "bs" ≠ 0 ∧ memW post (globN s "bs" + 32) ∈ S then htabValues post (memW post (globN s "bs" + 32)) else []) =
            (if globN s "bs" ≠ 0 ∧ memW s (globN s "bs" + 32) ∈ S then htabValues s (memW s (globN s "bs" + 32)) else []) := by
          by_cases hnz : globN s "bs" = 0
          · simp [hnz]
          · rw [InitECandidate.Solver.Wave8Contracts.M23.memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz (by omega)]
            by_cases hmS : memW s (globN s "bs" + 32) ∈ S
            · simp [hnz, hmS, InitECandidate.Solver.Wave8Contracts.M23.htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
            · simp [hnz, hmS]
        have hnest_ts : (if globN s "ts" ≠ 0 ∧ memW post (globN s "ts" + 32) ∈ S then htabValues post (memW post (globN s "ts" + 32)) else []) =
            (if globN s "ts" ≠ 0 ∧ memW s (globN s "ts" + 32) ∈ S then htabValues s (memW s (globN s "ts" + 32)) else []) := by
          by_cases hnz : globN s "ts" = 0
          · simp [hnz]
          · rw [InitECandidate.Solver.Wave8Contracts.M23.memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz (by omega)]
            by_cases hmS : memW s (globN s "ts" + 32) ∈ S
            · simp [hnz, hmS, InitECandidate.Solver.Wave8Contracts.M23.htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
            · simp [hnz, hmS]
        have hbal_fl : (balRecords s).flatMap (fun ad => [memW post ad, memW post (ad + 8)]) =
            (balRecords s).flatMap (fun ad => [memW s ad, memW s (ad + 8)]) := by
          apply List.flatMap_congr; intro ad had
          have had_mem := InitECandidate.Solver.Wave8Contracts.M23.balRecord_ivl_mem had
          rcases InitECandidate.Solver.Wave8Contracts.M23.fixedObject_le_2pow64 hAs.2 hWT.2.2.1
              (InitECandidate.Solver.Wave8Contracts.M23.bal_in_fixedObjects had_mem) with h0 | had_bnd
          · dsimp only at h0; omega
          · dsimp only at had_bnd
            have hwti_ad := InitECandidate.Solver.Wave8Contracts.M23.mem_worldTypedIvls_bal (S := S) (Nd := Nd_at) had_mem
            rw [InitECandidate.Solver.Wave8Contracts.M23.memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩,
                InitECandidate.Solver.Wave8Contracts.M23.memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩]
        have hjrn_mp : (List.range (globN s "journal_n")).map (fun k => memW post (globN s "journal" + 32 * k)) =
            (List.range (globN s "journal_n")).map (fun k => memW s (globN s "journal" + 32 * k)) := by
          apply List.map_congr_left; intro k hk; rw [List.mem_range] at hk
          have hjc_le := hWT.2.1.1
          have hjc_ne : globN s "journal_cap" ≠ 0 := by omega
          rcases hWT.2.1.2.2.1 with h0 | ⟨hal, _⟩
          · exact absurd h0 hjc_ne
          · have hbnd := InitECandidate.Solver.Wave8Contracts.M23.allocated_le_2pow64 hAs.2 hal; dsimp only at hbnd
            have hkle : 32 * k + 8 ≤ 32 * globN s "journal_cap" := by omega
            exact InitECandidate.Solver.Wave8Contracts.M23.memW_eq_of_cellHits hcell (by omega)
              (InitECandidate.Solver.Wave8Contracts.M23.mem_worldTypedIvls_journal (S := S) (Nd := Nd_at) hjc_ne)
              ⟨by dsimp only; omega, by dsimp only; omega⟩
        dsimp only
        rw [hglob_eq "bs", hglob_eq "ts", hws_sl, hbs_sl, hts_sl, hnest_bs, hnest_ts, hbal_fl, hjrn_mp]
      have hdelEx_iff : ∀ i t, DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
        intro i t; unfold DelExclusive; rw [hworldRefs_eq]
        refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
          forall_congr' fun k => imp_congr_right fun hk => ?_)
        have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
        have hk_ok : k + 8 ≤ 280 ∧ k ∉ headSimpleOffs := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl <;> exact ⟨by omega, by decide⟩
        rw [(hrec_eq _ hj_mem).1 k hk_ok.1 hk_ok.2]
      intro i hi
      have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
      have hm_eq := (hrec_eq _ hi_mem).2.1 48 (by omega) (by omega)
      have hmm_eq := (hrec_eq _ hi_mem).2.1 56 (by omega) (by omega)
      have he24_eq := (hrec_eq _ hi_mem).1 24 (by omega) (by decide)
      have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
          ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
        apply List.map_congr_left; intro ec hec
        exact (hrec_eq ec (List.mem_of_mem_take hec)).1 136 (by omega) (by decide)
      have hM := hMarks i hi; dsimp only at hM ⊢
      rw [hm_eq, hmm_eq, he24_eq, hframeScratch_eq _ hi_mem, hfeq, htake_eq]
      obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
      refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
      · intro j hj hij
        have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
        rw [hframeScratch_eq _ hj_mem, hframeObjects_eq _ hj_mem, hframeLogs_eq _ hj_mem,
            (hrec_eq _ hj_mem).1 112 (by omega) (by decide)]
        exact m5 j hj hij
      · intro t ht
        rw [hfp_eq_all t ht, hdelEx_iff i t]; exact m8 t ht
    · have hcg : ∀ g ∈ InitECandidate.Solver.Wave8Contracts.M23.coreWorldGlobals,
          globN post g = globN s g := fun g _ => hglob_eq g
      rw [InitECandidate.Solver.Wave8Contracts.M23.worldRoleSlots_eq hAs.2 hWT.1 hWT.2.2.1 hcell hcg,
          hframeRoleSlots_eq,
          InitECandidate.Solver.Wave8Contracts.M23.journalRoleSlots_eq hAs.2 hWT.2.1 hWT.2.2.1 hcell hcg]
      unfold RolesOK at hRoles ⊢
      refine ⟨fun a ha => ?_, hRoles.2⟩
      obtain ⟨haS, hkl⟩ := hRoles.1 a ha
      have htb := ((hWT.1.2.1 a.1 haS).1.1 (a.1, 88) (by simp [htabFootprint])).1
      rw [InitECandidate.Solver.Wave8Contracts.M23.htab_hdr_eq hcell haS htb 0 (by omega)]
      exact ⟨haS, hkl⟩
    · have hsum_eq : ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum =
          memW post (e0 + 64) + memW post (e0 + 192) +
            (((evmChain s).tail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) := by
        unfold OpDispatchSpec.evmR at hR_val; rw [hchain_eq] at hR_val; exact hR_val
      rw [hsum_eq]; exact hgas_le
  · intro ec hec
    obtain ⟨he_eq, hc_eq, _⟩ := hrec_eq ec hec
    exact ⟨hframeObjects_eq ec hec, hframeScratch_eq ec hec, hframeLogs_eq ec hec,
      he_eq 24 (by omega) (by decide), he_eq 32 (by omega) (by decide),
      he_eq 40 (by omega) (by decide), he_eq 112 (by omega) (by decide),
      hc_eq 56 (by omega) (by omega)⟩

theorem fcBranchState_of_head_simple {F : Type}
    {s0 s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (h : FcBranchState s0 s S)
    (hGp : GuestInv post)
    (hglob : post.globals = s.globals)
    (hbe : post.be = s.be)
    (hloc : post.locals = s.locals)
    (hmem_out : ∀ x : BitVec 64,
      (∀ off ∈ headSimpleOffs, x ≠ BitVec.ofNat 64 (globN s "ev" + off)) →
      post.memory x = s.memory x)
    (hsp_le : memW post (globN s "ev" + 16) ≤ memW s (globN s "ev" + 232))
    (hgas : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) +
      (((evmChain s).tail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) + 1 < 2 ^ 64)
    (hR : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) +
      (((evmChain s).tail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) ≤
        OpDispatchSpec.evmR s0) :
    FcBranchState s0 post S := by
  obtain ⟨hAp, hIp, hch, hfix, htab, hframes, hRp⟩ :=
    evmInvAt_of_head_simple h.arena h.inv hGp hglob hbe hmem_out hsp_le hgas
  have hhp : globN s "heap_ptr" ≤ globN post "heap_ptr" := by
    unfold globN; rw [hglob]
  have hRel := releaseReadyAt_transport h.release hhp hch
    (fun ec hec => (hframes ec hec).2.1)
    (fun ec hec => ⟨(hframes ec hec).2.2.2.1, (hframes ec hec).2.2.2.2.2.1⟩)
    (fun ec hec => Or.inl (hframes ec hec).2.2.1)
    (fun ec hec => (hframes ec hec).2.2.2.2.2.2.1)
    (fun t ht => Or.inl (htab t ht)) hfix
  refine ⟨hAp, hIp, hRel, fcEntryLocals_congr_locals hloc h.locals_ok,
    hch.trans h.chain_eq, ?_, ?_, ?_, ?_⟩
  · rw [hch]; exact h.length_eq
  · rw [hRp]; exact hR
  · intro ec hec
    rw [hch] at hec
    obtain ⟨a, b, c, d⟩ := h.cells ec hec
    have hf := (hframes ec hec).2.2.2
    exact ⟨hf.1.trans a, hf.2.1.trans b, hf.2.2.1.trans c, hf.2.2.2.2.trans d⟩
  · have hev : globN post "ev" = globN s "ev" := by unfold globN; rw [hglob]
    exact hev.trans h.ev_eq

def NonDelAccessTable {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) (t0 : Nat) : Prop :=
  t0 ∈ S ∧
  (∀ ec ∈ evmChain s, memW s (ec.1 + 136) ≠ t0) ∧
  (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) ∧
  (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
  globN s "bal_accounts" ≠ t0 ∧
  (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
  (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0)

structure FcPoppedChild {F : Type} (s0 st : PanSemStateFiniteExact 64 F)
    (S : List Nat) : Prop where
  child_scr : Inside (globN s0 "ev", 280) (globN st "scratch_ptr") scratchEnd ∧
    WordsOK st (globN s0 "ev", 280)
  rec_scr : Inside (globN s0 "cur_cont", 104) (globN st "scratch_ptr") scratchEnd ∧
    WordsOK st (globN s0 "cur_cont", 104)
  child_disj_fo : ∀ ec ∈ evmChain st, ∀ o ∈ frameObjects st ec, Disj (globN s0 "ev", 280) o
  rec_disj_fo : ∀ ec ∈ evmChain st, ∀ o ∈ frameObjects st ec, Disj (globN s0 "cur_cont", 104) o
  child_disj_ht : ∀ t ∈ S, ∀ i ∈ htabFootprint st t, Disj (globN s0 "ev", 280) i
  rec_disj_ht : ∀ t ∈ S, ∀ i ∈ htabFootprint st t, Disj (globN s0 "cur_cont", 104) i
  child_disj_fix : ∀ j ∈ fixedObjects st, Disj (globN s0 "ev", 280) j
  rec_disj_fix : ∀ j ∈ fixedObjects st, Disj (globN s0 "cur_cont", 104) j
  child_logs_scr : Inside (memW st (globN s0 "ev" + 88), 24) (globN st "scratch_ptr") scratchEnd ∧
    WordsOK st (memW st (globN s0 "ev" + 88), 24)
  child_logs_disj_fo : ∀ ec ∈ evmChain st, ∀ o ∈ frameObjects st ec,
    Disj (memW st (globN s0 "ev" + 88), 24) o ∧ Disj (frameLogs st (globN s0 "ev", globN s0 "cur_cont")) o
  child_logs_disj_ht : ∀ t ∈ S, ∀ i ∈ htabFootprint st t,
    Disj (memW st (globN s0 "ev" + 88), 24) i ∧ Disj (frameLogs st (globN s0 "ev", globN s0 "cur_cont")) i
  child_logs_arr_in : Inside (frameLogs st (globN s0 "ev", globN s0 "cur_cont")) sourceBase (globN st "heap_ptr") ∨
    Inside (frameLogs st (globN s0 "ev", globN s0 "cur_cont")) (globN st "scratch_ptr") scratchEnd
  child_logs_arr_wok : WordsOK st (frameLogs st (globN s0 "ev", globN s0 "cur_cont"))
  child_logs_ok : LogsListOK st (memW st (globN s0 "ev" + 88))
  child_logs_len_le : memW st (memW st (globN s0 "ev" + 88) + 8) ≤
    memW st (memW st (globN s0 "ev" + 88) + 16)
  child_log_objs_pw : (frameLogObjects st (globN s0 "ev", globN s0 "cur_cont")).Pairwise Disj
  child_log_objs_disj_fo : ∀ o1 ∈ frameLogObjects st (globN s0 "ev", globN s0 "cur_cont"),
    ∀ ec ∈ evmChain st, ∀ o2 ∈ frameObjects st ec, Disj o1 o2
  child_log_objs_disj_ht : ∀ o1 ∈ frameLogObjects st (globN s0 "ev", globN s0 "cur_cont"),
    ∀ t ∈ S, ∀ i ∈ htabFootprint st t, Disj o1 i
  child_log_objs_disj_fix : ∀ o1 ∈ frameLogObjects st (globN s0 "ev", globN s0 "cur_cont"),
    ∀ j ∈ fixedObjects st, Disj o1 j
  child_log_objs_avoids_tries : AvoidsTries st S (frameLogObjects st (globN s0 "ev", globN s0 "cur_cont"))
  child_log_objs_disj_msg : ∀ o ∈ frameLogObjects st (globN s0 "ev", globN s0 "cur_cont"),
    ∀ ec ∈ evmChain st, Disj (memW st (ec.1 + 112), 176) o
  addr_table_ok : NonDelAccessTable st S (memW st (globN s0 "ev" + 168))
  key_table_ok : NonDelAccessTable st S (memW st (globN s0 "ev" + 176))
  parent_room : memW st (globN st "ev" + 16) + 1 ≤ memW st (globN st "ev" + 232)
  out_win_ok : memW s0 (globN s0 "cur_cont" + 16) ≠ 2 →
    memW s0 (globN s0 "cur_cont" + 80) = 0 ∨
      memW s0 (globN s0 "cur_cont" + 72) + memW s0 (globN s0 "cur_cont" + 80) ≤
        memW st (globN st "ev" + 40)

theorem preludeRel_pop_full {F : Type}
    {s0 s post : PanSemStateFiniteExact 64 F} (h : PreludeRel s0 s)
    (hne : memW s (globN s "cur_cont" + 16) ≠ 0)
    (hAp : ArenaReady post) (hm : post.memory = s.memory)
    (hd : post.memaddrs = s.memaddrs) (hb : post.be = s.be)
    (hev : globN post "ev" = memW s (globN s "cur_cont"))
    (hcc : globN post "cur_cont" = memW s (globN s "cur_cont" + 8))
    (hg : ∀ name : String, name ≠ "ev" → name ≠ "cur_cont" →
      globN post name = globN s name)
    (hl : post.locals = s.locals)
    (hparent : memW s (globN s "cur_cont") = memW s0 (globN s0 "cur_cont")) :
    ∃ S, FcBranchState s0 post S ∧ FcPoppedChild s0 post S ∧
      OpDispatchSpec.evmR post + (memW post (globN s0 "ev" + 64) + memW post (globN s0 "ev" + 192)) ≤
        OpDispatchSpec.evmR s0 ∧
      OpDispatchSpec.evmR post + (memW post (globN s0 "ev" + 64) + memW post (globN s0 "ev" + 192)) + 1 <
        2 ^ 64 := by
  have hmw : ∀ a, memW post a = memW s a := fun a => by
    unfold memW; rw [hm]
  have hhead := congrArg List.head? h.chain_eq
  rw [evmChain_cons, evmChain_cons] at hhead
  simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at hhead
  have hev_s : globN s "ev" = globN s0 "ev" := hhead.1
  have hcur : globN s "cur_cont" = globN s0 "cur_cont" := hhead.2
  have hmem0 : (globN s0 "ev", globN s0 "cur_cont") ∈ evmChain s0 := by
    rw [evmChain_cons]; exact List.mem_cons_self
  have hmem_s : (globN s0 "ev", globN s0 "cur_cont") ∈ evmChain s := by
    rw [h.chain_eq]; exact hmem0
  have hcm : memW s (globN s "cur_cont" + 48) =
      memW s0 (globN s0 "cur_cont" + 48) := by
    rw [hcur]; exact h.mark_eq
  have hcmm : memW s (globN s "cur_cont" + 56) =
      memW s0 (globN s0 "cur_cont" + 56) := by
    rw [hcur]; exact (h.cells _ hmem0).2.2.2
  obtain ⟨S, hI⟩ := h.inv.2
  obtain ⟨S', hS'_sub, hS'_cases, hIp, hch_p, hR_sum⟩ :=
    evmInvAt_of_pop_globals h.inv.1 hI hne hAp hm hd hb hev hcc hg
  have hRel := releaseReadyAt_of_pop h.inv.1 hI hne hm hg hch_p hS'_sub hS'_cases
  have hcons := evmChain_cons_of_cont_ne_zero hne
  have hcons0 : evmChain s = (globN s0 "ev", globN s0 "cur_cont") :: (evmChain s).tail := by
    conv_lhs => rw [hcons]
    conv_rhs => rw [hcons]
    simp [hev_s, hcur]
  have hlen_p : (evmChain post).length + 1 = (evmChain s0).length := by
    rw [hch_p, ← h.chain_eq]
    conv_rhs => rw [hcons0]
    simp
  have hBs : FcBranchState s0 post S' := by
    refine ⟨hAp, hIp, ?_, fcEntryLocals_congr_locals hl h.locals_ok,
      hch_p.trans (congrArg List.tail h.chain_eq), hlen_p, ?_, ?_, hev.trans hparent⟩
    · rw [hcm, hcmm] at hRel; exact hRel
    · have := h.r_le; omega
    · intro ec hec
      have hec_s : ec ∈ evmChain s := List.mem_of_mem_tail (hch_p ▸ hec)
      have hec_0 : ec ∈ evmChain s0 := h.chain_eq ▸ hec_s
      obtain ⟨a0, b0, c0, d0⟩ := h.cells ec hec_0
      exact ⟨(hmw _).trans a0, (hmw _).trans b0, (hmw _).trans c0, (hmw _).trans d0⟩
  obtain ⟨hW_s, _, _, _, hFW_s, hFR_s, hRW_s, hFO_pw_s, hFO_disj_s, hAT_s, _, hRoles_s, hGas_s⟩ := hI
  have hFW_child := hFW_s _ hmem_s
  have hsc_eq : globN post "scratch_ptr" = globN s "scratch_ptr" := hg "scratch_ptr" (by decide) (by decide)
  have hhp_eq : globN post "heap_ptr" = globN s "heap_ptr" := hg "heap_ptr" (by decide) (by decide)
  have hvmsa_eq : globN post "vm_system_address" = globN s "vm_system_address" :=
    hg "vm_system_address" (by decide) (by decide)
  have hfo_eq : ∀ ec, frameObjects post ec = frameObjects s ec := fun ec => by
    unfold frameObjects frameLogs frameRet frameLogObjects logOwnedIvls logRecordIvls
    simp only [hmw, hvmsa_eq]
  have hfl_eq : ∀ ec, frameLogs post ec = frameLogs s ec := fun ec => by
    unfold frameLogs; simp only [hmw]
  have hflo_eq : ∀ ec, frameLogObjects post ec = frameLogObjects s ec := fun ec => by
    unfold frameLogObjects logOwnedIvls logRecordIvls; simp only [hmw, hvmsa_eq]
  have hfp_eq : ∀ t, htabFootprint post t = htabFootprint s t := fun t => by
    unfold htabFootprint hdr; simp only [hmw]
  have hhv_eq : ∀ t, htabValues post t = htabValues s t := fun t => by
    unfold htabValues hdr nodeF; simp only [hmw]
  have hbr_eq0 : balRecords post = balRecords s := by
    unfold balRecords hdr nodeF
    simp only [hmw, hg "bal_accounts" (by decide) (by decide)]
  have hfix_eq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects blockOutObjects balObjects lstObjects
    simp only [hmw, hhv_eq, hbr_eq0, hg "bo" (by decide) (by decide),
      hg "journal" (by decide) (by decide), hg "journal_cap" (by decide) (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne_gn : gn.1 ≠ "ev" ∧ gn.1 ≠ "cur_cont" := by
      revert gn hgn; decide
    rw [hg gn.1 hne_gn.1 hne_gn.2]
  have hpw_split :
      (frameObjects s (globN s0 "ev", globN s0 "cur_cont")).Pairwise Disj ∧
      (∀ o1 ∈ frameObjects s (globN s0 "ev", globN s0 "cur_cont"),
        ∀ ec ∈ (evmChain s).tail, ∀ o2 ∈ frameObjects s ec, Disj o1 o2) := by
    have hpw := hFO_pw_s
    rw [hcons0, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
    refine ⟨hpw.1, fun o1 ho1 ec hec o2 ho2 => hpw.2.2 o1 ho1 o2 ?_⟩
    exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, hec, rfl⟩, ho2⟩
  have hacc_ok : ∀ (off : Nat) (rname : String),
      (off = 168 ∧ rname = "frame.addr") ∨ (off = 176 ∧ rname = "frame.key") →
      NonDelAccessTable post S' (memW post (globN s0 "ev" + off)) := by
    intro off rname hor
    rw [hmw]
    set tacc := memW s (globN s0 "ev" + off)
    have htacc_S : tacc ∈ S := by
      rcases hor with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hFW_child.2.2.2.2.2.2.2.2.1
      · exact hFW_child.2.2.2.2.2.2.2.2.2.1
    have htacc_frs : (tacc, rname) ∈ frameRoleSlots s (evmChain s) := by
      unfold frameRoleSlots
      refine List.mem_flatMap.2 ⟨(globN s0 "ev", globN s0 "cur_cont"), hmem_s, ?_⟩
      rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [tacc]
    have hr_ne_del : rname ≠ "frame.del" := by
      rcases hor with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
    have htacc_ne_del : ∀ ec ∈ evmChain s, memW s (ec.1 + 136) ≠ tacc := by
      intro ec hec heq
      have hdel_frs : (memW s (ec.1 + 136), "frame.del") ∈ frameRoleSlots s (evmChain s) := by
        unfold frameRoleSlots
        exact List.mem_flatMap.2 ⟨ec, hec, by simp⟩
      have hpw_fr := (List.pairwise_append.1 hRoles_s.2.1).2.1
      rcases List.pairwise_iff_getElem.1 hpw_fr with hpw_idx
      obtain ⟨i1, hi1, hget1⟩ := List.mem_iff_getElem.1 htacc_frs
      obtain ⟨i2, hi2, hget2⟩ := List.mem_iff_getElem.1 hdel_frs
      by_cases hij : i1 = i2
      · subst hij; rw [hget1] at hget2
        exact hr_ne_del (Prod.mk.inj hget2).2
      · rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
        · have hrel := hpw_idx i1 i2 hi1 hi2 hlt
          rw [hget1, hget2] at hrel
          exact hr_ne_del (hrel heq.symm).1
        · have hrel := hpw_idx i2 i1 hi2 hi1 hgt
          rw [hget1, hget2] at hrel
          exact hr_ne_del (hrel heq).1.symm
    have htacc_S' : tacc ∈ S' := by
      rcases hS'_cases with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact htacc_S
      · refine List.mem_filter.2 ⟨htacc_S, bne_iff_ne.2 ?_⟩
        intro heq
        exact htacc_ne_del (globN s0 "ev", globN s0 "cur_cont") hmem_s
          (by rw [← hev_s]; exact heq.symm)
    have hnw := (@frame_access_not_in_world_or_journal F s S (evmChain s)
      (globN s0 "ev", globN s0 "cur_cont") off hRoles_s hmem_s
      (by rcases hor with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp)).1
    have htacc_pos : 0 < tacc := by
      have := ((hW_s.1.2.1 tacc htacc_S).1.1 (tacc, 88) (by simp [htabFootprint])).1.1
      have hsb : 0 < sourceBase := by decide
      dsimp at this; omega
    have hws_eq : globN post "ws" = globN s "ws" := hg "ws" (by decide) (by decide)
    have hbs_eq : globN post "bs" = globN s "bs" := hg "bs" (by decide) (by decide)
    have hts_eq : globN post "ts" = globN s "ts" := hg "ts" (by decide) (by decide)
    have hba_eq : globN post "bal_accounts" = globN s "bal_accounts" :=
      hg "bal_accounts" (by decide) (by decide)
    have hbr_eq : balRecords post = balRecords s := hbr_eq0
    refine ⟨htacc_S', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ec hec; rw [hmw]; exact htacc_ne_del ec (List.mem_of_mem_tail (hch_p ▸ hec))
    · intro hws heq; rw [hws_eq] at hws; rw [hmw, hws_eq] at heq
      refine hnw (memW s (globN s "ws" + 32), "ws+32") ?_ heq
      unfold worldRoleSlots
      refine List.mem_filter.2 ⟨?_, by simp [heq, Nat.ne_of_gt htacc_pos]⟩
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      unfold recRoles; simp [hws]
    · intro hbs heq; rw [hbs_eq] at hbs; rw [hmw, hbs_eq] at heq
      refine hnw (memW s (globN s "bs" + 32), "bs+32") ?_ heq
      unfold worldRoleSlots
      refine List.mem_filter.2 ⟨?_, by simp [heq, Nat.ne_of_gt htacc_pos]⟩
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
      unfold recRoles; simp [hbs]
    · intro heq; rw [hba_eq] at heq
      refine hnw (globN s "bal_accounts", "bal_accounts") ?_ heq
      unfold worldRoleSlots
      refine List.mem_filter.2 ⟨?_, by simp [heq, Nat.ne_of_gt htacc_pos]⟩
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      apply List.mem_append_right; simp
    · intro ad had heq; rw [hbr_eq] at had; rw [hmw] at heq
      refine hnw (memW s ad, "bal.stor") ?_ heq
      unfold worldRoleSlots
      refine List.mem_filter.2 ⟨?_, by simp [heq, Nat.ne_of_gt htacc_pos]⟩
      apply List.mem_append_right
      exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
    · intro hts heq; rw [hts_eq] at hts; rw [hmw, hts_eq] at heq
      refine hnw (memW s (globN s "ts" + 32), "ts+32") ?_ heq
      unfold worldRoleSlots
      refine List.mem_filter.2 ⟨?_, by simp [heq, Nat.ne_of_gt htacc_pos]⟩
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      apply List.mem_append_left; apply List.mem_append_right
      unfold recRoles; simp [hts]
  have hhead_p_in_tail : (globN post "ev", globN post "cur_cont") ∈ (evmChain s).tail := by
    rw [← hch_p, evmChain_cons]; exact List.mem_cons_self
  have hproom : memW post (globN post "ev" + 16) + 1 ≤ memW post (globN post "ev" + 232) := by
    rw [hmw, hmw]; exact hFR_s _ hhead_p_in_tail
  have hout_win : memW s0 (globN s0 "cur_cont" + 16) ≠ 2 →
      memW s0 (globN s0 "cur_cont" + 80) = 0 ∨
        memW s0 (globN s0 "cur_cont" + 72) + memW s0 (globN s0 "cur_cont" + 80) ≤
          memW post (globN post "ev" + 40) := by
    intro hne2
    obtain ⟨ho72, ho80⟩ := h.out_eq hne2
    have hch_p_cons := evmChain_cons post
    have hcons01 : evmChain s =
        (globN s0 "ev", globN s0 "cur_cont") ::
          (globN post "ev", globN post "cur_cont") :: (evmChain post).tail := by
      rw [hcons0, ← hch_p]
      conv_lhs => rw [hch_p_cons]
      conv_rhs => rw [hch_p_cons]
      simp
    have h01 : 0 + 1 < (evmChain s).length := by
      rw [hcons01]; simp
    have hrw0 := hRW_s 0 h01
    have hrw0' : memW s (globN s0 "cur_cont" + 80) = 0 ∨
        memW s (globN s0 "cur_cont" + 72) + memW s (globN s0 "cur_cont" + 80) ≤
          memW s (globN post "ev" + 40) := by
      simpa [hcons01] using hrw0
    rw [ho72, ho80] at hrw0'
    rw [hmw]
    exact hrw0'
  refine ⟨S', hBs, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hacc_ok 168 "frame.addr" (Or.inl ⟨rfl, rfl⟩),
      hacc_ok 176 "frame.key" (Or.inr ⟨rfl, rfl⟩),
      hproom, hout_win⟩
    · rw [hsc_eq]
      exact ⟨(hFW_child.1 (globN s0 "ev", 280) (by simp)).1,
        (R14Shards.OpHandlersA.wordsOK_congr_dom hd).mpr (by
          simpa [WordsOK, WordAt, hm] using (hFW_child.1 (globN s0 "ev", 280) (by simp)).2)⟩
    · rw [hsc_eq]
      exact ⟨(hFW_child.1 (globN s0 "cur_cont", 104) (by simp)).1,
        (R14Shards.OpHandlersA.wordsOK_congr_dom hd).mpr (by
          simpa [WordsOK, WordAt, hm] using (hFW_child.1 (globN s0 "cur_cont", 104) (by simp)).2)⟩
    · intro ec hec o ho
      rw [hch_p] at hec; rw [hfo_eq] at ho
      exact hpw_split.2 _ (by simp [frameObjects]) ec hec o ho
    · intro ec hec o ho
      rw [hch_p] at hec; rw [hfo_eq] at ho
      exact hpw_split.2 _ (by simp [frameObjects]) ec hec o ho
    · intro t ht i hi
      rw [hfp_eq] at hi
      exact (hFO_disj_s _ hmem_s _ (by simp [frameObjects])).1 t (hS'_sub t ht) i hi
    · intro t ht i hi
      rw [hfp_eq] at hi
      exact (hFO_disj_s _ hmem_s _ (by simp [frameObjects])).1 t (hS'_sub t ht) i hi
    · intro j hj; rw [hfix_eq] at hj
      exact (hFO_disj_s _ hmem_s _ (by simp [frameObjects])).2 j hj
    · intro j hj; rw [hfix_eq] at hj
      exact (hFO_disj_s _ hmem_s _ (by simp [frameObjects])).2 j hj
    · rw [hmw, hsc_eq]
      exact ⟨(hFW_child.1 (memW s (globN s0 "ev" + 88), 24) (by simp)).1,
        by
          have hw := (hFW_child.1 (memW s (globN s0 "ev" + 88), 24) (by simp)).2
          refine ⟨hw.1, hw.2.1, fun k hk => ?_⟩
          obtain ⟨w, hdom_k, hmem_k⟩ := hw.2.2 k hk
          exact ⟨w, hd ▸ hdom_k, hm ▸ hmem_k⟩⟩
    · intro ec hec o ho
      rw [hch_p] at hec; rw [hfo_eq] at ho; rw [hmw, hfl_eq]
      exact ⟨hpw_split.2 _ (by simp [frameObjects]) ec hec o ho,
        hpw_split.2 _ (by simp [frameObjects]) ec hec o ho⟩
    · intro t ht i hi
      rw [hfp_eq] at hi; rw [hmw, hfl_eq]
      exact ⟨(hFO_disj_s _ hmem_s _ (by simp [frameObjects])).1 t (hS'_sub t ht) i hi,
        (hFO_disj_s _ hmem_s _ (by simp [frameObjects])).1 t (hS'_sub t ht) i hi⟩
    · rw [hfl_eq, hhp_eq, hsc_eq]
      exact hFW_child.2.2.2.2.2.2.2.2.2.2.2.2.1
    · rw [hfl_eq]
      have hw := hFW_child.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      refine ⟨hw.1, hw.2.1, fun k hk => ?_⟩
      obtain ⟨w, hdom_k, hmem_k⟩ := hw.2.2 k hk
      exact ⟨w, hd ▸ hdom_k, hm ▸ hmem_k⟩
    · rw [hmw]
      rcases hFW_child.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨hw_l, hal_l, hlt28, hle_cap, hent⟩
      · exact Or.inl hz
      · right
        have hw_lp : WordsOK post (memW s (globN s0 "ev" + 88), 24) := by
          refine ⟨hw_l.1, hw_l.2.1, fun k hk => ?_⟩
          obtain ⟨w, hdom_k, hmem_k⟩ := hw_l.2.2 k hk
          exact ⟨w, hd ▸ hdom_k, hm ▸ hmem_k⟩
        have hal_lp : Allocated post (memW s (globN s0 "ev" + 88), 24) := by
          unfold Allocated; rw [hhp_eq, hsc_eq]; exact hal_l
        refine ⟨hw_lp, hal_lp, by simpa [hmw] using hlt28, by simpa [hmw] using hle_cap, fun i hi => ?_⟩
        rw [hmw] at hi
        obtain ⟨⟨wa, hdom_a, hmem_a⟩, hle⟩ := hent i hi
        refine ⟨⟨wa, by simpa [hmw, hd] using hdom_a, by simpa [hmw, hm] using hmem_a⟩, ?_⟩
        simp only [hmw]
        unfold LogEntryOK at hle ⊢
        simp only [hmw, hhp_eq]
        refine ⟨⟨hle.1.1, hle.1.2.1, fun k hk => ?_⟩, hle.2⟩
        obtain ⟨wk, hdom_k, hmem_k⟩ := hle.1.2.2 k hk
        exact ⟨wk, hd ▸ hdom_k, hm ▸ hmem_k⟩
    · simp only [hmw]; exact hFW_child.2.2.2.2.2.2.2.2.2.2.2.1
    · rw [hflo_eq]
      have hpw0 := hpw_split.1
      unfold frameObjects at hpw0
      exact (List.pairwise_append.1 hpw0).2.1
    · intro o1 ho1 ec hec o2 ho2
      rw [hflo_eq] at ho1; rw [hch_p] at hec; rw [hfo_eq] at ho2
      exact hpw_split.2 o1 (by unfold frameObjects; exact List.mem_append_right _ ho1) ec hec o2 ho2
    · intro o1 ho1 t ht i hi
      rw [hflo_eq] at ho1; rw [hfp_eq] at hi
      exact (hFO_disj_s _ hmem_s o1 (by unfold frameObjects; exact List.mem_append_right _ ho1)).1
        t (hS'_sub t ht) i hi
    · intro o1 ho1 j hj
      rw [hflo_eq] at ho1; rw [hfix_eq] at hj
      exact (hFO_disj_s _ hmem_s o1 (by unfold frameObjects; exact List.mem_append_right _ ho1)).2 j hj
    · rw [hflo_eq]
      obtain ⟨Nd_at, hTr_at_s, hAT_at_s⟩ := hAT_s
      obtain ⟨_, _, _, _, hTr_p_ex⟩ := hIp.1
      have hWT_p := InitECandidate.Solver.Wave8Contracts.M23.worldTypedWith_congr_w1
        h.inv.1 hAp (by rw [hhp_eq]) (by rw [hsc_eq])
        (fun g hg_in => by
          have hne_g : g ≠ "ev" ∧ g ≠ "cur_cont" := by
            revert g hg_in; decide
          exact hg g hne_g.1 hne_g.2)
        ⟨hb, hd, h.inv.1.1.memaddrs, fun _ _ => by rw [hm], fun _ _ _ _ => by rw [hm],
          fun _ _ _ => by unfold memB; rw [hm, hb]⟩
        ⟨hW_s.1, hW_s.2.1, hW_s.2.2.1, hTr_at_s⟩
        ⟨hIp.1.2.2.1, fun o ho => Or.inl (by rw [← hfix_eq]; exact ho)⟩
      have hTr_at_S' : TriesTypedWith post S' Nd_at := by
        obtain ⟨hNH_p, hnd_disj_p, hws_nd_p⟩ := hWT_p.1.2.2.2
        refine ⟨hNH_p, fun o ho => ⟨fun t ht i hi => (hnd_disj_p o ho).1 t (hS'_sub t ht) i hi,
          (hnd_disj_p o ho).2⟩, fun hws_nz => ?_⟩
        obtain ⟨hr24, hr32⟩ := hws_nd_p hws_nz
        exact ⟨hr24, fun htS' i hi => hr32 (hS'_sub _ htS') i hi⟩
      refine ⟨Nd_at, hTr_at_S', fun o1 ho1 j hj => ?_⟩
      have hne_eq : nodeExtents post Nd_at = nodeExtents s Nd_at := by
        unfold nodeExtents nodeIvl nodePath; simp only [hmw]
      rw [hne_eq] at hj
      refine hAT_at_s o1 ?_ j hj
      exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨_, hmem_s, rfl⟩,
        by unfold frameObjects; exact List.mem_append_right _ ho1⟩
    · intro o1 ho1 ec hec
      rw [hflo_eq] at ho1; rw [hch_p] at hec; rw [hmw]
      exact (hFW_s ec (List.mem_of_mem_tail hec)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        _ hmem_s o1 (by unfold frameObjects; exact List.mem_append_right _ ho1)
  · rw [hmw, hmw, ← hev_s]
    have := h.r_le
    omega
  · rw [hmw, hmw, ← hev_s, hR_sum]
    unfold OpDispatchSpec.evmR
    exact hGas_s

private abbrev M08IvlUnhitFc {F : Type} (s post : PanSemStateFiniteExact 64 F) (i : Ivl) : Prop :=
  InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post i

private theorem disj_symm_fc {i j : Ivl} (h : Disj i j) : Disj j i :=
  R11Shards.Disj.symm h

private theorem disj_fresh_of_allocated_fc {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {j : Ivl} (hj : Allocated s j) :
    Disj j (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨_, hs_hp, hs_fm, hs_sc, _⟩ := hAs
  obtain ⟨_, hp_hp, _, _, _⟩ := hAp
  rcases hj with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
  · exact Or.inr (Or.inr (Or.inr (by dsimp; omega)))

private theorem disj_fresh_of_zero_or_allocated_fc {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {j : Ivl} (hj : j.2 = 0 ∨ Allocated s j) :
    Disj j (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
  rcases hj with h0 | hal
  · exact Or.inl h0
  · exact disj_fresh_of_allocated_fc hAs hAp hhp hal

private theorem disj_fresh_of_frameObject_fc {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S : List Nat} {ec o : Ivl}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hFW : FrameWF s S ec) (ho : o ∈ frameObjects s ec) :
    Disj o (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
  have hsep : heapLimit ≤ scratchStart := by decide
  have hhp_lim : globN post "heap_ptr" ≤ heapLimit := hAp.2.1
  have hss_fm : scratchStart ≤ globN s "frame_mem_ptr" := hAs.2.2.1
  have hfm_sc : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hAs.2.2.2.1
  obtain ⟨hscr, hmem_in, _, _, _, _, _, _, _, _, _, _, hlogs_in, _, hret_in, hll_ok, _⟩ := hFW
  unfold frameObjects at ho
  rcases List.mem_append.1 ho with ho7 | holog
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho7
    rcases ho7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h := (hscr (ec.1, 280) (by simp)).1
      exact Or.inr (Or.inr (Or.inr (by unfold Inside at h; dsimp at h ⊢; omega)))
    · have h := (hscr (ec.2, 104) (by simp)).1
      exact Or.inr (Or.inr (Or.inr (by unfold Inside at h; dsimp at h ⊢; omega)))
    · have h := (hscr (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)) (by simp)).1
      exact Or.inr (Or.inr (Or.inr (by unfold Inside at h; dsimp at h ⊢; omega)))
    · exact Or.inr (Or.inr (Or.inr (by unfold Inside at hmem_in; dsimp at hmem_in ⊢; omega)))
    · have h := (hscr (memW s (ec.1 + 88), 24) (by simp)).1
      exact Or.inr (Or.inr (Or.inr (by unfold Inside at h; dsimp at h ⊢; omega)))
    · rcases hlogs_in with h | h
      · exact Or.inr (Or.inr (Or.inl (by unfold Inside at h; dsimp at h ⊢; omega)))
      · exact Or.inr (Or.inr (Or.inr (by unfold Inside at h; dsimp at h ⊢; omega)))
    · rcases hret_in with ⟨hz, _⟩ | ⟨h, _⟩
      · unfold frameRet; simp [hz]; exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl (by unfold Inside at h; dsimp at h ⊢; omega)))
  · unfold frameLogObjects at holog; dsimp only at holog
    obtain ⟨idx, hidx_mem, ho_own⟩ := List.mem_flatMap.1 holog
    rw [List.mem_range] at hidx_mem
    rcases hll_ok with hz | ⟨_, _, _, _, hent⟩
    · have hlo := (hscr (memW s (ec.1 + 88), 24) (by simp)).1.1
      have hss0 : 0 < scratchStart := by decide
      dsimp at hlo; omega
    · have hle := (hent idx hidx_mem).2
      have ho_rec := (List.mem_filter.1 ho_own).1
      simp only [logRecordIvls, List.mem_cons, List.not_mem_nil, or_false] at ho_rec
      rcases ho_rec with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inl (by have := hle.2.1.2; dsimp at this ⊢; omega)))
      · exact Or.inr (Or.inr (Or.inl (by have := hle.2.2.2.2.1.2; dsimp at this ⊢; omega)))
      · exact Or.inr (Or.inr (Or.inl (by have := hle.2.2.2.2.2.1.2; dsimp at this ⊢; omega)))
      · exact Or.inr (Or.inr (Or.inl (by have := hle.2.2.2.2.2.2.2; dsimp at this ⊢; omega)))

private theorem m08_ivlUnhit_of_frameOutside_fc {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {keep : List Ivl} {fresh i : Ivl}
    (hfr : FrameOutside s post keep fresh)
    (hk_al : ∀ j ∈ keep, j.1 % 8 = 0)
    (hf_al : fresh.1 % 8 = 0)
    (hk : ∀ j ∈ keep, Disj i j) (hf : Disj i fresh) :
    M08IvlUnhitFc s post i := by
  intro a ha8 h1 h2
  apply hfr a
  · intro j hj ⟨hc1, hc2⟩
    have hj1 := hk_al j hj
    rcases hk j hj with hd | hd | hd | hd <;> omega
  · intro ⟨hcf1, hcf2⟩
    rcases hf with hd | hd | hd | hd <;> omega

private theorem balObjects_eq_of_unhit_except_fc {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {S : List Nat} (hT : TablesTyped s S) (hF : FixedTyped s)
    (hbal_eq : globN post "bal_accounts" = globN s "bal_accounts")
    {t0 : Nat}
    (hu_other : ∀ u ∈ S, u ≠ t0 → ∀ i ∈ htabFootprint s u, M08IvlUnhitFc s post i)
    (ht0_not_bal : globN s "bal_accounts" ≠ t0 ∧ ∀ ad ∈ balRecords s, memW s ad ≠ t0)
    (hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → M08IvlUnhitFc s post i)
    (hm0 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16) :
    balObjects post = balObjects s ∧
    (∀ ad ∈ balRecords post, memW post ad = memW s ad ∧ memW post (ad + 8) = memW s (ad + 8) ∧
      htabValues post (memW post ad) = htabValues s (memW s ad) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat), LstOK post (memW post (ad + k))) ∧
      (∀ l ∈ htabValues post (memW post ad), LstOK post l)) := by
  open InitECandidate.Solver.Wave8Contracts.M08 in
  have hrecs : balRecords post = balRecords s :=
    balRecords_eq_of_unhit hT hbal_eq (fun hnz => by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hnz
      · exact hu_other _ hm ht0_not_bal.1)
  have hmem_fix_of_bal : ∀ i ∈ balObjects s, i ∈ fixedObjects s := fun i hi => by
    unfold fixedObjects; exact List.mem_append.2 (Or.inr hi)
  have had_props : ∀ ad ∈ balRecords s,
      (∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off)) ∧
      htabValues post (memW s ad) = htabValues s (memW s ad) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat),
        memW post (memW s (ad + k)) = memW s (memW s (ad + k)) ∧
        memW post (memW s (ad + k) + 8) = memW s (memW s (ad + k) + 8) ∧
        memW post (memW s (ad + k) + 16) = memW s (memW s (ad + k) + 16)) ∧
      (∀ l ∈ htabValues s (memW s ad),
        memW post l = memW s l ∧ memW post (l + 8) = memW s (l + 8) ∧ memW post (l + 16) = memW s (l + 16)) := by
    intro ad had
    have had_bal : (ad, 40) ∈ balObjects s := by
      unfold balObjects; exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
    rcases hF.1 _ (hmem_fix_of_bal _ had_bal) with h0 | ⟨hal_ad, hw_ad⟩
    · simp at h0
    have hhi_ad := (ivl_allocated_bound hA hal_ad).2
    have had8 : ad % 8 = 0 := hw_ad.1
    have hoff_eq : ∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off) := by
      intro off hoff
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl <;>
        exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
          (hu_bal _ had_bal (by simp)) (by omega) hhi_ad ⟨by omega, by omega⟩
    have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have hvals_ad : htabValues post (memW s ad) = htabValues s (memW s ad) :=
      htabValues_eq_of_unhit (hT.2.1 _ had_T.1).1 (hu_other _ had_T.1 (ht0_not_bal.2 ad had))
    have hlst_eq : ∀ l, (l, 24) ∈ balObjects s →
        memW post l = memW s l ∧ memW post (l + 8) = memW s (l + 8) ∧ memW post (l + 16) = memW s (l + 16) := by
      intro l hl_bal
      rcases hF.1 _ (hmem_fix_of_bal _ hl_bal) with h0 | ⟨hal_l, hw_l⟩
      · simp at h0
      have hhi_l := (ivl_allocated_bound hA hal_l).2
      have hl8 : l % 8 = 0 := hw_l.1
      have hul := hu_bal _ hl_bal (by simp)
      exact ⟨by simpa using InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩,
             InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩,
             InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩⟩
    refine ⟨hoff_eq, hvals_ad, ?_, ?_⟩
    · intro k hk
      by_cases hk0 : memW s (ad + k) = 0
      · simp [hk0, hm0.1, hm0.2.1, hm0.2.2]
      · apply hlst_eq; unfold balObjects; refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> simp [lstObjects, hk0]
    · intro l hl
      by_cases hl0 : l = 0
      · subst hl0; simp [hm0.1, hm0.2.1, hm0.2.2]
      · apply hlst_eq; unfold balObjects; refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
        apply List.mem_cons_of_mem; apply List.mem_append.2; right
        exact List.mem_flatMap.2 ⟨l, hl, by simp [lstObjects, hl0]⟩
  constructor
  · unfold balObjects; rw [hrecs]
    apply List.flatMap_congr; intro ad had
    obtain ⟨hoff_eq, hvals_ad, hklst, hllst⟩ := had_props ad had
    have h0 := hoff_eq 0 (by simp); simp only [Nat.add_zero] at h0
    have h16 := hoff_eq 16 (by simp); have h24 := hoff_eq 24 (by simp); have h32 := hoff_eq 32 (by simp)
    obtain ⟨hk16_0, _, hk16_16⟩ := hklst 16 (by simp)
    obtain ⟨hk24_0, _, hk24_16⟩ := hklst 24 (by simp)
    obtain ⟨hk32_0, _, hk32_16⟩ := hklst 32 (by simp)
    have htail : (htabValues post (memW post ad)).flatMap (fun l => lstObjects post l 40) =
        (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40) := by
      rw [h0, hvals_ad]; apply List.flatMap_congr; intro l hl
      obtain ⟨hl0, _, hl16⟩ := hllst l hl; simp [lstObjects, hl0, hl16]
    rw [htail, h16, h24, h32]
    simp [lstObjects, hk16_0, hk16_16, hk24_0, hk24_16, hk32_0, hk32_16]
  · intro ad had
    rw [hrecs] at had
    obtain ⟨hoff_eq, hvals_ad, hklst, hllst⟩ := had_props ad had
    have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have h0 := hoff_eq 0 (by simp); simp only [Nat.add_zero] at h0
    have h8 := hoff_eq 8 (by simp)
    refine ⟨h0, h8, by rw [h0, hvals_ad], ?_, ?_⟩
    · intro k hk
      have hk_in : k ∈ ([0, 8, 16, 24, 32] : List Nat) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        rcases hk with rfl | rfl | rfl <;> simp
      rw [hoff_eq k hk_in]; obtain ⟨_, hk8, hk16⟩ := hklst k hk
      unfold LstOK; rw [hk8, hk16]; exact had_T.2.2.1 k hk
    · intro l hl; rw [h0, hvals_ad] at hl; obtain ⟨_, hl8, hl16⟩ := hllst l hl
      unfold LstOK; rw [hl8, hl16]; exact had_T.2.2.2 l hl

theorem evmInvAt_of_nonDel_htab_step {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} {t0 : Nat}
    (hAs : ArenaReady s) (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (ht0_nd : NonDelAccessTable s S t0)
    (hAp : ArenaReady post) (hbe : post.be = s.be)
    (hwf_t0 : HtabWF post t0)
    (hhdr0_t0 : hdr post t0 0 = hdr s t0 0)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hfp_t0 : ∀ i ∈ htabFootprint post t0, Allocated post i ∧
      ((∃ j ∈ htabFootprint s t0, Inside i j.1 (j.1 + j.2)) ∨
        Inside i (globN s "heap_ptr") (globN s "heap_ptr" + (globN post "heap_ptr" - globN s "heap_ptr"))))
    (hfr : FrameOutside s post (htabFootprint s t0)
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    (hg_kept : InitECandidate.Solver.Wave8Contracts.M23.GlobalsKept ["heap_ptr"] s post) :
    InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt post S ∧
    evmChain post = evmChain s ∧
    OpDispatchSpec.evmR post = OpDispatchSpec.evmR s ∧
    fixedObjects post = fixedObjects s ∧
    balRecords post = balRecords s ∧
    (∀ u ∈ S, u ≠ t0 → htabFootprint post u = htabFootprint s u) ∧
    (∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec ∧
      frameScratch post ec = frameScratch s ec ∧
      frameLogs post ec = frameLogs s ec ∧
      memW post (ec.1 + 16) = memW s (ec.1 + 16) ∧
      memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
      memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧
      memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧
      memW post (ec.1 + 112) = memW s (ec.1 + 112) ∧
      memW post (ec.1 + 136) = memW s (ec.1 + 136) ∧
      memW post (ec.1 + 232) = memW s (ec.1 + 232) ∧
      memW post (ec.2 + 56) = memW s (ec.2 + 56)) := by
  open InitECandidate.Solver.Wave8Contracts.M08 in
  obtain ⟨ht0_S, ht0_no_del, ht0_no_ws32, ht0_no_bs32, ht0_no_ba, ht0_no_ad, ht0_no_ts32⟩ := ht0_nd
  obtain ⟨hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, hAT, hMarks, hRoles, hGas⟩ := hInv
  obtain ⟨hT, hJ, hF, _⟩ := hW
  obtain ⟨Nd_at, hTr_at, hAT_at⟩ := hAT
  have hdom_eq : post.memaddrs = s.memaddrs := hAp.1.memaddrs.trans hAs.1.memaddrs.symm
  have hg_nonHeap : ∀ name, ofString name ≠ ofString "heap_ptr" → globN post name = globN s name := by
    intro name h1
    exact globN_eq_of_lookup (hg_kept (ofString name) (by
      simp only [List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
      rintro ⟨w, rfl, heq⟩; exact h1 heq.symm))
  have hsc_eq : globN post "scratch_ptr" = globN s "scratch_ptr" := hg_nonHeap "scratch_ptr" (by decide)
  have hfm_eq : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := hg_nonHeap "frame_mem_ptr" (by decide)
  have hev_eq : globN post "ev" = globN s "ev" := hg_nonHeap "ev" (by decide)
  have hcc_eq : globN post "cur_cont" = globN s "cur_cont" := hg_nonHeap "cur_cont" (by decide)
  have hevm_empty_eq : globN post "evm_empty" = globN s "evm_empty" := hg_nonHeap "evm_empty" (by decide)
  have hvmsa_eq : globN post "vm_system_address" = globN s "vm_system_address" := hg_nonHeap "vm_system_address" (by decide)
  have hws_g : globN post "ws" = globN s "ws" := hg_nonHeap "ws" (by decide)
  have hbs_g : globN post "bs" = globN s "bs" := hg_nonHeap "bs" (by decide)
  have hts_g : globN post "ts" = globN s "ts" := hg_nonHeap "ts" (by decide)
  have hbo_g : globN post "bo" = globN s "bo" := hg_nonHeap "bo" (by decide)
  have hba_g : globN post "bal_accounts" = globN s "bal_accounts" := hg_nonHeap "bal_accounts" (by decide)
  have hbia_g : globN post "bal_idx_accts" = globN s "bal_idx_accts" := hg_nonHeap "bal_idx_accts" (by decide)
  have hbis_g : globN post "bal_idx_stor" = globN s "bal_idx_stor" := hg_nonHeap "bal_idx_stor" (by decide)
  have hj_g : globN post "journal" = globN s "journal" := hg_nonHeap "journal" (by decide)
  have hjn_g : globN post "journal_n" = globN s "journal_n" := hg_nonHeap "journal_n" (by decide)
  have hjc_g : globN post "journal_cap" = globN s "journal_cap" := hg_nonHeap "journal_cap" (by decide)
  have hag : AllocatorGrows s post := ⟨hhp, by rw [hsc_eq]⟩
  have hf_al1 : (globN s "heap_ptr") % 8 = 0 := hAs.2.2.2.2.2.2.1
  have ht0_al : ∀ j ∈ htabFootprint s t0, j.1 % 8 = 0 ∧ j.2 % 8 = 0 := fun j hj => by
    have hw := ((hT.2.1 t0 ht0_S).1.1 j hj).2; exact ⟨hw.1, hw.2.1⟩
  have ht0_al1 : ∀ j ∈ htabFootprint s t0, j.1 % 8 = 0 := fun j hj => (ht0_al j hj).1
  have hunhit_m08 : ∀ i : Ivl, (∀ j ∈ htabFootprint s t0, Disj i j) →
      (i.2 = 0 ∨ Allocated s i) → M08IvlUnhitFc s post i := fun i hdi hal =>
    m08_ivlUnhit_of_frameOutside_fc hfr ht0_al1 hf_al1 hdi
      (disj_fresh_of_zero_or_allocated_fc hAs.2 hAp.2 hhp hal)
  have hu_other : ∀ u ∈ S, u ≠ t0 → ∀ i ∈ htabFootprint s u, M08IvlUnhitFc s post i := fun u hu hne i hi =>
    hunhit_m08 i (fun j hj => hT.2.2.1 u hu t0 ht0_S hne i hi j hj)
      (Or.inr ((hT.2.1 u hu).2 i hi).1)
  have hu_fix : ∀ i ∈ fixedObjects s, M08IvlUnhitFc s post i := fun i hi =>
    hunhit_m08 i (fun j hj => disj_symm_fc (((hT.2.1 t0 ht0_S).2 j hj).2 i hi))
      (by rcases hF.1 i hi with h0 | ⟨hal, _⟩; exact Or.inl h0; exact Or.inr hal)
  have hm0 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 := by
    have hlow : ∀ a : Nat, a + 8 ≤ sourceBase → memW post a = memW s a := fun a ha => by
      have hsb_lt : sourceBase < 2 ^ 64 := by decide
      have ha_lt : a < 2 ^ 64 := lt_of_le_of_lt (by omega) hsb_lt
      have hm := hfr (BitVec.ofNat 64 a)
        (fun j hj ⟨h1, _⟩ => by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          have hlo := ((hT.2.1 t0 ht0_S).1.1 j hj).1.1; omega)
        (fun ⟨h1, _⟩ => by
          dsimp at h1; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          have hlo := hAs.2.1; omega)
      unfold memW; rw [hm]
    exact ⟨hlow 0 (by decide), hlow 8 (by decide), hlow 16 (by decide)⟩
  have hu_ws : globN s "ws" ≠ 0 → M08IvlUnhitFc s post (globN s "ws", 40) := fun hnz => by
    have hm := typedRecord_mem_fixedObjects s (r := ("ws", 40)) (by simp [typedRecords])
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm
  have hu_bs : globN s "bs" ≠ 0 → M08IvlUnhitFc s post (globN s "bs", 80) := fun hnz => by
    have hm := typedRecord_mem_fixedObjects s (r := ("bs", 80)) (by simp [typedRecords])
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm
  have hu_ts : globN s "ts" ≠ 0 → M08IvlUnhitFc s post (globN s "ts", 72) := fun hnz => by
    have hm := typedRecord_mem_fixedObjects s (r := ("ts", 72)) (by simp [typedRecords])
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm
  have hu_bo : globN s "bo" ≠ 0 → M08IvlUnhitFc s post (globN s "bo", 88) := fun hnz => by
    have hm := typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by simp [typedRecords])
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm
  have hu_jr : globN s "journal_cap" ≠ 0 → M08IvlUnhitFc s post (globN s "journal", 32 * globN s "journal_cap") := fun hnz => by
    apply hu_fix; unfold fixedObjects
    apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right; simp [hnz]
  have hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → M08IvlUnhitFc s post i := fun i hi _ =>
    hu_fix i (by unfold fixedObjects; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hi))))
  have hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → M08IvlUnhitFc s post i := fun i hi _ =>
    hu_fix i (by unfold fixedObjects; exact List.mem_append.2 (Or.inr hi))
  have hbo_words : globN s "bo" ≠ 0 → ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := fun hnz k hk => by
    have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    simpa [hbo_g] using rec_word_eq_of_unhit hAs.2 hF "bo" 88 (by simp [typedRecords]) hbo_g hnz (hu_bo hnz) hk_in.1 hk_in.2
  have hbo_eq := blockOutObjects_eq_of_bo_unhit hAs.2 hF hbo_g hT.2.2.2.2.2.2.2.2.2.2.1
    (fun h => hbo_words h 24 (by simp))
    (fun h => hbo_words h 32 (by simp))
    (fun h => hbo_words h 40 (by simp))
    (fun h => hbo_words h 56 (by simp))
    (fun h => hbo_words h 72 (by simp))
    (fun h => hbo_words h 80 (by simp))
    (fun _ _ => by simp [hm0.1, hm0.2.2])
    (fun _ _ => by simp [hm0.1, hm0.2.2])
    (fun h h40 => hu_bo_lst (memW s (globN s "bo" + 40), 24) (by simp [blockOutObjects, h, h40]) rfl)
    (fun h h72 => hu_bo_lst (memW s (globN s "bo" + 72), 24) (by simp [blockOutObjects, h, h72]) rfl)
  have hbal_eq := balObjects_eq_of_unhit_except_fc hAs.2 hT hF hba_g hu_other
    ⟨ht0_no_ba, ht0_no_ad⟩ hu_bal hm0
  have hfix_eq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [hbo_eq.1, hbal_eq.1, hj_g, hjc_g]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "heap_ptr" := by
      revert gn hgn; decide
    rw [hg_nonHeap gn.1 hne]
  have hF_post := fixedTyped_transfer hAs.1 hAp.1 hag hF hfix_eq
  have hrole_eq : ∀ t, journalRole post t = journalRole s t := fun t => by
    unfold journalRole
    by_cases h : globN s "ts" = 0
    · simp [hts_g, h]
    · have hw16 := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 16) (by omega) (by omega)
      have hw32 := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 32) (by omega) (by omega)
      have hw48 := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 48) (by omega) (by omega)
      have hw64 := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 64) (by omega) (by omega)
      simp only [hts_g] at hw16 hw32 hw48 hw64 ⊢
      rw [hw16, hw32, hw48, hw64]
  have hj_cells : ∀ i, i < globN s "journal_n" →
      memW post (globN s "journal" + 32 * i) = memW s (globN s "journal" + 32 * i) ∧
      memW post (globN s "journal" + 32 * i + 16) = memW s (globN s "journal" + 32 * i + 16) ∧
      memW post (globN s "journal" + 32 * i + 24) = memW s (globN s "journal" + 32 * i + 24) := by
    intro i hi
    have hcnz : globN s "journal_cap" ≠ 0 := by have := hJ.1; omega
    rcases hJ.2.2.1 with h0 | ⟨hal, hwords⟩
    · exact absurd h0 hcnz
    · have hhi := (ivl_allocated_bound hAs.2 hal).2
      have hj8 : (globN s "journal") % 8 = 0 := hwords.1
      have huj := hu_jr hcnz
      have hle : i < globN s "journal_cap" := lt_of_lt_of_le hi hJ.1
      exact ⟨InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit huj (by omega) hhi ⟨by omega, by omega⟩,
             InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit huj (by omega) hhi ⟨by omega, by omega⟩,
             InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit huj (by omega) hhi ⟨by omega, by omega⟩⟩
  have hJ_post : JournalTyped post S := by
    unfold JournalTyped
    rw [hjc_g, hj_g, hjn_g]
    refine ⟨hJ.1, hJ.2.1, ?_, fun i hi => ?_⟩
    · rcases hJ.2.2.1 with h0 | ⟨hal, hwords⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hag.allocated hal, wordsOK_transfer hAs.1 hAp.1 hwords⟩
    · rw [(hj_cells i hi).1]; exact hJ.2.2.2 i hi
  have hjrs_eq : journalRoleSlots post = journalRoleSlots s := by
    unfold journalRoleSlots; rw [hj_g, hjn_g]
    apply List.flatMap_congr; intro i hi
    have hi_lt : i < globN s "journal_n" := List.mem_range.1 hi
    obtain ⟨hc0, hc16, hc24⟩ := hj_cells i hi_lt
    dsimp only; rw [hc0, hc16, hc24, hrole_eq]
  have hother_fp : ∀ u ∈ S, u ≠ t0 →
      (∀ k, k < 11 → hdr post u k = hdr s u k) ∧ htabFootprint post u = htabFootprint s u := by
    intro u hu hne
    have hfp := (hT.2.1 u hu).1.1
    have ht_fp : (u, 88) ∈ htabFootprint s u := by simp [htabFootprint]
    have h264 : heapEnd ≤ 2 ^ 64 := by decide
    exact htabFootprint_eq_of_hdr_unhit ((hfp _ ht_fp).2.1)
      (by have := (hfp _ ht_fp).1.2; dsimp at this; omega) (hu_other u hu hne _ ht_fp)
  have hhdr0_all : ∀ u ∈ S, hdr post u 0 = hdr s u 0 := fun u hu => by
    by_cases heq : u = t0
    · subst heq; exact hhdr0_t0
    · exact (hother_fp u hu heq).1 0 (by omega)
  have transfer_tries : ∀ Nd, TriesTypedWith s S Nd →
      TriesTypedWith post S Nd ∧ nodeExtents post Nd = nodeExtents s Nd := by
    intro Nd hTr
    have hu_nd_rec : ∀ n ∈ Nd, M08IvlUnhitFc s post (nodeIvl s n) := fun n hn => by
      have hmem : nodeIvl s n ∈ nodeExtents s Nd := by
        unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
      exact hunhit_m08 _ (fun j hj => (hTr.2.1 _ hmem).1 t0 ht0_S j hj)
        (Or.inr (hTr.1.1 n hn).2.1)
    have hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
        ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k) := by
      intro n hn h12 hlen0 k hk
      have h264 : heapLimit ≤ 2 ^ 64 := by decide
      rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_p, hin_p, _⟩
      · exact absurd h0 hlen0
      · have hp_ne : (memW s (n + 32), memW s (n + 40)) ∈ nodeExtents s Nd := by
          unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩
        have ha_lt : memW s (n + 32) + k < 2 ^ 64 := by have := hin_p.2; omega
        let c := panByteAlignHOL (BitVec.ofNat 64 (memW s (n + 32) + k))
        have hc_nat : c.toNat = (memW s (n + 32) + k) / 8 * 8 := by
          rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
        have hmem := hfr c
          (fun j hj ⟨h1, h2⟩ => by
            rw [hc_nat] at h1 h2
            have hj_al := ht0_al j hj
            have hdj := (hTr.2.1 _ hp_ne).1 t0 ht0_S j hj
            rcases hdj with d | d | d | d <;> omega)
          (fun ⟨h1, h2⟩ => by
            dsimp at h1 h2; rw [hc_nat] at h1 h2
            have hp_hp8 : (globN post "heap_ptr") % 8 = 0 := hAp.2.2.2.2.2.2.1
            have hdj := disj_fresh_of_zero_or_allocated_fc hAs.2 hAp.2 hhp (Or.inr hal_p)
            rcases hdj with d | d | d | d <;> dsimp at d <;> omega)
        unfold memB
        change (match post.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (memW s (n + 32) + k)) v post.be).toNat) =
               (match s.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (memW s (n + 32) + k)) v s.be).toNat)
        rw [hmem, hbe]
    obtain ⟨hNH_post, hne_eq⟩ := nodeHeap_congr_bytes hAs.1 hAp.1 hag hTr.1 hu_nd_rec hu_nd_byte
    refine ⟨⟨hNH_post, ?_, ?_⟩, hne_eq⟩
    · rw [hne_eq, hfix_eq]
      intro o ho
      have ho_alloc : o.2 = 0 ∨ Allocated s o := by
        unfold nodeExtents at ho
        obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
        rcases hno with rfl | rfl
        · exact Or.inr (hTr.1.1 n hn).2.1
        · unfold nodePath; split_ifs with hc
          · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hc.1 with h0 | ⟨_, hal, _⟩
            · exact absurd h0 hc.2
            · exact Or.inr hal
          · exact Or.inl rfl
      refine ⟨fun u hu i hi => ?_, (hTr.2.1 o ho).2⟩
      by_cases hu0 : u = t0
      · rw [hu0] at hi
        rcases (hfp_t0 i hi).2 with ⟨k, hk, hin⟩ | hfresh
        · exact disj_symm_fc (disj_of_inside_left hin (disj_symm_fc ((hTr.2.1 o ho).1 t0 ht0_S k hk)))
        · exact disj_of_inside_right hfresh (disj_fresh_of_zero_or_allocated_fc hAs.2 hAp.2 hhp ho_alloc)
      · rw [(hother_fp u hu hu0).2] at hi
        exact (hTr.2.1 o ho).1 u hu i hi
    · intro hws_nz
      rw [hws_g] at hws_nz
      have e24 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hws_nz (hu_ws hws_nz) (k := 24) (by omega) (by omega)
      have e32 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hws_nz (hu_ws hws_nz) (k := 32) (by omega) (by omega)
      rw [e24, e32]
      obtain ⟨hr24, hr32⟩ := hTr.2.2 hws_nz
      refine ⟨hr24, fun htS i hi => ?_⟩
      have hne32 := ht0_no_ws32 hws_nz
      have hu32 := hu_other _ htS hne32
      have hwf32 := (hT.2.1 _ htS).1
      have hvals_eq := htabValues_eq_of_unhit hwf32 hu32
      obtain ⟨hhdr32, _⟩ := hother_fp _ htS hne32
      rw [hhdr32 3 (by omega)] at hi
      have hget : (htabValues post (memW s (globN s "ws" + 32)))[i]? =
          (htabValues s (memW s (globN s "ws" + 32)))[i]? := by rw [hvals_eq]
      simp only [htabValues, List.getElem?_map, List.getElem?_range, hhdr32 3 (by omega), hi,
        Option.map_some, Option.some.injEq] at hget
      rw [hget]; exact hr32 htS i hi
  obtain ⟨hTr_at_post, hne_at_eq⟩ := transfer_tries Nd_at hTr_at
  have hu_fo_m08 : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, M08IvlUnhitFc s post o := by
    intro ec hec o ho
    exact m08_ivlUnhit_of_frameOutside_fc hfr ht0_al1 hf_al1
      (fun j hj => (hFO_disj ec hec o ho).1 t0 ht0_S j hj)
      (disj_fresh_of_frameObject_fc hAs.2 hAp.2 hhp (hFW_all ec hec) ho)
  have hrec_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨hb1, hb2, hb88, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hAs.2 hFW
    have he1_8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
    have he2_8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
    have he88_8 : (memW s (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2.1
    refine ⟨fun k hk hk8 => InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
              (hu_fo_m08 ec hec (ec.1, 280) (by simp [frameObjects])) (by omega) hb1 ⟨by omega, by omega⟩,
            fun k hk hk8 => InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
              (hu_fo_m08 ec hec (ec.2, 104) (by simp [frameObjects])) (by omega) hb2 ⟨by omega, by omega⟩,
            fun k hk hk8 => InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
              (hu_fo_m08 ec hec (memW s (ec.1 + 88), 24) (by simp [frameObjects])) (by omega) hb88 ⟨by omega, by omega⟩⟩
  have hchain_aux : ∀ (fuel e c : Nat),
      (∀ ec ∈ evmChainFrom s fuel e c, ec ∈ evmChain s) →
      evmChainFrom post fuel e c = evmChainFrom s fuel e c := by
    intro fuel; induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro e c hsub
      have hec : (e, c) ∈ evmChain s := hsub (e, c) (by simp [evmChainFrom])
      obtain ⟨_, hc_eq, _⟩ := hrec_eq (e, c) hec
      have hc16 := hc_eq 16 (by omega) (by omega)
      have hc0 : memW post c = memW s c := by simpa using hc_eq 0 (by omega) (by omega)
      have hc8 := hc_eq 8 (by omega) (by omega)
      simp only [evmChainFrom, hc16, hc0, hc8]
      split
      · rfl
      · rename_i hne16
        rw [ih]; intro ec' hec'; exact hsub ec' (by simp [evmChainFrom, hne16, hec'])
  have hchain_eq : evmChain post = evmChain s := by
    unfold evmChain; rw [hev_eq, hcc_eq]
    exact hchain_aux _ _ _ (fun _ h => h)
  have hframeLogs_eq : ∀ ec ∈ evmChain s, frameLogs post ec = frameLogs s ec := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    unfold frameLogs
    rw [he_eq 88 (by omega) (by omega),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega)]
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameRet
    rw [he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega)]
  have hlogs_congr : ∀ ec ∈ evmChain s,
      frameLogObjects post ec = frameLogObjects s ec ∧ LogsListOK post (memW post (ec.1 + 88)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨_, _, _, hfob⟩ := InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hAs.2 hFW
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    set logs := memW s (ec.1 + 88)
    have hl0 : memW post logs = memW s logs := by simpa [logs] using h88_eq 0 (by omega) (by omega)
    have hl8 : memW post (logs + 8) = memW s (logs + 8) := h88_eq 8 (by omega) (by omega)
    have hl16 : memW post (logs + 16) = memW s (logs + 16) := h88_eq 16 (by omega) (by omega)
    have harr_eq : ∀ i, i < memW s (logs + 8) →
        memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i) := by
      intro i hi
      have hfl_in : frameLogs s ec ∈ frameObjects s ec := by simp [frameObjects]
      have hlen_le : memW s (logs + 8) ≤ memW s (logs + 16) := hFW.2.2.2.2.2.2.2.2.2.2.2.1
      have hfl_b : memW s logs + 8 * memW s (logs + 16) ≤ 2 ^ 64 := by
        rcases hfob _ hfl_in with h0 | hb
        · unfold frameLogs at h0; dsimp only [logs] at h0 hi hlen_le; omega
        · simpa [frameLogs, logs] using hb
      have hfl_8 : (memW s logs) % 8 = 0 := hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
      have hfl_u : M08IvlUnhitFc s post (memW s logs, 8 * memW s (logs + 16)) :=
        hu_fo_m08 ec hec (frameLogs s ec) hfl_in
      exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
        hfl_u (by omega) hfl_b ⟨by dsimp only; omega, by dsimp only; omega⟩
    have hlr_eq : ∀ i (hi : i < memW s (logs + 8)) off, off + 8 ≤ 40 → off % 8 = 0 →
        memW post (memW s (memW s logs + 8 * i) + off) = memW s (memW s (memW s logs + 8 * i) + off) := by
      intro i hi off hoff hoff8
      have hlr_in : (memW s (memW s logs + 8 * i), 40) ∈ frameObjects s ec := by
        unfold frameObjects; apply List.mem_append_right
        unfold frameLogObjects; dsimp only [logs]
        refine List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, ?_⟩
        unfold logOwnedIvls logRecordIvls
        exact List.mem_filter.2 ⟨by simp, by simp⟩
      have hlr_b : memW s (memW s logs + 8 * i) + 40 ≤ 2 ^ 64 := by
        rcases hfob _ hlr_in with h0 | hb
        · dsimp only at h0; omega
        · exact hb
      have hlr_8 : (memW s (memW s logs + 8 * i)) % 8 = 0 := by
        rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
        · have he88_in := (hFW.1 (logs, 24) (by simp [logs])).1.1
          have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
          have hss0 : 0 < scratchStart := by decide
          dsimp only at he88_in; omega
        · exact (hent i hi).2.1.1
      exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
        (hu_fo_m08 ec hec _ hlr_in) (by omega) hlr_b ⟨by omega, by omega⟩
    refine ⟨?_, ?_⟩
    · unfold frameLogObjects; dsimp only
      rw [he_eq 88 (by omega) (by omega), hl8]
      apply List.flatMap_congr; intro i hi; rw [List.mem_range] at hi
      rw [hl0, harr_eq i hi]
      have r0 := hlr_eq i hi 0 (by omega) (by omega)
      have r8 := hlr_eq i hi 8 (by omega) (by omega)
      have r16 := hlr_eq i hi 16 (by omega) (by omega)
      have r24 := hlr_eq i hi 24 (by omega) (by omega)
      have r32 := hlr_eq i hi 32 (by omega) (by omega)
      simp only [Nat.add_zero] at r0
      unfold logOwnedIvls logRecordIvls
      rw [r0, r8, r16, r24, r32, hvmsa_eq]
    · rw [he_eq 88 (by omega) (by omega)]
      rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨hw_l, hal_l, hlt28, hle_cap, hent⟩
      · exact Or.inl hz
      · right
        refine ⟨wordsOK_transfer hAs.1 hAp.1 hw_l, hag.allocated hal_l,
          by rw [hl8]; exact hlt28, by rw [hl8, hl16]; exact hle_cap, fun i hi => ?_⟩
        rw [hl8] at hi; rw [hl0]
        obtain ⟨hwa, hle⟩ := hent i hi
        have hwa_post : WordAt post (memW s logs + 8 * i) := by
          obtain ⟨_, hdom, _⟩ := hwa
          rcases hm : post.memory (BitVec.ofNat 64 (memW s logs + 8 * i)) with ⟨w⟩
          exact ⟨w, hdom_eq ▸ hdom, hm⟩
        refine ⟨hwa_post, ?_⟩
        rw [harr_eq i hi]
        have r0 := hlr_eq i hi 0 (by omega) (by omega)
        have r8 := hlr_eq i hi 8 (by omega) (by omega)
        have r16 := hlr_eq i hi 16 (by omega) (by omega)
        have r24 := hlr_eq i hi 24 (by omega) (by omega)
        have r32 := hlr_eq i hi 32 (by omega) (by omega)
        simp only [Nat.add_zero] at r0
        unfold LogEntryOK at hle ⊢
        rw [r0, r8, r16, r24, r32]
        exact ⟨wordsOK_transfer hAs.1 hAp.1 hle.1,
          ⟨hle.2.1.1, le_trans hle.2.1.2 hhp⟩,
          hle.2.2.1, hle.2.2.2.1,
          ⟨hle.2.2.2.2.1.1, le_trans hle.2.2.2.2.1.2 hhp⟩,
          ⟨hle.2.2.2.2.2.1.1, le_trans hle.2.2.2.2.2.1.2 hhp⟩,
          ⟨hle.2.2.2.2.2.2.1, le_trans hle.2.2.2.2.2.2.2 hhp⟩⟩
  have hframeObjects_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameObjects
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 24 (by omega) (by omega), he_eq 40 (by omega) (by omega),
        he_eq 88 (by omega) (by omega), hframeLogs_eq ec hec, hframeRet_eq ec hec,
        (hlogs_congr ec hec).1]
  have hframeScratch_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega), he_eq 88 (by omega) (by omega)]
  have hmap_fo_eq : (evmChain s).map (frameObjects post) = (evmChain s).map (frameObjects s) :=
    List.map_congr_left hframeObjects_eq
  have hfrs_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots; apply List.flatMap_congr; intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    rw [he_eq 136 (by omega) (by omega), he_eq 168 (by omega) (by omega), he_eq 176 (by omega) (by omega)]
  have hrec_ws_eq : recRoles post "ws" [(16, "ws+16"), (32, "ws+32")] = recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] := by
    unfold recRoles
    by_cases h : globN s "ws" = 0
    · simp [hws_g, h]
    · have hw16 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g h (hu_ws h) (k := 16) (by omega) (by omega)
      have hw32 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g h (hu_ws h) (k := 32) (by omega) (by omega)
      simp only [hws_g] at hw16 hw32 ⊢; simp [h, hw16, hw32]
  have hrec_bs_eq : recRoles post "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
      (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] =
      recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
      (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] := by
    unfold recRoles
    by_cases h : globN s "bs" = 0
    · simp [hbs_g, h]
    · simp only [hbs_g, h, ↓reduceIte]; apply List.map_congr_left
      intro ⟨k, r⟩ hkr
      have hk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
        rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
      have hw := rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g h (hu_bs h) hk.1 hk.2
      simp only [hbs_g] at hw; simp [hw]
  have hrec_ts_eq : recRoles post "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
      (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] =
      recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
      (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] := by
    unfold recRoles
    by_cases h : globN s "ts" = 0
    · simp [hts_g, h]
    · simp only [hts_g, h, ↓reduceIte]; apply List.map_congr_left
      intro ⟨k, r⟩ hkr
      have hk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
        rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
      have hw := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) hk.1 hk.2
      simp only [hts_g] at hw; simp [hw]
  have hnest_bs_eq : nestRoles post "bs" "bs.inner" = nestRoles s "bs" "bs.inner" := by
    unfold nestRoles
    by_cases h : globN s "bs" = 0
    · simp [hbs_g, h]
    · have hw32 := rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g h (hu_bs h) (k := 32) (by omega) (by omega)
      simp only [hbs_g] at hw32 ⊢; simp only [h, ↓reduceIte, hw32]
      by_cases h32 : memW s (globN s "bs" + 32) = 0
      · simp [h32]
      · simp only [h32, ↓reduceIte]
        have hmS : memW s (globN s "bs" + 32) ∈ S := by
          rcases hT.2.2.2.2.1 32 (by simp [bsTableSlots]) h with h0 | hm
          · exact absurd h0 h32
          · exact hm
        rw [htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_other _ hmS (ht0_no_bs32 h))]
  have hnest_ts_eq : nestRoles post "ts" "ts.inner" = nestRoles s "ts" "ts.inner" := by
    unfold nestRoles
    by_cases h : globN s "ts" = 0
    · simp [hts_g, h]
    · have hw32 := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 32) (by omega) (by omega)
      simp only [hts_g] at hw32 ⊢; simp only [h, ↓reduceIte, hw32]
      by_cases h32 : memW s (globN s "ts" + 32) = 0
      · simp [h32]
      · simp only [h32, ↓reduceIte]
        have hmS : memW s (globN s "ts" + 32) ∈ S := by
          rcases hT.2.2.2.2.2.1 32 (by simp [tsTableSlots]) h with h0 | hm
          · exact absurd h0 h32
          · exact hm
        rw [htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_other _ hmS (ht0_no_ts32 h))]
  have hrecs_bal := balRecords_eq_of_unhit hT hba_g (fun hnz => by
    rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
    · exact absurd h0 hnz
    · exact hu_other _ hm ht0_no_ba)
  have hbal_slots_eq : (balRecords post).flatMap (fun ad => [(memW post ad, "bal.stor"), (memW post (ad + 8), "bal.reads")]) =
      (balRecords s).flatMap (fun ad => [(memW s ad, "bal.stor"), (memW s (ad + 8), "bal.reads")]) := by
    rw [hrecs_bal]; apply List.flatMap_congr; intro ad had
    have had_p : ad ∈ balRecords post := by rwa [hrecs_bal]
    obtain ⟨e0, e8, _⟩ := hbal_eq.2 ad had_p
    rw [e0, e8]
  have hwrs_eq : worldRoleSlots post = worldRoleSlots s := by
    unfold worldRoleSlots
    rw [hrec_ws_eq, hrec_bs_eq, hrec_ts_eq, hba_g, hbia_g, hbis_g, hnest_bs_eq, hnest_ts_eq, hbal_slots_eq]
  have hRoles_evm_post : RolesOK post S (worldRoleSlots post ++ frameRoleSlots post (evmChain s)) (journalRoleSlots post) := by
    rw [hwrs_eq, hfrs_eq, hjrs_eq]
    refine ⟨fun a ha => ?_, hRoles.2.1, hRoles.2.2⟩
    obtain ⟨haS, hkl⟩ := hRoles.1 a ha
    exact ⟨haS, (hhdr0_all a.1 haS).trans hkl⟩
  have hRoles_world_post : RolesOK post S (worldRoleSlots post) (journalRoleSlots post) := by
    refine ⟨fun a ha => hRoles_evm_post.1 a ?_,
            (List.pairwise_append.1 hRoles_evm_post.2.1).1,
            fun a ha b hb => hRoles_evm_post.2.2 a ha b ?_⟩
    · rcases List.mem_append.1 ha with hw | hjr
      · exact List.mem_append_left _ (List.mem_append_left _ hw)
      · exact List.mem_append_right _ hjr
    · rcases List.mem_append.1 hb with hw | hjr
      · exact List.mem_append_left _ (List.mem_append_left _ hw)
      · exact List.mem_append_right _ hjr
  have ht0_disj_other : ∀ i ∈ htabFootprint post t0,
      (∀ u ∈ S, u ≠ t0 → ∀ j ∈ htabFootprint s u, Disj i j) ∧
      (∀ j ∈ fixedObjects s, Disj i j) := by
    intro i hi
    rcases (hfp_t0 i hi).2 with ⟨k, hk, hin⟩ | hfresh
    · exact ⟨fun u hu hne j hj => disj_of_inside_left hin (hT.2.2.1 t0 ht0_S u hu hne.symm k hk j hj),
             fun j hj => disj_of_inside_left hin (((hT.2.1 t0 ht0_S).2 k hk).2 j hj)⟩
    · exact ⟨fun u hu _ j hj => disj_symm_fc (disj_of_inside_right hfresh
                (disj_fresh_of_zero_or_allocated_fc hAs.2 hAp.2 hhp (Or.inr ((hT.2.1 u hu).2 j hj).1))),
             fun j hj => disj_symm_fc (disj_of_inside_right hfresh
                (disj_fresh_of_zero_or_allocated_fc hAs.2 hAp.2 hhp
                  (by rcases hF.1 j hj with h0 | ⟨hal, _⟩; exact Or.inl h0; exact Or.inr hal)))⟩
  have hT_post : TablesTyped post S := by
    obtain ⟨hnd, htwf, htpw, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, _⟩ := hT
    refine ⟨hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_eq.2, hRoles_world_post⟩
    · intro u hu
      by_cases heq : u = t0
      · rw [heq, hfix_eq]
        exact ⟨hwf_t0, fun i hi => ⟨(hfp_t0 i hi).1, (ht0_disj_other i hi).2⟩⟩
      · rw [(hother_fp u hu heq).2, hfix_eq]
        exact ⟨htabWF_congr_unhit hAs.1 hAp.1 (htwf u hu).1 (hu_other u hu heq),
          fun i hi => ⟨hag.allocated ((htwf u hu).2 i hi).1, ((htwf u hu).2 i hi).2⟩⟩
    · intro u hu v hv hne i hi j hj
      by_cases hu0 : u = t0
      · rw [hu0] at hi hne; rw [(hother_fp v hv hne.symm).2] at hj
        exact (ht0_disj_other i hi).1 v hv hne.symm j hj
      · by_cases hv0 : v = t0
        · rw [hv0] at hj; rw [(hother_fp u hu hu0).2] at hi
          exact disj_symm_fc ((ht0_disj_other j hj).1 u hu hu0 i hi)
        · rw [(hother_fp u hu hu0).2] at hi; rw [(hother_fp v hv hv0).2] at hj
          exact htpw u hu v hv hne i hi j hj
    · intro k hk hnz
      rw [hws_g] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hnz (hu_ws hnz) hk8.1 hk8.2]
      exact hwsR k hk hnz
    · intro k hk hnz
      rw [hbs_g] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g hnz (hu_bs hnz) hk8.1 hk8.2]
      exact hbsR k hk hnz
    · intro k hk hnz
      rw [hts_g] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g hnz (hu_ts hnz) hk8.1 hk8.2]
      exact htsR k hk hnz
    · intro g hg_mem
      have hne : ofString g ≠ ofString "heap_ptr" := by
        simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg_mem
        rcases hg_mem with rfl | rfl | rfl <;> decide
      rw [hg_nonHeap g hne]; exact hgR g hg_mem
    · intro hnz hmem
      rw [hbs_g] at hnz
      have ew := rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hmem ⊢
      exact htabValuesIn_congr_unhit (htwf _ hmem).1 (hu_other _ hmem (ht0_no_bs32 hnz)) (fun _ hx => hx) (hbsN hnz hmem)
    · intro hnz hmem
      rw [hts_g] at hnz
      have ew := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hmem ⊢
      exact htabValuesIn_congr_unhit (htwf _ hmem).1 (hu_other _ hmem (ht0_no_ts32 hnz)) (fun _ hx => hx) (htsN hnz hmem)
    · intro ad had
      have had_s : ad ∈ balRecords s := by rwa [← hrecs_bal]
      obtain ⟨e0, e8, _, hkl, hll⟩ := hbal_eq.2 ad had
      exact ⟨e0 ▸ (hbalT ad had_s).1, e8 ▸ (hbalT ad had_s).2.1, hkl, hll⟩
  have hW_post : WorldTyped post S := ⟨hT_post, hJ_post, hF_post, Nd_at, hTr_at_post⟩
  have hwref_eq : worldTableRefs post S = worldTableRefs s S := by
    unfold worldTableRefs recordSlots
    rw [hws_g, hbs_g, hts_g,
        show globalTableRoots.map (globN post) = globalTableRoots.map (globN s) by
          simp only [globalTableRoots, List.map, hba_g, hbia_g, hbis_g],
        hrecs_bal, hj_g, hjn_g]
    have hws_sl : (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW post (globN s "ws" + k)) =
        (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW s (globN s "ws" + k)) := by
      split; · rfl
      rename_i hnz; apply List.map_congr_left; intro k hk
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl <;> omega
      simpa [hws_g] using rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hnz (hu_ws hnz) hk8.1 hk8.2
    have hbs_sl : (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW post (globN s "bs" + k)) =
        (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW s (globN s "bs" + k)) := by
      split; · rfl
      rename_i hnz; apply List.map_congr_left; intro k hk
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      simpa [hbs_g] using rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g hnz (hu_bs hnz) hk8.1 hk8.2
    have hts_sl : (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW post (globN s "ts" + k)) =
        (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW s (globN s "ts" + k)) := by
      split; · rfl
      rename_i hnz; apply List.map_congr_left; intro k hk
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      simpa [hts_g] using rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g hnz (hu_ts hnz) hk8.1 hk8.2
    have hnest_bs_w : (if globN s "bs" ≠ 0 ∧ memW post (globN s "bs" + 32) ∈ S then htabValues post (memW post (globN s "bs" + 32)) else []) =
        (if globN s "bs" ≠ 0 ∧ memW s (globN s "bs" + 32) ∈ S then htabValues s (memW s (globN s "bs" + 32)) else []) := by
      by_cases hnz : globN s "bs" = 0
      · simp [hnz]
      · have ew := rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
        simp only [hbs_g] at ew; rw [ew]
        by_cases hmS : memW s (globN s "bs" + 32) ∈ S
        · simp [hnz, hmS, htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_other _ hmS (ht0_no_bs32 hnz))]
        · simp [hnz, hmS]
    have hnest_ts_w : (if globN s "ts" ≠ 0 ∧ memW post (globN s "ts" + 32) ∈ S then htabValues post (memW post (globN s "ts" + 32)) else []) =
        (if globN s "ts" ≠ 0 ∧ memW s (globN s "ts" + 32) ∈ S then htabValues s (memW s (globN s "ts" + 32)) else []) := by
      by_cases hnz : globN s "ts" = 0
      · simp [hnz]
      · have ew := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
        simp only [hts_g] at ew; rw [ew]
        by_cases hmS : memW s (globN s "ts" + 32) ∈ S
        · simp [hnz, hmS, htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_other _ hmS (ht0_no_ts32 hnz))]
        · simp [hnz, hmS]
    have hbal_fl : (balRecords s).flatMap (fun ad => [memW post ad, memW post (ad + 8)]) =
        (balRecords s).flatMap (fun ad => [memW s ad, memW s (ad + 8)]) := by
      apply List.flatMap_congr; intro ad had
      have had_p : ad ∈ balRecords post := by rwa [hrecs_bal]
      obtain ⟨e0, e8, _⟩ := hbal_eq.2 ad had_p
      rw [e0, e8]
    have hj_map : (List.range (globN s "journal_n")).map (fun k => memW post (globN s "journal" + 32 * k)) =
        (List.range (globN s "journal_n")).map (fun k => memW s (globN s "journal" + 32 * k)) := by
      apply List.map_congr_left; intro k hk
      exact (hj_cells k (List.mem_range.1 hk)).1
    dsimp only
    rw [hbs_g, hts_g, hws_sl, hbs_sl, hts_sl, hnest_bs_w, hnest_ts_w, hbal_fl, hj_map]
  have hdelEx_imp : ∀ (i : Nat) (hi : i + 1 < (evmChain s).length) (u : Nat),
      DelExclusive s S (evmChain s) i u →
      DelExclusive post S (evmChain s) i u := by
    intro i hi u ⟨hu_not_wref, hu_frames⟩
    refine ⟨by rwa [hwref_eq], fun j hj k hk hmem_eq => ?_⟩
    have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
    have hk_le : k + 8 ≤ 280 ∧ k % 8 = 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
    rw [(hrec_eq _ hj_mem).1 k hk_le.1 hk_le.2] at hmem_eq
    exact hu_frames j hj k hk hmem_eq
  have hR_eq : OpDispatchSpec.evmR post = OpDispatchSpec.evmR s := by
    unfold OpDispatchSpec.evmR; rw [hchain_eq]
    congr 1; apply List.map_congr_left; intro ec hec
    rw [(hrec_eq ec hec).1 64 (by omega) (by omega), (hrec_eq ec hec).1 192 (by omega) (by omega)]
  have hmap_gas : ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)) =
        ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)) := by
      apply List.map_congr_left; intro ec hec
      rw [(hrec_eq ec hec).1 64 (by decide) (by decide), (hrec_eq ec hec).1 192 (by decide) (by decide)]
  refine ⟨⟨hW_post, ?_⟩, hchain_eq, hR_eq, hfix_eq, hrecs_bal,
    fun u hu hne => (hother_fp u hu hne).2, fun ec hec => ?_⟩
  · dsimp only; rw [hchain_eq]
    refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, hmap_fo_eq ▸ hFO_pw, ?_, ?_, ?_, hRoles_evm_post, hmap_gas ▸ hGas⟩
    · obtain ⟨ec, hec, hk0⟩ := hch_last
      have hec_mem := List.mem_of_mem_getLast? hec
      exact ⟨ec, hec, by rw [(hrec_eq ec hec_mem).2.1 16 (by omega) (by omega)]; exact hk0⟩
    · intro ec hec
      obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, _, c17⟩ := hFW_all ec hec
      have hlo_ok := (hlogs_congr ec hec).2
      have hmsg_ok : MsgOwned post S (memW post (ec.1 + 112)) := by
        rw [he_eq 112 (by omega) (by omega)]
        obtain ⟨hal_m, hw_m, hdt, hdf, hdfo, Nd_m, hTr_m, hdj_m⟩ := c17
        obtain ⟨hTr_m_post, hne_m_eq⟩ := transfer_tries Nd_m hTr_m
        refine ⟨hag.allocated hal_m, wordsOK_transfer hAs.1 hAp.1 hw_m, ?_, ?_, ?_, Nd_m, hTr_m_post, ?_⟩
        · intro u hu i hi
          by_cases hu0 : u = t0
          · rw [hu0] at hi
            rcases (hfp_t0 i hi).2 with ⟨k, hk, hin⟩ | hfresh
            · exact disj_symm_fc (disj_of_inside_left hin (disj_symm_fc (hdt t0 ht0_S k hk)))
            · exact disj_of_inside_right hfresh (disj_fresh_of_allocated_fc hAs.2 hAp.2 hhp hal_m)
          · rw [(hother_fp u hu hu0).2] at hi; exact hdt u hu i hi
        · rw [hfix_eq]; exact hdf
        · rw [hchain_eq]; intro ec' hec' o ho; rw [hframeObjects_eq ec' hec'] at ho; exact hdfo ec' hec' o ho
        · intro o ho j hj; rw [hne_m_eq] at hj; exact hdj_m o ho j hj
      unfold FrameWF; dsimp only
      rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
          he_eq 88 (by omega) (by omega), he_eq 24 (by omega) (by omega),
          he_eq 40 (by omega) (by omega), he_eq 16 (by omega) (by omega),
          he_eq 32 (by omega) (by omega), he_eq 136 (by omega) (by omega),
          he_eq 168 (by omega) (by omega), he_eq 176 (by omega) (by omega),
          h88_eq 16 (by omega) (by omega), h88_eq 8 (by omega) (by omega),
          hframeLogs_eq ec hec, he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega),
          hframeRet_eq ec hec, hsc_eq, hfm_eq, hevm_empty_eq]
      rw [he_eq 88 (by omega) (by omega)] at hlo_ok
      refine ⟨fun i hi => ⟨(c1 i hi).1, wordsOK_transfer hAs.1 hAp.1 (c1 i hi).2⟩,
        c2, wordsOK_transfer hAs.1 hAp.1 c3, c4, c5, c6, c7, c8, c9, c10, c11, c12,
        ?_, wordsOK_transfer hAs.1 hAp.1 c14, ?_, hlo_ok, hmsg_ok⟩
      · rcases c13 with h | h
        · exact Or.inl ⟨h.1, le_trans h.2 hhp⟩
        · exact Or.inr h
      · rcases c15 with h0 | ⟨hin, hw⟩
        · exact Or.inl h0
        · exact Or.inr ⟨⟨hin.1, le_trans hin.2 hhp⟩, wordsOK_transfer hAs.1 hAp.1 hw⟩
    · intro ec hec
      have hec_mem := List.mem_of_mem_tail hec
      unfold FrameRoom
      rw [(hrec_eq ec hec_mem).1 16 (by omega) (by omega), (hrec_eq ec hec_mem).1 232 (by omega) (by omega)]
      exact hFR_all ec hec
    · intro i hi
      have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
      have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
      rw [(hrec_eq _ hi0).2.1 80 (by decide) (by decide),
          (hrec_eq _ hi0).2.1 72 (by decide) (by decide),
          (hrec_eq _ hi1).1 40 (by decide) (by decide)]
      exact hRW i hi
    · intro ec hec o ho
      have ho_s : o ∈ frameObjects s ec := by rwa [← hframeObjects_eq ec hec]
      rw [hfix_eq]
      refine ⟨fun u hu i hi => ?_, (hFO_disj ec hec o ho_s).2⟩
      by_cases hu0 : u = t0
      · rw [hu0] at hi
        rcases (hfp_t0 i hi).2 with ⟨k, hk, hin⟩ | hfresh
        · exact disj_symm_fc (disj_of_inside_left hin (disj_symm_fc ((hFO_disj ec hec o ho_s).1 t0 ht0_S k hk)))
        · exact disj_of_inside_right hfresh (disj_fresh_of_frameObject_fc hAs.2 hAp.2 hhp (hFW_all ec hec) ho_s)
      · rw [(hother_fp u hu hu0).2] at hi; exact (hFO_disj ec hec o ho_s).1 u hu i hi
    · rw [hmap_fo_eq]
      refine ⟨Nd_at, hTr_at_post, fun o ho j hj => ?_⟩
      rw [hne_at_eq] at hj; exact hAT_at o ho j hj
    · intro i hi
      have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
      have hm_eq := (hrec_eq _ hi_mem).2.1 48 (by omega) (by omega)
      have hmm_eq := (hrec_eq _ hi_mem).2.1 56 (by omega) (by omega)
      have he24_eq := (hrec_eq _ hi_mem).1 24 (by omega) (by omega)
      have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
          ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
        apply List.map_congr_left; intro ec hec
        exact (hrec_eq ec (List.mem_of_mem_take hec)).1 136 (by omega) (by omega)
      have hM := hMarks i hi
      dsimp only at hM ⊢
      rw [hm_eq, hmm_eq, he24_eq, hframeScratch_eq _ hi_mem, hfix_eq, htake_eq]
      obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
      refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
      · intro j hj hij
        have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
        rw [hframeScratch_eq _ hj_mem, hframeObjects_eq _ hj_mem, hframeLogs_eq _ hj_mem,
            (hrec_eq _ hj_mem).1 112 (by omega) (by omega)]
        exact m5 j hj hij
      · intro u hu
        by_cases hu0 : u = t0
        · rw [hu0]
          rcases m8 t0 ht0_S with ⟨htake, _⟩ | hloc
          · obtain ⟨ec, hec_tk, heq_del⟩ := List.mem_map.1 htake
            exact absurd heq_del (ht0_no_del ec (List.mem_of_mem_take hec_tk))
          · right; intro o ho
            rcases (hfp_t0 o ho).2 with ⟨k, hk, hin⟩ | hfresh
            · rcases hloc k hk with hh | hm
              · exact Or.inl ⟨le_trans hh.1 hin.1, le_trans hin.2 hh.2⟩
              · exact Or.inr ⟨le_trans hm.1 hin.1, le_trans hin.2 hm.2⟩
            · exact Or.inl ⟨le_trans hAs.2.1 hfresh.1,
                le_trans hfresh.2 (by rw [Nat.add_sub_of_le hhp]; exact hAp.2.2.1)⟩
        · rw [(hother_fp u hu hu0).2]
          rcases m8 u hu with ⟨htake, hdel⟩ | hloc
          · exact Or.inl ⟨htake, hdelEx_imp i hi u hdel⟩
          · exact Or.inr hloc
  · obtain ⟨he_eq, hc_eq, _⟩ := hrec_eq ec hec
    exact ⟨hframeObjects_eq ec hec, hframeScratch_eq ec hec, hframeLogs_eq ec hec,
      he_eq 16 (by omega) (by omega), he_eq 24 (by omega) (by omega),
      he_eq 32 (by omega) (by omega), he_eq 40 (by omega) (by omega),
      he_eq 112 (by omega) (by omega), he_eq 136 (by omega) (by omega),
      he_eq 232 (by omega) (by omega), hc_eq 56 (by omega) (by omega)⟩

theorem lookup_rollback_child_access :
    originalRuntimeCode.lookup (ofString "rollback_child_access") =
      some ([(ofString "child", .one)],
        sourceFnBody Guest.Software.guestFn_rollback_child_access, .one) :=
  lookup_of_guestAst_getElem 593 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rollback_child_access) rfl

theorem lookup_incorporate_child_on_error :
    originalRuntimeCode.lookup (ofString "incorporate_child_on_error") =
      some ([(ofString "child", .one)],
        sourceFnBody Guest.Software.guestFn_incorporate_child_on_error, .one) :=
  lookup_of_guestAst_getElem 591 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_incorporate_child_on_error) rfl

private theorem allocated_of_scratch_fc {F : Type} {s : PanSemStateFiniteExact 64 F} {i : Ivl}
    (_hA : ArenaOK s) (hin : Inside i (globN s "scratch_ptr") scratchEnd) :
    Allocated s i := by
  exact Or.inr hin

theorem call_htab_truncate_nonDel_step {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F} {S : List Nat}
    {offT offM : Nat}
    (hA : ArenaReady st)
    (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt st S)
    (hRel : ReleaseReadyAt st S (memW s0 (globN s0 "cur_cont" + 48))
      (memW s0 (globN s0 "cur_cont" + 56)))
    (hchild_lk : st.locals.lookup (ofString "child") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "ev")))))
    (hchild_scr : Inside (globN s0 "ev", 280) (globN st "scratch_ptr") scratchEnd ∧
      WordsOK st (globN s0 "ev", 280))
    (hrec_scr : Inside (globN s0 "cur_cont", 104) (globN st "scratch_ptr") scratchEnd ∧
      WordsOK st (globN s0 "cur_cont", 104))
    (hchild_dht : ∀ t ∈ S, ∀ i ∈ htabFootprint st t, Disj (globN s0 "ev", 280) i)
    (hrec_dht : ∀ t ∈ S, ∀ i ∈ htabFootprint st t, Disj (globN s0 "cur_cont", 104) i)
    (hoffT : offT + 8 ≤ 280 ∧ offT % 8 = 0)
    (hoffM : offM + 8 ≤ 280 ∧ offM % 8 = 0)
    (ht0_nd : NonDelAccessTable st S (memW st (globN s0 "ev" + offT)))
    (hnt : (evaluateHOLFiniteState st
      (.call (some (none, none)) (ofString "htab_truncate")
        [.load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 offT)]),
         .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 offM)])])).1 ≠
      some .timeOut) :
    let prog : ProgHOL 64 := .call (some (none, none)) (ofString "htab_truncate")
      [.load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 offT)]),
       .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 offM)])]
    (∀ u, (evaluateHOLFiniteState st prog).1 ≠ some (.returned u)) ∧
    ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState st prog).1 ∧
    ((evaluateHOLFiniteState st prog).1 = none →
      let post := (evaluateHOLFiniteState st prog).2
      ArenaReady post ∧
      InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt post S ∧
      ReleaseReadyAt post S (memW s0 (globN s0 "cur_cont" + 48))
        (memW s0 (globN s0 "cur_cont" + 56)) ∧
      post.locals = st.locals ∧
      globN st "heap_ptr" ≤ globN post "heap_ptr" ∧
      globN post "scratch_ptr" = globN st "scratch_ptr" ∧
      globN post "ev" = globN st "ev" ∧
      evmChain post = evmChain st ∧
      OpDispatchSpec.evmR post = OpDispatchSpec.evmR st ∧
      fixedObjects post = fixedObjects st ∧
      post.memaddrs = st.memaddrs ∧
      M08IvlUnhitFc st post (globN s0 "ev", 280) ∧
      M08IvlUnhitFc st post (globN s0 "cur_cont", 104) ∧
      (∀ off : Nat, off + 8 ≤ 280 → off % 8 = 0 → memW post (globN s0 "ev" + off) = memW st (globN s0 "ev" + off)) ∧
      (∀ ec ∈ evmChain st,
        frameObjects post ec = frameObjects st ec ∧
        memW post (ec.1 + 16) = memW st (ec.1 + 16) ∧
        memW post (ec.1 + 24) = memW st (ec.1 + 24) ∧
        memW post (ec.1 + 32) = memW st (ec.1 + 32) ∧
        memW post (ec.1 + 40) = memW st (ec.1 + 40) ∧
        memW post (ec.1 + 136) = memW st (ec.1 + 136) ∧
        memW post (ec.1 + 232) = memW st (ec.1 + 232) ∧
        memW post (ec.2 + 56) = memW st (ec.2 + 56)) ∧
      (∀ t1 : Nat, NonDelAccessTable st S t1 → NonDelAccessTable post S t1) ∧
      (∀ t ∈ S, ∀ i ∈ htabFootprint post t,
        Disj (globN s0 "ev", 280) i ∧ Disj (globN s0 "cur_cont", 104) i)) := by
  dsimp only
  obtain ⟨hne_ret, hnone, herr⟩ := call0_outcome_fc (s := st) (fname := ofString "htab_truncate")
    (args := [.load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 offT)]),
              .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 offM)])]) hnt
  have hcode : st.code = originalRuntimeCode := hA.1.code
  have hno_err : ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState st
      (.call (some (none, none)) (ofString "htab_truncate")
        [.load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 offT)]),
         .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 offM)])])).1 := by
    intro he
    obtain ⟨vals, body, cal, ret, v, cpost, _, hl, hrun, _⟩ := herr he
    have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "htab_truncate") vals =
        some (body, cal, ret) := by rwa [← hcode]
    obtain ⟨rfl, _, _, _, _, _, _⟩ :=
      R14Shards.OpHandlersA.two_word_arg_lookup (by decide) HtabC00Ports.lookup_htab_truncate hl_orig
    exact StateRestoreEpilogue.evaluate_noCatchableRaise
      StateRestoreEpilogue.htabMutCallees StateRestoreEpilogue.htabMutCallees_good
      (sourceFnBody Guest.Software.guestFn_htab_truncate) (by decide)
      (callEntryStateHOLFinite st cal) hcode (ofString "EvmErr") v (by decide)
      (by rw [hrun])
  refine ⟨hne_ret, hno_err, fun hn => ?_⟩
  obtain ⟨vals, body, cal, ret, rv, cpost, hargs, hl, hrun, hpost_eq⟩ := hnone hn
  have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "htab_truncate") vals =
      some (body, cal, ret) := by rwa [← hcode]
  obtain ⟨rfl, rfl, wT, wM, rfl, hcal_t, hcal_m⟩ :=
    R14Shards.OpHandlersA.two_word_arg_lookup (by decide) HtabC00Ports.lookup_htab_truncate hl_orig
  have hb_child : globN s0 "ev" + 280 ≤ 2 ^ 64 := by
    have hse := R11Shards.scratchEnd_val
    have : 34208742912 ≤ 2 ^ 64 := by decide
    have := hchild_scr.1.2; dsimp at this; omega
  have hb_rec : globN s0 "cur_cont" + 104 ≤ 2 ^ 64 := by
    have hse := R11Shards.scratchEnd_val
    have : 34208742912 ≤ 2 ^ 64 := by decide
    have := hrec_scr.1.2; dsimp at this; omega
  have hevT := eval_load_local_off st hchild_lk hA.1.memaddrs hchild_scr.2 hb_child hoffT.1 hoffT.2
  have hevM := eval_load_local_off st hchild_lk hA.1.memaddrs hchild_scr.2 hb_child hoffM.1 hoffM.2
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact, hevT, hevM, Option.some.injEq, List.cons.injEq, and_true] at hargs
  rcases hargs with ⟨hvT, hvM⟩
  injection hvT with hvT'; injection hvT' with hwT_eq
  have hwT_nat : wT.toNat = memW st (globN s0 "ev" + offT) := by
    have hlt : memW st (globN s0 "ev" + offT) < 2 ^ 64 := by
      unfold memW; cases st.memory _ with | word w => exact w.isLt
    rw [← hwT_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  set t0 := memW st (globN s0 "ev" + offT)
  set entry := callEntryStateHOLFinite st cal
  have hentry_loc_t : locN entry "t" = t0 := by
    unfold locN; simp [entry, callEntryStateHOLFinite, hcal_t, hwT_nat]
  obtain ⟨params_ht, body_ht, ret_ht, hlk_ht, hspec_ht⟩ := HtabC00Ports.htab_truncate_spec
  have hlk_eq := HtabC00Ports.lookup_htab_truncate.symm.trans hlk_ht
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨rfl, rfl⟩
  have hwf_entry : HtabArgWF entry := by
    refine ⟨⟨guestInv_with_locals_clock st cal _ hA.1, hA.2⟩, ?_, ?_⟩
    · rw [hentry_loc_t]
      exact (StateRestoreEpilogue.htabWF_lc st cal st.globals _ t0).2
        (hInv.1.1.2.1 t0 ht0_nd.1).1
    · rw [hentry_loc_t]
      intro i hi
      change i ∈ htabFootprint st t0 at hi
      exact ((hInv.1.1.2.1 t0 ht0_nd.1).2 i hi).1
  have hexit : HtabExit entry cpost := by
    have h := hspec_ht entry hcode hwf_entry ⟨[_, _], hl_orig⟩
      (by rw [hrun]; simp) rv (by rw [hrun])
    rwa [hrun] at h
  unfold HtabExit at hexit
  rw [hentry_loc_t] at hexit
  obtain ⟨hAc, hwf_c, hhdr0_c, _, hhp_c, hfp_c, hfr_c, hgk_c⟩ := hexit
  set post := (evaluateHOLFiniteState st
    (.call (some (none, none)) (ofString "htab_truncate")
      [.load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 offT)]),
       .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 offM)])])).2
  have hpost_lc : post = { cpost with locals := st.locals } := hpost_eq
  have hAp : ArenaReady post := by
    rw [hpost_lc]; exact (StateRestoreEpilogue.arenaReady_lc cpost st.locals cpost.clock).2 hAc
  have hbe_p : post.be = st.be := by
    rw [hpost_lc]
    have hbe0 := InitECandidate.Solver.Wave8GuestInv.R16Shards.evaluate_be_eq entry
      (sourceFnBody Guest.Software.guestFn_htab_truncate)
    rw [hrun] at hbe0
    exact hbe0
  have hwf_p : HtabWF post t0 := by
    rw [hpost_lc]; exact (StateRestoreEpilogue.htabWF_lc cpost st.locals cpost.globals cpost.clock t0).2 hwf_c
  have hhdr0_p : hdr post t0 0 = hdr st t0 0 := by
    rw [hpost_lc]; exact hhdr0_c
  have hhp_p : globN st "heap_ptr" ≤ globN post "heap_ptr" := by
    rw [hpost_lc]; exact hhp_c
  have hfp_p : ∀ i ∈ htabFootprint post t0, Allocated post i ∧
      ((∃ j ∈ htabFootprint st t0, Inside i j.1 (j.1 + j.2)) ∨
        Inside i (globN st "heap_ptr") (globN st "heap_ptr" + (globN post "heap_ptr" - globN st "heap_ptr"))) := by
    rw [hpost_lc]; exact hfp_c
  have hfr_p : FrameOutside st post (htabFootprint st t0)
      (globN st "heap_ptr", globN post "heap_ptr" - globN st "heap_ptr") := by
    rw [hpost_lc]; exact hfr_c
  have hgk_p : GlobalsKept ["heap_ptr"] st post := by
    intro k hk; rw [hpost_lc]; exact hgk_c k hk
  obtain ⟨hInv_p, hch_p, hR_p, hfix_p, hbal_p, hother_p, hframes_p⟩ :=
    evmInvAt_of_nonDel_htab_step hA hInv ht0_nd hAp hbe_p hwf_p hhdr0_p hhp_p hfp_p hfr_p hgk_p
  have hg_nonHeap : ∀ name, ofString name ≠ ofString "heap_ptr" → globN post name = globN st name := by
    intro name h1
    exact InitECandidate.Solver.Wave8Contracts.M08.globN_eq_of_lookup (hgk_p (ofString name) (by
      simp only [List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
      rintro ⟨w, rfl, heq⟩; exact h1 heq.symm))
  have hsc_p : globN post "scratch_ptr" = globN st "scratch_ptr" := hg_nonHeap "scratch_ptr" (by decide)
  have hev_p : globN post "ev" = globN st "ev" := hg_nonHeap "ev" (by decide)
  have hRel_p : ReleaseReadyAt post S (memW s0 (globN s0 "cur_cont" + 48))
      (memW s0 (globN s0 "cur_cont" + 56)) := by
    refine releaseReadyAt_transport hRel hhp_p hch_p
      (fun ec hec => (hframes_p ec hec).2.1)
      (fun ec hec => ⟨(hframes_p ec hec).2.2.2.2.1, (hframes_p ec hec).2.2.2.2.2.2.1⟩)
      (fun ec hec => Or.inl (hframes_p ec hec).2.2.1)
      (fun ec hec => (hframes_p ec hec).2.2.2.2.2.2.2.1)
      (fun u hu => ?_) hfix_p
    by_cases hu0 : u = t0
    · right; intro o ho; rw [hu0] at ho ⊢
      rcases (hfp_p o ho).2 with ⟨j, hj, hin⟩ | hfresh
      · exact Or.inl ⟨j, hj, hin⟩
      · exact Or.inr ⟨le_trans hA.2.1 hfresh.1,
          le_trans hfresh.2 (by rw [Nat.add_sub_of_le hhp_p])⟩
    · exact Or.inl (hother_p u hu hu0)
  have hloc_p : post.locals = st.locals := by rw [hpost_lc]
  have ht0_al1 : ∀ j ∈ htabFootprint st t0, j.1 % 8 = 0 :=
    fun j hj => ((hInv.1.1.2.1 t0 ht0_nd.1).1.1 j hj).2.1
  have hf_al1 : globN st "heap_ptr" % 8 = 0 := hA.2.2.2.2.2.2.1
  have hu_child : M08IvlUnhitFc st post (globN s0 "ev", 280) :=
    m08_ivlUnhit_of_frameOutside_fc hfr_p ht0_al1 hf_al1 (hchild_dht t0 ht0_nd.1)
      (disj_fresh_of_allocated_fc hA.2 hAp.2 hhp_p (allocated_of_scratch_fc hA.2 hchild_scr.1))
  have hu_rec : M08IvlUnhitFc st post (globN s0 "cur_cont", 104) :=
    m08_ivlUnhit_of_frameOutside_fc hfr_p ht0_al1 hf_al1 (hrec_dht t0 ht0_nd.1)
      (disj_fresh_of_allocated_fc hA.2 hAp.2 hhp_p (allocated_of_scratch_fc hA.2 hrec_scr.1))
  have hchild_mw : ∀ off : Nat, off + 8 ≤ 280 → off % 8 = 0 →
      memW post (globN s0 "ev" + off) = memW st (globN s0 "ev" + off) := by
    intro off hoff hoff8
    have hch8 : globN s0 "ev" % 8 = 0 := hchild_scr.2.1
    exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_child
      (by omega) hb_child ⟨by omega, by omega⟩
  have hnd_keep : ∀ t1 : Nat, NonDelAccessTable st S t1 → NonDelAccessTable post S t1 := by
    intro t1 ⟨ht1_S, ht1_del, ht1_ws, ht1_bs, ht1_ba, ht1_ad, ht1_ts⟩
    have hws_g := hg_nonHeap "ws" (by decide)
    have hbs_g := hg_nonHeap "bs" (by decide)
    have hts_g := hg_nonHeap "ts" (by decide)
    have hba_g := hg_nonHeap "bal_accounts" (by decide)
    have hu_fix_i : ∀ i ∈ fixedObjects st, M08IvlUnhitFc st post i := by
      intro i hi
      exact m08_ivlUnhit_of_frameOutside_fc hfr_p ht0_al1 hf_al1
        (fun j hj => disj_symm_fc (((hInv.1.1.2.1 t0 ht0_nd.1).2 j hj).2 i hi))
        (disj_fresh_of_zero_or_allocated_fc hA.2 hAp.2 hhp_p
          ((hInv.1.2.2.1.1 i hi).imp id And.left))
    refine ⟨ht1_S, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ec hec; rw [hch_p] at hec; rw [(hframes_p ec hec).2.2.2.2.2.2.2.2.1]; exact ht1_del ec hec
    · intro hnz
      rw [hws_g] at hnz
      have hm_ws := InitECandidate.Solver.Wave8Contracts.M08.typedRecord_mem_fixedObjects st
        (r := ("ws", 40)) (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords])
      simp only [hnz, ↓reduceIte] at hm_ws
      rw [InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hA.2 hInv.1.2.2.1 "ws" 40
        (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hws_g hnz (hu_fix_i _ hm_ws) (by omega) (by omega)]
      exact ht1_ws hnz
    · intro hnz
      rw [hbs_g] at hnz
      have hm_bs := InitECandidate.Solver.Wave8Contracts.M08.typedRecord_mem_fixedObjects st
        (r := ("bs", 80)) (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords])
      simp only [hnz, ↓reduceIte] at hm_bs
      rw [InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hA.2 hInv.1.2.2.1 "bs" 80
        (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hbs_g hnz (hu_fix_i _ hm_bs) (by omega) (by omega)]
      exact ht1_bs hnz
    · rw [hba_g]; exact ht1_ba
    · intro ad had; rw [hbal_p] at had
      have had_bal : (ad, 40) ∈ balObjects st := by
        unfold balObjects; exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
      have had_fix : (ad, 40) ∈ fixedObjects st := by
        unfold fixedObjects; exact List.mem_append.2 (Or.inr had_bal)
      rcases hInv.1.2.2.1.1 _ had_fix with h0 | ⟨hal_ad, hw_ad⟩
      · simp at h0
      have hhi_ad := (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hA.2 hal_ad).2
      have had8 := hw_ad.1
      have h0 : memW post ad = memW st ad := by
        simpa using InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit (hu_fix_i _ had_fix)
          (by omega) hhi_ad ⟨by omega, by omega⟩
      rw [h0]; exact ht1_ad ad had
    · intro hnz
      rw [hts_g] at hnz
      have hm_ts := InitECandidate.Solver.Wave8Contracts.M08.typedRecord_mem_fixedObjects st
        (r := ("ts", 72)) (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords])
      simp only [hnz, ↓reduceIte] at hm_ts
      rw [InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hA.2 hInv.1.2.2.1 "ts" 72
        (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hts_g hnz (hu_fix_i _ hm_ts) (by omega) (by omega)]
      exact ht1_ts hnz
  have hdisj_ht_p : ∀ t ∈ S, ∀ i ∈ htabFootprint post t,
      Disj (globN s0 "ev", 280) i ∧ Disj (globN s0 "cur_cont", 104) i := by
    intro t ht i hi
    by_cases ht0 : t = t0
    · rw [ht0] at hi
      rcases (hfp_p i hi).2 with ⟨j, hj, hin⟩ | hfresh
      · exact ⟨disj_symm_fc (InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_left hin (disj_symm_fc (hchild_dht t0 ht0_nd.1 j hj))),
               disj_symm_fc (InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_left hin (disj_symm_fc (hrec_dht t0 ht0_nd.1 j hj)))⟩
      · exact ⟨InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_right hfresh
                 (disj_fresh_of_allocated_fc hA.2 hAp.2 hhp_p (allocated_of_scratch_fc hA.2 hchild_scr.1)),
               InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_right hfresh
                 (disj_fresh_of_allocated_fc hA.2 hAp.2 hhp_p (allocated_of_scratch_fc hA.2 hrec_scr.1))⟩
    · rw [hother_p t ht ht0] at hi
      exact ⟨hchild_dht t ht i hi, hrec_dht t ht i hi⟩
  exact ⟨hAp, hInv_p, hRel_p, hloc_p, hhp_p, hsc_p, hev_p, hch_p, hR_p, hfix_p,
    hAp.1.memaddrs.trans hA.1.memaddrs.symm,
    hu_child, hu_rec, hchild_mw,
    fun ec hec => ⟨(hframes_p ec hec).1, (hframes_p ec hec).2.2.2.1,
      (hframes_p ec hec).2.2.2.2.1, (hframes_p ec hec).2.2.2.2.2.1,
      (hframes_p ec hec).2.2.2.2.2.2.1, (hframes_p ec hec).2.2.2.2.2.2.2.2.1,
      (hframes_p ec hec).2.2.2.2.2.2.2.2.2.1, (hframes_p ec hec).2.2.2.2.2.2.2.2.2.2⟩,
    hnd_keep, hdisj_ht_p⟩

private theorem nonDelAccessTable_lc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (ck : Nat) (S : List Nat) (t0 : Nat) :
    NonDelAccessTable { s with locals := L, clock := ck } S t0 ↔ NonDelAccessTable s S t0 := by
  simp only [NonDelAccessTable, evmChain_lc_fc s L ck]; rfl

private theorem htabFootprint_lc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (ck : Nat) (t : Nat) :
    htabFootprint { s with locals := L, clock := ck } t = htabFootprint s t := rfl

private theorem fixedObjects_lc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (ck : Nat) :
    fixedObjects { s with locals := L, clock := ck } = fixedObjects s := rfl

private theorem frameObjects_lc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (ck : Nat) (ec : Ivl) :
    frameObjects { s with locals := L, clock := ck } ec = frameObjects s ec := rfl

private theorem wordsOK_lc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (ck : Nat) (i : Ivl) :
    WordsOK { s with locals := L, clock := ck } i ↔ WordsOK s i := Iff.rfl

theorem rollback_child_access_step {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hBS : FcBranchState s0 st S)
    (hchild_scr : Inside (globN s0 "ev", 280) (globN st "scratch_ptr") scratchEnd ∧
      WordsOK st (globN s0 "ev", 280))
    (hrec_scr : Inside (globN s0 "cur_cont", 104) (globN st "scratch_ptr") scratchEnd ∧
      WordsOK st (globN s0 "cur_cont", 104))
    (hchild_dht : ∀ t ∈ S, ∀ i ∈ htabFootprint st t, Disj (globN s0 "ev", 280) i)
    (hrec_dht : ∀ t ∈ S, ∀ i ∈ htabFootprint st t, Disj (globN s0 "cur_cont", 104) i)
    (hchild_dfix : ∀ j ∈ fixedObjects st, Disj (globN s0 "ev", 280) j)
    (hchild_dfo : ∀ ec ∈ evmChain st, ∀ o ∈ frameObjects st ec, Disj (globN s0 "ev", 280) o)
    (ht168 : NonDelAccessTable st S (memW st (globN s0 "ev" + 168)))
    (ht176 : NonDelAccessTable st S (memW st (globN s0 "ev" + 176)))
    (hnt : (evaluateHOLFiniteState st
      (.call (some (none, none)) (ofString "rollback_child_access")
        [.var .local (ofString "child")])).1 ≠ some .timeOut) :
    let prog : ProgHOL 64 := .call (some (none, none)) (ofString "rollback_child_access")
      [.var .local (ofString "child")]
    (∀ u, (evaluateHOLFiniteState st prog).1 ≠ some (.returned u)) ∧
    ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState st prog).1 ∧
    ((evaluateHOLFiniteState st prog).1 = none →
      let post := (evaluateHOLFiniteState st prog).2
      FcBranchState s0 post S ∧
      post.locals = st.locals ∧
      globN post "scratch_ptr" = globN st "scratch_ptr" ∧
      globN post "ev" = globN st "ev" ∧
      evmChain post = evmChain st ∧
      OpDispatchSpec.evmR post = OpDispatchSpec.evmR st ∧
      Inside (globN s0 "ev", 280) (globN post "scratch_ptr") scratchEnd ∧
      WordsOK post (globN s0 "ev", 280) ∧
      (∀ t ∈ S, ∀ i ∈ htabFootprint post t, Disj (globN s0 "ev", 280) i) ∧
      (∀ j ∈ fixedObjects post, Disj (globN s0 "ev", 280) j) ∧
      (∀ ec ∈ evmChain post, ∀ o ∈ frameObjects post ec, Disj (globN s0 "ev", 280) o) ∧
      (∀ off : Nat, off + 8 ≤ 280 → off % 8 = 0 →
        memW post (globN s0 "ev" + off) = memW st (globN s0 "ev" + off)) ∧
      (∀ ec ∈ evmChain st,
        memW post (ec.1 + 16) = memW st (ec.1 + 16) ∧
        memW post (ec.1 + 40) = memW st (ec.1 + 40) ∧
        memW post (ec.1 + 232) = memW st (ec.1 + 232))) := by
  dsimp only
  obtain ⟨hne_ret, hnone, herr⟩ := call0_outcome_fc (s := st)
    (fname := ofString "rollback_child_access")
    (args := [.var .local (ofString "child")]) hnt
  have hcode : st.code = originalRuntimeCode := hBS.arena.1.code
  have hev_arg : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
      [.var .local (ofString "child")] =
      some [.val (.word (BitVec.ofNat 64 (globN s0 "ev")))] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact, evalHOLExact, hBS.locals_ok.child_lk]
  let c1_prog : ProgHOL 64 := .call (some (none, none)) (ofString "htab_truncate")
    [.load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 168)]),
     .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 264)])]
  let c2_prog : ProgHOL 64 := .call (some (none, none)) (ofString "htab_truncate")
    [.load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 176)]),
     .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 272)])]
  have hbody_rca : sourceFnBody Guest.Software.guestFn_rollback_child_access =
      .seq c1_prog (.seq c2_prog (.return (.const 0#64))) := rfl
  have hentry_facts : ∀ (cal : HolFiniteMapExact MlS (ValueHOL 64)),
      cal.lookup (ofString "child") = some (.val (.word (BitVec.ofNat 64 (globN s0 "ev")))) →
      (evaluateHOLFiniteState (callEntryStateHOLFinite st cal)
        (sourceFnBody Guest.Software.guestFn_rollback_child_access)).1 ≠ some .timeOut →
      ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState (callEntryStateHOLFinite st cal)
        (sourceFnBody Guest.Software.guestFn_rollback_child_access)).1 ∧
      ∀ rv cpost,
        evaluateHOLFiniteState (callEntryStateHOLFinite st cal)
          (sourceFnBody Guest.Software.guestFn_rollback_child_access) = (some (.returned rv), cpost) →
        let post : PanSemStateFiniteExact 64 F := { cpost with locals := st.locals }
        FcBranchState s0 post S ∧
        post.locals = st.locals ∧
        globN post "scratch_ptr" = globN st "scratch_ptr" ∧
        globN post "ev" = globN st "ev" ∧
        evmChain post = evmChain st ∧
        OpDispatchSpec.evmR post = OpDispatchSpec.evmR st ∧
        Inside (globN s0 "ev", 280) (globN post "scratch_ptr") scratchEnd ∧
        WordsOK post (globN s0 "ev", 280) ∧
        (∀ t ∈ S, ∀ i ∈ htabFootprint post t, Disj (globN s0 "ev", 280) i) ∧
        (∀ j ∈ fixedObjects post, Disj (globN s0 "ev", 280) j) ∧
        (∀ ec ∈ evmChain post, ∀ o ∈ frameObjects post ec, Disj (globN s0 "ev", 280) o) ∧
        (∀ off : Nat, off + 8 ≤ 280 → off % 8 = 0 →
          memW post (globN s0 "ev" + off) = memW st (globN s0 "ev" + off)) ∧
        (∀ ec ∈ evmChain st,
          memW post (ec.1 + 16) = memW st (ec.1 + 16) ∧
          memW post (ec.1 + 40) = memW st (ec.1 + 40) ∧
          memW post (ec.1 + 232) = memW st (ec.1 + 232)) := by
    intro cal hcal_child hnt_body
    let e0 : PanSemStateFiniteExact 64 F := callEntryStateHOLFinite st cal
    have he0_eq : e0 = { st with locals := cal, clock := e0.clock } := rfl
    have he0_A : ArenaReady e0 := (StateRestoreEpilogue.arenaReady_lc st cal e0.clock).2 hBS.arena
    have he0_Inv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt e0 S := by
      have hwt_e0 : WorldTyped e0 S ↔ WorldTyped st S := StateRestoreEpilogue.worldTyped_lc st cal e0.clock S
      have hch_e0' : evmChain e0 = evmChain st := evmChain_lc_fc st cal e0.clock
      have hE := hBS.inv
      dsimp only [InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt] at hE ⊢
      simp only [FrameWF, MsgOwned, hwt_e0, hch_e0'] at hE ⊢
      exact hE
    have he0_Rel : ReleaseReadyAt e0 S (memW s0 (globN s0 "cur_cont" + 48))
        (memW s0 (globN s0 "cur_cont" + 56)) :=
      (releaseReadyAt_lc st cal e0.clock S _ _).2 hBS.release
    have he0_cscr : Inside (globN s0 "ev", 280) (globN e0 "scratch_ptr") scratchEnd ∧
        WordsOK e0 (globN s0 "ev", 280) := ⟨hchild_scr.1, hchild_scr.2⟩
    have he0_rscr : Inside (globN s0 "cur_cont", 104) (globN e0 "scratch_ptr") scratchEnd ∧
        WordsOK e0 (globN s0 "cur_cont", 104) := ⟨hrec_scr.1, hrec_scr.2⟩
    have he0_168 : NonDelAccessTable e0 S (memW e0 (globN s0 "ev" + 168)) :=
      (nonDelAccessTable_lc st cal e0.clock S _).2 ht168
    have he0_176 : NonDelAccessTable e0 S (memW e0 (globN s0 "ev" + 176)) :=
      (nonDelAccessTable_lc st cal e0.clock S _).2 ht176
    change (evaluateHOLFiniteState e0 (sourceFnBody Guest.Software.guestFn_rollback_child_access)).1 ≠
      some .timeOut at hnt_body
    change ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState e0
        (sourceFnBody Guest.Software.guestFn_rollback_child_access)).1 ∧
      ∀ rv cpost,
        evaluateHOLFiniteState e0 (sourceFnBody Guest.Software.guestFn_rollback_child_access) =
          (some (.returned rv), cpost) → _
    rw [hbody_rca, evaluateHOLFiniteState_seq_line780] at hnt_body ⊢
    have hr1_eq := Prod.mk.eta (p := evaluateHOLFiniteState e0 c1_prog)
    set res1 := (evaluateHOLFiniteState e0 c1_prog).1
    set s1 := (evaluateHOLFiniteState e0 c1_prog).2
    have hnt_c1 : (evaluateHOLFiniteState e0 c1_prog).1 ≠ some .timeOut := by
      intro ht; change res1 = some .timeOut at ht
      rw [← hr1_eq, ht] at hnt_body; dsimp only at hnt_body; exact hnt_body rfl
    obtain ⟨hnret1, hnoerr1, hc1_none⟩ := call_htab_truncate_nonDel_step
      he0_A he0_Inv he0_Rel hcal_child he0_cscr he0_rscr hchild_dht hrec_dht
      ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ he0_168 hnt_c1
    rw [← hr1_eq] at hnt_body ⊢
    cases hres1 : res1 with
    | some r1 =>
      dsimp only at hnt_body ⊢
      refine ⟨by rw [← hres1]; exact hnoerr1, fun rv _ hret => ?_⟩
      exfalso; exact hnret1 rv (hres1.trans (Prod.mk.inj hret).1)
    | none =>
      dsimp only at hnt_body ⊢
      obtain ⟨hA1, hInv1, hRel1, hloc1, hhp1, hsc1, hev1, hch1, hR1, hfix1, hma1,
        hu_ch1, hu_rc1, hmw1, hfr1, hnd1, hdisj_ht1⟩ := hc1_none hres1
      rw [evaluateHOLFiniteState_seq_line780] at hnt_body ⊢
      have hr2_eq := Prod.mk.eta (p := evaluateHOLFiniteState s1 c2_prog)
      set res2 := (evaluateHOLFiniteState s1 c2_prog).1
      set s2 := (evaluateHOLFiniteState s1 c2_prog).2
      have hnt_c2 : (evaluateHOLFiniteState s1 c2_prog).1 ≠ some .timeOut := by
        intro ht; change res2 = some .timeOut at ht
        rw [← hr2_eq, ht] at hnt_body
        simp only [hres1] at hnt_body
        exact hnt_body rfl
      have hs1_child_lk : s1.locals.lookup (ofString "child") =
          some (.val (.word (BitVec.ofNat 64 (globN s0 "ev")))) := by
        rw [hloc1]; exact hcal_child
      have hs1_cscr : Inside (globN s0 "ev", 280) (globN s1 "scratch_ptr") scratchEnd ∧
          WordsOK s1 (globN s0 "ev", 280) :=
        ⟨by rw [hsc1]; exact he0_cscr.1,
         InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer he0_A.1 hA1.1 he0_cscr.2⟩
      have hs1_rscr : Inside (globN s0 "cur_cont", 104) (globN s1 "scratch_ptr") scratchEnd ∧
          WordsOK s1 (globN s0 "cur_cont", 104) :=
        ⟨by rw [hsc1]; exact he0_rscr.1,
         InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer he0_A.1 hA1.1 he0_rscr.2⟩
      have hs1_176 : NonDelAccessTable s1 S (memW s1 (globN s0 "ev" + 176)) := by
        rw [hmw1 176 (by decide) (by decide)]
        exact hnd1 _ he0_176
      obtain ⟨hnret2, hnoerr2, hc2_none⟩ := call_htab_truncate_nonDel_step
        hA1 hInv1 hRel1 hs1_child_lk hs1_cscr hs1_rscr
        (fun t ht i hi => (hdisj_ht1 t ht i hi).1)
        (fun t ht i hi => (hdisj_ht1 t ht i hi).2)
        ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ hs1_176 hnt_c2
      rw [← hr2_eq] at hnt_body ⊢
      cases hres2 : res2 with
      | some r2 =>
        dsimp only at hnt_body ⊢
        refine ⟨by rw [← hres2]; exact hnoerr2, fun rv _ hret => ?_⟩
        exfalso; exact hnret2 rv (hres2.trans (Prod.mk.inj hret).1)
      | none =>
        dsimp only at hnt_body ⊢
        obtain ⟨hA2, hInv2, hRel2, _, hhp2, hsc2, hev2, hch2, hR2, hfix2, _,
          _, _, hmw2, hfr2, _, hdisj_ht2⟩ := hc2_none hres2
        rw [evaluateHOLFiniteState_return]
        have hev0 : @evalHOLExact 64 F _ s2.toExact (fun x => Classical.propDecidable (s2.memaddrs x))
            (.const 0#64) = some (.val (.word 0#64)) := rfl
        rw [hev0]; dsimp only
        have hsz0 : sizeOfShapeWithContextHOL s2.structs (shapeOfHOLExact (.val (.word 0#64) : ValueHOL 64)) ≤ 32 := by
          simp [shapeOfHOLExact]
        rw [if_pos hsz0]; dsimp only
        refine ⟨by simp [OpDispatchSpec.IsEvmErr], fun rv cpost hret => ?_⟩
        injection hret with hr_eq hcpost_eq
        have hcpost : cpost = s2.emptyLocalsHOLFinite := hcpost_eq.symm
        set post : PanSemStateFiniteExact 64 F := { cpost with locals := st.locals }
        have hpost_s2 : post = { s2 with locals := st.locals, clock := s2.clock } := by
          simp [post, hcpost, PanSemStateFiniteExact.emptyLocalsHOLFinite]
        have hch_e0 : evmChain e0 = evmChain st := evmChain_lc_fc st cal e0.clock
        have hR_e0 : OpDispatchSpec.evmR e0 = OpDispatchSpec.evmR st := evmR_lc_fc st cal e0.clock
        have hch_s2 : evmChain s2 = evmChain st := hch2.trans (hch1.trans hch_e0)
        have hR_s2 : OpDispatchSpec.evmR s2 = OpDispatchSpec.evmR st := hR2.trans (hR1.trans hR_e0)
        have hsc_s2 : globN s2 "scratch_ptr" = globN st "scratch_ptr" := hsc2.trans hsc1
        have hev_s2 : globN s2 "ev" = globN st "ev" := hev2.trans hev1
        have hfix_s2 : fixedObjects s2 = fixedObjects st := hfix2.trans hfix1
        have hAp : ArenaReady post := by
          rw [hpost_s2]; exact (StateRestoreEpilogue.arenaReady_lc s2 st.locals s2.clock).2 hA2
        have hInvp : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt post S := by
          rw [hpost_s2]
          have hwt_s2 : WorldTyped { s2 with locals := st.locals, clock := s2.clock } S ↔
              WorldTyped s2 S := StateRestoreEpilogue.worldTyped_lc s2 st.locals s2.clock S
          have hch_s2' : evmChain { s2 with locals := st.locals, clock := s2.clock } =
              evmChain s2 := evmChain_lc_fc s2 st.locals s2.clock
          have hE := hInv2
          dsimp only [InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt] at hE ⊢
          simp only [FrameWF, MsgOwned, hwt_s2, hch_s2'] at hE ⊢
          exact hE
        have hRelp : ReleaseReadyAt post S (memW s0 (globN s0 "cur_cont" + 48))
            (memW s0 (globN s0 "cur_cont" + 56)) := by
          rw [hpost_s2]; exact (releaseReadyAt_lc s2 st.locals s2.clock S _ _).2 hRel2
        have hch_p : evmChain post = evmChain st := by
          rw [hpost_s2, evmChain_lc_fc]; exact hch_s2
        have hR_p : OpDispatchSpec.evmR post = OpDispatchSpec.evmR st := by
          rw [hpost_s2, evmR_lc_fc]; exact hR_s2
        have hsc_p : globN post "scratch_ptr" = globN st "scratch_ptr" := by
          rw [hpost_s2]; exact hsc_s2
        have hev_p : globN post "ev" = globN st "ev" := by
          rw [hpost_s2]; exact hev_s2
        have hBS_p : FcBranchState s0 post S := by
          refine ⟨hAp, hInvp, hRelp, fcEntryLocals_congr_locals (s1 := st) (s2 := post) rfl hBS.locals_ok,
            hch_p.trans hBS.chain_eq, ?_, ?_, ?_, hev_p.trans hBS.ev_eq⟩
          · rw [hch_p]; exact hBS.length_eq
          · rw [hR_p]; exact hBS.r_le
          · intro ec hec; rw [hch_p] at hec
            have hec_e0 : ec ∈ evmChain e0 := by rwa [hch_e0]
            have hec_s1 : ec ∈ evmChain s1 := by rwa [hch1]
            obtain ⟨a0, b0, c0, d0⟩ := hBS.cells ec hec
            have hf1 := hfr1 ec hec_e0
            have hf2 := hfr2 ec hec_s1
            have hm_p : ∀ addr, memW post addr = memW s2 addr := fun _ => by rw [hpost_s2]; rfl
            exact ⟨(hm_p _).trans (hf2.2.2.1.trans (hf1.2.2.1.trans a0)),
                   (hm_p _).trans (hf2.2.2.2.1.trans (hf1.2.2.2.1.trans b0)),
                   (hm_p _).trans (hf2.2.2.2.2.1.trans (hf1.2.2.2.2.1.trans c0)),
                   (hm_p _).trans (hf2.2.2.2.2.2.2.2.trans (hf1.2.2.2.2.2.2.2.trans d0))⟩
        refine ⟨hBS_p, rfl, hsc_p, hev_p, hch_p, hR_p, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hsc_p]; exact hchild_scr.1
        · exact InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hBS.arena.1 hAp.1 hchild_scr.2
        · intro t ht i hi
          rw [hpost_s2, htabFootprint_lc] at hi
          exact (hdisj_ht2 t ht i hi).1
        · intro j hj
          rw [hpost_s2, fixedObjects_lc, hfix_s2] at hj
          exact hchild_dfix j hj
        · intro ec hec o ho
          rw [hch_p] at hec
          have hec_e0 : ec ∈ evmChain e0 := by rwa [hch_e0]
          have hec_s1 : ec ∈ evmChain s1 := by rwa [hch1]
          rw [hpost_s2, frameObjects_lc, (hfr2 ec hec_s1).1, (hfr1 ec hec_e0).1, frameObjects_lc] at ho
          exact hchild_dfo ec hec o ho
        · intro off hoff hoff8
          have hm_p : memW post (globN s0 "ev" + off) = memW s2 (globN s0 "ev" + off) := by
            rw [hpost_s2]; rfl
          exact hm_p.trans ((hmw2 off hoff hoff8).trans (hmw1 off hoff hoff8))
        · intro ec hec
          have hec_e0 : ec ∈ evmChain e0 := by rwa [hch_e0]
          have hec_s1 : ec ∈ evmChain s1 := by rwa [hch1]
          have hf1 := hfr1 ec hec_e0
          have hf2 := hfr2 ec hec_s1
          have hm_p : ∀ addr, memW post addr = memW s2 addr := fun _ => by rw [hpost_s2]; rfl
          exact ⟨(hm_p _).trans (hf2.2.1.trans hf1.2.1),
                 (hm_p _).trans (hf2.2.2.2.2.1.trans hf1.2.2.2.2.1),
                 (hm_p _).trans (hf2.2.2.2.2.2.2.1.trans hf1.2.2.2.2.2.2.1)⟩
  have hno_err : ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState st
      (.call (some (none, none)) (ofString "rollback_child_access")
        [.var .local (ofString "child")])).1 := by
    intro he
    obtain ⟨vals, body, cal, ret, v, cpost, hargs, hl, hrun, _⟩ := herr he
    rw [hev_arg] at hargs; injection hargs with hvals; subst hvals
    have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup
        (ofString "rollback_child_access")
        [.val (.word (BitVec.ofNat 64 (globN s0 "ev")))] = some (body, cal, ret) := by
      rwa [← hcode]
    obtain ⟨rfl, _, w0, hw0, hcal_c⟩ :=
      R14Shards.OpHandlersA.one_word_arg_lookup lookup_rollback_child_access hl_orig
    injection hw0 with hw0'; injection hw0' with hw0_eq; subst hw0_eq
    have hnt_body : (evaluateHOLFiniteState (callEntryStateHOLFinite st cal)
        (sourceFnBody Guest.Software.guestFn_rollback_child_access)).1 ≠ some .timeOut := by
      rw [hrun]; simp
    exact (hentry_facts cal hcal_c hnt_body).1 ⟨v, by rw [hrun]⟩
  refine ⟨hne_ret, hno_err, fun hn => ?_⟩
  obtain ⟨vals, body, cal, ret, rv, cpost, hargs, hl, hrun, hpost_eq⟩ := hnone hn
  rw [hev_arg] at hargs; injection hargs with hvals; subst hvals
  have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "rollback_child_access")
      [.val (.word (BitVec.ofNat 64 (globN s0 "ev")))] = some (body, cal, ret) := by
    rwa [← hcode]
  obtain ⟨rfl, _, w0, hw0, hcal_c⟩ :=
    R14Shards.OpHandlersA.one_word_arg_lookup lookup_rollback_child_access hl_orig
  injection hw0 with hw0'; injection hw0' with hw0_eq; subst hw0_eq
  have hnt_body : (evaluateHOLFiniteState (callEntryStateHOLFinite st cal)
      (sourceFnBody Guest.Software.guestFn_rollback_child_access)).1 ≠ some .timeOut := by
    rw [hrun]; simp
  have hres := (hentry_facts cal hcal_c hnt_body).2 rv cpost hrun
  rwa [← hpost_eq] at hres

theorem fc_eval_add_words {F : Type} (s : PanSemStateFiniteExact 64 F)
    {a b : ExpHOL 64} {aw bw : BitVec 64}
    (ha : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) a =
      some (.val (.word aw)))
    (hb : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) b =
      some (.val (.word bw))) :
    @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.op .add [a, b]) = some (.val (.word (aw + bw))) := by
  simp [evalHOLExact, evalListHOLExact, ha, hb, wordOpHOL, wordOp,
    valueIsWord, valueWord]

theorem fc_store_add_words {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {off : Nat} {ew aw bw : BitVec 64} {a b : ExpHOL 64}
    (he : s.globals.lookup (ofString "ev") = some (.val (.word ew)))
    (hen : ew.toNat = globN s "ev")
    (hbound : globN s "ev" + off < 2 ^ 64)
    (ha : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) a =
      some (.val (.word aw)))
    (hb : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) b =
      some (.val (.word bw)))
    (hrun : evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)])
        (.op .add [a, b])) = (none, post)) :
    post = { s with
      memory := R14Shards.OpHandlersA.updW s.memory
        (BitVec.ofNat 64 (globN s "ev" + off)) (aw + bw) } := by
  have hv := fc_eval_add_words s ha hb
  obtain ⟨w, hw, hp⟩ := R14Shards.OpHandlersA.store_global_off_word
    he hen hbound (fun v h => by rw [hv] at h; exact ⟨aw + bw, (Option.some.inj h).symm⟩) hrun
  rw [hv] at hw
  have hw' : w = aw + bw := by simpa using hw.symm
  simpa only [hw'] using hp

private theorem wordsOK_updW {F : Type} (s : PanSemStateFiniteExact 64 F)
    {ivl : Ivl} (hw : WordsOK s ivl) (a w : BitVec 64) :
    WordsOK { s with memory := R14Shards.OpHandlersA.updW s.memory a w } ivl := by
  refine ⟨hw.1, hw.2.1, fun k hk => ?_⟩
  obtain ⟨wk, hdom, hm⟩ := hw.2.2 k hk
  dsimp only [WordAt, R14Shards.OpHandlersA.updW]
  by_cases heq : BitVec.ofNat 64 (ivl.1 + 8 * k) = a
  · exact ⟨w, hdom, if_pos heq⟩
  · exact ⟨wk, hdom, (if_neg heq).trans hm⟩

private theorem ev_head_facts {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hA : ArenaReady s) (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S) :
    globN s "ev" + 280 ≤ 2 ^ 64 ∧
    WordsOK s (globN s "ev", 280) ∧
    s.globals.lookup (ofString "ev") =
      some (.val (.word (BitVec.ofNat 64 (globN s "ev")))) ∧
    memW s (globN s "ev" + 16) ≤ memW s (globN s "ev" + 232) ∧
    OpDispatchSpec.evmR s =
      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) +
        (((evmChain s).tail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) := by
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    rw [evmChain_cons]; exact List.mem_cons_self
  have hFW := hInv.2.2.2.2.1 _ hhead
  have hbnd := (InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hA.2 hFW).1
  dsimp only at hbnd
  have hwok : WordsOK s (globN s "ev", 280) := (hFW.1 (globN s "ev", 280) (by simp)).2
  obtain ⟨evw, hevw⟩ := hA.2.2.2.2.2.2.2.2.2 "ev" (by decide)
  have hevw_eq : evw = BitVec.ofNat 64 (globN s "ev") := by
    apply BitVec.eq_of_toNat_eq
    unfold GlobalWord at hevw
    have hgn : globN s "ev" = evw.toNat := by simp [globN, hevw]
    rw [BitVec.toNat_ofNat, hgn, Nat.mod_eq_of_lt evw.isLt]
  subst hevw_eq
  unfold GlobalWord at hevw
  have hsp : memW s (globN s "ev" + 16) ≤ memW s (globN s "ev" + 232) := hFW.2.2.2.2.1
  have hR : OpDispatchSpec.evmR s =
      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) +
        (((evmChain s).tail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) := by
    unfold OpDispatchSpec.evmR
    conv_lhs => rw [evmChain_cons]
    conv_rhs => rw [evmChain_cons]
    simp [Nat.add_assoc]
  exact ⟨hbnd, hwok, hevw, hsp, hR⟩

private theorem eval_load_ev_off {F : Type} (s : PanSemStateFiniteExact 64 F)
    {base off : Nat}
    (hlk : s.globals.lookup (ofString "ev") = some (.val (.word (BitVec.ofNat 64 base))))
    (hwok : WordsOK s (base, 280))
    (hbnd : base + 280 ≤ 2 ^ 64)
    (hoff : off + 8 ≤ 280) (hoff8 : off % 8 = 0) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)])) =
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
  simp only [hmem_dom, ↓reduceIte, hmem_eq, Option.some.injEq, ValueHOL.val.injEq,
    HolWordLab.word.injEq]
  unfold memW
  rw [hmem_eq]; simp

theorem head_simple_release_step {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} {sm fm : Nat}
    (hA : ArenaReady s)
    (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (hRel : ReleaseReadyAt s S sm fm)
    (hGp : GuestInv post)
    (hglob : post.globals = s.globals)
    (hbe : post.be = s.be)
    (hmem_out : ∀ x : BitVec 64,
      (∀ off ∈ headSimpleOffs, x ≠ BitVec.ofNat 64 (globN s "ev" + off)) →
      post.memory x = s.memory x)
    (hsp : memW post (globN s "ev" + 16) ≤ memW s (globN s "ev" + 232))
    (hgas : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) +
      (((evmChain s).tail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) + 1 < 2 ^ 64) :
    ArenaReady post ∧
      InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt post S ∧
      ReleaseReadyAt post S sm fm ∧
      evmChain post = evmChain s ∧
      OpDispatchSpec.evmR post =
        memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) +
          (((evmChain s).tail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) := by
  obtain ⟨hAp, hIp, hch, hfix, htab, hframes, hR⟩ :=
    evmInvAt_of_head_simple hA hInv hGp hglob hbe hmem_out hsp hgas
  have hhp : globN s "heap_ptr" ≤ globN post "heap_ptr" := by
    unfold globN
    rw [hglob]
  have hRelp := releaseReadyAt_transport hRel hhp hch
    (fun ec hec => (hframes ec hec).2.1)
    (fun ec hec => ⟨(hframes ec hec).2.2.2.1, (hframes ec hec).2.2.2.2.2.1⟩)
    (fun ec hec => Or.inl (hframes ec hec).2.2.1)
    (fun ec hec => (hframes ec hec).2.2.2.2.2.2.1)
    (fun t ht => Or.inl (htab t ht)) hfix
  exact ⟨hAp, hIp, hRelp, hch, hR⟩

theorem incorporate_child_on_error_call_core {F : Type}
    {st : PanSemStateFiniteExact 64 F} {S : List Nat} {sm fm child : Nat}
    {childExp : ExpHOL 64}
    (hA : ArenaReady st)
    (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt st S)
    (hRel : ReleaseReadyAt st S sm fm)
    (hchild_arg : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
      [childExp] = some [.val (.word (BitVec.ofNat 64 child))])
    (hchild_wok : WordsOK st (child, 280))
    (hchild_bnd : child + 280 ≤ 2 ^ 64)
    (hgas : OpDispatchSpec.evmR st + memW st (child + 64) + 1 < 2 ^ 64)
    (hnt : (evaluateHOLFiniteState st
      (.call (some (none, none)) (ofString "incorporate_child_on_error") [childExp])).1 ≠
        some .timeOut) :
    let prog : ProgHOL 64 := .call (some (none, none)) (ofString "incorporate_child_on_error") [childExp]
    (∀ u, (evaluateHOLFiniteState st prog).1 ≠ some (.returned u)) ∧
    ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState st prog).1 ∧
    ((evaluateHOLFiniteState st prog).1 = none →
      let post := (evaluateHOLFiniteState st prog).2
      ArenaReady post ∧
      InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt post S ∧
      ReleaseReadyAt post S sm fm ∧
      post.locals = st.locals ∧
      post.globals = st.globals ∧
      post.be = st.be ∧
      evmChain post = evmChain st ∧
      OpDispatchSpec.evmR post = OpDispatchSpec.evmR st + memW st (child + 64) ∧
      memW post (globN st "ev" + 64) = memW st (globN st "ev" + 64) + memW st (child + 64) ∧
      (∀ x : BitVec 64,
        x ≠ BitVec.ofNat 64 (globN st "ev" + 64) →
        x ≠ BitVec.ofNat 64 (globN st "ev" + 72) →
        x ≠ BitVec.ofNat 64 (globN st "ev" + 184) →
        post.memory x = st.memory x)) := by
  dsimp only
  obtain ⟨hne_ret, hnone, herr⟩ := call0_outcome_fc (s := st)
    (fname := ofString "incorporate_child_on_error") (args := [childExp]) hnt
  have hcode : st.code = originalRuntimeCode := hA.1.code
  have hno_err : ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState st
      (.call (some (none, none)) (ofString "incorporate_child_on_error") [childExp])).1 := by
    intro he
    obtain ⟨vals, body, cal, ret, v, cpost, hargs, hl, hrun, _⟩ := herr he
    rw [hchild_arg] at hargs; injection hargs with hvals; subst hvals
    have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup
        (ofString "incorporate_child_on_error")
        [.val (.word (BitVec.ofNat 64 child))] = some (body, cal, ret) := by
      rwa [← hcode]
    obtain ⟨rfl, _, _, _, _⟩ :=
      R14Shards.OpHandlersA.one_word_arg_lookup lookup_incorporate_child_on_error hl_orig
    have hncr := StateRestoreEpilogue.evaluate_noCatchableRaise (fun _ => false)
      (by intro f hf; cases hf)
      (sourceFnBody Guest.Software.guestFn_incorporate_child_on_error) (by decide)
      (callEntryStateHOLFinite st cal) hcode
    exact hncr (ofString "EvmErr") v (by decide) (by rw [hrun])
  refine ⟨hne_ret, hno_err, fun hn => ?_⟩
  obtain ⟨vals, body, cal, ret, rv, cpost, hargs, hl, hrun, hpost_eq⟩ := hnone hn
  rw [hchild_arg] at hargs; injection hargs with hvals; subst hvals
  have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "incorporate_child_on_error")
      [.val (.word (BitVec.ofNat 64 child))] = some (body, cal, ret) := by
    rwa [← hcode]
  obtain ⟨rfl, _, w0, hw0, hcal_c⟩ :=
    R14Shards.OpHandlersA.one_word_arg_lookup lookup_incorporate_child_on_error hl_orig
  injection hw0 with hw0'; injection hw0' with hw0_eq; subst hw0_eq
  obtain ⟨he_bnd, he_wok, he_lk, he_sp, hR_st⟩ := ev_head_facts hA hInv
  set e0 := globN st "ev"
  set s0_c := callEntryStateHOLFinite st cal
  have he_nat : (BitVec.ofNat 64 e0).toNat = e0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hs0_ev : s0_c.globals.lookup (ofString "ev") = some (.val (.word (BitVec.ofNat 64 e0))) := he_lk
  have hs0_gn : globN s0_c "ev" = e0 := rfl
  have hs0_ewok : WordsOK s0_c (e0, 280) := he_wok
  have hs0_cwok : WordsOK s0_c (child, 280) := hchild_wok
  have hs0_ch : s0_c.locals.lookup (ofString "child") =
      some (.val (.word (BitVec.ofNat 64 child))) := hcal_c
  let p64 : ProgHOL 64 := .store
    (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 64)])
    (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 64)]),
               .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 64)])])
  let p72 : ProgHOL 64 := .store
    (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 72)])
    (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 72)]),
               .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 72)])])
  let p184 : ProgHOL 64 := .store
    (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 184)])
    (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 184)]),
               .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 184)])])
  have hbody_eq : sourceFnBody Guest.Software.guestFn_incorporate_child_on_error =
      .seq p64 (.seq p72 (.seq p184 (.return (.const 0#64)))) := rfl
  change evaluateHOLFiniteState s0_c
    (sourceFnBody Guest.Software.guestFn_incorporate_child_on_error) =
    (some (.returned rv), cpost) at hrun
  rw [hbody_eq, evaluateHOLFiniteState_seq_line780] at hrun
  have hr1_eta := Prod.mk.eta (p := evaluateHOLFiniteState s0_c p64)
  set r1 := (evaluateHOLFiniteState s0_c p64).1
  set s1 := (evaluateHOLFiniteState s0_c p64).2
  rw [← hr1_eta] at hrun
  cases hr1 : r1 with
  | some res1 =>
    rw [hr1] at hr1_eta hrun
    have herr1 := R14Shards.OpHandlersA.store_some_eq_error' hr1_eta.symm
    subst herr1
    dsimp only at hrun
    cases (Prod.mk.inj hrun).1
  | none =>
    rw [hr1] at hr1_eta hrun
    dsimp only at hrun
    have ha1 := eval_load_ev_off s0_c hs0_ev hs0_ewok he_bnd (off := 64) (by omega) (by omega)
    have hb1 := eval_load_local_off s0_c hs0_ch hA.1.memaddrs hs0_cwok hchild_bnd
      (off := 64) (by omega) (by omega)
    have hs1_eq := fc_store_add_words hs0_ev (by rw [hs0_gn]; exact he_nat)
      (by rw [hs0_gn]; omega) ha1 hb1 hr1_eta.symm
    have hs1_ewok : WordsOK s1 (e0, 280) := by rw [hs1_eq]; exact wordsOK_updW s0_c hs0_ewok _ _
    have hs1_cwok : WordsOK s1 (child, 280) := by rw [hs1_eq]; exact wordsOK_updW s0_c hs0_cwok _ _
    have hs1_ev : s1.globals.lookup (ofString "ev") = some (.val (.word (BitVec.ofNat 64 e0))) := by
      rw [hs1_eq]; exact hs0_ev
    have hs1_gn : globN s1 "ev" = e0 := by rw [hs1_eq]; exact hs0_gn
    have hs1_ch : s1.locals.lookup (ofString "child") =
        some (.val (.word (BitVec.ofNat 64 child))) := by rw [hs1_eq]; exact hs0_ch
    have hs1_dom : s1.memaddrs = ordinaryDomain := by rw [hs1_eq]; exact hA.1.memaddrs
    rw [evaluateHOLFiniteState_seq_line780] at hrun
    have hr2_eta := Prod.mk.eta (p := evaluateHOLFiniteState s1 p72)
    set r2 := (evaluateHOLFiniteState s1 p72).1
    set s2 := (evaluateHOLFiniteState s1 p72).2
    rw [← hr2_eta] at hrun
    cases hr2 : r2 with
    | some res2 =>
      rw [hr2] at hr2_eta hrun
      have herr2 := R14Shards.OpHandlersA.store_some_eq_error' hr2_eta.symm
      subst herr2
      dsimp only at hrun
      cases (Prod.mk.inj hrun).1
    | none =>
      rw [hr2] at hr2_eta hrun
      dsimp only at hrun
      have ha2 := eval_load_ev_off s1 hs1_ev hs1_ewok he_bnd (off := 72) (by omega) (by omega)
      have hb2 := eval_load_local_off s1 hs1_ch hs1_dom hs1_cwok hchild_bnd
        (off := 72) (by omega) (by omega)
      have hs2_eq := fc_store_add_words hs1_ev (by rw [hs1_gn]; exact he_nat)
        (by rw [hs1_gn]; omega) ha2 hb2 hr2_eta.symm
      have hs2_ewok : WordsOK s2 (e0, 280) := by rw [hs2_eq]; exact wordsOK_updW s1 hs1_ewok _ _
      have hs2_cwok : WordsOK s2 (child, 280) := by rw [hs2_eq]; exact wordsOK_updW s1 hs1_cwok _ _
      have hs2_ev : s2.globals.lookup (ofString "ev") = some (.val (.word (BitVec.ofNat 64 e0))) := by
        rw [hs2_eq]; exact hs1_ev
      have hs2_gn : globN s2 "ev" = e0 := by rw [hs2_eq]; exact hs1_gn
      have hs2_ch : s2.locals.lookup (ofString "child") =
          some (.val (.word (BitVec.ofNat 64 child))) := by rw [hs2_eq]; exact hs1_ch
      have hs2_dom : s2.memaddrs = ordinaryDomain := by rw [hs2_eq]; exact hs1_dom
      rw [evaluateHOLFiniteState_seq_line780] at hrun
      have hr3_eta := Prod.mk.eta (p := evaluateHOLFiniteState s2 p184)
      set r3 := (evaluateHOLFiniteState s2 p184).1
      set s3 := (evaluateHOLFiniteState s2 p184).2
      rw [← hr3_eta] at hrun
      cases hr3 : r3 with
      | some res3 =>
        rw [hr3] at hr3_eta hrun
        have herr3 := R14Shards.OpHandlersA.store_some_eq_error' hr3_eta.symm
        subst herr3
        dsimp only at hrun
        cases (Prod.mk.inj hrun).1
      | none =>
        rw [hr3] at hr3_eta hrun
        dsimp only at hrun
        have ha3 := eval_load_ev_off s2 hs2_ev hs2_ewok he_bnd (off := 184) (by omega) (by omega)
        have hb3 := eval_load_local_off s2 hs2_ch hs2_dom hs2_cwok hchild_bnd
          (off := 184) (by omega) (by omega)
        have hs3_eq := fc_store_add_words hs2_ev (by rw [hs2_gn]; exact he_nat)
          (by rw [hs2_gn]; omega) ha3 hb3 hr3_eta.symm
        rw [evaluateHOLFiniteState_return] at hrun
        dsimp only [evalHOLExact] at hrun
        have hsz0 : sizeOfShapeWithContextHOL s3.structs
            (shapeOfHOLExact (.val (.word (0#64 : BitVec 64)))) ≤ 32 := by
          simp [shapeOfHOLExact]
        rw [if_pos hsz0] at hrun
        have hcpost : s3.emptyLocalsHOLFinite = cpost := (Prod.mk.inj hrun).2
        subst hcpost
        set post := (evaluateHOLFiniteState st
          (.call (some (none, none)) (ofString "incorporate_child_on_error") [childExp])).2
        have hp_mem : post.memory = s3.memory := by rw [hpost_eq]; rfl
        have hp_glob : post.globals = st.globals := by
          rw [hpost_eq]; dsimp only [emptyLocalsHOLFinite]
          rw [hs3_eq, hs2_eq, hs1_eq]; rfl
        have hp_be : post.be = st.be := by
          rw [hpost_eq]; dsimp only [emptyLocalsHOLFinite]
          rw [hs3_eq, hs2_eq, hs1_eq]; rfl
        have hp_code : post.code = st.code := by
          rw [hpost_eq]; dsimp only [emptyLocalsHOLFinite]
          rw [hs3_eq, hs2_eq, hs1_eq]; rfl
        have hp_dom : post.memaddrs = st.memaddrs := by
          rw [hpost_eq]; dsimp only [emptyLocalsHOLFinite]
          rw [hs3_eq, hs2_eq, hs1_eq]; rfl
        have hp_sh : post.shMemaddrs = st.shMemaddrs := by
          rw [hpost_eq]; dsimp only [emptyLocalsHOLFinite]
          rw [hs3_eq, hs2_eq, hs1_eq]; rfl
        have hp_ba : post.baseAddr = st.baseAddr := by
          rw [hpost_eq]; dsimp only [emptyLocalsHOLFinite]
          rw [hs3_eq, hs2_eq, hs1_eq]; rfl
        have hp_loc : post.locals = st.locals := by rw [hpost_eq]
        have hGp : GuestInv post := guestInv_congr hp_code hp_dom hp_sh hp_ba hA.1
        have hmem_3 : ∀ x : BitVec 64,
            x ≠ BitVec.ofNat 64 (e0 + 64) →
            x ≠ BitVec.ofNat 64 (e0 + 72) →
            x ≠ BitVec.ofNat 64 (e0 + 184) →
            post.memory x = st.memory x := by
          intro x hn64 hn72 hn184
          have hs3_m : s3.memory x = s2.memory x := by
            rw [hs3_eq, hs2_gn]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hn184]
          have hs2_m : s2.memory x = s1.memory x := by
            rw [hs2_eq, hs1_gn]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hn72]
          have hs1_m : s1.memory x = s0_c.memory x := by
            rw [hs1_eq, hs0_gn]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hn64]
          rw [hp_mem, hs3_m, hs2_m, hs1_m]; rfl
        have hmem_out : ∀ x : BitVec 64,
            (∀ off ∈ headSimpleOffs, x ≠ BitVec.ofNat 64 (e0 + off)) →
            post.memory x = st.memory x := by
          intro x hx
          exact hmem_3 x (hx 64 (by decide)) (hx 72 (by decide)) (hx 184 (by decide))
        have hm64_post : memW post (e0 + 64) = memW st (e0 + 64) + memW st (child + 64) := by
          have hm3 : memW post (e0 + 64) = memW s3 (e0 + 64) := by unfold memW; rw [hp_mem]
          have hm2 : memW s3 (e0 + 64) = memW s2 (e0 + 64) := by
            rw [hs3_eq, hs2_gn]
            exact R14Shards.OpHandlersA.memW_updW_ne s2 (e0 + 184) (e0 + 64) _
              (by omega) (by omega) (by omega)
          have hm1 : memW s2 (e0 + 64) = memW s1 (e0 + 64) := by
            rw [hs2_eq, hs1_gn]
            exact R14Shards.OpHandlersA.memW_updW_ne s1 (e0 + 72) (e0 + 64) _
              (by omega) (by omega) (by omega)
          have hm0 : memW s1 (e0 + 64) =
              (BitVec.ofNat 64 (memW s0_c (e0 + 64)) + BitVec.ofNat 64 (memW s0_c (child + 64))).toNat := by
            rw [hs1_eq, hs0_gn]
            exact R14Shards.OpHandlersA.memW_updW_same s0_c (e0 + 64) _
          have hs0_m64 : memW s0_c (e0 + 64) = memW st (e0 + 64) := rfl
          have hs0_c64 : memW s0_c (child + 64) = memW st (child + 64) := rfl
          rw [hm3, hm2, hm1, hm0, hs0_m64, hs0_c64]
          have hsum_lt : memW st (e0 + 64) + memW st (child + 64) < 2 ^ 64 := by omega
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (show memW st (e0 + 64) < 2 ^ 64 by omega),
            Nat.mod_eq_of_lt (show memW st (child + 64) < 2 ^ 64 by omega),
            Nat.mod_eq_of_lt hsum_lt]
        have hbv_ne : ∀ (a b : Nat), a < 2 ^ 64 → b < 2 ^ 64 → a ≠ b →
            BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
          intro a b ha hb hne heq
          have := congrArg BitVec.toNat heq
          rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
          exact hne this
        have hm192_post : memW post (e0 + 192) = memW st (e0 + 192) := by
          unfold memW
          rw [hmem_3 _ (hbv_ne _ _ (by omega) (by omega) (by omega))
            (hbv_ne _ _ (by omega) (by omega) (by omega))
            (hbv_ne _ _ (by omega) (by omega) (by omega))]
        have hm16_post : memW post (e0 + 16) = memW st (e0 + 16) := by
          unfold memW
          rw [hmem_3 _ (hbv_ne _ _ (by omega) (by omega) (by omega))
            (hbv_ne _ _ (by omega) (by omega) (by omega))
            (hbv_ne _ _ (by omega) (by omega) (by omega))]
        obtain ⟨hAp, hIp, hRelp, hch_p, hR_p⟩ := head_simple_release_step hA hInv hRel
          hGp hp_glob hp_be hmem_out (by rw [hm16_post]; exact he_sp)
          (by rw [hm64_post, hm192_post]; omega)
        refine ⟨hAp, hIp, hRelp, hp_loc, hp_glob, hp_be, hch_p, ?_, hm64_post, hmem_3⟩
        rw [hR_p, hm64_post, hm192_post, hR_st]
        omega

theorem fcPoppedChild_child_cells_of_head_simple {F : Type}
    {s0 s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hBS : FcBranchState s0 s S)
    (hPC : FcPoppedChild s0 s S)
    (hmem_out : ∀ x : BitVec 64,
      (∀ off ∈ headSimpleOffs, x ≠ BitVec.ofNat 64 (globN s "ev" + off)) →
      post.memory x = s.memory x) :
    ∀ off : Nat, off + 8 ≤ 280 →
      memW post (globN s0 "ev" + off) = memW s (globN s0 "ev" + off) := by
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    rw [evmChain_cons]; exact List.mem_cons_self
  have hfo : (globN s "ev", 280) ∈ frameObjects s (globN s "ev", globN s "cur_cont") := by
    simp [frameObjects]
  have hdisj := hPC.child_disj_fo _ hhead _ hfo
  have hhead_bnd := (ev_head_facts hBS.arena hBS.inv).1
  have hchild_bnd :=
    (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hBS.arena.2
      (Or.inr hPC.child_scr.1)).2
  dsimp only at hchild_bnd
  intro k hk
  unfold memW
  rw [hmem_out]
  intro off hoff
  have hoff_bnd : off + 8 ≤ 280 := by
    revert off hoff; decide
  intro heq
  have hnat := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hnat
  dsimp [Disj] at hdisj
  omega

theorem incorporate_child_on_error_fc_step {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hBS : FcBranchState s0 st S)
    (hchild_wok : WordsOK st (globN s0 "ev", 280))
    (hchild_bnd : globN s0 "ev" + 280 ≤ 2 ^ 64)
    (hchild_dfo : ∀ ec ∈ evmChain st, ∀ o ∈ frameObjects st ec,
      Disj (globN s0 "ev", 280) o)
    (hr_sum : OpDispatchSpec.evmR st + memW st (globN s0 "ev" + 64) ≤ OpDispatchSpec.evmR s0)
    (hgas_sum : OpDispatchSpec.evmR st + memW st (globN s0 "ev" + 64) + 1 < 2 ^ 64)
    (hnt : (evaluateHOLFiniteState st
      (.call (some (none, none)) (ofString "incorporate_child_on_error")
        [.var .local (ofString "child")])).1 ≠ some .timeOut) :
    let prog : ProgHOL 64 := .call (some (none, none)) (ofString "incorporate_child_on_error")
      [.var .local (ofString "child")]
    (∀ u, (evaluateHOLFiniteState st prog).1 ≠ some (.returned u)) ∧
    ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState st prog).1 ∧
    ((evaluateHOLFiniteState st prog).1 = none →
      let post := (evaluateHOLFiniteState st prog).2
      FcBranchState s0 post S ∧ post.locals = st.locals ∧ post.globals = st.globals ∧
      evmChain post = evmChain st ∧
      OpDispatchSpec.evmR post = OpDispatchSpec.evmR st + memW st (globN s0 "ev" + 64) ∧
      (∀ off : Nat, off + 8 ≤ 280 →
        memW post (globN s0 "ev" + off) = memW st (globN s0 "ev" + off)) ∧
      memW post (globN post "ev" + 16) = memW st (globN st "ev" + 16) ∧
      memW post (globN post "ev" + 40) = memW st (globN st "ev" + 40) ∧
      memW post (globN post "ev" + 232) = memW st (globN st "ev" + 232)) := by
  dsimp only
  have harg : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
      [.var .local (ofString "child")] =
      some [.val (.word (BitVec.ofNat 64 (globN s0 "ev")))] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact, evalHOLExact, hBS.locals_ok.child_lk]
  obtain ⟨hnret, hnerr, hnone⟩ := incorporate_child_on_error_call_core
    hBS.arena hBS.inv hBS.release harg hchild_wok hchild_bnd hgas_sum hnt
  refine ⟨hnret, hnerr, fun hn => ?_⟩
  obtain ⟨hAp, hIp, hRelp, hloc, hglob, hbe, hch, hR, hm64, hmem⟩ := hnone hn
  set post := (evaluateHOLFiniteState st
    (.call (some (none, none)) (ofString "incorporate_child_on_error")
      [.var .local (ofString "child")])).2
  obtain ⟨hbnd, hwok, hlk, hsp, hRs⟩ := ev_head_facts hBS.arena hBS.inv
  have hout : ∀ x : BitVec 64,
      (∀ off ∈ headSimpleOffs, x ≠ BitVec.ofNat 64 (globN st "ev" + off)) →
      post.memory x = st.memory x := by
    intro x hx
    exact hmem x (hx 64 (by decide)) (hx 72 (by decide)) (hx 184 (by decide))
  have hcell : ∀ off : Nat, off + 8 ≤ 280 → off ≠ 64 → off ≠ 72 → off ≠ 184 →
      memW post (globN st "ev" + off) = memW st (globN st "ev" + off) := by
    intro off hoff hn64 hn72 hn184
    unfold memW
    rw [hmem]
    all_goals intro heq
    all_goals have he := congrArg BitVec.toNat heq
    all_goals simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show globN st "ev" + off < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show globN st "ev" + 64 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show globN st "ev" + 72 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show globN st "ev" + 184 < 2 ^ 64 by omega)] at he
    all_goals omega
  have hBSp : FcBranchState s0 post S := fcBranchState_of_head_simple hBS hAp.1
    hglob hbe hloc hout (by rw [hcell 16 (by omega) (by omega) (by omega) (by omega)]; exact hsp)
    (by rw [hm64, hcell 192 (by omega) (by omega) (by omega) (by omega)]; omega)
    (by rw [hm64, hcell 192 (by omega) (by omega) (by omega) (by omega)]; omega)
  have hchild : ∀ off : Nat, off + 8 ≤ 280 →
      memW post (globN s0 "ev" + off) = memW st (globN s0 "ev" + off) := by
    have hhead : (globN st "ev", globN st "cur_cont") ∈ evmChain st := by
      rw [evmChain_cons]; exact List.mem_cons_self
    have hfo : (globN st "ev", 280) ∈ frameObjects st (globN st "ev", globN st "cur_cont") := by
      simp [frameObjects]
    have hd := hchild_dfo _ hhead _ hfo
    dsimp only [Disj] at hd
    intro off hoff
    unfold memW
    rw [hmem]
    all_goals intro heq
    all_goals have he := congrArg BitVec.toNat heq
    all_goals simp only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show globN s0 "ev" + off < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show globN st "ev" + 64 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show globN st "ev" + 72 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show globN st "ev" + 184 < 2 ^ 64 by omega)] at he
    all_goals omega
  have hev : globN post "ev" = globN st "ev" := by unfold globN; rw [hglob]
  refine ⟨hBSp, hloc, hglob, hch, hR, hchild, ?_, ?_, ?_⟩
  all_goals rw [hev]
  · exact hcell 16 (by omega) (by omega) (by omega) (by omega)
  · exact hcell 40 (by omega) (by omega) (by omega) (by omega)
  · exact hcell 232 (by omega) (by omega) (by omega) (by omega)

theorem eval_min_body_exact {F : Type} (s : PanSemStateFiniteExact 64 F) {aw bw : BitVec 64}
    (ha : s.locals.lookup (ofString "a") = some (.val (.word aw)))
    (hb : s.locals.lookup (ofString "b") = some (.val (.word bw))) :
    evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_min) =
      (some (.returned (.val (.word (if aw < bw then aw else bw)))),
        s.emptyLocalsHOLFinite) := by
  have hbody : sourceFnBody Guest.Software.guestFn_min =
      .seq
        (.ite (.cmp .lower (.var .local (ofString "a")) (.var .local (ofString "b")))
          (.return (.var .local (ofString "a")))
          .skip)
        (.return (.var .local (ofString "b"))) := rfl
  rw [hbody, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  have hcmp : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.cmp .lower (.var .local (ofString "a")) (.var .local (ofString "b"))) =
      some (.val (.word (if aw < bw then 1 else 0))) := by
    simp [evalHOLExact, ha, hb, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp]; dsimp only
  by_cases hlt : aw < bw
  · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    simp only [hlt, ↓reduceIte, h10]
    rw [evaluateHOLFiniteState_return]
    have heva : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
        (.var .local (ofString "a")) = some (.val (.word aw)) := ha
    rw [heva]; dsimp only
    have hsz : sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact (.val (.word aw) : ValueHOL 64)) ≤ 32 := by
      simp [shapeOfHOLExact]
    rw [if_pos hsz]
  · simp only [hlt, ↓reduceIte, evaluateHOLFiniteState_skip]
    rw [evaluateHOLFiniteState_return]
    have hevb : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
        (.var .local (ofString "b")) = some (.val (.word bw)) := hb
    rw [hevb]; dsimp only
    have hsz : sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact (.val (.word bw) : ValueHOL 64)) ≤ 32 := by
      simp [shapeOfHOLExact]
    rw [if_pos hsz]

private theorem fc_eval_sub_words {F : Type} (s : PanSemStateFiniteExact 64 F)
    {a b : ExpHOL 64} {aw bw : BitVec 64}
    (ha : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) a =
      some (.val (.word aw)))
    (hb : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) b =
      some (.val (.word bw))) :
    @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.op .sub [a, b]) = some (.val (.word (aw - bw))) := by
  simp [evalHOLExact, evalListHOLExact, ha, hb, wordOpHOL, wordOp,
    valueIsWord, valueWord]

private theorem fc_store_sub_words {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {off : Nat} {ew aw bw : BitVec 64} {a b : ExpHOL 64}
    (he : s.globals.lookup (ofString "ev") = some (.val (.word ew)))
    (hen : ew.toNat = globN s "ev")
    (hbound : globN s "ev" + off < 2 ^ 64)
    (ha : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) a =
      some (.val (.word aw)))
    (hb : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) b =
      some (.val (.word bw)))
    (hrun : evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)])
        (.op .sub [a, b])) = (none, post)) :
    post = { s with
      memory := R14Shards.OpHandlersA.updW s.memory
        (BitVec.ofNat 64 (globN s "ev" + off)) (aw - bw) } := by
  have hv := fc_eval_sub_words s ha hb
  obtain ⟨w, hw, hp⟩ := R14Shards.OpHandlersA.store_global_off_word
    he hen hbound (fun v h => by rw [hv] at h; exact ⟨aw - bw, (Option.some.inj h).symm⟩) hrun
  rw [hv] at hw
  have hw' : w = aw - bw := by simpa using hw.symm
  simpa only [hw'] using hp

private theorem minOnlyCallees_good :
    ∀ function, (function == ofString "min") = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      StateRestoreEpilogue.noCatchableRaise (fun f => f == ofString "min") body = true := by
  intro function hfn values body callee rs hfound
  have heq : function = ofString "min" := by simpa only [beq_iff_eq] using hfn
  subst function
  obtain ⟨params, rs', hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
  rw [OpHandlersB.lookup_min_b] at hinst
  have hbody := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
  rw [← hbody]
  decide

theorem credit_state_gas_refund_fc_step {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F} {S : List Nat} {amtw : BitVec 64}
    (hBS : FcBranchState s0 st S)
    (hnt : (evaluateHOLFiniteState st
      (.call (some (none, none)) (ofString "credit_state_gas_refund")
        [.const amtw])).1 ≠ some .timeOut) :
    let prog : ProgHOL 64 := .call (some (none, none)) (ofString "credit_state_gas_refund")
      [.const amtw]
    (∀ u, (evaluateHOLFiniteState st prog).1 ≠ some (.returned u)) ∧
    ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState st prog).1 ∧
    ((evaluateHOLFiniteState st prog).1 = none →
      let post := (evaluateHOLFiniteState st prog).2
      FcBranchState s0 post S ∧ post.locals = st.locals ∧ post.globals = st.globals ∧
      post.be = st.be ∧ evmChain post = evmChain st ∧
      OpDispatchSpec.evmR post = OpDispatchSpec.evmR st ∧
      (∀ x : BitVec 64,
        x ≠ BitVec.ofNat 64 (globN st "ev" + 64) →
        x ≠ BitVec.ofNat 64 (globN st "ev" + 72) →
        x ≠ BitVec.ofNat 64 (globN st "ev" + 192) →
        post.memory x = st.memory x) ∧
      memW post (globN post "ev" + 16) = memW st (globN st "ev" + 16) ∧
      memW post (globN post "ev" + 40) = memW st (globN st "ev" + 40) ∧
      memW post (globN post "ev" + 232) = memW st (globN st "ev" + 232)) := by
  dsimp only
  obtain ⟨hne_ret, hnone, herr⟩ := call0_outcome_fc (s := st)
    (fname := ofString "credit_state_gas_refund") (args := [.const amtw]) hnt
  have hcode : st.code = originalRuntimeCode := hBS.arena.1.code
  have harg : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
      [.const amtw] = some [.val (.word amtw)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact, evalHOLExact]
  have hno_err : ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState st
      (.call (some (none, none)) (ofString "credit_state_gas_refund") [.const amtw])).1 := by
    intro he
    obtain ⟨vals, body, cal, ret, v, cpost, hargs, hl, hrun, _⟩ := herr he
    rw [harg] at hargs; injection hargs with hvals; subst hvals
    have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup
        (ofString "credit_state_gas_refund") [.val (.word amtw)] = some (body, cal, ret) := by
      rwa [← hcode]
    obtain ⟨rfl, _, _, _, _⟩ :=
      R14Shards.OpHandlersA.one_word_arg_lookup OpHandlersB.lookup_credit_state_gas_refund_b hl_orig
    have hncr := StateRestoreEpilogue.evaluate_noCatchableRaise (fun f => f == ofString "min")
      minOnlyCallees_good
      (sourceFnBody Guest.Software.guestFn_credit_state_gas_refund) (by decide)
      (callEntryStateHOLFinite st cal) hcode
    exact hncr (ofString "EvmErr") v (by decide) (by rw [hrun])
  refine ⟨hne_ret, hno_err, fun hn => ?_⟩
  obtain ⟨vals, body, cal, ret, rv, cpost, hargs, hl, hrun, hpost_eq⟩ := hnone hn
  rw [harg] at hargs; injection hargs with hvals; subst hvals
  have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "credit_state_gas_refund") [.val (.word amtw)] = some (body, cal, ret) := by
    rwa [← hcode]
  obtain ⟨rfl, _, w0, hw0, hcal_amt⟩ :=
    R14Shards.OpHandlersA.one_word_arg_lookup OpHandlersB.lookup_credit_state_gas_refund_b hl_orig
  injection hw0 with hw0'; injection hw0' with hw0_eq; subst hw0_eq
  obtain ⟨he_bnd, he_wok, he_lk, he_sp, hR_st⟩ := ev_head_facts hBS.arena hBS.inv
  have hR_lt : OpDispatchSpec.evmR st + 1 < 2 ^ 64 := hBS.inv.2.2.2.2.2.2.2.2.2.2.2.2
  set e0 := globN st "ev"
  set s0_c := callEntryStateHOLFinite st cal
  have he_nat : (BitVec.ofNat 64 e0).toNat = e0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hs0_ev : s0_c.globals.lookup (ofString "ev") = some (.val (.word (BitVec.ofNat 64 e0))) := he_lk
  have hs0_gn : globN s0_c "ev" = e0 := rfl
  have hs0_ewok : WordsOK s0_c (e0, 280) := he_wok
  have hs0_amt : s0_c.locals.lookup (ofString "amount") = some (.val (.word amtw)) := hcal_amt
  let p64 : ProgHOL 64 := .store
    (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 64)])
    (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 64)]),
               .var .local (ofString "from_gl")])
  let p192 : ProgHOL 64 := .store
    (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 192)])
    (.op .sub [.var .local (ofString "spilled"), .var .local (ofString "from_gl")])
  let p72 : ProgHOL 64 := .store
    (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 72)])
    (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 72)]),
               .op .sub [.var .local (ofString "amount"), .var .local (ofString "from_gl")]])
  have hbody_eq : sourceFnBody Guest.Software.guestFn_credit_state_gas_refund =
      .dec (ofString "spilled") .one
        (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 192)]))
        (.decCall (ofString "from_gl") .one (ofString "min")
          [.var .local (ofString "amount"), .var .local (ofString "spilled")]
          (.seq p64 (.seq p192 (.seq p72 (.return (.const 0#64)))))) := rfl
  change evaluateHOLFiniteState s0_c
    (sourceFnBody Guest.Software.guestFn_credit_state_gas_refund) =
    (some (.returned rv), cpost) at hrun
  rw [hbody_eq, evaluateHOLFiniteState_dec_total] at hrun
  dsimp only at hrun
  have hld_sp := eval_load_ev_off s0_c hs0_ev hs0_ewok he_bnd (off := 192) (by omega) (by omega)
  have hs0_m192 : memW s0_c (e0 + 192) = memW st (e0 + 192) := rfl
  rw [hld_sp, hs0_m192] at hrun
  dsimp only at hrun
  set spw := BitVec.ofNat 64 (memW st (e0 + 192))
  have hspw_nat : spw.toNat = memW st (e0 + 192) := by
    dsimp only [spw]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsh_sp : shapeEqHOL .one (shapeOfHOLExact (.val (.word spw) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh_sp] at hrun
  set s1 := setVarHOLFinite (ofString "spilled") (.val (.word spw)) s0_c
  have hs1_sp : s1.locals.lookup (ofString "spilled") = some (.val (.word spw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_amt : s1.locals.lookup (ofString "amount") = some (.val (.word amtw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs0_amt,
      show ofString "spilled" ≠ ofString "amount" by decide]
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
  have hargs_min : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
      [.var .local (ofString "amount"), .var .local (ofString "spilled")] =
      some [.val (.word amtw), .val (.word spw)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact, evalHOLExact, hs1_amt, hs1_sp]
  rw [hargs_min] at hrun; dsimp only at hrun
  have hs1_code : s1.code = originalRuntimeCode := hcode
  rcases hl_min : lookupCodeHOLFinite s1.code.lookup (ofString "min")
      [.val (.word amtw), .val (.word spw)] with _ | ⟨body_min, cal_min, ret_min⟩
  · rw [hl_min] at hrun; cases (Prod.mk.inj hrun).1
  · rw [hl_min] at hrun; dsimp only at hrun
    by_cases hclk0 : s1.clock = 0
    · simp [hclk0] at hrun
    · simp only [hclk0, ↓reduceIte] at hrun
      have hl_min_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "min")
          [.val (.word amtw), .val (.word spw)] = some (body_min, cal_min, ret_min) := by
        rwa [← hs1_code]
      obtain ⟨rfl, rfl, w_a, w_b, hvals_eq, hcal_a, hcal_b⟩ :=
        R14Shards.OpHandlersA.two_word_arg_lookup (by decide) OpHandlersB.lookup_min_b hl_min_orig
      injection hvals_eq with hv1 hrest_v
      injection hv1 with hv1'; injection hv1' with hw_a; subst hw_a
      injection hrest_v with hv2 _
      injection hv2 with hv2'; injection hv2' with hw_b; subst hw_b
      have hmin_run := eval_min_body_exact (callEntryStateHOLFinite s1 cal_min) hcal_a hcal_b
      rw [hmin_run] at hrun
      set fgw : BitVec 64 := if amtw < spw then amtw else spw
      have hfg_le_sp : fgw.toNat ≤ memW st (e0 + 192) := by
        dsimp only [fgw]
        by_cases hlt : amtw < spw
        · simp only [hlt, ↓reduceIte]
          rw [BitVec.lt_def, hspw_nat] at hlt; omega
        · simp only [hlt, ↓reduceIte, hspw_nat]; exact le_rfl
      have hsh_ok : (shapeEqHOL (shapeOfHOLExact (.val (.word fgw) : ValueHOL 64)) .one &&
          shapeEqHOL (shapeOfHOLExact (.val (.word fgw) : ValueHOL 64)) .one) = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      dsimp only at hrun
      simp only [hsh_ok, ↓reduceIte] at hrun
      set st_min := (callEntryStateHOLFinite s1 cal_min).emptyLocalsHOLFinite
      set s2 := setVarHOLFinite (ofString "from_gl") (.val (.word fgw))
        { st_min with locals := s1.locals }
      have hs2_ev : s2.globals.lookup (ofString "ev") = some (.val (.word (BitVec.ofNat 64 e0))) := hs0_ev
      have hs2_gn : globN s2 "ev" = e0 := rfl
      have hs2_ewok : WordsOK s2 (e0, 280) := hs0_ewok
      have hs2_fg : s2.locals.lookup (ofString "from_gl") = some (.val (.word fgw)) := by
        simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hs2_sp : s2.locals.lookup (ofString "spilled") = some (.val (.word spw)) := by
        simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_sp,
          show ofString "from_gl" ≠ ofString "spilled" by decide]
      have hs2_amt : s2.locals.lookup (ofString "amount") = some (.val (.word amtw)) := by
        simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_amt,
          show ofString "from_gl" ≠ ofString "amount" by decide]
      let kseq : ProgHOL 64 := .seq p64 (.seq p192 (.seq p72 (.return (.const 0#64))))
      have hk_eta := Prod.mk.eta (p := evaluateHOLFiniteState s2 kseq)
      set rk := (evaluateHOLFiniteState s2 kseq).1
      set sk := (evaluateHOLFiniteState s2 kseq).2
      change (rk, { sk with locals := _ }) = (some (.returned rv), cpost) at hrun
      have hrk_eq : rk = some (.returned rv) := (Prod.mk.inj hrun).1
      have hcpost_eq : { sk with
          locals := (sk.locals.resVarEq (ofString "from_gl", s1.locals.lookup (ofString "from_gl"))).resVarEq
            (ofString "spilled", s0_c.locals.lookup (ofString "spilled")) } = cpost :=
        (Prod.mk.inj hrun).2
      have hk_full : evaluateHOLFiniteState s2 kseq = (some (.returned rv), sk) := by
        rw [← hk_eta, hrk_eq]
      dsimp only [kseq] at hk_full
      rw [evaluateHOLFiniteState_seq_line780] at hk_full
      have hr3_eta := Prod.mk.eta (p := evaluateHOLFiniteState s2 p64)
      set r3 := (evaluateHOLFiniteState s2 p64).1
      set s3 := (evaluateHOLFiniteState s2 p64).2
      rw [← hr3_eta] at hk_full
      cases hr3 : r3 with
      | some res3 =>
        rw [hr3] at hr3_eta hk_full
        have herr3 := R14Shards.OpHandlersA.store_some_eq_error' hr3_eta.symm
        subst herr3
        dsimp only at hk_full
        cases (Prod.mk.inj hk_full).1
      | none =>
        rw [hr3] at hr3_eta hk_full
        dsimp only at hk_full
        have ha3 := eval_load_ev_off s2 hs2_ev hs2_ewok he_bnd (off := 64) (by omega) (by omega)
        have hb3 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
            (.var .local (ofString "from_gl")) = some (.val (.word fgw)) := hs2_fg
        have hs3_eq := fc_store_add_words hs2_ev (by rw [hs2_gn]; exact he_nat)
          (by rw [hs2_gn]; omega) ha3 hb3 hr3_eta.symm
        have hs3_ewok : WordsOK s3 (e0, 280) := by rw [hs3_eq]; exact wordsOK_updW s2 hs2_ewok _ _
        have hs3_ev : s3.globals.lookup (ofString "ev") = some (.val (.word (BitVec.ofNat 64 e0))) := by
          rw [hs3_eq]; exact hs2_ev
        have hs3_gn : globN s3 "ev" = e0 := by rw [hs3_eq]; exact hs2_gn
        have hs3_fg : s3.locals.lookup (ofString "from_gl") = some (.val (.word fgw)) := by
          rw [hs3_eq]; exact hs2_fg
        have hs3_sp : s3.locals.lookup (ofString "spilled") = some (.val (.word spw)) := by
          rw [hs3_eq]; exact hs2_sp
        have hs3_amt : s3.locals.lookup (ofString "amount") = some (.val (.word amtw)) := by
          rw [hs3_eq]; exact hs2_amt
        rw [evaluateHOLFiniteState_seq_line780] at hk_full
        have hr4_eta := Prod.mk.eta (p := evaluateHOLFiniteState s3 p192)
        set r4 := (evaluateHOLFiniteState s3 p192).1
        set s4 := (evaluateHOLFiniteState s3 p192).2
        rw [← hr4_eta] at hk_full
        cases hr4 : r4 with
        | some res4 =>
          rw [hr4] at hr4_eta hk_full
          have herr4 := R14Shards.OpHandlersA.store_some_eq_error' hr4_eta.symm
          subst herr4
          dsimp only at hk_full
          cases (Prod.mk.inj hk_full).1
        | none =>
          rw [hr4] at hr4_eta hk_full
          dsimp only at hk_full
          have ha4 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
              (.var .local (ofString "spilled")) = some (.val (.word spw)) := hs3_sp
          have hb4 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
              (.var .local (ofString "from_gl")) = some (.val (.word fgw)) := hs3_fg
          have hs4_eq := fc_store_sub_words hs3_ev (by rw [hs3_gn]; exact he_nat)
            (by rw [hs3_gn]; omega) ha4 hb4 hr4_eta.symm
          have hs4_ewok : WordsOK s4 (e0, 280) := by rw [hs4_eq]; exact wordsOK_updW s3 hs3_ewok _ _
          have hs4_ev : s4.globals.lookup (ofString "ev") = some (.val (.word (BitVec.ofNat 64 e0))) := by
            rw [hs4_eq]; exact hs3_ev
          have hs4_gn : globN s4 "ev" = e0 := by rw [hs4_eq]; exact hs3_gn
          have hs4_fg : s4.locals.lookup (ofString "from_gl") = some (.val (.word fgw)) := by
            rw [hs4_eq]; exact hs3_fg
          have hs4_amt : s4.locals.lookup (ofString "amount") = some (.val (.word amtw)) := by
            rw [hs4_eq]; exact hs3_amt
          rw [evaluateHOLFiniteState_seq_line780] at hk_full
          have hr5_eta := Prod.mk.eta (p := evaluateHOLFiniteState s4 p72)
          set r5 := (evaluateHOLFiniteState s4 p72).1
          set s5 := (evaluateHOLFiniteState s4 p72).2
          rw [← hr5_eta] at hk_full
          cases hr5 : r5 with
          | some res5 =>
            rw [hr5] at hr5_eta hk_full
            have herr5 := R14Shards.OpHandlersA.store_some_eq_error' hr5_eta.symm
            subst herr5
            dsimp only at hk_full
            cases (Prod.mk.inj hk_full).1
          | none =>
            rw [hr5] at hr5_eta hk_full
            dsimp only at hk_full
            have ha5 := eval_load_ev_off s4 hs4_ev hs4_ewok he_bnd (off := 72) (by omega) (by omega)
            have hb5 := fc_eval_sub_words s4
              (show @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
                  (.var .local (ofString "amount")) = some (.val (.word amtw)) from hs4_amt)
              (show @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
                  (.var .local (ofString "from_gl")) = some (.val (.word fgw)) from hs4_fg)
            have hs5_eq := fc_store_add_words hs4_ev (by rw [hs4_gn]; exact he_nat)
              (by rw [hs4_gn]; omega) ha5 hb5 hr5_eta.symm
            rw [evaluateHOLFiniteState_return] at hk_full
            dsimp only [evalHOLExact] at hk_full
            have hsz0 : sizeOfShapeWithContextHOL s5.structs
                (shapeOfHOLExact (.val (.word (0#64 : BitVec 64)))) ≤ 32 := by
              simp [shapeOfHOLExact]
            rw [if_pos hsz0] at hk_full
            have hsk : sk = s5.emptyLocalsHOLFinite := (Prod.mk.inj hk_full).2.symm
            subst hcpost_eq
            set post := (evaluateHOLFiniteState st
              (.call (some (none, none)) (ofString "credit_state_gas_refund") [.const amtw])).2
            have hp_mem : post.memory = s5.memory := by rw [hpost_eq, hsk]; rfl
            have hp_glob : post.globals = st.globals := by
              rw [hpost_eq, hsk]; dsimp only [emptyLocalsHOLFinite]
              rw [hs5_eq, hs4_eq, hs3_eq]; rfl
            have hp_be : post.be = st.be := by
              rw [hpost_eq, hsk]; dsimp only [emptyLocalsHOLFinite]
              rw [hs5_eq, hs4_eq, hs3_eq]; rfl
            have hp_code : post.code = st.code := by
              rw [hpost_eq, hsk]; dsimp only [emptyLocalsHOLFinite]
              rw [hs5_eq, hs4_eq, hs3_eq]; rfl
            have hp_dom : post.memaddrs = st.memaddrs := by
              rw [hpost_eq, hsk]; dsimp only [emptyLocalsHOLFinite]
              rw [hs5_eq, hs4_eq, hs3_eq]; rfl
            have hp_sh : post.shMemaddrs = st.shMemaddrs := by
              rw [hpost_eq, hsk]; dsimp only [emptyLocalsHOLFinite]
              rw [hs5_eq, hs4_eq, hs3_eq]; rfl
            have hp_ba : post.baseAddr = st.baseAddr := by
              rw [hpost_eq, hsk]; dsimp only [emptyLocalsHOLFinite]
              rw [hs5_eq, hs4_eq, hs3_eq]; rfl
            have hp_loc : post.locals = st.locals := by rw [hpost_eq]
            have hGp : GuestInv post := guestInv_congr hp_code hp_dom hp_sh hp_ba hBS.arena.1
            have hmem_3 : ∀ x : BitVec 64,
                x ≠ BitVec.ofNat 64 (e0 + 64) →
                x ≠ BitVec.ofNat 64 (e0 + 72) →
                x ≠ BitVec.ofNat 64 (e0 + 192) →
                post.memory x = st.memory x := by
              intro x hn64 hn72 hn192
              have hs5_m : s5.memory x = s4.memory x := by
                rw [hs5_eq, hs4_gn]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hn72]
              have hs4_m : s4.memory x = s3.memory x := by
                rw [hs4_eq, hs3_gn]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hn192]
              have hs3_m : s3.memory x = s2.memory x := by
                rw [hs3_eq, hs2_gn]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hn64]
              rw [hp_mem, hs5_m, hs4_m, hs3_m]; rfl
            have hmem_out : ∀ x : BitVec 64,
                (∀ off ∈ headSimpleOffs, x ≠ BitVec.ofNat 64 (e0 + off)) →
                post.memory x = st.memory x := by
              intro x hx
              exact hmem_3 x (hx 64 (by decide)) (hx 72 (by decide)) (hx 192 (by decide))
            have hm64_post : memW post (e0 + 64) = memW st (e0 + 64) + fgw.toNat := by
              have hm5 : memW post (e0 + 64) = memW s5 (e0 + 64) := by unfold memW; rw [hp_mem]
              have hm4 : memW s5 (e0 + 64) = memW s4 (e0 + 64) := by
                rw [hs5_eq, hs4_gn]
                exact R14Shards.OpHandlersA.memW_updW_ne s4 (e0 + 72) (e0 + 64) _
                  (by omega) (by omega) (by omega)
              have hm3 : memW s4 (e0 + 64) = memW s3 (e0 + 64) := by
                rw [hs4_eq, hs3_gn]
                exact R14Shards.OpHandlersA.memW_updW_ne s3 (e0 + 192) (e0 + 64) _
                  (by omega) (by omega) (by omega)
              have hm2 : memW s3 (e0 + 64) =
                  (BitVec.ofNat 64 (memW s2 (e0 + 64)) + fgw).toNat := by
                rw [hs3_eq, hs2_gn]
                exact R14Shards.OpHandlersA.memW_updW_same s2 (e0 + 64) _
              have hs2_m64 : memW s2 (e0 + 64) = memW st (e0 + 64) := rfl
              rw [hm5, hm4, hm3, hm2, hs2_m64]
              have hsum_lt : memW st (e0 + 64) + fgw.toNat < 2 ^ 64 := by omega
              simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (show memW st (e0 + 64) < 2 ^ 64 by omega),
                Nat.mod_eq_of_lt hsum_lt]
            have hm192_post : memW post (e0 + 192) = memW st (e0 + 192) - fgw.toNat := by
              have hm5 : memW post (e0 + 192) = memW s5 (e0 + 192) := by unfold memW; rw [hp_mem]
              have hm4 : memW s5 (e0 + 192) = (spw - fgw).toNat := by
                rw [hs5_eq, hs4_gn, R14Shards.OpHandlersA.memW_updW_ne s4 (e0 + 72) (e0 + 192) _
                  (by omega) (by omega) (by omega),
                  hs4_eq, hs3_gn, R14Shards.OpHandlersA.memW_updW_same s3 (e0 + 192) _]
              rw [hm5, hm4, BitVec.toNat_sub_of_le (BitVec.le_def.2 (by rw [hspw_nat]; exact hfg_le_sp)),
                hspw_nat]
            have hcell : ∀ off : Nat, off + 8 ≤ 280 → off ≠ 64 → off ≠ 72 → off ≠ 192 →
                memW post (e0 + off) = memW st (e0 + off) := by
              intro off hoff hn64 hn72 hn192
              unfold memW
              rw [hmem_3]
              all_goals intro heq
              all_goals have he := congrArg BitVec.toNat heq
              all_goals simp only [BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (show e0 + off < 2 ^ 64 by omega),
                Nat.mod_eq_of_lt (show e0 + 64 < 2 ^ 64 by omega),
                Nat.mod_eq_of_lt (show e0 + 72 < 2 ^ 64 by omega),
                Nat.mod_eq_of_lt (show e0 + 192 < 2 ^ 64 by omega)] at he
              all_goals omega
            have hsum_eq : memW post (e0 + 64) + memW post (e0 + 192) =
                memW st (e0 + 64) + memW st (e0 + 192) := by
              rw [hm64_post, hm192_post]; omega
            have hBSp : FcBranchState s0 post S := fcBranchState_of_head_simple hBS hGp
              hp_glob hp_be hp_loc hmem_out
              (by change memW post (e0 + 16) ≤ _; rw [hcell 16 (by omega) (by omega) (by omega) (by omega)]; exact he_sp)
              (by change memW post (e0 + 64) + memW post (e0 + 192) + _ + 1 < _; omega)
              (by change memW post (e0 + 64) + memW post (e0 + 192) + _ ≤ _; have := hBS.r_le; omega)
            obtain ⟨_, _, _, hch_p, hR_p⟩ := head_simple_release_step hBS.arena hBS.inv hBS.release
              hGp hp_glob hp_be hmem_out
              (by change memW post (e0 + 16) ≤ _; rw [hcell 16 (by omega) (by omega) (by omega) (by omega)]; exact he_sp)
              (by change memW post (e0 + 64) + memW post (e0 + 192) + _ + 1 < _; omega)
            have hev : globN post "ev" = e0 := by
              change globN post "ev" = globN st "ev"
              unfold globN; rw [hp_glob]
            refine ⟨hBSp, hp_loc, hp_glob, hp_be, hch_p, ?_, hmem_3, ?_, ?_, ?_⟩
            · have hR_p' : OpDispatchSpec.evmR post = memW post (e0 + 64) + memW post (e0 + 192) +
                  (((evmChain st).tail.map fun ec => memW st (ec.1 + 64) + memW st (ec.1 + 192)).sum) := hR_p
              rw [hR_p', hR_st]; omega
            · rw [hev]; exact hcell 16 (by omega) (by omega) (by omega) (by omega)
            · rw [hev]; exact hcell 40 (by omega) (by omega) (by omega) (by omega)
            · rw [hev]; exact hcell 232 (by omega) (by omega) (by omega) (by omega)

theorem htab_union_into_exitR_spec :
    FunSpec UnionArgWF (OnReturn (fun s0 post => HtabUnionInto.ExitR (locN s0 "dst") s0 post))
      (ofString "htab_union_into") := by
  refine ⟨_, _, _, HtabUnionInto.lookup_htab_union_into, ?_⟩
  intro F s0 hcode hP _ _ v hv
  have hb : sourceFnBody Guest.Software.guestFn_htab_union_into =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_htab_union_into).body := rfl
  suffices key : Wave8M19.Htab.Ret s0 (sourceFnBody Guest.Software.guestFn_htab_union_into)
      (fun _ post => HtabUnionInto.ExitR (locN s0 "dst") s0 post) from key v hv
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_htab_union_into,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  apply Wave8M19.Htab.Ret.dec
  intro capv _
  set s1 := setVarHOLFinite (ofString "cap") capv s0 with hs1
  apply Wave8M19.Htab.Ret.dec
  intro iv _
  set s2 := setVarHOLFinite (ofString "i") iv s1 with hs2
  have hI2 : HtabUnionInto.UInv s0 s2 := by
    refine ⟨hcode, ?_, ?_, ?_⟩
    · simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "i" ≠ ofString "dst" by decide, show ofString "cap" ≠ ofString "dst" by decide]
    · exact LocalsOnly.setVar HtabUnionInto.localsOnly_unionArgWF
        (by simp only [List.mem_singleton]; rintro _ rfl; decide) iv s1
        (LocalsOnly.setVar HtabUnionInto.localsOnly_unionArgWF
          (by simp only [List.mem_singleton]; rintro _ rfl; decide) capv s0 hP)
    · have h0 : HtabUnionInto.ExitR (locN s0 "dst") s0 s0 :=
        HtabUnionInto.ExitR.refl _ s0 hP.1 hP.2.1 hP.2.2
      have h2 : HtabUnionInto.ExitR (locN s0 "dst")
          { s0 with locals := s0.locals, clock := s0.clock }
          { s0 with locals := s2.locals, clock := s0.clock } := by
        rw [HtabUnionInto.exitR_locals]; exact h0
      exact h2
  apply Wave8M19.Htab.Ret.seq
  · intro w hw
    exfalso
    have hnr : Wave8M19.Htab.NoRet
        (.decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item")
          [.var .local (ofString "src"), .var .local (ofString "i")]
          (.seq
            (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0))
              (.call (some (none, none)) (ofString "htab_set")
                [.var .local (ofString "dst"),
                 .rfield 1 (.var .local (ofString "s")),
                 .rfield 2 (.var .local (ofString "s"))])
              .skip)
            (.assign .local (ofString "i")
              (.op .add [.var .local (ofString "i"), .const 1])))) :=
      Wave8M19.Htab.NoRet.decCall (Wave8M19.Htab.NoRet.seq
        (Wave8M19.Htab.NoRet.ite Wave8M19.Htab.NoRet.call0 Wave8M19.Htab.NoRet.skip)
        Wave8M19.Htab.NoRet.assign)
    exact Wave8M19.Htab.while_noRet _ _ (fun st v => hnr st v) _ s2 le_rfl w hw
  · intro u hu
    apply Wave8M19.Htab.Ret.ret
    intro val _
    have hIu : HtabUnionInto.UInv s0 u := by
      have := Wave8M19.Htab.while_inv (HtabUnionInto.UInv s0) _ _
        (fun x hx _ hfl => HtabUnionInto.union_iter R13SoloHtabSet.htab_set_spec_proof _ _ _ _ s0 x hx hfl)
        s2.clock s2 le_rfl hI2 (by rw [hu])
      rw [hu] at this
      exact this
    obtain ⟨_, _, _, hR⟩ := hIu
    have h2 : HtabUnionInto.ExitR (locN s0 "dst")
        { s0 with locals := s0.locals, clock := s0.clock }
        { u with locals := u.locals, clock := u.clock } := hR
    rw [← HtabUnionInto.exitR_locals (L1 := s0.locals) (k1 := s0.clock)
      (L2 := HolFiniteMapExact.resVarEq
        (HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite u).locals
          (ofString "i", s1.locals.lookup (ofString "i")))
        (ofString "cap", s0.locals.lookup (ofString "cap")))
      (k2 := u.clock)] at h2
    exact h2

def htabUnionCallees (f : MlS) : Bool :=
  StateRestoreEpilogue.htabMutCallees f ||
    f == ofString "htab_item" || f == ofString "htab_union_into"

theorem htabUnionCallees_good :
    ∀ f, htabUnionCallees f = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      StateRestoreEpilogue.noCatchableRaise htabUnionCallees body = true := by
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
  simp only [htabUnionCallees, StateRestoreEpilogue.htabMutCallees, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with ((((((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
  · have hl := lookup_of_guestAst_getElem 3 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_trap_with) rfl
    change originalRuntimeCode.lookup (ofString "trap_with") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_alloc) rfl
    change originalRuntimeCode.lookup (ofString "alloc") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_memcpy) rfl
    change originalRuntimeCode.lookup (ofString "memcpy") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 18 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_memeq) rfl
    change originalRuntimeCode.lookup (ofString "memeq") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 130 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_first_diff) rfl
    change originalRuntimeCode.lookup (ofString "htab_first_diff") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 131 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_find_leaf) rfl
    change originalRuntimeCode.lookup (ofString "htab_find_leaf") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 134 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_new_node) rfl
    change originalRuntimeCode.lookup (ofString "htab_new_node") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 135 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_new_leaf) rfl
    change originalRuntimeCode.lookup (ofString "htab_new_leaf") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 136 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_new_internal) rfl
    change originalRuntimeCode.lookup (ofString "htab_new_internal") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 137 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_grow) rfl
    change originalRuntimeCode.lookup (ofString "htab_grow") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 138 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_set) rfl
    change originalRuntimeCode.lookup (ofString "htab_set") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 139 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_del) rfl
    change originalRuntimeCode.lookup (ofString "htab_del") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 143 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_item) rfl
    change originalRuntimeCode.lookup (ofString "htab_item") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 400 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_union_into) rfl
    change originalRuntimeCode.lookup (ofString "htab_union_into") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl

theorem evmInvAt_of_head_del_union_exit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hA : ArenaReady s)
    (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (hbe : post.be = s.be)
    (hexit : HtabUnionInto.ExitR (memW s (globN s "ev" + 136)) s post) :
    InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt post S ∧
      evmChain post = evmChain s ∧
      OpDispatchSpec.evmR post = OpDispatchSpec.evmR s := by
  obtain ⟨hAp, hwf, hh0, _, hhp, hfp, hfr, hg⟩ := hexit
  exact OpHandlersB.evmInvAt_of_head_del_htab_step
    hA hInv hAp hbe hwf hh0 hhp hfp hfr hg

theorem call_htab_union_into_head_del_step {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hBS : FcBranchState s0 st S)
    (hchild_scr : Inside (globN s0 "ev", 280) (globN st "scratch_ptr") scratchEnd ∧
      WordsOK st (globN s0 "ev", 280))
    (hnt : (evaluateHOLFiniteState st
      (.call (some (none, none)) (ofString "htab_union_into")
        [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 136)]),
         .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 136)])])).1 ≠
      some .timeOut) :
    let prog : ProgHOL 64 := .call (some (none, none)) (ofString "htab_union_into")
      [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 136)]),
       .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 136)])]
    (∀ u, (evaluateHOLFiniteState st prog).1 ≠ some (.returned u)) ∧
    ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState st prog).1 ∧
    ((evaluateHOLFiniteState st prog).1 = none →
      let post := (evaluateHOLFiniteState st prog).2
      FcBranchState s0 post S ∧
      post.locals = st.locals ∧
      globN st "heap_ptr" ≤ globN post "heap_ptr" ∧
      GlobalsKept ["heap_ptr"] st post ∧
      evmChain post = evmChain st ∧
      OpDispatchSpec.evmR post = OpDispatchSpec.evmR st ∧
      (∀ i : Ivl, (∀ j ∈ htabFootprint st (memW st (globN st "ev" + 136)), Disj i j) →
        (i.2 = 0 ∨ Allocated st i) → M08IvlUnhitFc st post i)) := by
  dsimp only
  obtain ⟨hne_ret, hnone, herr⟩ := call0_outcome_fc (s := st) (fname := ofString "htab_union_into")
    (args := [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 136)]),
              .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 136)])]) hnt
  have hcode : st.code = originalRuntimeCode := hBS.arena.1.code
  have hno_err : ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState st
      (.call (some (none, none)) (ofString "htab_union_into")
        [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 136)]),
         .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 136)])])).1 := by
    intro he
    obtain ⟨vals, body, cal, ret, v, cpost, _, hl, hrun, _⟩ := herr he
    have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "htab_union_into") vals =
        some (body, cal, ret) := by rwa [← hcode]
    obtain ⟨rfl, _, _, _, _, _, _⟩ :=
      R14Shards.OpHandlersA.two_word_arg_lookup (by decide) HtabUnionInto.lookup_htab_union_into hl_orig
    exact StateRestoreEpilogue.evaluate_noCatchableRaise
      htabUnionCallees htabUnionCallees_good
      (sourceFnBody Guest.Software.guestFn_htab_union_into) (by decide)
      (callEntryStateHOLFinite st cal) hcode (ofString "EvmErr") v (by decide)
      (by rw [hrun])
  refine ⟨hne_ret, hno_err, fun hn => ?_⟩
  obtain ⟨vals, body, cal, ret, rv, cpost, hargs, hl, hrun, hpost_eq⟩ := hnone hn
  have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "htab_union_into") vals =
      some (body, cal, ret) := by rwa [← hcode]
  obtain ⟨rfl, rfl, wD, wS, rfl, hcal_d, _⟩ :=
    R14Shards.OpHandlersA.two_word_arg_lookup (by decide) HtabUnionInto.lookup_htab_union_into hl_orig
  obtain ⟨hb_ev, hw_ev, hev_lk, _, _⟩ := ev_head_facts hBS.arena hBS.inv
  have hb_child : globN s0 "ev" + 280 ≤ 2 ^ 64 := by
    have hse := R11Shards.scratchEnd_val
    have : 34208742912 ≤ 2 ^ 64 := by decide
    have := hchild_scr.1.2; dsimp at this; omega
  have hevD := eval_load_ev_off st hev_lk hw_ev hb_ev (off := 136) (by omega) (by omega)
  have hevS := eval_load_local_off st hBS.locals_ok.child_lk hBS.arena.1.memaddrs hchild_scr.2 hb_child
    (off := 136) (by omega) (by omega)
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact, hevD, hevS, Option.some.injEq, List.cons.injEq, and_true] at hargs
  rcases hargs with ⟨hvD, _⟩
  injection hvD with hvD'; injection hvD' with hwD_eq
  set t0 := memW st (globN st "ev" + 136)
  obtain ⟨⟨hT, hJ, hF, _⟩, _, _, _, hFW_all, _, _, _, hFO_disj, _, _, hRoles, _⟩ := hBS.inv
  have hwD_nat : wD.toNat = t0 := by
    have hlt : t0 < 2 ^ 64 := by
      dsimp only [t0]; unfold memW
      cases st.memory (BitVec.ofNat 64 (globN st "ev" + 136)) with | word w => exact w.isLt
    rw [← hwD_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  set entry := callEntryStateHOLFinite st cal
  have hentry_dst : locN entry "dst" = t0 := by
    unfold locN; simp [entry, callEntryStateHOLFinite, hcal_d, hwD_nat]
  have hhead_st : (globN st "ev", globN st "cur_cont") ∈ evmChain st := by
    rw [evmChain_cons]; exact List.mem_cons_self
  have ht0_S : t0 ∈ S := (hFW_all _ hhead_st).2.2.2.2.2.2.2.1
  obtain ⟨params_u, body_u, ret_u, hlk_u, hspec_u⟩ := htab_union_into_exitR_spec
  have hlk_eq := HtabUnionInto.lookup_htab_union_into.symm.trans hlk_u
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨rfl, rfl⟩
  have hwf_entry : UnionArgWF entry := by
    refine ⟨⟨guestInv_with_locals_clock st cal _ hBS.arena.1, hBS.arena.2⟩, ?_, ?_⟩
    · rw [hentry_dst]
      exact (StateRestoreEpilogue.htabWF_lc st cal st.globals _ t0).2
        (hT.2.1 t0 ht0_S).1
    · rw [hentry_dst]
      intro i hi
      change i ∈ htabFootprint st t0 at hi
      exact ((hT.2.1 t0 ht0_S).2 i hi).1
  have hexit_c : HtabUnionInto.ExitR (locN entry "dst") entry cpost := by
    have h := hspec_u entry hcode hwf_entry ⟨[_, _], hl_orig⟩
      (by rw [hrun]; simp) rv (by rw [hrun])
    rwa [hrun] at h
  rw [hentry_dst] at hexit_c
  set post := (evaluateHOLFiniteState st
    (.call (some (none, none)) (ofString "htab_union_into")
      [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 136)]),
       .load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 136)])])).2
  have hpost_lc : post = { cpost with locals := st.locals } := hpost_eq
  have hexit : HtabUnionInto.ExitR t0 st post := by
    have h2 : HtabUnionInto.ExitR t0
        { st with locals := cal, clock := st.clock - 1 }
        { cpost with locals := cpost.locals, clock := cpost.clock } := hexit_c
    rw [HtabUnionInto.exitR_locals] at h2
    have h3 : HtabUnionInto.ExitR t0
        { st with locals := st.locals, clock := st.clock }
        { cpost with locals := st.locals, clock := cpost.clock } := by
      rw [HtabUnionInto.exitR_locals]; exact h2
    simpa [← hpost_lc] using h3
  have hbe_p : post.be = st.be := by
    rw [hpost_lc]
    have hbe0 := InitECandidate.Solver.Wave8GuestInv.R16Shards.evaluate_be_eq entry
      (sourceFnBody Guest.Software.guestFn_htab_union_into)
    rw [hrun] at hbe0
    exact hbe0
  obtain ⟨hInv_p, hch_p, hR_p⟩ := evmInvAt_of_head_del_union_exit hBS.arena hBS.inv hbe_p hexit
  obtain ⟨hAp, _, _, _, hhp_p, hfp_p, hfr_p, hgk_p⟩ := hexit
  have hg_nonHeap : ∀ name, ofString name ≠ ofString "heap_ptr" → globN post name = globN st name := by
    intro name h1
    exact InitECandidate.Solver.Wave8Contracts.M08.globN_eq_of_lookup (hgk_p (ofString name) (by
      simp only [List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
      rintro ⟨w, rfl, heq⟩; exact h1 heq.symm))
  have ht0_al1 : ∀ j ∈ htabFootprint st t0, j.1 % 8 = 0 :=
    fun j hj => ((hT.2.1 t0 ht0_S).1.1 j hj).2.1
  have hf_al1 : globN st "heap_ptr" % 8 = 0 := hBS.arena.2.2.2.2.2.2.1
  have hunhit : ∀ i : Ivl, (∀ j ∈ htabFootprint st t0, Disj i j) →
      (i.2 = 0 ∨ Allocated st i) → M08IvlUnhitFc st post i := fun i hdi hal =>
    m08_ivlUnhit_of_frameOutside_fc hfr_p ht0_al1 hf_al1 hdi
      (disj_fresh_of_zero_or_allocated_fc hBS.arena.2 hAp.2 hhp_p hal)
  have hu_fo : ∀ ec ∈ evmChain st, ∀ o ∈ frameObjects st ec, M08IvlUnhitFc st post o := by
    intro ec hec o ho
    exact m08_ivlUnhit_of_frameOutside_fc hfr_p ht0_al1 hf_al1
      (fun j hj => (hFO_disj ec hec o ho).1 t0 ht0_S j hj)
      (disj_fresh_of_frameObject_fc hBS.arena.2 hAp.2 hhp_p (hFW_all ec hec) ho)
  have hrec_eq : ∀ ec ∈ evmChain st,
      (∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW post (ec.1 + k) = memW st (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW st (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → k % 8 = 0 →
        memW post (memW st (ec.1 + 88) + k) = memW st (memW st (ec.1 + 88) + k)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨hb1, hb2, hb88, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hBS.arena.2 hFW
    have he1_8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
    have he2_8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
    have he88_8 : (memW st (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW st (ec.1 + 88), 24) (by simp)).2.1
    refine ⟨fun k hk hk8 => InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
              (hu_fo ec hec (ec.1, 280) (by simp [frameObjects])) (by omega) hb1 ⟨by omega, by omega⟩,
            fun k hk hk8 => InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
              (hu_fo ec hec (ec.2, 104) (by simp [frameObjects])) (by omega) hb2 ⟨by omega, by omega⟩,
            fun k hk hk8 => InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
              (hu_fo ec hec (memW st (ec.1 + 88), 24) (by simp [frameObjects])) (by omega) hb88 ⟨by omega, by omega⟩⟩
  have hfs_eq : ∀ ec ∈ evmChain st, frameScratch post ec = frameScratch st ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega), he_eq 88 (by omega) (by omega)]
  have hfl_eq : ∀ ec ∈ evmChain st, frameLogs post ec = frameLogs st ec := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    unfold frameLogs
    rw [he_eq 88 (by omega) (by omega),
      show memW post (memW st (ec.1 + 88)) = memW st (memW st (ec.1 + 88)) by simpa using h88_eq 0 (by omega) (by omega),
      h88_eq 16 (by omega) (by omega)]
  have hu_other : ∀ u ∈ S, u ≠ t0 → ∀ i ∈ htabFootprint st u, M08IvlUnhitFc st post i := fun u hu hne i hi =>
    hunhit i (fun j hj => hT.2.2.1 u hu t0 ht0_S hne i hi j hj)
      (Or.inr ((hT.2.1 u hu).2 i hi).1)
  have hother_fp : ∀ u ∈ S, u ≠ t0 → htabFootprint post u = htabFootprint st u := by
    intro u hu hne
    have hfp := (hT.2.1 u hu).1.1
    have ht_fp : (u, 88) ∈ htabFootprint st u := by simp [htabFootprint]
    have h264 : heapEnd ≤ 2 ^ 64 := by decide
    exact (InitECandidate.Solver.Wave8Contracts.M08.htabFootprint_eq_of_hdr_unhit
      ((hfp _ ht_fp).2.1) (by have := (hfp _ ht_fp).1.2; dsimp at this; omega)
      (hu_other u hu hne _ ht_fp)).2
  have hu_fix : ∀ i ∈ fixedObjects st, M08IvlUnhitFc st post i := fun i hi =>
    hunhit i (fun j hj => disj_symm_fc (((hT.2.1 t0 ht0_S).2 j hj).2 i hi))
      (by rcases hF.1 i hi with h0 | ⟨hal, _⟩; exact Or.inl h0; exact Or.inr hal)
  have hm0 : memW post 0 = memW st 0 ∧ memW post 8 = memW st 8 ∧ memW post 16 = memW st 16 := by
    have hlow : ∀ a : Nat, a + 8 ≤ sourceBase → memW post a = memW st a := fun a ha => by
      have hsb_lt : sourceBase < 2 ^ 64 := by decide
      have ha_lt : a < 2 ^ 64 := lt_of_le_of_lt (by omega) hsb_lt
      have hm := hfr_p (BitVec.ofNat 64 a)
        (fun j hj ⟨h1, _⟩ => by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          have hlo := ((hT.2.1 t0 ht0_S).1.1 j hj).1.1; omega)
        (fun ⟨h1, _⟩ => by
          dsimp at h1; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          have hlo := hBS.arena.2.1; omega)
      unfold memW; rw [hm]
    exact ⟨hlow 0 (by decide), hlow 8 (by decide), hlow 16 (by decide)⟩
  have hbo_g : globN post "bo" = globN st "bo" := hg_nonHeap "bo" (by decide)
  have hba_g : globN post "bal_accounts" = globN st "bal_accounts" := hg_nonHeap "bal_accounts" (by decide)
  have hj_g : globN post "journal" = globN st "journal" := hg_nonHeap "journal" (by decide)
  have hjc_g : globN post "journal_cap" = globN st "journal_cap" := hg_nonHeap "journal_cap" (by decide)
  have hu_bo : globN st "bo" ≠ 0 → M08IvlUnhitFc st post (globN st "bo", 88) := fun hnz => by
    have hm := InitECandidate.Solver.Wave8Contracts.M08.typedRecord_mem_fixedObjects st
      (r := ("bo", 88)) (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords])
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm
  have hbo_words : globN st "bo" ≠ 0 → ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW post (globN st "bo" + k) = memW st (globN st "bo" + k) := fun hnz k hk => by
    have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    simpa [hbo_g] using InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
      hBS.arena.2 hF "bo" 88
      (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords])
      hbo_g hnz (hu_bo hnz) hk_in.1 hk_in.2
  have hbo_eq := InitECandidate.Solver.Wave8Contracts.M08.blockOutObjects_eq_of_bo_unhit
    hBS.arena.2 hF hbo_g hT.2.2.2.2.2.2.2.2.2.2.1
    (fun h => hbo_words h 24 (by simp))
    (fun h => hbo_words h 32 (by simp))
    (fun h => hbo_words h 40 (by simp))
    (fun h => hbo_words h 56 (by simp))
    (fun h => hbo_words h 72 (by simp))
    (fun h => hbo_words h 80 (by simp))
    (fun _ _ => by simp [hm0.1, hm0.2.2])
    (fun _ _ => by simp [hm0.1, hm0.2.2])
    (fun h h40 => hu_fix (memW st (globN st "bo" + 40), 24)
      (by unfold fixedObjects; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr (by simp [blockOutObjects, h, h40]))))))
    (fun h h72 => hu_fix (memW st (globN st "bo" + 72), 24)
      (by unfold fixedObjects; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr (by simp [blockOutObjects, h, h72]))))))
  have ht0_pos : 0 < t0 := by
    have := ((hT.2.1 t0 ht0_S).1.1 (t0, 88) (by simp [htabFootprint])).1.1
    have hsb : 0 < sourceBase := by decide
    dsimp at this; omega
  have ht0_frs : (t0, "frame.del") ∈ frameRoleSlots st (evmChain st) := by
    unfold frameRoleSlots
    exact List.mem_flatMap.2 ⟨(globN st "ev", globN st "cur_cont"), hhead_st, by simp [t0]⟩
  have hnot_world_role : ∀ r : String, r ≠ "frame.del" → (t0, r) ∉ worldRoleSlots st := by
    intro r hne hwr
    have hpw := (List.pairwise_append.1 hRoles.2.1).2.2 _ hwr _ ht0_frs rfl
    exact hne hpw.1
  have ht0_no_ba : globN st "bal_accounts" ≠ t0 := by
    intro heq
    apply hnot_world_role "bal_accounts" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_right; simp [heq]
  have ht0_no_ad : ∀ ad ∈ balRecords st, memW st ad ≠ t0 := by
    intro ad had heq
    apply hnot_world_role "bal.stor" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_right
    exact List.mem_flatMap.2 ⟨ad, had, by simp [heq]⟩
  have hbal_eq := balObjects_eq_of_unhit_except_fc hBS.arena.2 hT hF
    hba_g hu_other ⟨ht0_no_ba, ht0_no_ad⟩
    (fun i hi _ => hu_fix i (by unfold fixedObjects; exact List.mem_append.2 (Or.inr hi))) hm0
  have hfix_p : fixedObjects post = fixedObjects st := by
    unfold fixedObjects
    rw [hbo_eq.1, hbal_eq.1, hj_g, hjc_g]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "heap_ptr" := by
      revert gn hgn; decide
    rw [hg_nonHeap gn.1 hne]
  have hRel_p : ReleaseReadyAt post S (memW s0 (globN s0 "cur_cont" + 48))
      (memW s0 (globN s0 "cur_cont" + 56)) := by
    refine releaseReadyAt_transport hBS.release hhp_p hch_p hfs_eq
      (fun ec hec => ⟨(hrec_eq ec hec).1 24 (by omega) (by omega), (hrec_eq ec hec).1 40 (by omega) (by omega)⟩)
      (fun ec hec => Or.inl (hfl_eq ec hec))
      (fun ec hec => (hrec_eq ec hec).1 112 (by omega) (by omega))
      (fun u hu => ?_) hfix_p
    by_cases hu0 : u = t0
    · right; intro o ho; rw [hu0] at ho ⊢
      rcases (hfp_p o ho).2 with ⟨j, hj, hin⟩ | hfresh
      · exact Or.inl ⟨j, hj, hin⟩
      · exact Or.inr ⟨le_trans hBS.arena.2.1 hfresh.1,
          le_trans hfresh.2 (by rw [Nat.add_sub_of_le hhp_p])⟩
    · exact Or.inl (hother_fp u hu hu0)
  have hloc_p : post.locals = st.locals := by rw [hpost_lc]
  have hBSp : FcBranchState s0 post S := by
    refine ⟨hAp, hInv_p, hRel_p, fcEntryLocals_congr_locals hloc_p hBS.locals_ok,
      hch_p.trans hBS.chain_eq, ?_, ?_, ?_, ?_⟩
    · rw [hch_p]; exact hBS.length_eq
    · rw [hR_p]; exact hBS.r_le
    · intro ec hec; rw [hch_p] at hec
      obtain ⟨a0, b0, c0, d0⟩ := hBS.cells ec hec
      obtain ⟨he_eq, hc_eq, _⟩ := hrec_eq ec hec
      exact ⟨(he_eq 24 (by omega) (by omega)).trans a0,
             (he_eq 32 (by omega) (by omega)).trans b0,
             (he_eq 40 (by omega) (by omega)).trans c0,
             (hc_eq 56 (by omega) (by omega)).trans d0⟩
    · exact (hg_nonHeap "ev" (by decide)).trans hBS.ev_eq
  exact ⟨hBSp, hloc_p, hhp_p, hgk_p, hch_p, hR_p, hunhit⟩

theorem fcPoppedChild_with_locals_clock {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F} {S : List Nat}
    (h : FcPoppedChild s0 st S)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (ck : Nat) :
    FcPoppedChild s0 { st with locals := L, clock := ck } S := by
  refine {
    child_scr := h.child_scr
    rec_scr := h.rec_scr
    child_disj_fo := ?_
    rec_disj_fo := ?_
    child_disj_ht := h.child_disj_ht
    rec_disj_ht := h.rec_disj_ht
    child_disj_fix := h.child_disj_fix
    rec_disj_fix := h.rec_disj_fix
    child_logs_scr := h.child_logs_scr
    child_logs_disj_fo := ?_
    child_logs_disj_ht := h.child_logs_disj_ht
    child_logs_arr_in := h.child_logs_arr_in
    child_logs_arr_wok := h.child_logs_arr_wok
    child_logs_ok := h.child_logs_ok
    child_logs_len_le := h.child_logs_len_le
    child_log_objs_pw := h.child_log_objs_pw
    child_log_objs_disj_fo := ?_
    child_log_objs_disj_ht := h.child_log_objs_disj_ht
    child_log_objs_disj_fix := h.child_log_objs_disj_fix
    child_log_objs_avoids_tries := h.child_log_objs_avoids_tries
    child_log_objs_disj_msg := ?_
    addr_table_ok := ?_
    key_table_ok := ?_
    parent_room := h.parent_room
    out_win_ok := h.out_win_ok }
  · simpa only [evmChain_lc_fc st L ck, frameObjects_lc] using h.child_disj_fo
  · simpa only [evmChain_lc_fc st L ck, frameObjects_lc] using h.rec_disj_fo
  · simpa only [evmChain_lc_fc st L ck, frameObjects_lc, frameLogs, memW] using h.child_logs_disj_fo
  · simpa only [evmChain_lc_fc st L ck, frameObjects_lc, frameLogObjects, logOwnedIvls, logRecordIvls, globN, memW] using h.child_log_objs_disj_fo
  · simpa only [evmChain_lc_fc st L ck, frameLogObjects, logOwnedIvls, logRecordIvls, globN, memW] using h.child_log_objs_disj_msg
  · exact (nonDelAccessTable_lc st L ck S _).2 h.addr_table_ok
  · exact (nonDelAccessTable_lc st L ck S _).2 h.key_table_ok

theorem fcPoppedChild_callEntry {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F} {S : List Nat}
    (h : FcPoppedChild s0 st S)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) :
    FcPoppedChild s0 (callEntryStateHOLFinite st L) S := by
  exact fcPoppedChild_with_locals_clock h L (st.clock - 1)

theorem fcPoppedChild_child_bound {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hBS : FcBranchState s0 st S) (h : FcPoppedChild s0 st S) :
    globN s0 "ev" + 280 ≤ 2 ^ 64 := by
  exact (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hBS.arena.2
    (Or.inr h.child_scr.1)).2

theorem fcPoppedChild_eval_child_off {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hBS : FcBranchState s0 st S) (h : FcPoppedChild s0 st S)
    {off : Nat} (hoff : off + 8 ≤ 280) (hoff8 : off % 8 = 0) :
    @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 off)])) =
      some (.val (.word (BitVec.ofNat 64 (memW st (globN s0 "ev" + off))))) := by
  exact eval_load_local_off st hBS.locals_ok.child_lk hBS.arena.1.memaddrs
    h.child_scr.2 (fcPoppedChild_child_bound hBS h) hoff hoff8

theorem fcLogTransfer_prefix_partition (parent : List Ivl) (logs : Nat → List Ivl)
    {n k : Nat} (hk : k ≤ n)
    (hparent : parent.Pairwise Disj)
    (hchild : ((List.range n).flatMap logs).Pairwise Disj)
    (hdisj : ∀ a ∈ parent, ∀ b ∈ (List.range n).flatMap logs, Disj a b) :
    (parent ++ (List.range k).flatMap logs).Pairwise Disj ∧
    ((List.range (n - k)).flatMap (fun i => logs (k + i))).Pairwise Disj ∧
    (∀ a ∈ parent ++ (List.range k).flatMap logs,
      ∀ b ∈ (List.range (n - k)).flatMap (fun i => logs (k + i)), Disj a b) := by
  have hsplit : (List.range n).flatMap logs =
      (List.range k).flatMap logs ++
        (List.range (n - k)).flatMap (fun i => logs (k + i)) := by
    conv_lhs => rw [show n = k + (n - k) by omega]
    rw [List.range_add, List.flatMap_append, List.flatMap_map]
  rw [hsplit, List.pairwise_append] at hchild
  have hprefix : ∀ a ∈ parent, ∀ b ∈ (List.range k).flatMap logs, Disj a b := by
    intro a ha b hb
    exact hdisj a ha b (hsplit ▸ List.mem_append_left _ hb)
  refine ⟨List.pairwise_append.mpr ⟨hparent, hchild.1, hprefix⟩, hchild.2.1, ?_⟩
  intro a ha b hb
  rcases List.mem_append.mp ha with ha | ha
  · exact hdisj a ha b (hsplit ▸ List.mem_append_right _ hb)
  · exact hchild.2.2 a ha b hb

def logAppendCallees (f : MlS) : Bool :=
  f == ofString "trap_with" || f == ofString "alloc" ||
    f == ofString "memcpy" || f == ofString "lst_push" ||
    f == ofString "log_append"

theorem logAppendCallees_good :
    ∀ f, logAppendCallees f = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      StateRestoreEpilogue.noCatchableRaise logAppendCallees body = true := by
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
  simp only [logAppendCallees, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with (((rfl | rfl) | rfl) | rfl) | rfl
  · have hl := lookup_of_guestAst_getElem 3 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_trap_with) rfl
    change originalRuntimeCode.lookup (ofString "trap_with") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_alloc) rfl
    change originalRuntimeCode.lookup (ofString "alloc") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_memcpy) rfl
    change originalRuntimeCode.lookup (ofString "memcpy") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 410 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_lst_push) rfl
    change originalRuntimeCode.lookup (ofString "lst_push") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 523 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_log_append) rfl
    change originalRuntimeCode.lookup (ofString "log_append") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl

theorem lookup_alloc_fc :
    originalRuntimeCode.lookup (ofString "alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_alloc, .one) :=
  lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_alloc) rfl

theorem lookup_memcpy_fc :
    originalRuntimeCode.lookup (ofString "memcpy") =
      some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memcpy, .one) :=
  lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memcpy) rfl

theorem lookup_lst_push_fc :
    originalRuntimeCode.lookup (ofString "lst_push") =
      some ([(ofString "l", .one), (ofString "esz", .one)],
        sourceFnBody Guest.Software.guestFn_lst_push, .one) :=
  lookup_of_guestAst_getElem 410 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_lst_push) rfl

theorem lookup_log_append_fc :
    originalRuntimeCode.lookup (ofString "log_append") =
      some ([(ofString "e", .one), (ofString "log", .one)],
        sourceFnBody Guest.Software.guestFn_log_append, .one) :=
  lookup_of_guestAst_getElem 523 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_log_append) rfl

private abbrev R14W := InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.updW

theorem lookup_set_retdata_fc :
    originalRuntimeCode.lookup (ofString "set_retdata") =
      some ([(ofString "p", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_set_retdata, .one) :=
  lookup_of_guestAst_getElem 595 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_set_retdata) rfl

/-- Forward form of `store_global_off_word`: when the stored value's evaluation
is known and the target address is in the domain, the store runs to `(none, …)`. -/
private theorem store_global_off_word_run {F : Type} (t : PanSemStateFiniteExact 64 F)
    {gname : String} {gbase off : Nat} {gw w : BitVec 64} {valExp : ExpHOL 64}
    (hg_lk : t.globals.lookup (ofString gname) = some (.val (.word gw)))
    (hg_nat : gw.toNat = gbase)
    (hbnd : gbase + off < 2 ^ 64)
    (hdom : t.memaddrs (BitVec.ofNat 64 (gbase + off)))
    (hvalEval : @evalHOLExact 64 F _ t.toExact
        (fun a => Classical.propDecidable (t.memaddrs a)) valExp = some (.val (.word w))) :
    evaluateHOLFiniteState t
        (.store (.op .add [.var .global (ofString gname), .const (BitVec.ofNat 64 off)]) valExp) =
      (none, { t with memory := R14W t.memory (BitVec.ofNat 64 (gbase + off)) w }) := by
  have hdst : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.op .add [.var .global (ofString gname), .const (BitVec.ofNat 64 off)]) =
      some (.val (.word (BitVec.ofNat 64 (gbase + off)))) := by
    simp only [evalHOLExact, evalListHOLExact, hg_lk, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
    congr 3
    apply BitVec.eq_of_toNat_eq
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hg_nat, hz0, Nat.add_zero,
      Nat.mod_eq_of_lt (show off < 2 ^ 64 by omega), Nat.mod_eq_of_lt hbnd]
  rw [evaluateHOLFiniteState_store, hdst, hvalEval]
  dsimp only
  have hmem : @panMemStoresHOL 64 _ (BitVec.ofNat 64 (gbase + off)) (flattenHOL (.val (.word w)))
      t.memaddrs (fun a => Classical.propDecidable (t.memaddrs a)) t.memory
      = some (R14W t.memory (BitVec.ofNat 64 (gbase + off)) w) := by
    simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom, ↓reduceIte]
    rfl
  rw [hmem]

/-- `set_retdata(p, 0)` writes only `ev+144 := evm_empty`, `ev+152 := 0`, `ev+216 := 0`
and returns `0`; the outer `dec cap` tail is unreachable. -/
theorem set_retdata_zero_body_run {F : Type} (X : PanSemStateFiniteExact 64 F)
    {e evw pv : BitVec 64}
    (he : X.globals.lookup (ofString "ev") = some (.val (.word e)))
    (hev : X.globals.lookup (ofString "evm_empty") = some (.val (.word evw)))
    (_hp : X.locals.lookup (ofString "p") = some (.val (.word pv)))
    (hn : X.locals.lookup (ofString "n") = some (.val (.word 0#64)))
    (hbnd : e.toNat + 232 < 2 ^ 64)
    (hdom144 : X.memaddrs (e + 144#64))
    (hdom152 : X.memaddrs (e + 152#64))
    (hdom216 : X.memaddrs (e + 216#64)) :
    evaluateHOLFiniteState X (sourceFnBody Guest.Software.guestFn_set_retdata) =
      (some (.returned (.val (.word 0#64))),
       emptyLocalsHOLFinite
         { X with memory :=
             (R14W (R14W (R14W X.memory (BitVec.ofNat 64 (e.toNat + 144)) evw)
               (BitVec.ofNat 64 (e.toNat + 152)) 0#64)
               (BitVec.ofNat 64 (e.toNat + 216)) 0#64) }) := by
  have hb144 : e.toNat + 144 < 2 ^ 64 := by omega
  have hb152 : e.toNat + 152 < 2 ^ 64 := by omega
  have hb216 : e.toNat + 216 < 2 ^ 64 := by omega
  have heq144 : (e + 144#64) = BitVec.ofNat 64 (e.toNat + 144) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb144]
  have heq152 : (e + 152#64) = BitVec.ofNat 64 (e.toNat + 152) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb152]
  have heq216 : (e + 216#64) = BitVec.ofNat 64 (e.toNat + 216) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb216]
  have hvalEv : @evalHOLExact 64 F _ X.toExact (fun a => Classical.propDecidable (X.memaddrs a))
      (.var .global (ofString "evm_empty")) = some (.val (.word evw)) := by
    simp [evalHOLExact, hev]
  have hval0 (t : PanSemStateFiniteExact 64 F) :
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.const 0#64) = some (.val (.word 0#64)) := by
    simp [evalHOLExact]
  have hst1 : evaluateHOLFiniteState X
      (.store (.op .add [.var .global (ofString "ev"), .const 144#64])
        (.var .global (ofString "evm_empty"))) =
      (none, { X with memory := R14W X.memory (BitVec.ofNat 64 (e.toNat + 144)) evw }) :=
    store_global_off_word_run X he rfl hb144 (by rw [← heq144]; exact hdom144) hvalEv
  have hst2 : evaluateHOLFiniteState
      { X with memory := R14W X.memory (BitVec.ofNat 64 (e.toNat + 144)) evw }
      (.store (.op .add [.var .global (ofString "ev"), .const 152#64]) (.const 0#64)) =
      (none, { X with memory :=
          (R14W (R14W X.memory (BitVec.ofNat 64 (e.toNat + 144)) evw)
            (BitVec.ofNat 64 (e.toNat + 152)) 0#64) }) :=
    store_global_off_word_run _ he rfl hb152 (by rw [← heq152]; exact hdom152) (hval0 _)
  have hst3 : evaluateHOLFiniteState
      { X with memory :=
          (R14W (R14W X.memory (BitVec.ofNat 64 (e.toNat + 144)) evw)
            (BitVec.ofNat 64 (e.toNat + 152)) 0#64) }
      (.store (.op .add [.var .global (ofString "ev"), .const 216#64]) (.const 0#64)) =
      (none, { X with memory :=
          (R14W (R14W (R14W X.memory (BitVec.ofNat 64 (e.toNat + 144)) evw)
            (BitVec.ofNat 64 (e.toNat + 152)) 0#64)
            (BitVec.ofNat 64 (e.toNat + 216)) 0#64) }) :=
    store_global_off_word_run _ he rfl hb216 (by rw [← heq216]; exact hdom216) (hval0 _)
  have hthen : evaluateHOLFiniteState X
      (ProgHOL.seq
        (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "ev"),
            ExpHOL.const 144#64])
          (ExpHOL.var VarKind.global (ofString "evm_empty")))
        (ProgHOL.seq
          (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "ev"),
              ExpHOL.const 152#64])
            (ExpHOL.const 0#64))
          (ProgHOL.seq
            (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "ev"),
                ExpHOL.const 216#64])
              (ExpHOL.const 0#64))
            (ProgHOL.return (ExpHOL.const 0#64))))) =
      (some (.returned (.val (.word 0#64))),
       emptyLocalsHOLFinite
         { X with memory :=
             (R14W (R14W (R14W X.memory (BitVec.ofNat 64 (e.toNat + 144)) evw)
               (BitVec.ofNat 64 (e.toNat + 152)) 0#64)
               (BitVec.ofNat 64 (e.toNat + 216)) 0#64) }) := by
    rw [evaluateHOLFiniteState_seq_line780, hst1]; dsimp only
    rw [evaluateHOLFiniteState_seq_line780, hst2]; dsimp only
    rw [evaluateHOLFiniteState_seq_line780, hst3]; dsimp only
    rw [evaluateHOLFiniteState_return]
    rw [hval0 _]
    dsimp only
    have hsz : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL
        { X with memory :=
            (R14W (R14W (R14W X.memory (BitVec.ofNat 64 (e.toNat + 144)) evw)
              (BitVec.ofNat 64 (e.toNat + 152)) 0#64)
              (BitVec.ofNat 64 (e.toNat + 216)) 0#64) }.structs
        (shapeOfHOLExact (.val (.word 0#64) : ValueHOL 64)) ≤ 32 := by
      simp [shapeOfHOLExact]
    rw [if_pos hsz]
  have hb : sourceFnBody Guest.Software.guestFn_set_retdata =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_set_retdata).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_set_retdata,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  rw [evaluateHOLFiniteState_seq_line780]
  rw [evaluateHOLFiniteState_ite]
  have hcmp : @evalHOLExact 64 F _ X.toExact
      (fun a => Classical.propDecidable (X.memaddrs a))
      (.cmp .equal (.var .local (ofString "n")) (.const (0#64))) =
      some (.val (.word (1#64))) := by
    simp [evalHOLExact, hn, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp]
  dsimp only
  have h10 : ¬ (1#64 = (0 : BitVec 64)) := by decide
  rw [if_neg h10]
  rw [hthen]

theorem alloc_entry_returned_fc {F : Type}
    (s : PanSemStateFiniteExact 64 F) (nw : BitVec 64)
    (hP : ArenaReady s)
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState
      (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word nw))))
      (sourceFnBody Guest.Software.guestFn_alloc)).1 = some (.returned v)) :
    let ent := callEntryStateHOLFinite s
      (HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word nw)))
    let post := (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_alloc)).2
    ∃ pw qw : BitVec 64,
      v = .val (.word pw) ∧
      pw.toNat = globN s "heap_ptr" ∧
      pw.toNat % 8 = 0 ∧
      pw.toNat + nw.toNat ≤ qw.toNat ∧
      qw.toNat ≤ heapLimit ∧
      qw.toNat % 8 = 0 ∧
      ArenaReady post ∧
      AllocatorGrows s post ∧
      InitECandidate.Solver.Wave8Contracts.M25.FreshBlock ent post pw.toNat nw.toNat ∧
      post.memory = s.memory ∧
      post.be = s.be ∧
      post.globals = s.globals.update (ofString "heap_ptr", .val (.word qw)) := by
  dsimp only
  set cmap := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word nw))
  set ent := callEntryStateHOLFinite s cmap
  have hent_code : ent.code = originalRuntimeCode := hP.1.code
  have hent_AR : ArenaReady ent := ⟨guestInv_with_locals_clock s cmap _ hP.1, hP.2⟩
  have hlk_one := pan_one_word_lookup
    originalRuntimeCode.lookup (ofString "alloc") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_alloc) nw lookup_alloc_fc
  obtain ⟨params_a, body_a, ret_a, hlk_a, hspec_a⟩ := InitECandidate.Solver.Wave8Contracts.M25.rt_alloc
  have hlk_eq := lookup_alloc_fc.symm.trans hlk_a
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨rfl, rfl⟩
  have hnt : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_alloc)).1 ≠ some .timeOut := by
    rw [hret]; simp
  obtain ⟨pw_rt, hpw_v, hAp, hag, hfb⟩ :=
    hspec_a ent hent_code hent_AR ⟨[.val (.word nw)], hlk_one⟩ hnt v hret
  have hent_n_val : locN ent "n" = nw.toNat := by
    simp [ent, cmap, locN, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [hent_n_val] at hfb
  have hp_word : ∃ p : BitVec 64, ent.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) := by
    have hp_lo : sourceBase ≤ globN ent "heap_ptr" := hent_AR.2.1
    rcases hg : ent.globals.lookup (ofString "heap_ptr") with _ | gv
    · simp [globN, hg, sourceBase] at hp_lo
    · rcases gv with ⟨⟨p⟩⟩ | fs | ⟨nm, fs⟩
      · exact ⟨p, rfl⟩
      · simp [globN, hg, sourceBase] at hp_lo
      · simp [globN, hg, sourceBase] at hp_lo
  obtain ⟨pw, hpw_lk⟩ := hp_word
  have hpw_glob : globN s "heap_ptr" = pw.toNat := by
    change globN ent "heap_ptr" = pw.toNat
    simp [globN, hpw_lk]
  have hent_n_lk : ent.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hcmax_val : HeapPotential.cMax.toNat = 2952790016 := rfl
  have hpw_hi : pw.toNat ≤ HeapPotential.cMax.toNat := by
    have h1 : pw.toNat ≤ heapLimit := by rw [← hpw_glob]; exact hP.2.2.1
    rw [R11Shards.heapLimit_val] at h1
    omega
  obtain ⟨hv_pw, hp_add_le, hq_le_cmax, hq_al, hpa_al⟩ :=
    R13SoloHtabSet.alloc_body_run ent pw nw hent_code hpw_hi hpw_lk hent_n_lk v hret
  have hpw_eq_rt : pw = pw_rt := by
    rw [hv_pw] at hpw_v; injection hpw_v with h1; injection h1
  subst hpw_eq_rt
  have hq_lim : ((pw + (nw + 7)) &&& ((0 : BitVec 64) - 8)).toNat ≤ heapLimit := by
    rw [R11Shards.heapLimit_val]; omega
  set qw := (pw + (nw + 7)) &&& ((0 : BitVec 64) - 8)
  set post := (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_alloc)).2
  have hpost_mem : post.memory = s.memory := (congrArg PanSemStateFiniteExact.memory hpa_al).trans rfl
  have hpost_be : post.be = s.be := (congrArg PanSemStateFiniteExact.be hpa_al).trans rfl
  have hpost_glob : post.globals = s.globals.update (ofString "heap_ptr", .val (.word qw)) :=
    (congrArg PanSemStateFiniteExact.globals hpa_al).trans rfl
  exact ⟨pw, qw, hv_pw, hpw_glob.symm, hfb.1, hp_add_le, hq_lim, hq_al, hAp,
    ⟨hag.1, hag.2⟩, hfb, hpost_mem, hpost_be, hpost_glob⟩

theorem frameLogObjects_append_fc {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {ec : Ivl} {log : Nat}
    (hlen : memW post (memW post (ec.1 + 88) + 8) =
      memW s (memW s (ec.1 + 88) + 8) + 1)
    (hprefix : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      logOwnedIvls post (memW post (memW post (memW post (ec.1 + 88)) + 8 * i)) =
        logOwnedIvls s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i)))
    (hlast : memW post (memW post (memW post (ec.1 + 88)) +
      8 * memW s (memW s (ec.1 + 88) + 8)) = log)
    (hlog : logOwnedIvls post log = logOwnedIvls s log) :
    frameLogObjects post ec = frameLogObjects s ec ++ logOwnedIvls s log := by
  unfold frameLogObjects
  dsimp only
  rw [hlen, List.range_succ, List.flatMap_append]
  have hp : (List.range (memW s (memW s (ec.1 + 88) + 8))).flatMap
      (fun i => logOwnedIvls post
        (memW post (memW post (memW post (ec.1 + 88)) + 8 * i))) =
      (List.range (memW s (memW s (ec.1 + 88) + 8))).flatMap
        (fun i => logOwnedIvls s
          (memW s (memW s (memW s (ec.1 + 88)) + 8 * i))) := by
    apply List.flatMap_congr
    intro i hi
    exact hprefix i (List.mem_range.mp hi)
  rw [hp]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hlast, hlog]

theorem logEntryOK_transport_fc {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {log : Nat}
    (h : LogEntryOK s log)
    (hdom : post.memaddrs = s.memaddrs)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hwords : ∀ off ∈ ([0, 8, 16, 24, 32] : List Nat),
      memW post (log + off) = memW s (log + off)) :
    LogEntryOK post log := by
  obtain ⟨hw, hin, htopics, hsize, haddr, htopic_in, hdata⟩ := h
  have h0 := hwords 0 (by simp)
  have h8 := hwords 8 (by simp)
  have h16 := hwords 16 (by simp)
  have h24 := hwords 24 (by simp)
  have h32 := hwords 32 (by simp)
  simp only [Nat.add_zero] at h0
  unfold LogEntryOK
  rw [h0, h8, h16, h24, h32]
  refine ⟨(R14Shards.OpHandlersA.wordsOK_congr_dom hdom).2 hw,
    ⟨hin.1, le_trans hin.2 hhp⟩, htopics, hsize,
    ⟨haddr.1, le_trans haddr.2 hhp⟩,
    ⟨htopic_in.1, le_trans htopic_in.2 hhp⟩,
    ⟨hdata.1, le_trans hdata.2 hhp⟩⟩

theorem logOwnedIvls_transport_fc {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {log : Nat}
    (haddr : globN post "vm_system_address" = globN s "vm_system_address")
    (hwords : ∀ off ∈ ([0, 8, 16, 24, 32] : List Nat),
      memW post (log + off) = memW s (log + off)) :
    logOwnedIvls post log = logOwnedIvls s log := by
  have h0 := hwords 0 (by simp)
  have h8 := hwords 8 (by simp)
  have h16 := hwords 16 (by simp)
  have h24 := hwords 24 (by simp)
  have h32 := hwords 32 (by simp)
  simp only [Nat.add_zero] at h0
  unfold logOwnedIvls logRecordIvls
  rw [h0, h8, h16, h24, h32, haddr]

theorem evmInvAt_of_head_log_store_fc {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    {p' cap' log : Nat}
    (hAs : ArenaReady s)
    (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (hGp : GuestInv post)
    (hglob : post.globals = s.globals)
    (hbe : post.be = s.be)
    (harr_cases : (p', 8 * cap') = frameLogs s (globN s "ev", globN s "cur_cont") ∨
      (Inside (p', 8 * cap') sourceBase (globN s "heap_ptr") ∧
        WordsOK s (p', 8 * cap') ∧
        (∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, Disj (p', 8 * cap') o) ∧
        (∀ t ∈ S, ∀ o ∈ htabFootprint s t, Disj (p', 8 * cap') o) ∧
        (∀ o ∈ fixedObjects s, Disj (p', 8 * cap') o) ∧
        AvoidsTries s S [(p', 8 * cap')] ∧
        (∀ ec ∈ evmChain s, Disj (memW s (ec.1 + 112), 176) (p', 8 * cap')) ∧
        (∀ o ∈ logOwnedIvls s log, Disj (p', 8 * cap') o)))
    (hcap_pos : 1 ≤ cap')
    (hlen_le : memW s (memW s (globN s "ev" + 88) + 8) + 1 ≤ cap')
    (hmem_out : ∀ x : BitVec 64,
      let l0 := memW s (globN s "ev" + 88)
      let n0 := memW s (l0 + 8)
      x ≠ BitVec.ofNat 64 l0 →
      x ≠ BitVec.ofNat 64 (l0 + 8) →
      x ≠ BitVec.ofNat 64 (l0 + 16) →
      x ≠ BitVec.ofNat 64 (p' + 8 * n0) →
      post.memory x = s.memory x)
    (hl0_post : memW post (memW s (globN s "ev" + 88)) = p')
    (hl8_post : memW post (memW s (globN s "ev" + 88) + 8) =
      memW s (memW s (globN s "ev" + 88) + 8) + 1)
    (hl16_post : memW post (memW s (globN s "ev" + 88) + 16) = cap')
    (hslot_post : memW post (p' + 8 * memW s (memW s (globN s "ev" + 88) + 8)) = log)
    (hprefix_s : ∀ i < memW s (memW s (globN s "ev" + 88) + 8),
      memW s (p' + 8 * i) =
        memW s (memW s (memW s (globN s "ev" + 88)) + 8 * i))
    (_hlog_wa : WordAt s log)
    (hlog_ok : LogEntryOK s log)
    (hlog_pw : (logOwnedIvls s log).Pairwise Disj)
    (hlog_disj_fo : ∀ ec ∈ evmChain s, ∀ o1 ∈ logOwnedIvls s log,
      ∀ o2 ∈ frameObjects s ec, Disj o1 o2)
    (hlog_disj_ht : ∀ o ∈ logOwnedIvls s log, ∀ t ∈ S,
      ∀ j ∈ htabFootprint s t, Disj o j)
    (hlog_disj_fix : ∀ o ∈ logOwnedIvls s log,
      ∀ j ∈ fixedObjects s, Disj o j)
    (hlog_avoids : AvoidsTries s S (logOwnedIvls s log))
    (hlog_disj_msg : ∀ o ∈ logOwnedIvls s log,
      ∀ ec ∈ evmChain s, Disj (memW s (ec.1 + 112), 176) o) :
    ArenaReady post ∧
    InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt post S ∧
    evmChain post = evmChain s ∧
    OpDispatchSpec.evmR post = OpDispatchSpec.evmR s ∧
    fixedObjects post = fixedObjects s ∧
    (∀ t ∈ S, htabFootprint post t = htabFootprint s t) ∧
    (∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec ∧
      memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
      memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧
      memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧
      memW post (ec.1 + 112) = memW s (ec.1 + 112) ∧
      memW post (ec.2 + 56) = memW s (ec.2 + 56)) ∧
    frameLogs post (globN s "ev", globN s "cur_cont") = (p', 8 * cap') ∧
    (∀ ec ∈ (evmChain s).tail,
      frameLogs post ec = frameLogs s ec ∧
      frameObjects post ec = frameObjects s ec) ∧
    frameObjects post (globN s "ev", globN s "cur_cont") =
      [(globN s "ev", 280), (globN s "cur_cont", 104),
       (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232)),
       (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)),
       (memW s (globN s "ev" + 88), 24), (p', 8 * cap'),
       frameRet s (globN s "ev", globN s "cur_cont")] ++
      frameLogObjects s (globN s "ev", globN s "cur_cont") ++
      logOwnedIvls s log := by
  obtain ⟨hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, hAT, hMarks, hRoles, hGas⟩ := hInv
  obtain ⟨Nd_old, hTr_old, hAT_old⟩ := hAT
  obtain ⟨Nd_at, hTr_at, hAT_at, harr_nodes⟩ :
      ∃ Nd, TriesTypedWith s S Nd ∧
        (∀ o ∈ ((evmChain s).map (frameObjects s)).flatten,
          ∀ j ∈ nodeExtents s Nd, Disj o j) ∧
        (∀ j ∈ nodeExtents s Nd, Disj (p', 8 * cap') j) := by
    rcases harr_cases with heq | ⟨_, _, _, _, _, ⟨Nd_p, hTr_p, hd_p⟩, _⟩
    · refine ⟨Nd_old, hTr_old, hAT_old, fun j hj => ?_⟩
      rw [heq]
      exact hAT_old _ (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨_, by
        unfold evmChain; exact List.mem_cons_self, rfl⟩,
        by simp [frameObjects]⟩) j hj
    · obtain ⟨hTr_i, hsub_i⟩ := R11Shards.triesTypedWith_inter hTr_old hTr_p
      exact ⟨_, hTr_i, fun o ho j hj => hAT_old o ho j (hsub_i j hj).1,
        fun j hj => hd_p _ (by simp) j (hsub_i j hj).2⟩
  have hWT : InitECandidate.Solver.Wave8Contracts.M23.WorldTypedWith s S Nd_at :=
    ⟨hW.1, hW.2.1, hW.2.2.1, hTr_at⟩
  set e0 := globN s "ev"
  set c0 := globN s "cur_cont"
  set l0 := memW s (e0 + 88)
  set n0 := memW s (l0 + 8)
  have hch_cons : ∃ tl, evmChain s = (e0, c0) :: tl := ⟨_, rfl⟩
  obtain ⟨chTail, hch_eq⟩ := hch_cons
  have hhead_mem : (e0, c0) ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_self
  have hhead_FW := hFW_all _ hhead_mem
  obtain ⟨_, _, hb88, hfob_head⟩ := InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hAs.2 hhead_FW
  dsimp only at hb88
  have hl0_in_fs : (l0, 24) ∈ frameScratch s (e0, c0) := by simp [frameScratch, l0]
  have hl0_wok : WordsOK s (l0, 24) := (hhead_FW.1 (l0, 24) hl0_in_fs).2
  have hl0_8 : l0 % 8 = 0 := hl0_wok.1
  have hl0_fo : (l0, 24) ∈ frameObjects s (e0, c0) := by simp [frameObjects, l0]
  have hfl0_fo : frameLogs s (e0, c0) ∈ frameObjects s (e0, c0) := by simp [frameObjects]
  have harr_alloc_wok :
      (Inside (p', 8 * cap') sourceBase (globN s "heap_ptr") ∨
        Inside (p', 8 * cap') (globN s "scratch_ptr") scratchEnd) ∧
      WordsOK s (p', 8 * cap') := by
    rcases harr_cases with heq | ⟨hin, hw, _⟩
    · rw [heq]; exact ⟨hhead_FW.2.2.2.2.2.2.2.2.2.2.2.2.1, hhead_FW.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
    · exact ⟨Or.inl hin, hw⟩
  have harr_wok : WordsOK s (p', 8 * cap') := harr_alloc_wok.2
  have hp'_8 : p' % 8 = 0 := harr_wok.1
  have harr_bnd : p' + 8 * cap' ≤ 2 ^ 64 :=
    InitECandidate.Solver.Wave8Contracts.M23.allocated_le_2pow64 hAs.2 harr_alloc_wok.1
  have hn1_lt28 : n0 + 1 < 2 ^ 28 := by
    rcases harr_alloc_wok.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hhlim := hAs.2.2.1
      rw [R11Shards.sourceBase_val] at h1; rw [R11Shards.heapLimit_val] at hhlim
      dsimp only at h1 h2; omega
    · have hs1 := hAs.2.2.2.1; have hs2 := hAs.2.2.2.2.1
      rw [R11Shards.scratchStart_val] at hs1; rw [R11Shards.scratchEnd_val] at h2
      dsimp only at h1 h2; omega
  have hdom_eq : post.memaddrs = s.memaddrs := hGp.memaddrs.trans hAs.1.memaddrs.symm
  have hl0_dom0 : s.memaddrs (BitVec.ofNat 64 l0) := by
    obtain ⟨_, hdom, _⟩ := hl0_wok.2.2 0 (by omega); simpa using hdom
  have hl0_dom8 : s.memaddrs (BitVec.ofNat 64 (l0 + 8)) := by
    obtain ⟨_, hdom, _⟩ := hl0_wok.2.2 1 (by omega); simpa using hdom
  have hl0_dom16 : s.memaddrs (BitVec.ofNat 64 (l0 + 16)) := by
    obtain ⟨_, hdom, _⟩ := hl0_wok.2.2 2 (by omega); simpa using hdom
  have hslot_dom : s.memaddrs (BitVec.ofNat 64 (p' + 8 * n0)) := by
    obtain ⟨_, hdom, _⟩ := harr_wok.2.2 n0 (by dsimp only; omega); exact hdom
  have heff : InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect s post
      [(l0, 24), (p', 8 * cap')] := by
    refine ⟨hGp.code.trans hAs.1.code.symm, hdom_eq,
      hGp.shMemaddrs.trans hAs.1.shMemaddrs.symm,
      hGp.baseAddr.trans hAs.1.baseAddr.symm, hbe, hglob, ?_, ?_, ?_⟩
    · intro a hna
      exact hmem_out a (fun h => hna (h ▸ hl0_dom0)) (fun h => hna (h ▸ hl0_dom8))
        (fun h => hna (h ▸ hl0_dom16)) (fun h => hna (h ▸ hslot_dom))
    · intro a ha
      refine hmem_out a ?_ ?_ ?_ ?_
      · intro rfl
        have htn : (BitVec.ofNat 64 l0).toNat = l0 := Nat.mod_eq_of_lt (by omega)
        exact ha (l0, 24) (by simp) ⟨by rw [htn]; omega, by rw [htn]; omega⟩
      · intro rfl
        have htn : (BitVec.ofNat 64 (l0 + 8)).toNat = l0 + 8 := Nat.mod_eq_of_lt (by omega)
        exact ha (l0, 24) (by simp) ⟨by rw [htn]; omega, by rw [htn]; omega⟩
      · intro rfl
        have htn : (BitVec.ofNat 64 (l0 + 16)).toNat = l0 + 16 := Nat.mod_eq_of_lt (by omega)
        exact ha (l0, 24) (by simp) ⟨by rw [htn]; omega, by rw [htn]; omega⟩
      · intro rfl
        have htn : (BitVec.ofNat 64 (p' + 8 * n0)).toNat = p' + 8 * n0 := Nat.mod_eq_of_lt (by omega)
        exact ha (p', 8 * cap') (by simp) ⟨by rw [htn]; omega, by rw [htn]; omega⟩
    · intro b hb hno
      unfold memB
      have hal_b : (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := by
        rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
      rw [hmem_out (panByteAlignHOL (BitVec.ofNat 64 b)) ?_ ?_ ?_ ?_, hbe]
      · intro heq
        have := congrArg BitVec.toNat heq
        rw [hal_b, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact hno (l0, 24) (by simp) ⟨by dsimp only; omega, by dsimp only; omega⟩
      · intro heq
        have := congrArg BitVec.toNat heq
        rw [hal_b, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact hno (l0, 24) (by simp) ⟨by dsimp only; omega, by dsimp only; omega⟩
      · intro heq
        have := congrArg BitVec.toNat heq
        rw [hal_b, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact hno (l0, 24) (by simp) ⟨by dsimp only; omega, by dsimp only; omega⟩
      · intro heq
        have := congrArg BitVec.toNat heq
        rw [hal_b, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact hno (p', 8 * cap') (by simp) ⟨by dsimp only; omega, by dsimp only; omega⟩
  have hRl8 : ∀ x ∈ ([(l0, 24), (p', 8 * cap')] : List Ivl), x.1 % 8 = 0 := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hl0_8
    · exact hp'_8
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, hglob]
  have hApost : ArenaReady post := ⟨hGp, arenaOK_congr hglob hAs.2⟩
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq]
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq]
  have hfo_disj_wti : ∀ o ∈ frameObjects s (e0, c0),
      ∀ i ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Nd_at,
      i.2 = 0 ∨ Disj o i := by
    intro o ho i hi
    unfold InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls at hi
    simp only [List.mem_append] at hi
    rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
      exact Or.inr ((hFO_disj _ hhead_mem _ ho).1 t ht i hfp)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
      exact Or.inr ((hFO_disj _ hhead_mem _ ho).2 _
        (InitECandidate.Solver.Wave8Contracts.M23.typedRec_in_fixedObjects s hr))
    · simp only [List.mem_singleton] at h3; subst h3
      have hfix_j : (if globN s "journal_cap" = 0 then 0 else globN s "journal",
          32 * globN s "journal_cap") ∈ fixedObjects s := by
        unfold fixedObjects
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
      exact Or.inr ((hFO_disj _ hhead_mem _ ho).2 _ hfix_j)
    · exact Or.inr ((hFO_disj _ hhead_mem _ ho).2 _
        (InitECandidate.Solver.Wave8Contracts.M23.blockOut_in_fixedObjects h4))
    · exact Or.inr ((hFO_disj _ hhead_mem _ ho).2 _
        (InitECandidate.Solver.Wave8Contracts.M23.bal_in_fixedObjects h5))
    · exact Or.inr (hAT_at _ (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨_, hhead_mem, rfl⟩, ho⟩) i h6)
  have harr_disj_wti : ∀ i ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Nd_at,
      i.2 = 0 ∨ Disj (p', 8 * cap') i := by
    rcases harr_cases with heq | ⟨_, _, _, hd_ht, hd_fix, _, _⟩
    · intro i hi; rw [heq]; exact hfo_disj_wti _ hfl0_fo i hi
    · intro i hi
      unfold InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls at hi
      simp only [List.mem_append] at hi
      rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
      · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
        exact Or.inr (hd_ht t ht i hfp)
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
        exact Or.inr (hd_fix _ (InitECandidate.Solver.Wave8Contracts.M23.typedRec_in_fixedObjects s hr))
      · simp only [List.mem_singleton] at h3; subst h3
        have hfix_j : (if globN s "journal_cap" = 0 then 0 else globN s "journal",
            32 * globN s "journal_cap") ∈ fixedObjects s := by
          unfold fixedObjects
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
        exact Or.inr (hd_fix _ hfix_j)
      · exact Or.inr (hd_fix _ (InitECandidate.Solver.Wave8Contracts.M23.blockOut_in_fixedObjects h4))
      · exact Or.inr (hd_fix _ (InitECandidate.Solver.Wave8Contracts.M23.bal_in_fixedObjects h5))
      · exact Or.inr (harr_nodes i h6)
  have hcell : InitECandidate.Solver.Wave8Contracts.M23.SameTypedCells s post S Nd_at :=
    InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect.sameTypedCells
      (Rl := []) (extra := [(l0, 24), (p', 8 * cap')]) hAs.1.memaddrs hWT
      (fun _ h => by simp at h)
      (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact hfo_disj_wti _ hl0_fo
        · exact harr_disj_wti)
      (by simpa using heff)
  have hfeq := InitECandidate.Solver.Wave8Contracts.M23.fixedObjects_eq_of_nonHeapGlobalsKept
    hAs.2 hWT.1 hWT.2.2.1 hcell (fun name _ _ _ => by rw [hglob])
  have hFT_post := InitECandidate.Solver.Wave8Contracts.M23.fixedTyped_of_eq hApost hWT.2.2.1 hh hsc hfeq
  obtain ⟨hWT_post, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.worldTypedWith_congr_w1 hAs hApost hh hsc
    (fun g _ => hglob_eq g) hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hW_post : WorldTyped post S :=
    ⟨hWT_post.1, hWT_post.2.1, hWT_post.2.2.1, Nd_at, hWT_post.2.2.2⟩
  have hpw_head_tail :
      (frameObjects s (e0, c0)).Pairwise Disj ∧
      (∀ o1 ∈ frameObjects s (e0, c0),
        ∀ ec ∈ chTail, ∀ o2 ∈ frameObjects s ec, Disj o1 o2) := by
    have hpw := hFO_pw
    rw [hch_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
    refine ⟨hpw.1, fun o1 ho1 ec hec o2 ho2 => hpw.2.2 o1 ho1 o2 ?_⟩
    exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, hec, rfl⟩, ho2⟩
  have hhead_pw_cons := hpw_head_tail.1
  unfold frameObjects at hhead_pw_cons
  obtain ⟨hd_e0, hpw1⟩ := List.pairwise_cons.1 hhead_pw_cons
  obtain ⟨hd_c0, hpw2⟩ := List.pairwise_cons.1 hpw1
  obtain ⟨hd_stk, hpw3⟩ := List.pairwise_cons.1 hpw2
  obtain ⟨hd_mem, hpw4⟩ := List.pairwise_cons.1 hpw3
  obtain ⟨hd_l0, hpw5⟩ := List.pairwise_cons.1 hpw4
  obtain ⟨hd_fl0, hpw6⟩ := List.pairwise_cons.1 hpw5
  obtain ⟨hd_ret0, hpw_flo0⟩ := List.pairwise_cons.1 hpw6
  have hl0_disj_arr : Disj (l0, 24) (p', 8 * cap') := by
    rcases harr_cases with heq | ⟨_, _, hd_fo, _⟩
    · rw [heq]; exact hd_l0 _ (by simp)
    · exact disj_symm_fc (hd_fo _ hhead_mem _ hl0_fo)
  have hdisj_Rl_head_nonlog : ∀ o ∈
      ([(e0, 280), (c0, 104), (memW s (e0 + 8), 32 * memW s (e0 + 232)),
        (memW s (e0 + 24), memW s (e0 + 40)), frameRet s (e0, c0)] ++
       frameLogObjects s (e0, c0)),
      ∀ x ∈ ([(l0, 24), (p', 8 * cap')] : List Ivl), Disj x o := by
    intro o ho x hx
    have ho_fo : o ∈ frameObjects s (e0, c0) := by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with (rfl | rfl | rfl | rfl | rfl) | hflo
      · simp [frameObjects]
      · simp [frameObjects]
      · simp [frameObjects]
      · simp [frameObjects]
      · simp [frameObjects]
      · unfold frameObjects; exact List.mem_append_right _ hflo
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with (rfl | rfl | rfl | rfl | rfl) | hflo
      · exact disj_symm_fc (hd_e0 _ (by simp [l0]))
      · exact disj_symm_fc (hd_c0 _ (by simp [l0]))
      · exact disj_symm_fc (hd_stk _ (by simp [l0]))
      · exact disj_symm_fc (hd_mem _ (by simp [l0]))
      · exact hd_l0 _ (by simp)
      · exact hd_l0 _ (by simp [hflo])
    · rcases harr_cases with heq | ⟨_, _, hd_fo, _⟩
      · rw [heq]
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with (rfl | rfl | rfl | rfl | rfl) | hflo
        · exact disj_symm_fc (hd_e0 _ (by simp))
        · exact disj_symm_fc (hd_c0 _ (by simp))
        · exact disj_symm_fc (hd_stk _ (by simp))
        · exact disj_symm_fc (hd_mem _ (by simp))
        · exact hd_fl0 _ (by simp)
        · exact hd_fl0 _ (by simp [hflo])
      · exact hd_fo _ hhead_mem _ ho_fo
  have hdisj_Rl_tail : ∀ ec ∈ chTail, ∀ o ∈ frameObjects s ec,
      ∀ x ∈ ([(l0, 24), (p', 8 * cap')] : List Ivl), Disj x o := by
    intro ec htail o ho x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hpw_head_tail.2 _ hl0_fo ec htail o ho
    · rcases harr_cases with heq | ⟨_, _, hd_fo, _⟩
      · rw [heq]; exact hpw_head_tail.2 _ hfl0_fo ec htail o ho
      · exact hd_fo ec (by rw [hch_eq]; exact List.mem_cons_of_mem _ htail) o ho
  have hrec_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨hb1, hb2, _, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hAs.2 hFW
    have he1_8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
    have he2_8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · exact ⟨fun k hk hk8 => R14Shards.OpHandlersA.memW_eq_of_disj_eff heff hRl8 hb1 he1_8 hk8 hk
        (hdisj_Rl_head_nonlog (e0, 280) (by simp)),
        fun k hk hk8 => R14Shards.OpHandlersA.memW_eq_of_disj_eff heff hRl8 hb2 he2_8 hk8 hk
          (hdisj_Rl_head_nonlog (c0, 104) (by simp))⟩
    · exact ⟨fun k hk hk8 => R14Shards.OpHandlersA.memW_eq_of_disj_eff heff hRl8 hb1 he1_8 hk8 hk
        (hdisj_Rl_tail ec htail (ec.1, 280) (by simp [frameObjects])),
        fun k hk hk8 => R14Shards.OpHandlersA.memW_eq_of_disj_eff heff hRl8 hb2 he2_8 hk8 hk
          (hdisj_Rl_tail ec htail (ec.2, 104) (by simp [frameObjects]))⟩
  have htail_l88_eq : ∀ ec ∈ chTail, ∀ k, k + 8 ≤ 24 → k % 8 = 0 →
      memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k) := by
    intro ec htail k hk hk8
    have hec : ec ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ htail
    have hFW := hFW_all ec hec
    obtain ⟨_, _, hb88_t, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hAs.2 hFW
    have he88_8 : (memW s (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2.1
    exact R14Shards.OpHandlersA.memW_eq_of_disj_eff heff hRl8 hb88_t he88_8 hk8 hk
      (hdisj_Rl_tail ec htail (memW s (ec.1 + 88), 24) (by simp [frameObjects]))
  have hchain_aux : ∀ (fuel e c : Nat),
      (∀ ec ∈ evmChainFrom s fuel e c, ec ∈ evmChain s) →
      evmChainFrom post fuel e c = evmChainFrom s fuel e c := by
    intro fuel; induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro e c hsub
      have hec : (e, c) ∈ evmChain s := hsub (e, c) (by simp [evmChainFrom])
      obtain ⟨_, hc_eq⟩ := hrec_eq (e, c) hec
      have hc16 := hc_eq 16 (by omega) (by omega)
      have hc0 : memW post c = memW s c := by simpa using hc_eq 0 (by omega) (by omega)
      have hc8 := hc_eq 8 (by omega) (by omega)
      simp only [evmChainFrom, hc16, hc0, hc8]
      split
      · rfl
      · rename_i hne16
        rw [ih]; intro ec' hec'; exact hsub ec' (by simp [evmChainFrom, hne16, hec'])
  have hchain_eq : evmChain post = evmChain s := by
    unfold evmChain; rw [hglob_eq "ev", hglob_eq "cur_cont"]
    exact hchain_aux _ _ _ (fun _ h => h)
  have hframeLogs_head : frameLogs post (e0, c0) = (p', 8 * cap') := by
    obtain ⟨he_eq, _⟩ := hrec_eq (e0, c0) hhead_mem
    unfold frameLogs; dsimp only
    rw [he_eq 88 (by omega) (by decide)]
    change (memW post l0, 8 * memW post (l0 + 16)) = (p', 8 * cap')
    rw [hl0_post, hl16_post]
  have hframeLogs_tail : ∀ ec ∈ chTail, frameLogs post ec = frameLogs s ec := by
    intro ec htail
    have hec : ec ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ htail
    obtain ⟨he_eq, _⟩ := hrec_eq ec hec
    have h88_eq := htail_l88_eq ec htail
    unfold frameLogs
    rw [he_eq 88 (by omega) (by decide),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega)]
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec
    obtain ⟨he_eq, _⟩ := hrec_eq ec hec
    unfold frameRet
    rw [he_eq 216 (by omega) (by decide), he_eq 144 (by omega) (by decide)]
  have hprefix_post : ∀ i < n0,
      memW post (p' + 8 * i) = memW s (memW s l0 + 8 * i) := by
    intro i hi
    rw [← hprefix_s i hi]
    unfold memW
    rw [hmem_out (BitVec.ofNat 64 (p' + 8 * i)) ?_ ?_ ?_ ?_]
    · intro heq
      have := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      rcases hl0_disj_arr with h0 | h0 | h1 | h2 <;> dsimp only at * <;> omega
    · intro heq
      have := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      rcases hl0_disj_arr with h0 | h0 | h1 | h2 <;> dsimp only at * <;> omega
    · intro heq
      have := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      rcases hl0_disj_arr with h0 | h0 | h1 | h2 <;> dsimp only at * <;> omega
    · intro heq
      have := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      omega
  have hlog_words_post : ∀ off ∈ ([0, 8, 16, 24, 32] : List Nat),
      memW post (log + off) = memW s (log + off) := by
    intro off hoff
    have hoff_p : off + 8 ≤ 40 ∧ off % 8 = 0 := by revert off hoff; decide
    have hlog40_mem : (log, 40) ∈ logOwnedIvls s log := by
      unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩
    have hlog40_bnd : log + 40 ≤ 2 ^ 64 :=
      InitECandidate.Solver.Wave8Contracts.M23.allocated_le_2pow64 hAs.2 (Or.inl hlog_ok.2.1)
    have hlog_8 : log % 8 = 0 := hlog_ok.1.1
    exact R14Shards.OpHandlersA.memW_eq_of_disj_eff heff hRl8 hlog40_bnd hlog_8 hoff_p.2 hoff_p.1
      (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact disj_symm_fc (hlog_disj_fo _ hhead_mem _ hlog40_mem _ hl0_fo)
        · rcases harr_cases with heq | ⟨_, _, _, _, _, _, _, hd_lo⟩
          · rw [heq]; exact disj_symm_fc (hlog_disj_fo _ hhead_mem _ hlog40_mem _ hfl0_fo)
          · exact hd_lo _ hlog40_mem)
  have hlog_ok_post : LogEntryOK post log :=
    logEntryOK_transport_fc hlog_ok hdom_eq hh hlog_words_post
  have hlog_ivls_post : logOwnedIvls post log = logOwnedIvls s log :=
    logOwnedIvls_transport_fc (hglob_eq "vm_system_address") hlog_words_post
  have hhead_lr_eq : ∀ i (hi : i < n0) off, off + 8 ≤ 40 → off % 8 = 0 →
      memW post (memW s (memW s l0 + 8 * i) + off) =
        memW s (memW s (memW s l0 + 8 * i) + off) := by
    intro i hi off hoff hoff8
    have hlr_flo : (memW s (memW s l0 + 8 * i), 40) ∈ frameLogObjects s (e0, c0) := by
      unfold frameLogObjects; dsimp only
      exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by
        unfold logOwnedIvls logRecordIvls
        exact List.mem_filter.2 ⟨by simp [l0], by simp⟩⟩
    have hlr_in : (memW s (memW s l0 + 8 * i), 40) ∈ frameObjects s (e0, c0) := by
      unfold frameObjects; exact List.mem_append_right _ hlr_flo
    have hlr_b : memW s (memW s l0 + 8 * i) + 40 ≤ 2 ^ 64 := by
      rcases hfob_head _ hlr_in with h0 | hb
      · dsimp only at h0; omega
      · exact hb
    have hlr_8 : (memW s (memW s l0 + 8 * i)) % 8 = 0 := by
      rcases hhead_FW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
      · have he88_in := (hhead_FW.1 (l0, 24) hl0_in_fs).1.1
        have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
        rw [R11Shards.scratchStart_val] at h1
        change l0 = 0 at hz; dsimp only at he88_in; omega
      · exact (hent i hi).2.1.1
    exact R14Shards.OpHandlersA.memW_eq_of_disj_eff heff hRl8 hlr_b hlr_8 hoff8 hoff
      (hdisj_Rl_head_nonlog _ (List.mem_append_right _ hlr_flo))
  have he0_88_post : memW post (e0 + 88) = l0 :=
    (hrec_eq (e0, c0) hhead_mem).1 88 (by omega) (by decide)
  have hflo_head_post :
      frameLogObjects post (e0, c0) =
        frameLogObjects s (e0, c0) ++ logOwnedIvls s log := by
    refine frameLogObjects_append_fc
      (by dsimp only; rw [he0_88_post]; exact hl8_post) ?_ ?_ hlog_ivls_post
    · intro i hi
      dsimp only at hi ⊢
      rw [he0_88_post, hl0_post, hprefix_post i hi]
      refine logOwnedIvls_transport_fc (hglob_eq "vm_system_address") (fun off hoff => ?_)
      have hp : off + 8 ≤ 40 ∧ off % 8 = 0 := by revert off hoff; decide
      exact hhead_lr_eq i hi off hp.1 hp.2
    · dsimp only; rw [he0_88_post, hl0_post]; exact hslot_post
  have hlogs_ok_head_post : LogsListOK post (memW post (e0 + 88)) := by
    rw [he0_88_post]
    rcases hhead_FW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨hw_l, hal_l, _, _, hent⟩
    · have he88_in := (hhead_FW.1 (l0, 24) hl0_in_fs).1.1
      have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
      rw [R11Shards.scratchStart_val] at h1
      change l0 = 0 at hz; dsimp only at he88_in; omega
    · right
      refine ⟨(R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 hw_l,
        InitECandidate.Solver.Wave8Contracts.M23.allocated_mono hh hsc hal_l,
        by rw [hl8_post]; exact hn1_lt28,
        by rw [hl8_post, hl16_post]; exact hlen_le, fun i hi => ?_⟩
      rw [hl8_post] at hi; rw [hl0_post]
      have hwa_slot : WordAt post (p' + 8 * i) :=
        (R14Shards.OpHandlersA.wordAt_congr_dom hdom_eq).2
          (harr_wok.2.2 i (by dsimp only; omega))
      by_cases hlt : i < n0
      · obtain ⟨_, hle⟩ := hent i hlt
        rw [hprefix_post i hlt]
        refine ⟨hwa_slot, ?_⟩
        refine logEntryOK_transport_fc hle hdom_eq hh (fun off hoff => ?_)
        have hp : off + 8 ≤ 40 ∧ off % 8 = 0 := by revert off hoff; decide
        exact hhead_lr_eq i hlt off hp.1 hp.2
      · have hi_eq : i = n0 := by omega
        subst hi_eq
        rw [hslot_post]
        exact ⟨hwa_slot, hlog_ok_post⟩
  have htail_logs_congr : ∀ ec ∈ chTail,
      frameLogObjects post ec = frameLogObjects s ec ∧ LogsListOK post (memW post (ec.1 + 88)) := by
    intro ec htail
    have hec : ec ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ htail
    have hFW := hFW_all ec hec
    obtain ⟨_, _, _, hfob⟩ := InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hAs.2 hFW
    obtain ⟨he_eq, _⟩ := hrec_eq ec hec
    have h88_eq := htail_l88_eq ec htail
    have hl0_t : memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) := by
      simpa using h88_eq 0 (by omega) (by omega)
    have hl8_t : memW post (memW s (ec.1 + 88) + 8) = memW s (memW s (ec.1 + 88) + 8) :=
      h88_eq 8 (by omega) (by omega)
    have hl16_t : memW post (memW s (ec.1 + 88) + 16) = memW s (memW s (ec.1 + 88) + 16) :=
      h88_eq 16 (by omega) (by omega)
    have harr_eq : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
        memW post (memW s (memW s (ec.1 + 88)) + 8 * i) = memW s (memW s (memW s (ec.1 + 88)) + 8 * i) := by
      intro i hi
      have hfl_in : frameLogs s ec ∈ frameObjects s ec := by simp [frameObjects]
      have hlen_le_t : memW s (memW s (ec.1 + 88) + 8) ≤ memW s (memW s (ec.1 + 88) + 16) :=
        hFW.2.2.2.2.2.2.2.2.2.2.2.1
      have hfl_b : (frameLogs s ec).1 + (frameLogs s ec).2 ≤ 2 ^ 64 := by
        rcases hfob _ hfl_in with h0 | hb
        · unfold frameLogs at h0; dsimp only at h0; omega
        · exact hb
      have hfl_8 : (memW s (memW s (ec.1 + 88))) % 8 = 0 := hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
      exact R14Shards.OpHandlersA.memW_eq_of_disj_eff heff hRl8 hfl_b hfl_8 (by omega)
        (by unfold frameLogs; dsimp only; omega)
        (hdisj_Rl_tail ec htail _ hfl_in)
    have hlr_eq : ∀ i (hi : i < memW s (memW s (ec.1 + 88) + 8)) off, off + 8 ≤ 40 → off % 8 = 0 →
        memW post (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + off) =
          memW s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + off) := by
      intro i hi off hoff hoff8
      have hlr_in : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40) ∈ frameObjects s ec := by
        unfold frameObjects; apply List.mem_append_right
        unfold frameLogObjects; dsimp only
        exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by
          unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
      have hlr_b : memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + 40 ≤ 2 ^ 64 := by
        rcases hfob _ hlr_in with h0 | hb
        · dsimp only at h0; omega
        · exact hb
      have hlr_8 : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) % 8 = 0 := by
        rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
        · have he88_in := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1.1
          have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
          rw [R11Shards.scratchStart_val] at h1; dsimp only at he88_in; omega
        · exact (hent i hi).2.1.1
      exact R14Shards.OpHandlersA.memW_eq_of_disj_eff heff hRl8 hlr_b hlr_8 hoff8 hoff
        (hdisj_Rl_tail ec htail _ hlr_in)
    refine ⟨?_, ?_⟩
    · unfold frameLogObjects; dsimp only
      rw [he_eq 88 (by omega) (by decide), hl8_t]
      apply List.flatMap_congr; intro i hi; rw [List.mem_range] at hi
      rw [hl0_t, harr_eq i hi]
      refine logOwnedIvls_transport_fc (hglob_eq "vm_system_address") (fun off hoff => ?_)
      have hp : off + 8 ≤ 40 ∧ off % 8 = 0 := by revert off hoff; decide
      exact hlr_eq i hi off hp.1 hp.2
    · rw [he_eq 88 (by omega) (by decide)]
      rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨hw_l, hal_l, hlt28_t, hle_cap_t, hent⟩
      · exact Or.inl hz
      · right
        refine ⟨(R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 hw_l,
          InitECandidate.Solver.Wave8Contracts.M23.allocated_mono hh hsc hal_l,
          by rw [hl8_t]; exact hlt28_t, by rw [hl8_t, hl16_t]; exact hle_cap_t, fun i hi => ?_⟩
        rw [hl8_t] at hi; rw [hl0_t]
        obtain ⟨hwa, hle⟩ := hent i hi
        rw [harr_eq i hi]
        refine ⟨(R14Shards.OpHandlersA.wordAt_congr_dom hdom_eq).2 hwa,
          logEntryOK_transport_fc hle hdom_eq hh (fun off hoff => ?_)⟩
        have hp : off + 8 ≤ 40 ∧ off % 8 = 0 := by revert off hoff; decide
        exact hlr_eq i hi off hp.1 hp.2
  have hfo_head :
      frameObjects post (e0, c0) =
        [(e0, 280), (c0, 104),
         (memW s (e0 + 8), 32 * memW s (e0 + 232)),
         (memW s (e0 + 24), memW s (e0 + 40)),
         (memW s (e0 + 88), 24), (p', 8 * cap'),
         frameRet s (e0, c0)] ++
        frameLogObjects s (e0, c0) ++
        logOwnedIvls s log := by
    obtain ⟨he_eq, _⟩ := hrec_eq (e0, c0) hhead_mem
    unfold frameObjects; dsimp only
    rw [he_eq 8 (by omega) (by decide), he_eq 232 (by omega) (by decide),
        he_eq 24 (by omega) (by decide), he_eq 40 (by omega) (by decide),
        he_eq 88 (by omega) (by decide),
        hframeLogs_head, hframeRet_eq (e0, c0) hhead_mem, hflo_head_post]
    simp only [List.cons_append, List.nil_append]
  have hfo_tail : ∀ ec ∈ chTail, frameObjects post ec = frameObjects s ec := by
    intro ec htail
    have hec : ec ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ htail
    obtain ⟨he_eq, _⟩ := hrec_eq ec hec
    unfold frameObjects
    rw [he_eq 8 (by omega) (by decide), he_eq 232 (by omega) (by decide),
        he_eq 24 (by omega) (by decide), he_eq 40 (by omega) (by decide),
        he_eq 88 (by omega) (by decide),
        hframeLogs_tail ec htail, hframeRet_eq ec hec, (htail_logs_congr ec htail).1]
  have hfo_head_mem : ∀ o ∈ frameObjects post (e0, c0),
      o ∈ frameObjects s (e0, c0) ∨ o = (p', 8 * cap') ∨ o ∈ logOwnedIvls s log := by
    intro o ho
    rw [hfo_head] at ho
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hflo) | hlo
    · exact Or.inl (by simp [frameObjects])
    · exact Or.inl (by simp [frameObjects])
    · exact Or.inl (by simp [frameObjects])
    · exact Or.inl (by simp [frameObjects])
    · exact Or.inl (by simp [frameObjects])
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (by simp [frameObjects])
    · exact Or.inl (by unfold frameObjects; exact List.mem_append_right _ hflo)
    · exact Or.inr (Or.inr hlo)
  have hfo_post_mem : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects post ec,
      (∃ ec' ∈ evmChain s, o ∈ frameObjects s ec') ∨
      o = (p', 8 * cap') ∨ o ∈ logOwnedIvls s log := by
    intro ec hec o ho
    have hec' := hec
    rw [hch_eq, List.mem_cons] at hec'
    rcases hec' with rfl | htail
    · rcases hfo_head_mem o ho with h1 | h2 | h3
      · exact Or.inl ⟨(e0, c0), hhead_mem, h1⟩
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr h3)
    · rw [hfo_tail ec htail] at ho
      exact Or.inl ⟨ec, hec, ho⟩
  have hframeScratch_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _⟩ := hrec_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega) (by decide), he_eq 232 (by omega) (by decide),
        he_eq 88 (by omega) (by decide)]
  have hframeRoleSlots_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots; apply List.flatMap_congr; intro ec hec
    obtain ⟨he_eq, _⟩ := hrec_eq ec hec
    rw [he_eq 136 (by omega) (by decide), he_eq 168 (by omega) (by decide),
        he_eq 176 (by omega) (by decide)]
  have hfp_eq_all : ∀ t ∈ S, htabFootprint post t = htabFootprint s t :=
    fun t ht => InitECandidate.Solver.Wave8Contracts.M23.htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1
  have hR_eq : OpDispatchSpec.evmR post = OpDispatchSpec.evmR s := by
    unfold OpDispatchSpec.evmR; rw [hchain_eq]
    congr 1; apply List.map_congr_left; intro ec hec
    obtain ⟨he_eq, _⟩ := hrec_eq ec hec
    rw [he_eq 64 (by omega) (by decide), he_eq 192 (by omega) (by decide)]
  have htail_eq_s : (evmChain s).tail = chTail := by rw [hch_eq]; rfl
  refine ⟨hApost, ?_, hchain_eq, hR_eq, hfeq, hfp_eq_all, ?_, hframeLogs_head, ?_, hfo_head⟩
  · unfold InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt
    refine ⟨hW_post, ?_⟩
    dsimp only; rw [hchain_eq]
    refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨ec, hec, hk0⟩ := hch_last
      have hec_mem := List.mem_of_mem_getLast? hec
      exact ⟨ec, hec, by rw [(hrec_eq ec hec_mem).2 16 (by omega) (by omega)]; exact hk0⟩
    · intro ec hec
      obtain ⟨he_eq, _⟩ := hrec_eq ec hec
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩ := hFW_all ec hec
      have hmsg_ok : MsgOwned post S (memW post (ec.1 + 112)) := by
        rw [he_eq 112 (by omega) (by decide)]
        obtain ⟨hal_m, hw_m, hdt, hdf, hdfo, Nd_m, hTr_m, hdj_m⟩ := c17
        obtain ⟨hTr_int, hsub_int⟩ := R11Shards.triesTypedWith_inter hTr_at hTr_m
        set Ndi := Nd_at.filter (fun n => decide (n ∈ Nd_m))
        have hcell_i : InitECandidate.Solver.Wave8Contracts.M23.SameTypedCells s post S Ndi := by
          have hwti_sub : ∀ i ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Ndi,
              i ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Nd_at := by
            intro i hi; unfold InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls at hi ⊢
            rcases List.mem_append.1 hi with hpre | hne
            · exact List.mem_append_left _ hpre
            · apply List.mem_append_right; unfold nodeExtents at hne ⊢
              obtain ⟨n, hn, hnx⟩ := List.mem_flatMap.1 hne
              exact List.mem_flatMap.2 ⟨n, (List.mem_filter.1 hn).1, hnx⟩
          refine ⟨hcell.1, hcell.2.1, hcell.2.2.1, hcell.2.2.2.1,
            fun a ha ha8 ⟨i, hi, h1, h2⟩ => hcell.2.2.2.2.1 a ha ha8 ⟨i, hwti_sub i hi, h1, h2⟩,
            fun b hb ⟨i, hi, h1, h2⟩ => hcell.2.2.2.2.2 b hb ⟨i, hwti_sub i hi, h1, h2⟩⟩
        obtain ⟨hWT_i_post, _⟩ :=
          InitECandidate.Solver.Wave8Contracts.M23.worldTypedWith_congr_w1
            hAs hApost hh hsc (fun g _ => hglob_eq g) hcell_i
            ⟨hWT.1, hWT.2.1, hWT.2.2.1, hTr_int⟩
            ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
        refine ⟨InitECandidate.Solver.Wave8Contracts.M23.allocated_mono hh hsc hal_m,
          (R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 hw_m,
          fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact hdt t ht i hi,
          fun i hi => by rw [hfeq] at hi; exact hdf i hi,
          fun ec' hec' i hi => ?_,
          Ndi, hWT_i_post.2.2.2,
          fun o ho j hj => ?_⟩
        · rw [hchain_eq] at hec'
          rcases hfo_post_mem ec' hec' i hi with ⟨ec'', hec'', hi_s⟩ | rfl | hi_log
          · exact hdfo ec'' hec'' i hi_s
          · rcases harr_cases with heq_fl | ⟨_, _, _, _, _, _, hd_msg_p, _⟩
            · rw [heq_fl]; exact hdfo (e0, c0) hhead_mem _ hfl0_fo
            · exact hd_msg_p ec hec
          · exact hlog_disj_msg i hi_log ec hec
        · rw [InitECandidate.Solver.Wave8Contracts.M23.nodeExtents_eq hTr_int.1 hcell_i] at hj
          exact hdj_m o ho j (hsub_int j hj).2
      have hec_cases := hec
      rw [hch_eq, List.mem_cons] at hec_cases
      rcases hec_cases with rfl | htail
      · unfold FrameWF; dsimp only
        rw [he_eq 8 (by omega) (by decide), he_eq 232 (by omega) (by decide),
            he_eq 88 (by omega) (by decide), he_eq 24 (by omega) (by decide),
            he_eq 40 (by omega) (by decide),
            he_eq 32 (by omega) (by decide), he_eq 136 (by omega) (by decide),
            he_eq 168 (by omega) (by decide), he_eq 176 (by omega) (by decide),
            hl16_post, hl8_post,
            hframeLogs_head,
            he_eq 216 (by omega) (by decide), he_eq 144 (by omega) (by decide),
            hframeRet_eq (e0, c0) hhead_mem,
            hglob_eq "scratch_ptr", hglob_eq "frame_mem_ptr", hglob_eq "heap_ptr", hglob_eq "evm_empty"]
        rw [he_eq 88 (by omega) (by decide)] at hlogs_ok_head_post
        refine ⟨fun i hi => ⟨(c1 i hi).1, (R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 (c1 i hi).2⟩,
          c2, (R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 c3,
          c4, by rw [he_eq 16 (by omega) (by decide)]; exact c5, c6, c7, c8, c9, c10,
          hcap_pos, hlen_le,
          harr_alloc_wok.1, (R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 harr_wok,
          ?_, hlogs_ok_head_post, hmsg_ok⟩
        rcases c15 with h0 | ⟨hin, hw⟩
        · exact Or.inl h0
        · exact Or.inr ⟨hin, (R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 hw⟩
      · have h88_eq := htail_l88_eq ec htail
        have hlo_ok := (htail_logs_congr ec htail).2
        unfold FrameWF; dsimp only
        rw [he_eq 8 (by omega) (by decide), he_eq 232 (by omega) (by decide),
            he_eq 88 (by omega) (by decide), he_eq 24 (by omega) (by decide),
            he_eq 40 (by omega) (by decide),
            he_eq 32 (by omega) (by decide), he_eq 136 (by omega) (by decide),
            he_eq 168 (by omega) (by decide), he_eq 176 (by omega) (by decide),
            h88_eq 16 (by omega) (by omega), h88_eq 8 (by omega) (by omega),
            hframeLogs_tail ec htail,
            he_eq 216 (by omega) (by decide), he_eq 144 (by omega) (by decide),
            hframeRet_eq ec hec,
            hglob_eq "scratch_ptr", hglob_eq "frame_mem_ptr", hglob_eq "heap_ptr", hglob_eq "evm_empty"]
        rw [he_eq 88 (by omega) (by decide)] at hlo_ok
        refine ⟨fun i hi => ⟨(c1 i hi).1, (R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 (c1 i hi).2⟩,
          c2, (R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 c3,
          c4, by rw [he_eq 16 (by omega) (by decide)]; exact c5, c6, c7, c8, c9, c10, c11, c12,
          c13, (R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 c14, ?_, hlo_ok, hmsg_ok⟩
        rcases c15 with h0 | ⟨hin, hw⟩
        · exact Or.inl h0
        · exact Or.inr ⟨hin, (R14Shards.OpHandlersA.wordsOK_congr_dom hdom_eq).2 hw⟩
    · intro ec hec
      have hec_mem : ec ∈ evmChain s := List.mem_of_mem_tail hec
      unfold FrameRoom
      rw [(hrec_eq ec hec_mem).1 16 (by omega) (by decide),
          (hrec_eq ec hec_mem).1 232 (by omega) (by decide)]
      exact hFR_all ec hec
    · intro i hi
      have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
      have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
      rw [(hrec_eq _ hi0).2 80 (by omega) (by omega),
          (hrec_eq _ hi0).2 72 (by omega) (by omega),
          (hrec_eq _ hi1).1 40 (by omega) (by decide)]
      exact hRW i hi
    · rw [hch_eq, List.map_cons, List.flatten_cons, List.pairwise_append]
      have htail_map_eq : chTail.map (frameObjects post) = chTail.map (frameObjects s) :=
        List.map_congr_left hfo_tail
      rw [htail_map_eq]
      have hpw_tail : (chTail.map (frameObjects s)).flatten.Pairwise Disj := by
        have hpw := hFO_pw
        rw [hch_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
        exact hpw.2.1
      refine ⟨?_, hpw_tail, ?_⟩
      · rw [hfo_head]
        have hpw_pre :
            ([(e0, 280), (c0, 104),
              (memW s (e0 + 8), 32 * memW s (e0 + 232)),
              (memW s (e0 + 24), memW s (e0 + 40)),
              (memW s (e0 + 88), 24), (p', 8 * cap'),
              frameRet s (e0, c0)] ++
             frameLogObjects s (e0, c0)).Pairwise Disj := by
          rcases harr_cases with heq | ⟨_, _, hd_fo, _⟩
          · rw [heq]; exact hpw_head_tail.1
          · change List.Pairwise Disj
              ((e0, 280) :: (c0, 104) :: (memW s (e0 + 8), 32 * memW s (e0 + 232)) ::
               (memW s (e0 + 24), memW s (e0 + 40)) :: (memW s (e0 + 88), 24) ::
               (p', 8 * cap') :: frameRet s (e0, c0) :: frameLogObjects s (e0, c0))
            refine List.pairwise_cons.2 ⟨fun o ho => ?_, List.pairwise_cons.2 ⟨fun o ho => ?_,
              List.pairwise_cons.2 ⟨fun o ho => ?_, List.pairwise_cons.2 ⟨fun o ho => ?_,
              List.pairwise_cons.2 ⟨fun o ho => ?_, List.pairwise_cons.2 ⟨fun o ho => ?_,
              List.pairwise_cons.2 ⟨hd_ret0, hpw_flo0⟩⟩⟩⟩⟩⟩⟩
            · simp only [List.mem_cons] at ho
              rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | hflo
              · exact hd_e0 _ (by simp)
              · exact hd_e0 _ (by simp)
              · exact hd_e0 _ (by simp)
              · exact hd_e0 _ (by simp)
              · exact disj_symm_fc (hd_fo _ hhead_mem (e0, 280) (by simp [frameObjects]))
              · exact hd_e0 _ (by simp)
              · exact hd_e0 _ (by simp [hflo])
            · simp only [List.mem_cons] at ho
              rcases ho with rfl | rfl | rfl | rfl | rfl | hflo
              · exact hd_c0 _ (by simp)
              · exact hd_c0 _ (by simp)
              · exact hd_c0 _ (by simp)
              · exact disj_symm_fc (hd_fo _ hhead_mem (c0, 104) (by simp [frameObjects]))
              · exact hd_c0 _ (by simp)
              · exact hd_c0 _ (by simp [hflo])
            · simp only [List.mem_cons] at ho
              rcases ho with rfl | rfl | rfl | rfl | hflo
              · exact hd_stk _ (by simp)
              · exact hd_stk _ (by simp)
              · exact disj_symm_fc (hd_fo _ hhead_mem _ (by simp [frameObjects]))
              · exact hd_stk _ (by simp)
              · exact hd_stk _ (by simp [hflo])
            · simp only [List.mem_cons] at ho
              rcases ho with rfl | rfl | rfl | hflo
              · exact hd_mem _ (by simp)
              · exact disj_symm_fc (hd_fo _ hhead_mem _ (by simp [frameObjects]))
              · exact hd_mem _ (by simp)
              · exact hd_mem _ (by simp [hflo])
            · simp only [List.mem_cons] at ho
              rcases ho with rfl | rfl | hflo
              · exact disj_symm_fc (hd_fo _ hhead_mem _ hl0_fo)
              · exact hd_l0 _ (by simp)
              · exact hd_l0 _ (by simp [hflo])
            · simp only [List.mem_cons] at ho
              rcases ho with rfl | hflo
              · exact hd_fo _ hhead_mem _ (by simp [frameObjects])
              · exact hd_fo _ hhead_mem _ (by unfold frameObjects; exact List.mem_append_right _ hflo)
        refine List.pairwise_append.2 ⟨hpw_pre, hlog_pw, fun o1 ho1 o2 ho2 => ?_⟩
        have ho1_cases : o1 ∈ frameObjects s (e0, c0) ∨ o1 = (p', 8 * cap') := by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ho1
          rcases ho1 with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hflo
          · exact Or.inl (by simp [frameObjects])
          · exact Or.inl (by simp [frameObjects])
          · exact Or.inl (by simp [frameObjects])
          · exact Or.inl (by simp [frameObjects])
          · exact Or.inl (by simp [frameObjects])
          · exact Or.inr rfl
          · exact Or.inl (by simp [frameObjects])
          · exact Or.inl (by unfold frameObjects; exact List.mem_append_right _ hflo)
        rcases ho1_cases with ho1_s | rfl
        · exact disj_symm_fc (hlog_disj_fo _ hhead_mem o2 ho2 o1 ho1_s)
        · rcases harr_cases with heq | ⟨_, _, _, _, _, _, _, hd_lo⟩
          · rw [heq]; exact disj_symm_fc (hlog_disj_fo _ hhead_mem o2 ho2 _ hfl0_fo)
          · exact hd_lo o2 ho2
      · intro o1 ho1 o2 ho2
        obtain ⟨_, hmem_m, ho2_ec⟩ := List.mem_flatten.1 ho2
        obtain ⟨ec, htail, rfl⟩ := List.mem_map.1 hmem_m
        have hec : ec ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ htail
        rcases hfo_head_mem o1 ho1 with ho1_s | rfl | ho1_log
        · exact hpw_head_tail.2 o1 ho1_s ec htail o2 ho2_ec
        · rcases harr_cases with heq | ⟨_, _, hd_fo, _⟩
          · rw [heq]; exact hpw_head_tail.2 _ hfl0_fo ec htail o2 ho2_ec
          · exact hd_fo ec hec o2 ho2_ec
        · exact hlog_disj_fo ec hec o1 ho1_log o2 ho2_ec
    · intro ec hec o ho
      rw [hfeq]
      rcases hfo_post_mem ec hec o ho with ⟨ec', hec', ho_s⟩ | rfl | ho_log
      · exact ⟨fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact (hFO_disj ec' hec' o ho_s).1 t ht i hi,
          (hFO_disj ec' hec' o ho_s).2⟩
      · rcases harr_cases with heq | ⟨_, _, _, hd_ht, hd_fix, _⟩
        · rw [heq]
          exact ⟨fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact (hFO_disj _ hhead_mem _ hfl0_fo).1 t ht i hi,
            (hFO_disj _ hhead_mem _ hfl0_fo).2⟩
        · exact ⟨fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact hd_ht t ht i hi, hd_fix⟩
      · exact ⟨fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact hlog_disj_ht o ho_log t ht i hi,
          hlog_disj_fix o ho_log⟩
    · obtain ⟨Nd_l, hTr_l, hdj_l⟩ := hlog_avoids
      obtain ⟨hTr_al, hsub_al⟩ := R11Shards.triesTypedWith_inter hTr_at hTr_l
      set Ndx := Nd_at.filter (fun n => decide (n ∈ Nd_l))
      have hNdx_sub : ∀ n ∈ Ndx, n ∈ Nd_at := fun n hn => (List.mem_filter.1 hn).1
      have hcell_x : InitECandidate.Solver.Wave8Contracts.M23.SameTypedCells s post S Ndx := by
        have hwti_sub : ∀ i ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Ndx,
            i ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Nd_at := by
          intro i hi; unfold InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls at hi ⊢
          rcases List.mem_append.1 hi with hpre | hne
          · exact List.mem_append_left _ hpre
          · apply List.mem_append_right; unfold nodeExtents at hne ⊢
            obtain ⟨n, hn, hnx⟩ := List.mem_flatMap.1 hne
            exact List.mem_flatMap.2 ⟨n, hNdx_sub n hn, hnx⟩
        refine ⟨hcell.1, hcell.2.1, hcell.2.2.1, hcell.2.2.2.1,
          fun a ha ha8 ⟨i, hi, h1, h2⟩ => hcell.2.2.2.2.1 a ha ha8 ⟨i, hwti_sub i hi, h1, h2⟩,
          fun b hb ⟨i, hi, h1, h2⟩ => hcell.2.2.2.2.2 b hb ⟨i, hwti_sub i hi, h1, h2⟩⟩
      obtain ⟨hWT_x_post, _⟩ :=
        InitECandidate.Solver.Wave8Contracts.M23.worldTypedWith_congr_w1
          hAs hApost hh hsc (fun g _ => hglob_eq g) hcell_x
          ⟨hWT.1, hWT.2.1, hWT.2.2.1, hTr_al⟩
          ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
      refine ⟨Ndx, hWT_x_post.2.2.2, fun o ho j hj => ?_⟩
      rw [InitECandidate.Solver.Wave8Contracts.M23.nodeExtents_eq hTr_al.1 hcell_x] at hj
      obtain ⟨_, hmem_m, ho_ec⟩ := List.mem_flatten.1 ho
      obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hmem_m
      rcases hfo_post_mem ec hec o ho_ec with ⟨ec', hec', ho_s⟩ | rfl | ho_log
      · exact hAT_at o (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec', hec', rfl⟩, ho_s⟩)
          j (hsub_al j hj).1
      · exact harr_nodes j (hsub_al j hj).1
      · exact hdj_l o ho_log j (hsub_al j hj).2
    · have hworldRefs_eq : worldTableRefs post S = worldTableRefs s S := by
        unfold worldTableRefs recordSlots
        rw [hglob_eq "ws", hglob_eq "bs", hglob_eq "ts",
            show globalTableRoots.map (globN post) = globalTableRoots.map (globN s) by
              simp only [globalTableRoots, List.map, hglob_eq],
            InitECandidate.Solver.Wave8Contracts.M23.balRecords_eq hWT.1 hcell (hglob_eq "bal_accounts"),
            hglob_eq "journal_n", hglob_eq "journal"]
        have hws_sl : (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW post (globN s "ws" + k)) =
            (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW s (globN s "ws" + k)) := by
          split; · rfl
          rename_i hnz; apply List.map_congr_left; intro k hk
          exact InitECandidate.Solver.Wave8Contracts.M23.memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 40) (by decide) hnz
            (by simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl <;> omega)
        have hbs_sl : (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW post (globN s "bs" + k)) =
            (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW s (globN s "bs" + k)) := by
          split; · rfl
          rename_i hnz; apply List.map_congr_left; intro k hk
          exact InitECandidate.Solver.Wave8Contracts.M23.memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz
            (by simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
        have hts_sl : (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW post (globN s "ts" + k)) =
            (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW s (globN s "ts" + k)) := by
          split; · rfl
          rename_i hnz; apply List.map_congr_left; intro k hk
          exact InitECandidate.Solver.Wave8Contracts.M23.memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz
            (by simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
        have hnest_bs : (if globN s "bs" ≠ 0 ∧ memW post (globN s "bs" + 32) ∈ S then htabValues post (memW post (globN s "bs" + 32)) else []) =
            (if globN s "bs" ≠ 0 ∧ memW s (globN s "bs" + 32) ∈ S then htabValues s (memW s (globN s "bs" + 32)) else []) := by
          by_cases hnz : globN s "bs" = 0
          · simp [hnz]
          · rw [InitECandidate.Solver.Wave8Contracts.M23.memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz (by omega)]
            by_cases hmS : memW s (globN s "bs" + 32) ∈ S
            · simp [hnz, hmS, InitECandidate.Solver.Wave8Contracts.M23.htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
            · simp [hnz, hmS]
        have hnest_ts : (if globN s "ts" ≠ 0 ∧ memW post (globN s "ts" + 32) ∈ S then htabValues post (memW post (globN s "ts" + 32)) else []) =
            (if globN s "ts" ≠ 0 ∧ memW s (globN s "ts" + 32) ∈ S then htabValues s (memW s (globN s "ts" + 32)) else []) := by
          by_cases hnz : globN s "ts" = 0
          · simp [hnz]
          · rw [InitECandidate.Solver.Wave8Contracts.M23.memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz (by omega)]
            by_cases hmS : memW s (globN s "ts" + 32) ∈ S
            · simp [hnz, hmS, InitECandidate.Solver.Wave8Contracts.M23.htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
            · simp [hnz, hmS]
        have hbal_fl : (balRecords s).flatMap (fun ad => [memW post ad, memW post (ad + 8)]) =
            (balRecords s).flatMap (fun ad => [memW s ad, memW s (ad + 8)]) := by
          apply List.flatMap_congr; intro ad had
          have had_mem := InitECandidate.Solver.Wave8Contracts.M23.balRecord_ivl_mem had
          rcases InitECandidate.Solver.Wave8Contracts.M23.fixedObject_le_2pow64 hAs.2 hWT.2.2.1
              (InitECandidate.Solver.Wave8Contracts.M23.bal_in_fixedObjects had_mem) with h0 | had_bnd
          · dsimp only at h0; omega
          · dsimp only at had_bnd
            have hwti_ad := InitECandidate.Solver.Wave8Contracts.M23.mem_worldTypedIvls_bal (S := S) (Nd := Nd_at) had_mem
            rw [InitECandidate.Solver.Wave8Contracts.M23.memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩,
                InitECandidate.Solver.Wave8Contracts.M23.memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩]
        have hjrn_mp : (List.range (globN s "journal_n")).map (fun k => memW post (globN s "journal" + 32 * k)) =
            (List.range (globN s "journal_n")).map (fun k => memW s (globN s "journal" + 32 * k)) := by
          apply List.map_congr_left; intro k hk; rw [List.mem_range] at hk
          have hjc_le := hWT.2.1.1
          have hjc_ne : globN s "journal_cap" ≠ 0 := by omega
          rcases hWT.2.1.2.2.1 with h0 | ⟨hal, _⟩
          · exact absurd h0 hjc_ne
          · have hbnd := InitECandidate.Solver.Wave8Contracts.M23.allocated_le_2pow64 hAs.2 hal; dsimp only at hbnd
            have hkle : 32 * k + 8 ≤ 32 * globN s "journal_cap" := by omega
            exact InitECandidate.Solver.Wave8Contracts.M23.memW_eq_of_cellHits hcell (by omega)
              (InitECandidate.Solver.Wave8Contracts.M23.mem_worldTypedIvls_journal (S := S) (Nd := Nd_at) hjc_ne)
              ⟨by dsimp only; omega, by dsimp only; omega⟩
        dsimp only
        rw [hglob_eq "bs", hglob_eq "ts", hws_sl, hbs_sl, hts_sl, hnest_bs, hnest_ts, hbal_fl, hjrn_mp]
      have hdelEx_iff : ∀ i t, DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
        intro i t; unfold DelExclusive; rw [hworldRefs_eq]
        refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
          forall_congr' fun k => imp_congr_right fun hk => ?_)
        have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
        have hk_ok : k + 8 ≤ 280 ∧ k % 8 = 0 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl <;> exact ⟨by omega, by decide⟩
        rw [(hrec_eq _ hj_mem).1 k hk_ok.1 hk_ok.2]
      intro i hi
      have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
      have hm_eq := (hrec_eq _ hi_mem).2 48 (by omega) (by omega)
      have hmm_eq := (hrec_eq _ hi_mem).2 56 (by omega) (by omega)
      have he24_eq := (hrec_eq _ hi_mem).1 24 (by omega) (by decide)
      have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
          ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
        apply List.map_congr_left; intro ec hec
        exact (hrec_eq ec (List.mem_of_mem_take hec)).1 136 (by omega) (by decide)
      have hM := hMarks i hi; dsimp only at hM ⊢
      rw [hm_eq, hmm_eq, he24_eq, hframeScratch_eq _ hi_mem, hfeq, htake_eq]
      obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
      refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
      · intro j hj hij
        have hj_ne : j ≠ 0 := by omega
        have hj_tail : (evmChain s)[j] ∈ chTail := by
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj_ne
          have hget : (evmChain s)[k + 1] = chTail[k]'(by rw [← htail_eq_s]; simp; omega) := by
            simp [hch_eq]
          rw [hget]; exact List.getElem_mem _
        have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
        rw [hframeScratch_eq _ hj_mem, hfo_tail _ hj_tail, hframeLogs_tail _ hj_tail,
            (hrec_eq _ hj_mem).1 112 (by omega) (by decide)]
        exact m5 j hj hij
      · intro t ht
        rw [hfp_eq_all t ht, hdelEx_iff i t]; exact m8 t ht
    · have hcg : ∀ g ∈ InitECandidate.Solver.Wave8Contracts.M23.coreWorldGlobals,
          globN post g = globN s g := fun g _ => hglob_eq g
      rw [InitECandidate.Solver.Wave8Contracts.M23.worldRoleSlots_eq hAs.2 hWT.1 hWT.2.2.1 hcell hcg,
          hframeRoleSlots_eq,
          InitECandidate.Solver.Wave8Contracts.M23.journalRoleSlots_eq hAs.2 hWT.2.1 hWT.2.2.1 hcell hcg]
      unfold RolesOK at hRoles ⊢
      refine ⟨fun a ha => ?_, hRoles.2⟩
      obtain ⟨haS, hkl⟩ := hRoles.1 a ha
      have htb := ((hWT.1.2.1 a.1 haS).1.1 (a.1, 88) (by simp [htabFootprint])).1
      rw [InitECandidate.Solver.Wave8Contracts.M23.htab_hdr_eq hcell haS htb 0 (by omega)]
      exact ⟨haS, hkl⟩
    · have hsum_eq : ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum =
          OpDispatchSpec.evmR s := by
        unfold OpDispatchSpec.evmR at hR_eq; rw [hchain_eq] at hR_eq; exact hR_eq
      rw [hsum_eq]; exact hGas
  · intro ec hec
    obtain ⟨he_eq, hc_eq⟩ := hrec_eq ec hec
    exact ⟨hframeScratch_eq ec hec,
      he_eq 24 (by omega) (by decide), he_eq 32 (by omega) (by decide),
      he_eq 40 (by omega) (by decide), he_eq 112 (by omega) (by decide),
      hc_eq 56 (by omega) (by omega)⟩
  · intro ec hec
    rw [htail_eq_s] at hec
    exact ⟨hframeLogs_tail ec hec, hfo_tail ec hec⟩

theorem fcBranchState_of_log_step_fc {F : Type}
    {s0 s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (h : FcBranchState s0 s S)
    (hAp : ArenaReady post)
    (hIp : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt post S)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hch : evmChain post = evmChain s)
    (hR : OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
    (hloc : post.locals = s.locals)
    (hev : globN post "ev" = globN s "ev")
    (hfix : fixedObjects post = fixedObjects s)
    (hht : ∀ t ∈ S, htabFootprint post t = htabFootprint s t)
    (hcells : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec ∧
      memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
      memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧
      memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧
      memW post (ec.1 + 112) = memW s (ec.1 + 112) ∧
      memW post (ec.2 + 56) = memW s (ec.2 + 56))
    (hlogs : ∀ ec ∈ evmChain s,
      frameLogs post ec = frameLogs s ec ∨
        Inside (frameLogs post ec) sourceBase (globN post "heap_ptr")) :
    FcBranchState s0 post S := by
  refine ⟨hAp, hIp, ?_, fcEntryLocals_congr_locals hloc h.locals_ok,
    hch.trans h.chain_eq, ?_, ?_, ?_, hev.trans h.ev_eq⟩
  · exact releaseReadyAt_transport h.release hhp hch
      (fun ec hec => (hcells ec hec).1)
      (fun ec hec => ⟨(hcells ec hec).2.1, (hcells ec hec).2.2.2.1⟩)
      hlogs (fun ec hec => (hcells ec hec).2.2.2.2.1)
      (fun t ht => Or.inl (hht t ht)) hfix
  · rw [hch]; exact h.length_eq
  · rw [hR]; exact h.r_le
  · intro ec hec
    rw [hch] at hec
    obtain ⟨_, h24, h32, h40, _, h56⟩ := hcells ec hec
    obtain ⟨h24_0, h32_0, h40_0, h56_0⟩ := h.cells ec hec
    exact ⟨h24.trans h24_0, h32.trans h32_0, h40.trans h40_0, h56.trans h56_0⟩

theorem eval_call_memcpy_exact_fc {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dstExp srcExp nExp : ExpHOL 64)
    (dst0 src0 n0 : BitVec 64)
    (hG : GuestInv s)
    (hdst : evalAt s dstExp = some (.val (.word dst0)))
    (hsrc : evalAt s srcExp = some (.val (.word src0)))
    (hn : evalAt s nExp = some (.val (.word n0)))
    (hd_nw : dst0.toNat + n0.toNat < 2 ^ 64)
    (hs_nw : src0.toNat + n0.toNat < 2 ^ 64)
    (hn_small : n0.toNat + 32 < 2 ^ 63)
    (hdisj : Disj (dst0.toNat, n0.toNat) (src0.toNat, n0.toNat))
    (hnone : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])).1 = none) :
    let post := (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])).2
    GuestInv post ∧
    post.globals = s.globals ∧
    post.be = s.be ∧
    post.locals = s.locals ∧
    InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect s post [(dst0.toNat, n0.toNat)] ∧
    (∀ k < n0.toNat, memB post ((dst0 + BitVec.ofNat 64 k).toNat) =
      memB s ((src0 + BitVec.ofNat 64 k).toNat)) ∧
    (∀ a : Nat, a < 2 ^ 64 → ¬ InIvl a (dst0.toNat, n0.toNat) → memB post a = memB s a) := by
  dsimp only
  have hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])).1 ≠ some .timeOut := by
    rw [hnone]; simp
  obtain ⟨hmemcpy, _⟩ := M11.eval_call_memcpy_bre s dstExp srcExp nExp dst0 src0 n0
    [(dst0.toNat, n0.toNat)] hG.code hG.memaddrs hdst hsrc hn
    (fun _ => ⟨(dst0.toNat, n0.toNat), by simp, le_refl _, le_refl _⟩) hnt
  obtain ⟨heff_m11, _⟩ := hmemcpy hnone
  have heff_call : InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect s
      (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])).2
      [(dst0.toNat, n0.toNat)] :=
    ⟨heff_m11.code, heff_m11.memaddrs, heff_m11.shMemaddrs, heff_m11.baseAddr,
     heff_m11.be, heff_m11.globals, heff_m11.out_dom, heff_m11.cell_frame, heff_m11.byte_frame⟩
  rw [evaluateHOLFiniteState_call] at hnone heff_call ⊢
  have hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) [dstExp, srcExp, nExp] =
      some [.val (.word dst0), .val (.word src0), .val (.word n0)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalAt] at hdst hsrc hn ⊢
    simp [hdst, hsrc, hn]
  have hlook := pan_three_word_lookup s.code.lookup (ofString "memcpy")
    (ofString "dst") (ofString "src") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_memcpy) dst0 src0 n0
    (by decide) (by decide) (by decide)
    (by rw [hG.code]; exact lookup_memcpy_fc)
  rw [hargs] at hnone heff_call ⊢; dsimp only at hnone heff_call ⊢
  rw [hlook] at hnone heff_call ⊢; dsimp only at hnone heff_call ⊢
  by_cases hclk0 : s.clock = 0
  · rw [if_pos hclk0] at hnone; simp at hnone
  · rw [if_neg hclk0] at hnone heff_call ⊢
    let cmap : HolFiniteMapExact MlS (ValueHOL 64) :=
      ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
        (ofString "src", ValueHOL.val (.word src0))).update (ofString "n", ValueHOL.val (.word n0))
    let entry := callEntryStateHOLFinite s cmap
    have hent_dst : entry.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      have h1 : ofString "n" ≠ ofString "dst" := by decide
      have h2 : ofString "src" ≠ ofString "dst" := by decide
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2]
    have hent_src : entry.locals.lookup (ofString "src") = some (.val (.word src0)) := by
      have h1 : ofString "n" ≠ ofString "src" := by decide
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1]
    have hent_n : entry.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_memcpy) with ⟨br, bs⟩
    have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_memcpy) = (br, bs) := hb
    rw [hb'] at hnone heff_call
    cases br with
    | none => simp at hnone
    | some r =>
      cases r with
      | timeOut | «break» | «continue» | error | finalFfi _ | exception _ _ => simp at hnone
      | returned rv =>
        obtain ⟨rfl, hrel⟩ := R13SoloHtabSet.memcpy_body_spec entry dst0 src0 n0
          hd_nw hs_nw hn_small hdisj hent_dst hent_src hent_n rv (congrArg Prod.fst hb)
        rw [hb] at hrel; dsimp only at hrel hnone heff_call
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word 0#64) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hsh] at heff_call
        dsimp only at heff_call
        have hGp : GuestInv { bs with locals := s.locals } :=
          ⟨hrel.1.trans hG.code, hrel.2.1.trans hG.memaddrs,
           hrel.2.2.1.trans hG.shMemaddrs, hrel.2.2.2.1.trans hG.baseAddr⟩
        simp only [hsh, ↓reduceIte]
        exact ⟨hGp, hrel.2.2.2.2.2.1, hrel.2.2.2.2.1, True.intro, heff_call,
          hrel.2.2.2.2.2.2.2.1, hrel.2.2.2.2.2.2.2.2⟩

theorem logOwnedIvls_zero_or_heap_fc {F : Type}
    {s : PanSemStateFiniteExact 64 F} {log : Nat}
    (h : LogEntryOK s log) :
    ∀ o ∈ logOwnedIvls s log, o.2 = 0 ∨ Inside o sourceBase (globN s "heap_ptr") := by
  obtain ⟨_, hin, _, _, haddr, htop, hdat⟩ := h
  intro o ho
  have ho_rec := (List.mem_filter.1 ho).1
  simp only [logRecordIvls, List.mem_cons, List.not_mem_nil, or_false] at ho_rec
  rcases ho_rec with rfl | rfl | rfl | rfl
  · exact Or.inr hin
  · exact Or.inr haddr
  · by_cases hz : 32 * memW s (log + 16) = 0
    · exact Or.inl hz
    · exact Or.inr htop
  · by_cases hz : memW s (log + 32) = 0
    · exact Or.inl hz
    · exact Or.inr hdat

theorem lst_push_body_logs_fc {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lw : BitVec 64)
    (hAs : ArenaReady s)
    (hlw_wok : WordsOK s (lw.toNat, 24))
    (_hlw_bnd : lw.toNat + 24 ≤ 2 ^ 64)
    (hcap_pos : 1 ≤ memW s (lw.toNat + 16))
    (hlen_le : memW s (lw.toNat + 8) ≤ memW s (lw.toNat + 16))
    (harr_alloc : Inside (memW s lw.toNat, 8 * memW s (lw.toNat + 16)) sourceBase (globN s "heap_ptr") ∨
      Inside (memW s lw.toNat, 8 * memW s (lw.toNat + 16)) (globN s "scratch_ptr") scratchEnd)
    (harr_wok : WordsOK s (memW s lw.toNat, 8 * memW s (lw.toNat + 16)))
    (_hl_disj_arr : Disj (lw.toNat, 24) (memW s lw.toNat, 8 * memW s (lw.toNat + 16)))
    (vb : ValueHOL 64)
    (hret : (evaluateHOLFiniteState
      (callEntryStateHOLFinite s
        ((HolFiniteMapExact.empty.update (ofString "l", ValueHOL.val (.word lw))).update
          (ofString "esz", ValueHOL.val (.word 8#64))))
      (sourceFnBody Guest.Software.guestFn_lst_push)).1 = some (.returned vb)) :
    let cmap := (HolFiniteMapExact.empty.update (ofString "l", ValueHOL.val (.word lw))).update
      (ofString "esz", ValueHOL.val (.word 8#64))
    let sb := (evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
      (sourceFnBody Guest.Software.guestFn_lst_push)).2
    (memW s (lw.toNat + 8) < memW s (lw.toNat + 16) ∧
      ∃ slotw : BitVec 64,
        vb = .val (.word slotw) ∧
        slotw.toNat = memW s lw.toNat + 8 * memW s (lw.toNat + 8) ∧
        GuestInv sb ∧
        sb.globals = s.globals ∧
        sb.be = s.be ∧
        (∀ x : BitVec 64, x ≠ BitVec.ofNat 64 (lw.toNat + 8) → sb.memory x = s.memory x) ∧
        memW sb lw.toNat = memW s lw.toNat ∧
        memW sb (lw.toNat + 8) = memW s (lw.toNat + 8) + 1 ∧
        memW sb (lw.toNat + 16) = memW s (lw.toNat + 16)) ∨
    (memW s (lw.toNat + 8) = memW s (lw.toNat + 16) ∧
      ∃ (s_mc : PanSemStateFiniteExact 64 F) (npw slotw : BitVec 64),
        vb = .val (.word slotw) ∧
        npw.toNat = globN s "heap_ptr" ∧
        slotw.toNat = npw.toNat + 8 * memW s (lw.toNat + 8) ∧
        ArenaReady s_mc ∧
        s_mc.be = s.be ∧
        npw.toNat + 16 * memW s (lw.toNat + 16) ≤ globN s_mc "heap_ptr" ∧
        GlobalsKept ["heap_ptr"] s s_mc ∧
        (∀ a : BitVec 64, ¬ s.memaddrs a → s_mc.memory a = s.memory a) ∧
        (∀ b : Nat, b < 2 ^ 64 →
          ¬ (globN s "heap_ptr" ≤ b ∧ b < globN s_mc "heap_ptr") → memB s_mc b = memB s b) ∧
        WordsOK s_mc (npw.toNat, 16 * memW s (lw.toNat + 16)) ∧
        (∀ i < memW s (lw.toNat + 8),
          memW s_mc (npw.toNat + 8 * i) = memW s (memW s lw.toNat + 8 * i)) ∧
        GuestInv sb ∧
        sb.globals = s_mc.globals ∧
        sb.be = s_mc.be ∧
        (∀ x : BitVec 64,
          x ≠ BitVec.ofNat 64 lw.toNat →
          x ≠ BitVec.ofNat 64 (lw.toNat + 8) →
          x ≠ BitVec.ofNat 64 (lw.toNat + 16) →
          sb.memory x = s_mc.memory x) ∧
        memW sb lw.toNat = npw.toNat ∧
        memW sb (lw.toNat + 8) = memW s (lw.toNat + 8) + 1 ∧
        memW sb (lw.toNat + 16) = 2 * memW s (lw.toNat + 16)) := by
  dsimp only
  set cmap := (HolFiniteMapExact.empty.update (ofString "l", ValueHOL.val (.word lw))).update
    (ofString "esz", ValueHOL.val (.word 8#64))
  set ent := callEntryStateHOLFinite s cmap
  have hent_l : ent.locals.lookup (ofString "l") = some (.val (.word lw)) := by
    simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "esz" ≠ ofString "l" by decide]
  have hent_e : ent.locals.lookup (ofString "esz") = some (.val (.word 8#64)) := by
    simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hma_s : s.memaddrs = ordinaryDomain := hAs.1.memaddrs
  have hent_ma : ent.memaddrs = ordinaryDomain := hma_s
  have hl0_bv : lw + 0#64 = BitVec.ofNat 64 lw.toNat := by simp
  have hl8_bv : lw + 8#64 = BitVec.ofNat 64 (lw.toNat + 8) := by bv_omega
  have hl16_bv : lw + 16#64 = BitVec.ofNat 64 (lw.toNat + 16) := by bv_omega
  have hdom_l0 : s.memaddrs (lw + 0#64) := by
    rw [hl0_bv]; obtain ⟨_, hdom, _⟩ := hlw_wok.2.2 0 (by omega); simpa using hdom
  have hdom_l8 : s.memaddrs (lw + 8#64) := by
    rw [hl8_bv]; obtain ⟨_, hdom, _⟩ := hlw_wok.2.2 1 (by omega); simpa using hdom
  have hdom_l16 : s.memaddrs (lw + 16#64) := by
    rw [hl16_bv]; obtain ⟨_, hdom, _⟩ := hlw_wok.2.2 2 (by omega); simpa using hdom
  set p0w : BitVec 64 := BitVec.ofNat 64 (memW s lw.toNat)
  set nw : BitVec 64 := BitVec.ofNat 64 (memW s (lw.toNat + 8))
  set capw : BitVec 64 := BitVec.ofNat 64 (memW s (lw.toNat + 16))
  have hm_l0 : s.memory (lw + 0#64) = .word p0w := by
    rw [hl0_bv]; dsimp [p0w]; unfold memW
    rcases s.memory (BitVec.ofNat 64 lw.toNat) with ⟨w⟩; simp
  have hm_l8 : s.memory (lw + 8#64) = .word nw := by
    rw [hl8_bv]; dsimp [nw]; unfold memW
    rcases s.memory (BitVec.ofNat 64 (lw.toNat + 8)) with ⟨w⟩; simp
  have hm_l16 : s.memory (lw + 16#64) = .word capw := by
    rw [hl16_bv]; dsimp [capw]; unfold memW
    rcases s.memory (BitVec.ofNat 64 (lw.toNat + 16)) with ⟨w⟩; simp
  have hp0_lt64 : memW s lw.toNat < 2 ^ 64 := by
    unfold memW; rcases s.memory (BitVec.ofNat 64 lw.toNat) with ⟨w⟩; exact w.isLt
  have hn_lt64 : memW s (lw.toNat + 8) < 2 ^ 64 := by
    unfold memW; rcases s.memory (BitVec.ofNat 64 (lw.toNat + 8)) with ⟨w⟩; exact w.isLt
  have hcap_lt64 : memW s (lw.toNat + 16) < 2 ^ 64 := by
    unfold memW; rcases s.memory (BitVec.ofNat 64 (lw.toNat + 16)) with ⟨w⟩; exact w.isLt
  have hp0w_nat : p0w.toNat = memW s lw.toNat := Nat.mod_eq_of_lt hp0_lt64
  have hnw_nat : nw.toNat = memW s (lw.toNat + 8) := Nat.mod_eq_of_lt hn_lt64
  have hcapw_nat : capw.toNat = memW s (lw.toNat + 16) := Nat.mod_eq_of_lt hcap_lt64
  have harr_sz_le : 8 * memW s (lw.toNat + 16) ≤ 251658240 := by
    rcases harr_alloc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hhlim := hAs.2.2.1
      rw [R11Shards.sourceBase_val] at h1; rw [R11Shards.heapLimit_val] at hhlim
      dsimp only at h1 h2; omega
    · have hs1 := hAs.2.2.2.1; have hs2 := hAs.2.2.2.2.1
      rw [R11Shards.scratchStart_val] at hs1; rw [R11Shards.scratchEnd_val] at h2
      dsimp only at h1 h2; omega
  have harr_bnd : memW s lw.toNat + 8 * memW s (lw.toNat + 16) ≤ 2 ^ 64 :=
    InitECandidate.Solver.Wave8Contracts.M23.allocated_le_2pow64 hAs.2 harr_alloc
  rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_lst_push) with ⟨rb, sb⟩
  dsimp only
  have hrb : rb = some (.returned vb) := by
    change (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_lst_push)).1 = _ at hret
    rw [hrun] at hret; exact hret
  subst hrb
  let e1 := setVarHOLFinite (ofString "n") (.val (.word nw)) ent
  let e2 := setVarHOLFinite (ofString "cap") (.val (.word capw)) e1
  let growProg : ProgHOL 64 :=
    .decCall (ofString "np") .one (ofString "alloc")
      [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2#64]]
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "np"),
           .load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
           .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
        (.seq
          (.store (.op .add [.var .local (ofString "l"), .const 0#64]) (.var .local (ofString "np")))
          (.store (.op .add [.var .local (ofString "l"), .const 16#64])
            (.panop .mul [.var .local (ofString "cap"), .const 2#64]))))
  let tailProg : ProgHOL 64 :=
    .seq
      (.store (.op .add [.var .local (ofString "l"), .const 8#64])
        (.op .add [.var .local (ofString "n"), .const 1#64]))
      (.return (.op .add
        [.load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
         .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]))
  have hbody_e2 : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_lst_push) =
      (let out := evaluateHOLFiniteState e2
        (.seq (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
                growProg .skip)
              tailProg);
       (out.1, { out.2 with
         locals := HolFiniteMapExact.resVarEq
           (HolFiniteMapExact.resVarEq out.2.locals (ofString "cap", e1.locals.lookup (ofString "cap")))
           (ofString "n", ent.locals.lookup (ofString "n")) })) := by
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_lst_push,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    have hz_8 : (8#64 : BitVec 64) + 0 = 8#64 := BitVec.add_zero _
    have hz_16 : (16#64 : BitVec 64) + 0 = 16#64 := BitVec.add_zero _
    have hev1 : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "l"), .const 8#64])) =
        some (.val (.word nw)) := by
      have hed8 : ent.memaddrs (lw + 8#64) := hdom_l8
      have hem8 : ent.memory (lw + 8#64) = .word nw := hm_l8
      simp only [evalHOLExact, evalListHOLExact, hent_l, valueIsWord, valueWord,
        wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_8,
        memLoadHOLExact, isWfShapeExactHOL, hed8, hem8, ↓reduceIte]
    rw [hev1]; dsimp only
    rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
    have he1_def : setVarHOLFinite (ofString "n") (.val (.word nw)) ent = e1 := rfl
    rw [he1_def, evaluateHOLFiniteState_dec_total]; dsimp only
    have he1_l : e1.locals.lookup (ofString "l") = some (.val (.word lw)) := by
      simp [e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "l" by decide, hent_l]
    have he1_dom16 : e1.memaddrs (lw + 16#64) := hdom_l16
    have he1_m16 : e1.memory (lw + 16#64) = .word capw := hm_l16
    have hev2 : @evalHOLExact 64 F _ e1.toExact (fun a => Classical.propDecidable (e1.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "l"), .const 16#64])) =
        some (.val (.word capw)) := by
      simp only [evalHOLExact, evalListHOLExact, he1_l, valueIsWord, valueWord,
        wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_16,
        memLoadHOLExact, isWfShapeExactHOL, he1_dom16, he1_m16, ↓reduceIte]
    rw [hev2]; dsimp only
    rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
  rw [hbody_e2] at hrun; dsimp only at hrun
  rcases hout_e2 : evaluateHOLFiniteState e2
      (.seq (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
              growProg .skip)
            tailProg) with ⟨ro2, so2⟩
  rw [hout_e2] at hrun
  dsimp only at hrun
  injection hrun with hro2 hsb_eq
  subst hro2
  have he2_AR : ArenaReady e2 := ⟨guestInv_with_locals_clock s e2.locals (s.clock - 1) hAs.1, hAs.2⟩
  have he2_l : e2.locals.lookup (ofString "l") = some (.val (.word lw)) := by
    simp [e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "cap" ≠ ofString "l" by decide,
      show ofString "n" ≠ ofString "l" by decide, hent_l]
  have he2_e : e2.locals.lookup (ofString "esz") = some (.val (.word 8#64)) := by
    simp [e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "cap" ≠ ofString "esz" by decide,
      show ofString "n" ≠ ofString "esz" by decide, hent_e]
  have he2_n : e2.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    simp [e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "cap" ≠ ofString "n" by decide]
  have he2_c : e2.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
    simp [e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hcmp_nl : @evalHOLExact 64 F _ e2.toExact (fun a => Classical.propDecidable (e2.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap"))) =
      some (.val (.word (if capw.toNat ≤ nw.toNat then 1#64 else 0#64))) := by
    simp only [evalHOLExact, he2_n, he2_c, Compiler.Encoders.Asm.wordCmpHOL]
    by_cases hle : capw.toNat ≤ nw.toNat
    · have hlt_f : ¬ (nw < capw) := fun h => by have := (BitVec.lt_def).1 h; omega
      simp [hle, hlt_f]
    · have hlt_bv : nw < capw := (BitVec.lt_def).2 (by omega)
      simp [hle, hlt_bv]
  rw [evaluateHOLFiniteState_seq_line780] at hout_e2
  rcases hite_out : evaluateHOLFiniteState e2
      (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
        growProg .skip) with ⟨ri, si⟩
  rw [hite_out] at hout_e2
  cases ri with
  | some ri' =>
    dsimp only at hout_e2
    injection hout_e2 with hri _
    injection hri with hri'
    exfalso
    have hnr := ite_ne_returned_fc
      (c := .cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
      (y := growProg) (n := .skip)
      (decCall_ne_returned_fc (seq_ne_returned_fc
        (fun t u => call0_ne_returned_fc t _ _ u)
        (seq_ne_returned_fc (fun t u => store_ne_returned_fc t _ _ u)
          (fun t u => store_ne_returned_fc t _ _ u))))
      (fun t u => skip_ne_returned_fc t u)
      e2 vb
    rw [hite_out, hri'] at hnr
    exact hnr rfl
  | none =>
    dsimp only at hout_e2
    rw [evaluateHOLFiniteState_ite, hcmp_nl] at hite_out
    dsimp only at hite_out
    by_cases hgrow_cond : capw.toNat ≤ nw.toNat
    · right
      have hn_eq_cap : memW s (lw.toNat + 8) = memW s (lw.toNat + 16) := by omega
      have hnw_eq_capw : nw = capw := BitVec.eq_of_toNat_eq (by omega)
      refine ⟨hn_eq_cap, ?_⟩
      rw [if_pos hgrow_cond, if_neg (by decide : (1#64 : BitVec 64) ≠ 0)] at hite_out
      dsimp only [growProg] at hite_out
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hite_out
      have hev_alloc : evalListHOLFinite e2 (h := fun a => Classical.propDecidable (e2.memaddrs a))
          [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2#64]] =
          some [.val (.word (8#64 * capw * 2#64))] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, he2_e, he2_c,
          valueIsWord, valueWord, panOpHOL]
      have hlk_alloc := pan_one_word_lookup e2.code.lookup (ofString "alloc") (ofString "n")
        (sourceFnBody Guest.Software.guestFn_alloc) (8#64 * capw * 2#64)
        (by rw [he2_AR.1.code]; exact lookup_alloc_fc)
      rw [hev_alloc] at hite_out; dsimp only at hite_out
      rw [hlk_alloc] at hite_out; dsimp only at hite_out
      by_cases hc_e2 : e2.clock = 0
      · rw [if_pos hc_e2] at hite_out; simp at hite_out
      · rw [if_neg hc_e2] at hite_out
        let cmap_a := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word (8#64 * capw * 2#64)))
        let ent_a := callEntryStateHOLFinite e2 cmap_a
        rcases hrun_a : evaluateHOLFiniteState ent_a (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ra, sa⟩
        have hrun_a' : evaluateHOLFiniteState (callEntryStateHOLFinite e2 cmap_a)
            (sourceFnBody Guest.Software.guestFn_alloc) = (ra, sa) := hrun_a
        rw [hrun_a'] at hite_out
        cases ra with
        | none => simp at hite_out
        | some ra' =>
          cases ra' with
          | timeOut | «break» | «continue» | error | finalFfi _ | exception _ _ => simp at hite_out
          | returned va =>
            obtain ⟨npw, qw, rfl, hnpw_hp_e2, hnpw8, hnpw_add_le, hqw_lim, hqw8,
              hAsa, _, hfb_sa, hsa_mem_e2, hsa_be_e2, hsa_glob_e2⟩ :=
              alloc_entry_returned_fc e2 (8#64 * capw * 2#64) he2_AR va (congrArg Prod.fst hrun_a)
            rw [hrun_a] at hAsa hfb_sa hsa_mem_e2 hsa_be_e2 hsa_glob_e2
            dsimp only at hAsa hfb_sa hsa_mem_e2 hsa_be_e2 hsa_glob_e2 hite_out
            have hsh_a : (shapeEqHOL (shapeOfHOLExact (.val (.word npw) : ValueHOL 64)) .one &&
                shapeEqHOL (shapeOfHOLExact (.val (.word npw) : ValueHOL 64)) .one) = true := by
              simp [shapeOfHOLExact, shapeEqHOL]
            rw [if_pos hsh_a] at hite_out
            let ma := setVarHOLFinite (ofString "np") (.val (.word npw)) { sa with locals := e2.locals }
            have hma_AR : ArenaReady ma := ⟨guestInv_with_locals_clock sa ma.locals sa.clock hAsa.1, hAsa.2⟩
            have hma_mem : ma.memory = s.memory := hsa_mem_e2
            have hma_be : ma.be = s.be := hsa_be_e2
            have hma_glob : ma.globals = s.globals.update (ofString "heap_ptr", .val (.word qw)) := hsa_glob_e2
            have hnpw_hp : npw.toNat = globN s "heap_ptr" := hnpw_hp_e2
            have hqw_hp : globN ma "heap_ptr" = qw.toNat := by
              simp [globN, hma_glob, HolFiniteMapExact.lookup_update, FUPDATE]
            have hmul8_nat : (8#64 * capw).toNat = 8 * memW s (lw.toNat + 16) := by
              rw [BitVec.toNat_mul]
              have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
              rw [h8, hcapw_nat, Nat.mod_eq_of_lt (by omega)]
            have hmul16_nat : (8#64 * capw * 2#64).toNat = 16 * memW s (lw.toNat + 16) := by
              rw [BitVec.toNat_mul, hmul8_nat]
              have h2 : (2#64 : BitVec 64).toNat = 2 := rfl
              rw [h2, Nat.mod_eq_of_lt (by omega)]; omega
            have hmuln_nat : (8#64 * nw).toNat = 8 * memW s (lw.toNat + 8) := by
              rw [hnw_eq_capw, hmul8_nat, hn_eq_cap]
            have h16_div : (16 * memW s (lw.toNat + 16) + 7) / 8 * 8 = 16 * memW s (lw.toNat + 16) := by omega
            have hma_arr_wok : WordsOK ma (npw.toNat, 16 * memW s (lw.toNat + 16)) := by
              have hw0 := hfb_sa.2.2
              rw [hmul16_nat, h16_div] at hw0
              exact hw0
            rcases hma_cont : evaluateHOLFiniteState ma
              (.seq
                (.call (some (none, none)) (ofString "memcpy")
                  [.var .local (ofString "np"),
                   .load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                   .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
                (.seq
                  (.store (.op .add [.var .local (ofString "l"), .const 0#64]) (.var .local (ofString "np")))
                  (.store (.op .add [.var .local (ofString "l"), .const 16#64])
                    (.panop .mul [.var .local (ofString "cap"), .const 2#64])))) with ⟨rg1, sg1⟩
            rw [hma_cont] at hite_out; dsimp only at hite_out
            injection hite_out with hrg1 hsi_eq
            subst hrg1
            rw [evaluateHOLFiniteState_seq_line780] at hma_cont
            rcases hmc_out : evaluateHOLFiniteState ma
              (.call (some (none, none)) (ofString "memcpy")
                [.var .local (ofString "np"),
                 .load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                 .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]]) with ⟨rmc, smc⟩
            rw [hmc_out] at hma_cont
            cases rmc with
            | some _ => dsimp only at hma_cont; simp at hma_cont
            | none =>
              dsimp only at hma_cont
              have hma_np : ma.locals.lookup (ofString "np") = some (.val (.word npw)) := by
                simp [ma, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              have hma_l : ma.locals.lookup (ofString "l") = some (.val (.word lw)) := by
                simp [ma, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "np" ≠ ofString "l" by decide, he2_l]
              have hma_e : ma.locals.lookup (ofString "esz") = some (.val (.word 8#64)) := by
                simp [ma, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "np" ≠ ofString "esz" by decide, he2_e]
              have hma_n : ma.locals.lookup (ofString "n") = some (.val (.word nw)) := by
                simp [ma, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "np" ≠ ofString "n" by decide, he2_n]
              have hma_c : ma.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
                simp [ma, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "np" ≠ ofString "cap" by decide, he2_c]
              have hma_dom0 : ma.memaddrs (lw + 0#64) := by rw [hma_AR.1.memaddrs, ← hma_s]; exact hdom_l0
              have hma_m0 : ma.memory (lw + 0#64) = .word p0w := by rw [hma_mem]; exact hm_l0
              have hz_0 : (0#64 : BitVec 64) + 0 = 0#64 := rfl
              have hev_mc_dst : evalAt ma (.var .local (ofString "np")) = some (.val (.word npw)) := by
                simp [evalAt, evalHOLExact, hma_np]
              have hev_mc_src : evalAt ma (.load .one (.op .add [.var .local (ofString "l"), .const 0#64])) =
                  some (.val (.word p0w)) := by
                simp only [evalAt, evalHOLExact, evalListHOLExact,
                  hma_l, valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map,
                  Bool.and_self, List.foldr, hz_0, memLoadHOLExact, isWfShapeExactHOL, hma_dom0, hma_m0, ↓reduceIte]
              have hev_mc_n : evalAt ma (.panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]) =
                  some (.val (.word (8#64 * nw))) := by
                simp [evalAt, evalHOLExact, evalListHOLExact,
                  hma_e, hma_n, valueIsWord, valueWord, panOpHOL]
              have hd_mc_nw : npw.toNat + (8#64 * nw).toNat < 2 ^ 64 := by
                have hhlim_v := R11Shards.heapLimit_val
                rw [hmuln_nat]; rw [hmul16_nat] at hnpw_add_le; omega
              have hs_mc_nw : p0w.toNat + (8#64 * nw).toNat < 2 ^ 64 := by
                rw [hp0w_nat, hmuln_nat]
                rcases harr_alloc with ⟨_, h2⟩ | ⟨_, h2⟩
                · have hhlim := hAs.2.2.1; rw [R11Shards.heapLimit_val] at hhlim; dsimp only at h2; omega
                · rw [R11Shards.scratchEnd_val] at h2; dsimp only at h2; omega
              have hn_mc_small : (8#64 * nw).toNat + 32 < 2 ^ 63 := by
                rw [hmuln_nat]; omega
              have hdisj_mc : Disj (npw.toNat, (8#64 * nw).toNat) (p0w.toNat, (8#64 * nw).toNat) := by
                rw [hp0w_nat, hmuln_nat, hn_eq_cap, hnpw_hp]
                rcases harr_alloc with ⟨_, h2⟩ | ⟨h1, _⟩
                · exact Or.inr (Or.inr (Or.inr (by dsimp only at *; omega)))
                · have hhlim := hAs.2.2.1; have hs1 := hAs.2.2.2.1; have hs2 := hAs.2.2.2.2.1
                  have hlt_hl_ss : heapLimit ≤ scratchStart := by
                    rw [R11Shards.heapLimit_val, R11Shards.scratchStart_val]
                  exact Or.inr (Or.inr (Or.inl (by dsimp only at *; omega)))
              obtain ⟨hG_smc, hsmc_glob, hsmc_be, hsmc_loc, heff_mc, hcopy_mc, hout_mc⟩ :=
                eval_call_memcpy_exact_fc ma _ _ _ npw p0w (8#64 * nw) hma_AR.1
                  hev_mc_dst hev_mc_src hev_mc_n hd_mc_nw hs_mc_nw hn_mc_small hdisj_mc
                  (congrArg Prod.fst hmc_out)
              rw [hmc_out] at hG_smc hsmc_glob hsmc_be hsmc_loc heff_mc hcopy_mc hout_mc
              dsimp only at hG_smc hsmc_glob hsmc_be hsmc_loc heff_mc hcopy_mc hout_mc
              have hsmc_AR : ArenaReady smc := ⟨hG_smc, arenaOK_congr hsmc_glob hma_AR.2⟩
              have hsmc_hp : globN smc "heap_ptr" = qw.toNat := by
                rw [show globN smc "heap_ptr" = globN ma "heap_ptr" by simp [globN, hsmc_glob], hqw_hp]
              have hsmc_arr_wok : WordsOK smc (npw.toNat, 16 * memW s (lw.toNat + 16)) :=
                (R14Shards.OpHandlersA.wordsOK_congr_dom heff_mc.memaddrs).2 hma_arr_wok
              have hsmc_prefix : ∀ i < memW s (lw.toNat + 8),
                  memW smc (npw.toNat + 8 * i) = memW s (memW s lw.toNat + 8 * i) := by
                intro i hi
                have hp0_8 : (memW s lw.toNat) % 8 = 0 := harr_wok.1
                have ha1_lt : npw.toNat + 8 * i + 8 < 2 ^ 64 := by
                  rw [hmul16_nat] at hnpw_add_le; have hhlim_v := R11Shards.heapLimit_val; omega
                have ha2_lt : memW s lw.toNat + 8 * i + 8 < 2 ^ 64 := by
                  rcases harr_alloc with ⟨_, h2⟩ | ⟨_, h2⟩
                  · have hhlim := hAs.2.2.1; rw [R11Shards.heapLimit_val] at hhlim; dsimp only at h2; omega
                  · rw [R11Shards.scratchEnd_val] at h2; dsimp only at h2; omega
                rw [(R13SoloHtabSet.memW_eq_iff_memB (hsmc_be.trans hma_be)
                  (by omega) (by omega) ha1_lt ha2_lt).2]
                intro r hr
                have hk_lt : 8 * i + r < (8#64 * nw).toNat := by rw [hmuln_nat]; omega
                have hd_eq : (npw + BitVec.ofNat 64 (8 * i + r)).toNat = npw.toNat + 8 * i + r := by
                  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
                      Nat.mod_eq_of_lt (by omega)]; omega
                have hs_eq : (p0w + BitVec.ofNat 64 (8 * i + r)).toNat = memW s lw.toNat + 8 * i + r := by
                  rw [BitVec.toNat_add, hp0w_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
                      Nat.mod_eq_of_lt (by omega)]; omega
                have hmb_ma : memB ma (memW s lw.toNat + 8 * i + r) = memB s (memW s lw.toNat + 8 * i + r) := by
                  simp [memB, hma_mem, hma_be]
                rw [← hmb_ma, ← hs_eq, ← hd_eq]
                exact hcopy_mc (8 * i + r) hk_lt
              have hsmc_gk : GlobalsKept ["heap_ptr"] s smc := by
                intro k hk
                have hne : k ≠ ofString "heap_ptr" := by simpa using hk
                rw [hsmc_glob, hma_glob]
                simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]
              have hsmc_out_dom : ∀ a : BitVec 64, ¬ s.memaddrs a → smc.memory a = s.memory a := by
                intro a hna
                rw [heff_mc.out_dom a (by rwa [hma_AR.1.memaddrs, ← hma_s]), hma_mem]
              have hsmc_byte : ∀ b : Nat, b < 2 ^ 64 →
                  ¬ (globN s "heap_ptr" ≤ b ∧ b < globN smc "heap_ptr") → memB smc b = memB s b := by
                intro b hb hnb
                have hni : ¬ InIvl b (npw.toNat, (8#64 * nw).toNat) := by
                  intro ⟨h1, h2⟩
                  change npw.toNat ≤ b at h1
                  change b < npw.toNat + (8#64 * nw).toNat at h2
                  rw [hmuln_nat] at h2; rw [hmul16_nat] at hnpw_add_le
                  apply hnb
                  exact ⟨by omega, by rw [hsmc_hp]; omega⟩
                have hmb_ma : memB ma b = memB s b := by simp [memB, hma_mem, hma_be]
                exact (hout_mc b hb hni).trans hmb_ma
              rw [evaluateHOLFiniteState_seq_line780] at hma_cont
              rcases hst0_out : evaluateHOLFiniteState smc
                (.store (.op .add [.var .local (ofString "l"), .const 0#64]) (.var .local (ofString "np"))) with ⟨rst0, sst0⟩
              rw [hst0_out] at hma_cont
              cases rst0 with
              | some _ => dsimp only at hma_cont; simp at hma_cont
              | none =>
                dsimp only at hma_cont
                have hsmc_ma : smc.memaddrs = ordinaryDomain := hG_smc.memaddrs
                have hsmc_l : smc.locals.lookup (ofString "l") = some (.val (.word lw)) := by
                  rw [hsmc_loc]; exact hma_l
                have hsmc_np : smc.locals.lookup (ofString "np") = some (.val (.word npw)) := by
                  rw [hsmc_loc]; exact hma_np
                have hsmc_dom0' : smc.memaddrs lw := by
                  rw [hsmc_ma, ← hma_s]; simpa using hdom_l0
                have hev_st0_d : @evalHOLExact 64 F _ smc.toExact (fun a => Classical.propDecidable (smc.memaddrs a))
                    (.op .add [.var .local (ofString "l"), .const 0#64]) =
                    some (.val (.word (lw + 0#64))) := by
                  simp [evalHOLExact, evalListHOLExact, hsmc_l, valueIsWord, valueWord, wordOpHOL, wordOp]
                have hev_st0_v : @evalHOLExact 64 F _ smc.toExact (fun a => Classical.propDecidable (smc.memaddrs a))
                    (.var .local (ofString "np")) = some (.val (.word npw)) := by
                  simp [evalHOLExact, hsmc_np]
                have hst0_eq : evaluateHOLFiniteState smc
                    (.store (.op .add [.var .local (ofString "l"), .const 0#64]) (.var .local (ofString "np"))) =
                    (none, { smc with memory := fun a => if a = lw + 0#64 then .word npw else smc.memory a }) := by
                  rw [evaluateHOLFiniteState_store, hev_st0_d, hev_st0_v]; dsimp only
                  simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hsmc_dom0']
                have hsst0_eq : sst0 = { smc with memory := fun a => if a = lw + 0#64 then .word npw else smc.memory a } := by
                  rw [hst0_out] at hst0_eq; exact (Prod.mk.inj hst0_eq).2
                have hsst0_l : sst0.locals.lookup (ofString "l") = some (.val (.word lw)) := by
                  rw [hsst0_eq]; exact hsmc_l
                have hsst0_c : sst0.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
                  rw [hsst0_eq, hsmc_loc]; exact hma_c
                have hsst0_dom16 : sst0.memaddrs (lw + 16#64) := by
                  rw [hsst0_eq, hsmc_ma, ← hma_s]; exact hdom_l16
                have hev_st16_d : @evalHOLExact 64 F _ sst0.toExact (fun a => Classical.propDecidable (sst0.memaddrs a))
                    (.op .add [.var .local (ofString "l"), .const 16#64]) =
                    some (.val (.word (lw + 16#64))) := by
                  simp [evalHOLExact, evalListHOLExact, hsst0_l, valueIsWord, valueWord, wordOpHOL, wordOp]
                have hev_st16_v : @evalHOLExact 64 F _ sst0.toExact (fun a => Classical.propDecidable (sst0.memaddrs a))
                    (.panop .mul [.var .local (ofString "cap"), .const 2#64]) =
                    some (.val (.word (capw * 2#64))) := by
                  simp [evalHOLExact, evalListHOLExact, hsst0_c, valueIsWord, valueWord, panOpHOL]
                have hst16_eq : evaluateHOLFiniteState sst0
                    (.store (.op .add [.var .local (ofString "l"), .const 16#64])
                      (.panop .mul [.var .local (ofString "cap"), .const 2#64])) =
                    (none, { sst0 with memory := fun a => if a = lw + 16#64 then .word (capw * 2#64) else sst0.memory a }) := by
                  rw [evaluateHOLFiniteState_store, hev_st16_d, hev_st16_v]; dsimp only
                  simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hsst0_dom16]
                have hsg1_eq : sg1 = { sst0 with memory := fun a => if a = lw + 16#64 then .word (capw * 2#64) else sst0.memory a } := by
                  rw [hma_cont] at hst16_eq; exact (Prod.mk.inj hst16_eq).2
                have hsi_ma : si.memaddrs = ordinaryDomain := by
                  rw [← hsi_eq, hsg1_eq, hsst0_eq]; exact hsmc_ma
                have hsi_l : si.locals.lookup (ofString "l") = some (.val (.word lw)) := by
                  rw [← hsi_eq]; dsimp only
                  rw [PanRunBounded.resVarEq_lookup, if_neg (by decide), hsg1_eq, hsst0_eq]; exact hsmc_l
                have hsi_n : si.locals.lookup (ofString "n") = some (.val (.word nw)) := by
                  rw [← hsi_eq]; dsimp only
                  rw [PanRunBounded.resVarEq_lookup, if_neg (by decide), hsg1_eq, hsst0_eq, hsmc_loc]; exact hma_n
                have hsi_e : si.locals.lookup (ofString "esz") = some (.val (.word 8#64)) := by
                  rw [← hsi_eq]; dsimp only
                  rw [PanRunBounded.resVarEq_lookup, if_neg (by decide), hsg1_eq, hsst0_eq, hsmc_loc]; exact hma_e
                have hsi_dom8 : si.memaddrs (lw + 8#64) := by rw [hsi_ma, ← hma_s]; exact hdom_l8
                have hsi_dom0 : si.memaddrs (lw + 0#64) := by rw [hsi_ma, ← hma_s]; exact hdom_l0
                dsimp only [tailProg] at hout_e2
                rw [evaluateHOLFiniteState_seq_line780] at hout_e2
                have hev_st8_d : @evalHOLExact 64 F _ si.toExact (fun a => Classical.propDecidable (si.memaddrs a))
                    (.op .add [.var .local (ofString "l"), .const 8#64]) =
                    some (.val (.word (lw + 8#64))) := by
                  simp [evalHOLExact, evalListHOLExact, hsi_l, valueIsWord, valueWord, wordOpHOL, wordOp]
                have hev_st8_v : @evalHOLExact 64 F _ si.toExact (fun a => Classical.propDecidable (si.memaddrs a))
                    (.op .add [.var .local (ofString "n"), .const 1#64]) =
                    some (.val (.word (nw + 1#64))) := by
                  simp [evalHOLExact, evalListHOLExact, hsi_n, valueIsWord, valueWord, wordOpHOL, wordOp]
                have hst8_eq : evaluateHOLFiniteState si
                    (.store (.op .add [.var .local (ofString "l"), .const 8#64])
                      (.op .add [.var .local (ofString "n"), .const 1#64])) =
                    (none, { si with memory := fun a => if a = lw + 8#64 then .word (nw + 1#64) else si.memory a }) := by
                  rw [evaluateHOLFiniteState_store, hev_st8_d, hev_st8_v]; dsimp only
                  simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hsi_dom8]
                rw [hst8_eq] at hout_e2; dsimp only at hout_e2
                let st8 : PanSemStateFiniteExact 64 F :=
                  { si with memory := fun a => if a = lw + 8#64 then .word (nw + 1#64) else si.memory a }
                have hne_0_16 : lw + 0#64 ≠ lw + 16#64 := by
                  rw [hl0_bv, hl16_bv]; intro h; have := congrArg BitVec.toNat h
                  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; omega
                have hne_0_8 : lw + 0#64 ≠ lw + 8#64 := by
                  rw [hl0_bv, hl8_bv]; intro h; have := congrArg BitVec.toNat h
                  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; omega
                have hne_16_8 : lw + 16#64 ≠ lw + 8#64 := by
                  rw [hl16_bv, hl8_bv]; intro h; have := congrArg BitVec.toNat h
                  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; omega
                have hst8_m0 : st8.memory (lw + 0#64) = .word npw := by
                  dsimp [st8]; rw [if_neg hne_0_8, ← hsi_eq]; dsimp only
                  rw [hsg1_eq]; dsimp only; rw [if_neg hne_0_16, hsst0_eq]; simp
                have hst8_m8 : st8.memory (lw + 8#64) = .word (nw + 1#64) := by
                  dsimp [st8]; simp
                have hst8_m16 : st8.memory (lw + 16#64) = .word (capw * 2#64) := by
                  dsimp [st8]; rw [if_neg hne_16_8, ← hsi_eq]; dsimp only
                  rw [hsg1_eq]; simp
                have hev_ret : @evalHOLExact 64 F _ st8.toExact (fun a => Classical.propDecidable (st8.memaddrs a))
                    (.op .add
                      [.load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                       .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]) =
                    some (.val (.word (npw + nw * 8#64))) := by
                  have hz_0 : (0#64 : BitVec 64) + 0 = 0#64 := rfl
                  have hst8_l : st8.locals.lookup (ofString "l") = some (.val (.word lw)) := hsi_l
                  have hst8_n : st8.locals.lookup (ofString "n") = some (.val (.word nw)) := hsi_n
                  have hst8_e : st8.locals.lookup (ofString "esz") = some (.val (.word 8#64)) := hsi_e
                  have hst8_dom0 : st8.memaddrs (lw + 0#64) := hsi_dom0
                  simp only [evalHOLExact, evalListHOLExact, hst8_l, hst8_n, hst8_e,
                    valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
                    List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_0,
                    memLoadHOLExact, isWfShapeExactHOL, hst8_dom0, hst8_m0, ↓reduceIte]
                  rw [show (nw * 8#64 : BitVec 64) + 0 = nw * 8#64 from BitVec.add_zero _]
                rw [evaluateHOLFiniteState_return, hev_ret] at hout_e2
                dsimp only at hout_e2
                rw [if_pos (by simp [shapeOfHOLExact])] at hout_e2
                injection hout_e2 with hvb_eq hso2_eq
                have hvb_ret : ValueHOL.val (.word (npw + nw * 8#64)) = vb := by
                  cases hvb_eq; rfl
                have hmul_nw8 : (nw * 8#64).toNat = 8 * memW s (lw.toNat + 8) := by
                  simp only [BitVec.toNat_mul, hnw_nat, BitVec.toNat_ofNat]
                  omega
                have hslot_nat : (npw + nw * 8#64).toNat = npw.toNat + 8 * memW s (lw.toNat + 8) := by
                  rw [BitVec.toNat_add, hmul_nw8]
                  rw [hmul16_nat] at hnpw_add_le
                  have hhlim_v := R11Shards.heapLimit_val
                  exact Nat.mod_eq_of_lt (by omega)
                have hsb_mem_eq : sb.memory = st8.memory := by
                  rw [← hsb_eq, ← hso2_eq]; rfl
                have hG_sb : GuestInv sb := by
                  rw [← hsb_eq, ← hso2_eq, ← hsi_eq, hsg1_eq, hsst0_eq]
                  exact ⟨hG_smc.code, hG_smc.memaddrs, hG_smc.shMemaddrs, hG_smc.baseAddr⟩
                have hsb_glob : sb.globals = smc.globals := by
                  rw [← hsb_eq, ← hso2_eq, ← hsi_eq, hsg1_eq, hsst0_eq]; rfl
                have hsb_be : sb.be = smc.be := by
                  rw [← hsb_eq, ← hso2_eq, ← hsi_eq, hsg1_eq, hsst0_eq]; rfl
                refine ⟨smc, npw, npw + nw * 8#64, hvb_ret.symm, hnpw_hp, hslot_nat,
                  hsmc_AR, hsmc_be.trans hma_be,
                  by rw [hsmc_hp]; rw [hmul16_nat] at hnpw_add_le; exact hnpw_add_le,
                  hsmc_gk, hsmc_out_dom, hsmc_byte, hsmc_arr_wok, hsmc_prefix,
                  hG_sb, hsb_glob, hsb_be, ?_, ?_, ?_, ?_⟩
                · intro x hx0 hx8 hx16
                  rw [hsb_mem_eq]; change (if x = lw + 8#64 then .word (nw + 1#64) else si.memory x) = smc.memory x
                  rw [if_neg (by rwa [hl8_bv]), ← hsi_eq, hsg1_eq]
                  change (if x = lw + 16#64 then .word (capw * 2#64) else sst0.memory x) = smc.memory x
                  rw [if_neg (by rwa [hl16_bv]), hsst0_eq]
                  change (if x = lw + 0#64 then .word npw else smc.memory x) = smc.memory x
                  rw [if_neg (by rwa [hl0_bv])]
                · have hw0 : sb.memory (BitVec.ofNat 64 lw.toNat) = .word npw := by
                    rw [hsb_mem_eq, ← hl0_bv, hst8_m0]
                  unfold memW; rw [hw0]
                · have hw8 : sb.memory (BitVec.ofNat 64 (lw.toNat + 8)) = .word (nw + 1#64) := by
                    rw [hsb_mem_eq, ← hl8_bv, hst8_m8]
                  unfold memW; rw [hw8]
                  change (nw + 1#64).toNat = memW s (lw.toNat + 8) + 1
                  rw [BitVec.toNat_add, hnw_nat]
                  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
                  rw [h1, Nat.mod_eq_of_lt (by omega)]
                · have hw16 : sb.memory (BitVec.ofNat 64 (lw.toNat + 16)) = .word (capw * 2#64) := by
                    rw [hsb_mem_eq, ← hl16_bv, hst8_m16]
                  unfold memW; rw [hw16]
                  change (capw * 2#64).toNat = 2 * memW s (lw.toNat + 16)
                  rw [BitVec.toNat_mul, hcapw_nat]
                  have h2 : (2#64 : BitVec 64).toNat = 2 := rfl
                  rw [h2, Nat.mod_eq_of_lt (by omega)]; omega
    · left
      have hn_lt_cap : memW s (lw.toNat + 8) < memW s (lw.toNat + 16) := by omega
      refine ⟨hn_lt_cap, ?_⟩
      rw [if_neg hgrow_cond, if_pos (by decide : (0#64 : BitVec 64) = 0), evaluateHOLFiniteState_skip] at hite_out
      injection hite_out with _ hsi_eq
      subst hsi_eq
      have he2_dom8 : e2.memaddrs (lw + 8#64) := hdom_l8
      have he2_dom0 : e2.memaddrs (lw + 0#64) := hdom_l0
      dsimp only [tailProg] at hout_e2
      rw [evaluateHOLFiniteState_seq_line780] at hout_e2
      have hev_st8_d : @evalHOLExact 64 F _ e2.toExact (fun a => Classical.propDecidable (e2.memaddrs a))
          (.op .add [.var .local (ofString "l"), .const 8#64]) =
          some (.val (.word (lw + 8#64))) := by
        simp [evalHOLExact, evalListHOLExact, he2_l, valueIsWord, valueWord, wordOpHOL, wordOp]
      have hev_st8_v : @evalHOLExact 64 F _ e2.toExact (fun a => Classical.propDecidable (e2.memaddrs a))
          (.op .add [.var .local (ofString "n"), .const 1#64]) =
          some (.val (.word (nw + 1#64))) := by
        simp [evalHOLExact, evalListHOLExact, he2_n, valueIsWord, valueWord, wordOpHOL, wordOp]
      have hst8_eq : evaluateHOLFiniteState e2
          (.store (.op .add [.var .local (ofString "l"), .const 8#64])
            (.op .add [.var .local (ofString "n"), .const 1#64])) =
          (none, { e2 with memory := fun a => if a = lw + 8#64 then .word (nw + 1#64) else e2.memory a }) := by
        rw [evaluateHOLFiniteState_store, hev_st8_d, hev_st8_v]; dsimp only
        simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, he2_dom8]
      rw [hst8_eq] at hout_e2; dsimp only at hout_e2
      let st8 : PanSemStateFiniteExact 64 F :=
        { e2 with memory := fun a => if a = lw + 8#64 then .word (nw + 1#64) else e2.memory a }
      have hne_0_8 : lw + 0#64 ≠ lw + 8#64 := by
        rw [hl0_bv, hl8_bv]; intro h; have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; omega
      have hne_16_8 : lw + 16#64 ≠ lw + 8#64 := by
        rw [hl16_bv, hl8_bv]; intro h; have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; omega
      have hst8_m0 : st8.memory (lw + 0#64) = .word p0w := by
        dsimp [st8]; rw [if_neg hne_0_8]; exact hm_l0
      have hst8_m8 : st8.memory (lw + 8#64) = .word (nw + 1#64) := by
        dsimp [st8]; simp
      have hst8_m16 : st8.memory (lw + 16#64) = .word capw := by
        dsimp [st8]; rw [if_neg hne_16_8]; exact hm_l16
      have hev_ret : @evalHOLExact 64 F _ st8.toExact (fun a => Classical.propDecidable (st8.memaddrs a))
          (.op .add
            [.load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
             .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]) =
          some (.val (.word (p0w + nw * 8#64))) := by
        have hz_0 : (0#64 : BitVec 64) + 0 = 0#64 := rfl
        have hst8_l : st8.locals.lookup (ofString "l") = some (.val (.word lw)) := he2_l
        have hst8_n : st8.locals.lookup (ofString "n") = some (.val (.word nw)) := he2_n
        have hst8_e : st8.locals.lookup (ofString "esz") = some (.val (.word 8#64)) := he2_e
        have hst8_dom0 : st8.memaddrs (lw + 0#64) := he2_dom0
        simp only [evalHOLExact, evalListHOLExact, hst8_l, hst8_n, hst8_e,
          valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
          List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_0,
          memLoadHOLExact, isWfShapeExactHOL, hst8_dom0, hst8_m0, ↓reduceIte]
        rw [show (nw * 8#64 : BitVec 64) + 0 = nw * 8#64 from BitVec.add_zero _]
      rw [evaluateHOLFiniteState_return, hev_ret] at hout_e2
      dsimp only at hout_e2
      rw [if_pos (by simp [shapeOfHOLExact])] at hout_e2
      injection hout_e2 with hvb_eq hso2_eq
      have hvb_ret : ValueHOL.val (.word (p0w + nw * 8#64)) = vb := by
        cases hvb_eq; rfl
      have hmul_nw8 : (nw * 8#64).toNat = 8 * memW s (lw.toNat + 8) := by
        simp only [BitVec.toNat_mul, hnw_nat, BitVec.toNat_ofNat]
        omega
      have hslot_nat : (p0w + nw * 8#64).toNat = memW s lw.toNat + 8 * memW s (lw.toNat + 8) := by
        rw [BitVec.toNat_add, hp0w_nat, hmul_nw8, Nat.mod_eq_of_lt (by omega)]
      have hsb_mem_eq : sb.memory = st8.memory := by
        rw [← hsb_eq, ← hso2_eq]; rfl
      have hG_sb : GuestInv sb := by
        rw [← hsb_eq, ← hso2_eq]
        exact ⟨hAs.1.code, hAs.1.memaddrs, hAs.1.shMemaddrs, hAs.1.baseAddr⟩
      refine ⟨p0w + nw * 8#64, hvb_ret.symm, hslot_nat, hG_sb,
        by rw [← hsb_eq, ← hso2_eq]; rfl,
        by rw [← hsb_eq, ← hso2_eq]; rfl, ?_, ?_, ?_, ?_⟩
      · intro x hx8
        rw [hsb_mem_eq]; change (if x = lw + 8#64 then .word (nw + 1#64) else e2.memory x) = s.memory x
        rw [if_neg (by rwa [hl8_bv])]; rfl
      · have hw0 : sb.memory (BitVec.ofNat 64 lw.toNat) = .word p0w := by
          rw [hsb_mem_eq, ← hl0_bv, hst8_m0]
        unfold memW; rw [hw0]; exact hp0w_nat
      · have hw8 : sb.memory (BitVec.ofNat 64 (lw.toNat + 8)) = .word (nw + 1#64) := by
          rw [hsb_mem_eq, ← hl8_bv, hst8_m8]
        unfold memW; rw [hw8]
        change (nw + 1#64).toNat = memW s (lw.toNat + 8) + 1
        rw [BitVec.toNat_add, hnw_nat]
        have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
        rw [h1, Nat.mod_eq_of_lt (by omega)]
      · have hw16 : sb.memory (BitVec.ofNat 64 (lw.toNat + 16)) = .word capw := by
          rw [hsb_mem_eq, ← hl16_bv, hst8_m16]
        unfold memW; rw [hw16]; exact hcapw_nat

theorem ivlUnhit_of_fresh_heap_bytes_fc {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {j : Ivl}
    (hbe : post.be = s.be)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") →
        memB post b = memB s b)
    (hj_bound : j.1 + j.2 < 2 ^ 64)
    (hdj : Disj j (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")) :
    M08IvlUnhitFc s post j := by
  intro a ha8 h1 h2
  have ha_bound : a.toNat + 8 < 2 ^ 64 := by omega
  have hw : memW post a.toNat = memW s a.toNat := by
    apply (R13SoloHtabSet.memW_eq_iff_memB hbe ha8 ha8 ha_bound ha_bound).2
    intro k hk
    apply hbyte (a.toNat + k) (by omega)
    intro ⟨hlo, hhi⟩
    rcases hdj with hd | hd | hd | hd
    · omega
    · dsimp only at hd; omega
    · dsimp only at hd; omega
    · dsimp only at hd; omega
  cases hp : post.memory a with
  | word wp =>
    cases hs : s.memory a with
    | word ws =>
      simp only [memW, BitVec.ofNat_toNat, BitVec.setWidth_eq, hp, hs] at hw
      exact congrArg HolWordLab.word (BitVec.eq_of_toNat_eq hw)

theorem logEntry_fresh_heap_transport_fc {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {log : Nat}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hbe : post.be = s.be)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (haddr : globN post "vm_system_address" = globN s "vm_system_address")
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") →
        memB post b = memB s b)
    (hlog : LogEntryOK s log) :
    LogEntryOK post log ∧ logOwnedIvls post log = logOwnedIvls s log ∧
      (∀ off ∈ ([0, 8, 16, 24, 32] : List Nat),
        memW post (log + off) = memW s (log + off)) := by
  have hb : log + 40 < 2 ^ 64 := by
    have hh := hAs.2.2.1
    have hl := hlog.2.1.2
    rw [R11Shards.heapLimit_val] at hh
    dsimp only at hl
    omega
  have hu : M08IvlUnhitFc s post (log, 40) :=
    ivlUnhit_of_fresh_heap_bytes_fc hbe hhp hbyte hb
      (disj_fresh_of_allocated_fc hAs.2 hAp.2 hhp (Or.inl hlog.2.1))
  have hw : ∀ off ∈ ([0, 8, 16, 24, 32] : List Nat),
      memW post (log + off) = memW s (log + off) := by
    intro off hoff
    have ho : off + 8 ≤ 40 ∧ off % 8 = 0 := by revert off hoff; decide
    exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu
      (by have := hlog.1.1; omega) (by omega) ⟨by omega, by omega⟩
  exact ⟨logEntryOK_transport_fc hlog
      (hAp.1.memaddrs.trans hAs.1.memaddrs.symm) hhp hw,
    logOwnedIvls_transport_fc haddr hw, hw⟩

theorem avoidsTries_fresh_heap_transport_fc {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} {ivls : List Ivl}
    (hAs : ArenaReady s) (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (hAp : ArenaReady post) (hbe : post.be = s.be)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hg_kept : GlobalsKept ["heap_ptr"] s post)
    (hout_dom : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") →
        memB post b = memB s b)
    (hav : AvoidsTries s S ivls) :
    AvoidsTries post S ivls := by
  obtain ⟨Nd, hTr, hdj⟩ := hav
  have hWT : InitECandidate.Solver.Wave8Contracts.M23.WorldTypedWith s S Nd :=
    ⟨hInv.1.1, hInv.1.2.1, hInv.1.2.2.1, hTr⟩
  have hdom_eq : post.memaddrs = s.memaddrs := hAp.1.memaddrs.trans hAs.1.memaddrs.symm
  have hglob_nonHeap : ∀ nm : String, ofString nm ≠ ofString "heap_ptr" → globN post nm = globN s nm := by
    intro nm hne
    exact InitECandidate.Solver.Wave8Contracts.M08.globN_eq_of_lookup
      (hg_kept (ofString nm) (by simp [hne]))
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by
    rw [hglob_nonHeap "scratch_ptr" (by decide)]
  have hcg : ∀ g ∈ InitECandidate.Solver.Wave8Contracts.M23.coreWorldGlobals,
      globN post g = globN s g := by
    intro g hg
    have hne : ofString g ≠ ofString "heap_ptr" := by revert g hg; decide
    exact hglob_nonHeap g hne
  have hcell : InitECandidate.Solver.Wave8Contracts.M23.SameTypedCells s post S Nd := by
    have hwti_disj : ∀ i ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Nd,
        Disj i (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
      intro i hi
      exact disj_fresh_of_zero_or_allocated_fc hAs.2 hAp.2 hhp
        (InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls_allocated hWT hi)
    refine ⟨hbe, hdom_eq, hAs.1.memaddrs, ?_, ?_, ?_⟩
    · intro a hna
      apply hout_dom a
      rwa [hAs.1.memaddrs]
    · intro a ha ha8 ⟨i, hi, ha1, ha2⟩
      by_cases hdom : ordinaryDomain (BitVec.ofNat 64 a)
      · have hord := (InitECandidate.Solver.Wave8Contracts.M23.ordinaryDomain_iff (BitVec.ofNat 64 a)).mp hdom
        have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
        have hhe : heapEnd < 2 ^ 64 := by rw [R11Shards.heapEnd_val]; decide
        have ha_bound : a + 8 < 2 ^ 64 := by rw [hbit] at hord; omega
        have hw : memW post a = memW s a := by
          apply (R13SoloHtabSet.memW_eq_iff_memB (a₁ := a) (a₂ := a) hbe ha8 ha8 ha_bound ha_bound).2
          intro k hk
          apply hbyte (a + k) (by omega)
          intro ⟨hb1, hb2⟩
          rcases hwti_disj i hi with hd | hd | hd | hd
          · omega
          · dsimp only at hd; omega
          · dsimp only at hd; omega
          · dsimp only at hd; omega
        cases hp : post.memory (BitVec.ofNat 64 a) with
        | word wp =>
          cases hs : s.memory (BitVec.ofNat 64 a) with
          | word ws =>
            simp only [memW, hp, hs] at hw
            exact congrArg HolWordLab.word (BitVec.eq_of_toNat_eq hw)
      · apply hout_dom _ (by rwa [hAs.1.memaddrs])
    · intro b hb ⟨i, hi, hb1, hb2⟩
      apply hbyte b hb
      intro ⟨h1, h2⟩
      rcases hwti_disj i hi with hd | hd | hd | hd
      · omega
      · dsimp only at hd; omega
      · dsimp only at hd; omega
      · dsimp only at hd; omega
  have hfeq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [InitECandidate.Solver.Wave8Contracts.M23.blockOutObjects_eq hAs.2 hWT.2.2.1 hcell
          (hglob_nonHeap "bo" (by decide)),
        InitECandidate.Solver.Wave8Contracts.M23.balObjects_eq hAs.2 hWT.1 hWT.2.2.1 hcell
          (hglob_nonHeap "bal_accounts" (by decide)),
        hglob_nonHeap "journal" (by decide),
        hglob_nonHeap "journal_cap" (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "heap_ptr" := by revert gn hgn; decide
    rw [hglob_nonHeap gn.1 hne]
  have hFT_post := InitECandidate.Solver.Wave8Contracts.M23.fixedTyped_of_eq hAp hWT.2.2.1 hhp hsc hfeq
  obtain ⟨hWT_post, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.worldTypedWith_congr_w1
    hAs hAp hhp hsc hcg hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  refine ⟨Nd, hWT_post.2.2.2, fun o ho j hj => ?_⟩
  rw [InitECandidate.Solver.Wave8Contracts.M23.nodeExtents_eq hTr.1 hcell] at hj
  exact hdj o ho j hj

theorem logOwnedIvls_avoidsTries_fresh_heap_fc {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} {log : Nat}
    (hAs : ArenaReady s) (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (hAp : ArenaReady post) (hbe : post.be = s.be)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hg_kept : GlobalsKept ["heap_ptr"] s post)
    (hout_dom : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") →
        memB post b = memB s b)
    (hlog_ok : LogEntryOK s log)
    (hav : AvoidsTries s S (logOwnedIvls s log)) :
    AvoidsTries post S (logOwnedIvls post log) := by
  have haddr : globN post "vm_system_address" = globN s "vm_system_address" :=
    InitECandidate.Solver.Wave8Contracts.M08.globN_eq_of_lookup
      (hg_kept (ofString "vm_system_address") (by decide))
  obtain ⟨_, hown_eq, _⟩ := logEntry_fresh_heap_transport_fc hAs hAp hbe hhp haddr hbyte hlog_ok
  rw [hown_eq]
  exact avoidsTries_fresh_heap_transport_fc hAs hInv hAp hbe hhp hg_kept hout_dom hbyte hav

theorem fresh_heap_ivl_props_fc {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} {p sz : Nat}
    (hAs : ArenaReady s) (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (hAp : ArenaReady post) (hbe : post.be = s.be)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hg_kept : GlobalsKept ["heap_ptr"] s post)
    (hout_dom : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") →
        memB post b = memB s b)
    (hin_fresh : Inside (p, sz) (globN s "heap_ptr") (globN post "heap_ptr")) :
    Inside (p, sz) sourceBase (globN post "heap_ptr") ∧
    (∀ ec ∈ evmChain post, ∀ o ∈ frameObjects post ec, Disj (p, sz) o) ∧
    (∀ t ∈ S, ∀ o ∈ htabFootprint post t, Disj (p, sz) o) ∧
    (∀ o ∈ fixedObjects post, Disj (p, sz) o) ∧
    AvoidsTries post S [(p, sz)] ∧
    (∀ ec ∈ evmChain post, Disj (memW post (ec.1 + 112), 176) (p, sz)) := by
  obtain ⟨_, hch_p, _⟩ := OpHandlersB.evmInvAt_of_fresh_heap_step
    hAs hInv hAp hbe hhp hg_kept hout_dom hbyte
  have hglob_nonHeap : ∀ nm : String, ofString nm ≠ ofString "heap_ptr" → globN post nm = globN s nm := by
    intro nm hne
    exact InitECandidate.Solver.Wave8Contracts.M08.globN_eq_of_lookup
      (hg_kept (ofString nm) (by simp [hne]))
  have hdom_eq : post.memaddrs = s.memaddrs := hAp.1.memaddrs.trans hAs.1.memaddrs.symm
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by
    rw [hglob_nonHeap "scratch_ptr" (by decide)]
  have hcg : ∀ g ∈ InitECandidate.Solver.Wave8Contracts.M23.coreWorldGlobals,
      globN post g = globN s g := by
    intro g hg
    have hne : ofString g ≠ ofString "heap_ptr" := by revert g hg; decide
    exact hglob_nonHeap g hne
  obtain ⟨Nd_s, hTr_s, _⟩ := hInv.2.2.2.2.2.2.2.2.2.1
  have hWT_s : InitECandidate.Solver.Wave8Contracts.M23.WorldTypedWith s S Nd_s :=
    ⟨hInv.1.1, hInv.1.2.1, hInv.1.2.2.1, hTr_s⟩
  have hcell : InitECandidate.Solver.Wave8Contracts.M23.SameTypedCells s post S Nd_s := by
    have hwti_disj : ∀ i ∈ InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls s S Nd_s,
        Disj i (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
      intro i hi
      exact disj_fresh_of_zero_or_allocated_fc hAs.2 hAp.2 hhp
        (InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls_allocated hWT_s hi)
    refine ⟨hbe, hdom_eq, hAs.1.memaddrs, ?_, ?_, ?_⟩
    · intro a hna; apply hout_dom a; rwa [hAs.1.memaddrs]
    · intro a ha ha8 ⟨i, hi, ha1, ha2⟩
      by_cases hdom : ordinaryDomain (BitVec.ofNat 64 a)
      · have hord := (InitECandidate.Solver.Wave8Contracts.M23.ordinaryDomain_iff (BitVec.ofNat 64 a)).mp hdom
        have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
        have hhe : heapEnd < 2 ^ 64 := by rw [R11Shards.heapEnd_val]; decide
        have ha_bound : a + 8 < 2 ^ 64 := by rw [hbit] at hord; omega
        have hw : memW post a = memW s a := by
          apply (R13SoloHtabSet.memW_eq_iff_memB (a₁ := a) (a₂ := a) hbe ha8 ha8 ha_bound ha_bound).2
          intro k hk
          apply hbyte (a + k) (by omega)
          intro ⟨hb1, hb2⟩
          rcases hwti_disj i hi with hd | hd | hd | hd
          · omega
          · dsimp only at hd; omega
          · dsimp only at hd; omega
          · dsimp only at hd; omega
        cases hp : post.memory (BitVec.ofNat 64 a) with
        | word wp =>
          cases hs : s.memory (BitVec.ofNat 64 a) with
          | word ws =>
            simp only [memW, hp, hs] at hw
            exact congrArg HolWordLab.word (BitVec.eq_of_toNat_eq hw)
      · apply hout_dom _ (by rwa [hAs.1.memaddrs])
    · intro b hb ⟨i, hi, hb1, hb2⟩
      apply hbyte b hb
      intro ⟨h1, h2⟩
      rcases hwti_disj i hi with hd | hd | hd | hd
      · omega
      · dsimp only at hd; omega
      · dsimp only at hd; omega
      · dsimp only at hd; omega
  have hfeq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [InitECandidate.Solver.Wave8Contracts.M23.blockOutObjects_eq hAs.2 hWT_s.2.2.1 hcell
          (hglob_nonHeap "bo" (by decide)),
        InitECandidate.Solver.Wave8Contracts.M23.balObjects_eq hAs.2 hWT_s.1 hWT_s.2.2.1 hcell
          (hglob_nonHeap "bal_accounts" (by decide)),
        hglob_nonHeap "journal" (by decide),
        hglob_nonHeap "journal_cap" (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "heap_ptr" := by revert gn hgn; decide
    rw [hglob_nonHeap gn.1 hne]
  have hFT_post := InitECandidate.Solver.Wave8Contracts.M23.fixedTyped_of_eq hAp hWT_s.2.2.1 hhp hsc hfeq
  obtain ⟨hWT_post, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.worldTypedWith_congr_w1
    hAs hAp hhp hsc hcg hcell hWT_s
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hfp_eq : ∀ t ∈ S, htabFootprint post t = htabFootprint s t :=
    fun t ht => InitECandidate.Solver.Wave8Contracts.M23.htabFootprint_eq hcell ht (hWT_s.1.2.1 t ht).1
  have hdj_alloc_s : ∀ o : Ivl, o.2 = 0 ∨ Allocated s o → Disj (p, sz) o := by
    intro o ho
    exact disj_symm_fc (InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_right
      (by rw [Nat.add_sub_of_le hhp]; exact hin_fresh)
      (disj_fresh_of_zero_or_allocated_fc hAs.2 hAp.2 hhp ho))
  have hhe_lt : heapEnd < 2 ^ 64 := by rw [R11Shards.heapEnd_val]; decide
  have hu_fo : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, o.1 + o.2 < 2 ^ 64 →
      M08IvlUnhitFc s post o := by
    intro ec hec o ho hob
    exact ivlUnhit_of_fresh_heap_bytes_fc hbe hhp hbyte hob
      (disj_fresh_of_frameObject_fc hAs.2 hAp.2 hhp (hInv.2.2.2.2.1 ec hec) ho)
  have hrec_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    have hFW := hInv.2.2.2.2.1 ec hec
    have hse_lt : scratchEnd < 2 ^ 64 := by rw [R11Shards.scratchEnd_val]; decide
    have hb1 : ec.1 + 280 < 2 ^ 64 := by
      have h := (hFW.1 (ec.1, 280) (by simp)).1.2; dsimp only at h; omega
    have hb88 : memW s (ec.1 + 88) + 24 < 2 ^ 64 := by
      have h := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1.2; dsimp only at h; omega
    have he1_8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
    have he88_8 : (memW s (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2.1
    refine ⟨fun k hk hk8 => InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
              (hu_fo ec hec (ec.1, 280) (by simp [frameObjects]) hb1)
              (by omega) (by omega) ⟨by omega, by omega⟩,
            fun k hk hk8 => InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
              (hu_fo ec hec (memW s (ec.1 + 88), 24) (by simp [frameObjects]) hb88)
              (by omega) (by omega) ⟨by omega, by omega⟩⟩
  have hfo_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec := by
    intro ec hec
    have hFW := hInv.2.2.2.2.1 ec hec
    obtain ⟨he_eq, h88_eq⟩ := hrec_eq ec hec
    have hl0 : memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) := by
      simpa using h88_eq 0 (by omega) (by omega)
    have hl8 : memW post (memW s (ec.1 + 88) + 8) = memW s (memW s (ec.1 + 88) + 8) :=
      h88_eq 8 (by omega) (by omega)
    have hl16 : memW post (memW s (ec.1 + 88) + 16) = memW s (memW s (ec.1 + 88) + 16) :=
      h88_eq 16 (by omega) (by omega)
    have harr_eq : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
        memW post (memW s (memW s (ec.1 + 88)) + 8 * i) = memW s (memW s (memW s (ec.1 + 88)) + 8 * i) := by
      intro i hi
      have hfl_in : frameLogs s ec ∈ frameObjects s ec := by simp [frameObjects]
      have hlen_le := hFW.2.2.2.2.2.2.2.2.2.2.2.1
      have hfl_b : (frameLogs s ec).1 + (frameLogs s ec).2 < 2 ^ 64 := by
        rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.1 with ⟨_, h2⟩ | ⟨_, h2⟩
        · have hh := hAs.2.2.1; rw [R11Shards.heapLimit_val] at hh; omega
        · have hs := R11Shards.scratchEnd_val; omega
      have hfl_8 : (memW s (memW s (ec.1 + 88))) % 8 = 0 := hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
      exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
        (hu_fo ec hec _ hfl_in hfl_b)
        (by unfold frameLogs at hfl_b; omega) (by omega)
        ⟨by unfold frameLogs; omega, by unfold frameLogs; omega⟩
    have hflo_eq : frameLogObjects post ec = frameLogObjects s ec := by
      unfold frameLogObjects; dsimp only
      rw [he_eq 88 (by omega) (by omega), hl8]
      apply List.flatMap_congr; intro i hi; rw [List.mem_range] at hi
      rw [hl0, harr_eq i hi]
      rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
      · have he88_in := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1.1
        have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
        rw [R11Shards.scratchStart_val] at h1; dsimp only at he88_in; omega
      · exact (logEntry_fresh_heap_transport_fc hAs hAp hbe hhp
          (hglob_nonHeap "vm_system_address" (by decide)) hbyte (hent i hi).2).2.1
    unfold frameObjects frameLogs frameRet
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 24 (by omega) (by omega), he_eq 40 (by omega) (by omega),
        he_eq 88 (by omega) (by omega), hl0, hl16,
        he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega), hflo_eq]
  refine ⟨⟨le_trans hAs.2.1 hin_fresh.1, hin_fresh.2⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro ec hec o ho
    rw [hch_p] at hec; rw [hfo_eq ec hec] at ho
    exact disj_symm_fc (InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_right
      (by rw [Nat.add_sub_of_le hhp]; exact hin_fresh)
      (disj_fresh_of_frameObject_fc hAs.2 hAp.2 hhp (hInv.2.2.2.2.1 ec hec) ho))
  · intro t ht o ho
    rw [hfp_eq t ht] at ho
    exact hdj_alloc_s o (Or.inr ((hWT_s.1.2.1 t ht).2 o ho).1)
  · intro o ho
    rw [hfeq] at ho
    exact hdj_alloc_s o ((hWT_s.2.2.1.1 o ho).imp id And.left)
  · refine ⟨Nd_s, hWT_post.2.2.2, fun x hx j hj => ?_⟩
    rw [List.mem_singleton] at hx; subst hx
    rw [InitECandidate.Solver.Wave8Contracts.M23.nodeExtents_eq hTr_s.1 hcell] at hj
    exact hdj_alloc_s j (InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls_allocated hWT_s
      (by simp [InitECandidate.Solver.Wave8Contracts.M23.worldTypedIvls, hj]))
  · intro ec hec
    rw [hch_p] at hec
    rw [(hrec_eq ec hec).1 112 (by omega) (by omega)]
    exact disj_symm_fc (hdj_alloc_s _ (Or.inr (hInv.2.2.2.2.1 ec hec).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
