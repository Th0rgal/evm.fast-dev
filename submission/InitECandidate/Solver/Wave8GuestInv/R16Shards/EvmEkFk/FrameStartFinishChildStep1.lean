import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.FrameStartFinishChild
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.StorageCreateFinish

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8Contracts.M23 (EvmStep EvmKeeps EvmAvoids GlobalsKept)
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.StorageCreateFinish

section CreateFinishSpecsProof

private def CfStep {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  EvmStep ["heap_ptr", "journal_n", "scratch_ptr"] s post ∧
  OpDispatchSpec.evmR post ≤ OpDispatchSpec.evmR s ∧
  memW post (globN s "cur_cont" + 48) = memW s (globN s "cur_cont" + 48) ∧
  ChainCellsAgree s post

private theorem cfStep_refl {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s) : CfStep s s :=
  ⟨evmStep_refl_gw hInv, le_rfl, rfl, chainCellsAgree_refl s⟩

private theorem cfStep_with_locals_clock {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (h : CfStep s post) (ls : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    CfStep s { post with locals := ls, clock := k } := by
  refine ⟨evmStep_with_locals_clock h.1 ls k, ?_, h.2.2.1, h.2.2.2⟩
  rw [evmR_lc_fc post ls k]; exact h.2.1

private theorem cfStep_trans {F : Type} {a b c : PanSemStateFiniteExact 64 F}
    (h1 : CfStep a b) (h2 : CfStep b c) : CfStep a c := by
  have hcc_ab : globN b "cur_cont" = globN a "cur_cont" :=
    InitECandidate.Solver.Wave8Contracts.M08.globN_eq_of_lookup (h1.1.2.2.1 (ofString "cur_cont") (by decide))
  refine ⟨evmStep_trans h1.1 h2.1, le_trans h2.2.1 h1.2.1, ?_,
    chainCellsAgree_trans h1.2.2.2 h1.1.2.2.2 h2.2.2.2⟩
  rw [← hcc_ab]
  exact h2.2.2.1.trans (hcc_ab ▸ h1.2.2.1)

private def HeadSafeAddrCf (e0 c0 a : Nat) : Prop :=
  (∃ k, a = e0 + k ∧ k < 280 ∧ k ≠ 24 ∧ k ≠ 32 ∧ k ≠ 40) ∨
  (∃ k, a = c0 + k ∧ k < 104 ∧ k ≠ 48 ∧ k ≠ 56)

private theorem evmInv_head_ev_bounds_cf {F : Type} {s : PanSemStateFiniteExact 64 F} (hInv : EvmInv s) :
    0 < globN s "ev" ∧ globN s "ev" + 280 ≤ 2 ^ 64 := by
  obtain ⟨hAs, S, _, _, _, _, hFW_all, _⟩ := hInv
  have hSS : scratchStart = 2952790016 := rfl
  have hSE : scratchEnd = 2965299200 := rfl
  have hfmp := hAs.2.2.2.1
  have hsp := hAs.2.2.2.2.1
  rw [hSS] at hfmp
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    unfold evmChain
    have hmc : 0 < maxChain := by decide
    obtain ⟨m, hm⟩ : ∃ m, maxChain = m + 1 := ⟨maxChain - 1, by omega⟩
    rw [hm]; simp [evmChainFrom]
  have he_in := ((hFW_all _ hhead).1 (globN s "ev", 280) (by simp)).1
  dsimp only [Inside] at he_in
  rw [hSE] at he_in
  omega

private theorem headSafeAddr_preserves_cells_cf {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hE : EvmInv s)
    (hmem_out : ∀ x : BitVec 64,
      ¬ HeadSafeAddrCf (globN s "ev") (globN s "cur_cont") x.toNat →
      post.memory x = s.memory x) :
    memW post (globN s "cur_cont" + 48) = memW s (globN s "cur_cont" + 48) ∧
    ChainCellsAgree s post := by
  obtain ⟨_, S, _, hrest⟩ := hE
  dsimp only at hrest
  obtain ⟨_, _, _, hFWF, _, _, hPair, _⟩ := hrest
  obtain ⟨tl, hcs⟩ : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl := ⟨_, rfl⟩
  have hSE : scratchEnd = 2965299200 := rfl
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by rw [hcs]; exact List.mem_cons_self
  have hFW0 := hFWF _ hhead
  have he_in := (hFW0.1 (globN s "ev", 280) (by simp)).1.2
  have hc_in := (hFW0.1 (globN s "cur_cont", 104) (by simp)).1.2
  dsimp only at he_in hc_in
  rw [hcs, List.map_cons, List.flatten_cons, List.pairwise_append] at hPair
  obtain ⟨hP0, _, hcross⟩ := hPair
  have hdec : Disj (globN s "ev", 280) (globN s "cur_cont", 104) := by
    unfold frameObjects at hP0
    exact (List.pairwise_cons.mp (List.pairwise_append.mp hP0).1).1 _ (by simp)
  have hsafe : ∀ a : Nat, a < 2 ^ 64 →
      ¬ HeadSafeAddrCf (globN s "ev") (globN s "cur_cont") a → memW post a = memW s a := by
    intro a hlt hne
    unfold memW
    rw [hmem_out (BitVec.ofNat 64 a)]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    exact hne
  constructor
  · unfold Disj at hdec; dsimp only at hdec
    rw [hSE] at he_in hc_in
    apply hsafe (globN s "cur_cont" + 48) (by omega)
    rintro (⟨k, hk, _⟩ | ⟨k, hk, _⟩) <;> omega
  · intro ec hec
    rw [hcs] at hec
    rcases List.mem_cons.mp hec with rfl | htl
    · unfold Disj at hdec; dsimp only at hdec
      rw [hSE] at he_in hc_in
      refine ⟨hsafe (globN s "ev" + 24) (by omega) ?_,
              hsafe (globN s "ev" + 32) (by omega) ?_,
              hsafe (globN s "ev" + 40) (by omega) ?_,
              hsafe (globN s "cur_cont" + 56) (by omega) ?_⟩ <;>
        (rintro (⟨k, hk, _⟩ | ⟨k, hk, _⟩) <;> omega)
    · have hFec := hFWF ec (by rw [hcs]; exact List.mem_cons_of_mem _ htl)
      have hr_in := (hFec.1 (ec.1, 280) (by simp)).1.2
      have hk_in := (hFec.1 (ec.2, 104) (by simp)).1.2
      dsimp only at hr_in hk_in
      have hmemb : ∀ o ∈ [(ec.1, 280), (ec.2, 104)],
          o ∈ ((tl.map (frameObjects s)).flatten) := by
        intro o ho
        exact List.mem_flatten.2 ⟨frameObjects s ec, List.mem_map_of_mem htl,
          by unfold frameObjects; simp only [List.mem_cons, List.mem_append] at ho ⊢; tauto⟩
      have hA : (globN s "ev", 280) ∈ frameObjects s (globN s "ev", globN s "cur_cont") := by
        unfold frameObjects; simp
      have hB : (globN s "cur_cont", 104) ∈ frameObjects s (globN s "ev", globN s "cur_cont") := by
        unfold frameObjects; simp
      have d1 := hcross _ hA _ (hmemb (ec.1, 280) (by simp))
      have d2 := hcross _ hB _ (hmemb (ec.1, 280) (by simp))
      have d3 := hcross _ hA _ (hmemb (ec.2, 104) (by simp))
      have d4 := hcross _ hB _ (hmemb (ec.2, 104) (by simp))
      unfold Disj at d1 d2 d3 d4; dsimp only at d1 d2 d3 d4
      rw [hSE] at he_in hc_in hr_in hk_in
      refine ⟨hsafe (ec.1 + 24) (by omega) ?_,
              hsafe (ec.1 + 32) (by omega) ?_,
              hsafe (ec.1 + 40) (by omega) ?_,
              hsafe (ec.2 + 56) (by omega) ?_⟩ <;>
        (rintro (⟨k, hk, _⟩ | ⟨k, hk, _⟩) <;> omega)

private def HeadSafeValProgCf : ExpHOL 64 → Bool
  | .const _ | .op _ _ | .shift _ _ _ | .cmp _ _ _ => true
  | _ => false

private def HeadSafeStoreProgCf (dst val : ExpHOL 64) : Bool :=
  match dst with
  | .op .add [.var .global g, .const k] =>
    (g == ofString "ev") &&
    decide (k.toNat + 8 ≤ 280 ∧ k.toNat % 8 = 0 ∧ k.toNat ≠ 24 ∧ k.toNat ≠ 32 ∧ k.toNat ≠ 40) &&
    HeadSafeValProgCf val
  | _ => false

private def headSafeProgCf (good : MlS → Bool) : ProgHOL 64 → Bool
  | .dec _ _ _ body => headSafeProgCf good body
  | .seq first second => headSafeProgCf good first && headSafeProgCf good second
  | .ite _ yes no => headSafeProgCf good yes && headSafeProgCf good no
  | .decCall _ _ fname _ cont => good fname && headSafeProgCf good cont
  | .store dst val => HeadSafeStoreProgCf dst val
  | .assign .local _ _ => true
  | .primitive _ _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | _ => false

private def HeadSafeStepCf {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  post.code = s.code ∧ post.globals = s.globals ∧
    ∀ a : BitVec 64, ¬ HeadSafeAddrCf (globN s "ev") (globN s "cur_cont") a.toNat → post.memory a = s.memory a

private theorem HeadSafeStepCf.of_locFrame {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : LocFrame s post) : HeadSafeStepCf s post := by
  refine ⟨by unfold LocFrame at h; rw [h], by unfold LocFrame at h; rw [h], fun a _ => ?_⟩
  unfold LocFrame at h; rw [h]

private theorem HeadSafeStepCf.trans {F : Type} {s m post : PanSemStateFiniteExact 64 F}
    (h1 : HeadSafeStepCf s m) (h2 : HeadSafeStepCf m post) : HeadSafeStepCf s post := by
  refine ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun a ha => ?_⟩
  have hev : globN m "ev" = globN s "ev" := by unfold globN; rw [h1.2.1]
  have hcc : globN m "cur_cont" = globN s "cur_cont" := by unfold globN; rw [h1.2.1]
  exact (h2.2.2 a (by rw [hev, hcc]; exact ha)).trans (h1.2.2 a ha)

private theorem HeadSafeStepCf.with_locals_clock {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : HeadSafeStepCf s post) (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    HeadSafeStepCf s { post with locals := L, clock := k } := h

private def HeadSafeOrTrappedCf {F : Type} (s : PanSemStateFiniteExact 64 F)
    (out : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F) : Prop :=
  HeadSafeStepCf s out.2 ∨
    (out.1 ≠ none ∧ out.1 ≠ some .continue ∧ out.1 ≠ some .break ∧
     ¬ InitECandidate.Solver.Wave8Contracts.M23.Resumes out.1)

private theorem HeadSafeOrTrappedCf.to_resumes {F : Type} {s : PanSemStateFiniteExact 64 F}
    {out : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F}
    (h : HeadSafeOrTrappedCf s out)
    (hr : InitECandidate.Solver.Wave8Contracts.M23.Resumes out.1) : HeadSafeStepCf s out.2 :=
  h.elim id (fun ⟨_, _, _, hnr⟩ => (hnr hr).elim)

private theorem headSafeValProgCf_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (val : ExpHOL 64) (hshape : HeadSafeValProgCf val = true)
    (vv : ValueHOL 64)
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val = some vv) :
    ∃ w : BitVec 64, vv = .val (.word w) := by
  cases val with
  | const w =>
    simp [evalHOLExact] at hv; exact ⟨w, hv.symm⟩
  | op op es =>
    simp [evalHOLExact] at hv
    rcases hes : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) es with _ | vs
    · rw [hes] at hv; simp at hv
    · rw [hes] at hv; dsimp only at hv
      split at hv
      · rcases hw : wordOpHOL op (List.map valueWord vs) with _ | w
        · rw [hw] at hv; simp at hv
        · rw [hw] at hv; simp at hv; exact ⟨w, hv.symm⟩
      · simp at hv
  | shift sh e n =>
    simp [evalHOLExact] at hv
    rcases he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | ev
    · rw [he] at hv; simp at hv
    · rw [he] at hv
      rcases hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) n with _ | nv
      · rw [hn] at hv; rcases ev with ⟨⟨_⟩⟩ | _ | _ <;> simp at hv
      · rw [hn] at hv
        rcases ev with ⟨⟨w1⟩⟩ | _ | _ <;> rcases nv with ⟨⟨w2⟩⟩ | _ | _ <;> try simp at hv
        rcases hs_w : wordShiftHOL sh w1 w2.toNat with _ | w
        · rw [hs_w] at hv; simp at hv
        · rw [hs_w] at hv; simp at hv; exact ⟨w, hv.symm⟩
  | cmp c e1 e2 =>
    simp [evalHOLExact] at hv
    rcases he1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
    · rw [he1] at hv; simp at hv
    · rw [he1] at hv
      rcases he2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | v2
      · rw [he2] at hv; simp at hv
      · rw [he2] at hv
        rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;> simp at hv
        exact ⟨_, hv.symm⟩
  | _ => simp [HeadSafeValProgCf] at hshape

private theorem evaluate_headSafeProgCf {F : Type} (good : MlS → Bool)
    (hgood : ∀ function, good function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      readOnlyProg good body = true)
    (program : ProgHOL 64) (supported : headSafeProgCf good program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode)
    (hev_pos : 0 < globN state "ev") (hev_bnd : globN state "ev" + 280 ≤ 2 ^ 64) :
    HeadSafeOrTrappedCf state (evaluateHOLFiniteState state program) := by
  cases shape : program with
  | skip =>
    rw [evaluateHOLFiniteState_skip]; exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
  | «break» =>
    rw [evaluateHOLFiniteState_break]; exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
  | «continue» =>
    rw [evaluateHOLFiniteState_continue]; exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
  | annot _ _ =>
    rw [evaluateHOLFiniteState_annot]; exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
  | raise _ _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
    · exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
    · split <;> exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
  | assign kind _ _ =>
    cases kind with
    | global => simp [shape, headSafeProgCf] at supported
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
      · split <;> exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
  | primitive _ _ _ =>
    rw [evaluateHOLFiniteState_primitive]
    split
    · exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
    · split
      · exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
      · split <;> exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
  | dec name _ expr body =>
    have child : headSafeProgCf good body = true := by simpa [shape, headSafeProgCf] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
    · rename_i v _
      split
      · have ih := evaluate_headSafeProgCf good hgood body child (setVarHOLFinite name v state) code hev_pos hev_bnd
        rcases hrun : evaluateHOLFiniteState (setVarHOLFinite name v state) body with ⟨r, st⟩
        rw [hrun] at ih; dsimp only at ih ⊢
        rcases ih with hstep | htrap
        · exact Or.inl ⟨hstep.1, hstep.2.1, hstep.2.2⟩
        · exact Or.inr htrap
      · exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
  | seq first second =>
    have children : headSafeProgCf good first = true ∧ headSafeProgCf good second = true := by
      simpa only [shape, headSafeProgCf, Bool.and_eq_true] using supported
    have ih1 := evaluate_headSafeProgCf good hgood first children.1 state code hev_pos hev_bnd
    have remaining := evaluateHOLFiniteState_clock_le state first
    rw [evaluateHOLFiniteState_seq_line780]
    rcases firstRun : evaluateHOLFiniteState state first with ⟨result, middle⟩
    rw [firstRun] at ih1 remaining; dsimp only at ih1 remaining ⊢
    cases result with
    | none =>
      rcases ih1 with hstep1 | ⟨hnn, _⟩
      · dsimp only at hstep1
        have mclock : middle.clock ≤ state.clock := remaining
        have hev_m : globN middle "ev" = globN state "ev" := by unfold globN; rw [hstep1.2.1]
        have ih2 := evaluate_headSafeProgCf good hgood second children.2 middle
          (hstep1.1.trans code) (by rw [hev_m]; exact hev_pos) (by rw [hev_m]; exact hev_bnd)
        rcases ih2 with hstep2 | htrap2
        · exact Or.inl (hstep1.trans hstep2)
        · exact Or.inr htrap2
      · exact absurd rfl hnn
    | some r =>
      rcases ih1 with hstep1 | ⟨_, hnc, hnb, hnr⟩
      · exact Or.inl hstep1
      · exact Or.inr ⟨by simp, hnc, hnb, hnr⟩
  | ite condition yes no =>
    have children : headSafeProgCf good yes = true ∧ headSafeProgCf good no = true := by
      simpa only [shape, headSafeProgCf, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_headSafeProgCf good hgood no children.2 state code hev_pos hev_bnd
      · exact evaluate_headSafeProgCf good hgood yes children.1 state code hev_pos hev_bnd
    · exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
  | decCall name _ function arguments continuation =>
    have children : good function = true ∧ headSafeProgCf good continuation = true := by
      simpa only [shape, headSafeProgCf, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    rcases hargs : evalListHOLFinite state
        (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with _ | values
    · exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
    · dsimp only
      rcases found : PanSemStateFiniteExact.lookupCodeHOLFinite state.code.lookup function values with _ | ⟨body, callee, rs⟩
      · exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
      · dsimp only
        have found' : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
            some (body, callee, rs) := by rwa [← code]
        have bodyOk := hgood function children.1 values body callee rs found'
        split
        · exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
        · have ih := evaluate_readOnlyProg good hgood body bodyOk
            (callEntryStateHOLFinite state callee) code
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨res, st⟩
          rw [hrun] at ih cl; dsimp only at ih cl ⊢
          change st.clock ≤ state.clock - 1 at cl
          have small : st.clock < state.clock := by omega
          cases res with
          | none =>
            rcases ih with hloc | ⟨hnn, _⟩
            · dsimp only at hloc
              have ih' : LocFrame state st := by unfold LocFrame at hloc ⊢; rw [hloc]; rfl
              exact Or.inl (HeadSafeStepCf.of_locFrame ih')
            · exact absurd rfl hnn
          | some r =>
            cases r with
            | returned v =>
              have hloc : LocFrame (callEntryStateHOLFinite state callee) st :=
                ih.to_resumes (Or.inl ⟨v, rfl⟩)
              have ih' : LocFrame state st := by unfold LocFrame at hloc ⊢; rw [hloc]; rfl
              dsimp only
              split
              · set resumed := setVarHOLFinite name v { st with locals := state.locals }
                have smallR : resumed.clock < state.clock := small
                have ihR : HeadSafeStepCf state resumed :=
                  (HeadSafeStepCf.of_locFrame ih').with_locals_clock _ _
                have hev_r : globN resumed "ev" = globN state "ev" := by unfold globN; rw [ihR.2.1]
                have ih2 := evaluate_headSafeProgCf good hgood continuation children.2 resumed
                  (ihR.1.trans code) (by rw [hev_r]; exact hev_pos) (by rw [hev_r]; exact hev_bnd)
                rcases hcont : evaluateHOLFiniteState resumed continuation with ⟨res2, st2⟩
                rw [hcont] at ih2
                rcases ih2 with hstep2 | ⟨hnn2, hnc2, hnb2, hnr2⟩
                · exact Or.inl ((ihR.trans hstep2).with_locals_clock _ _)
                · exact Or.inr ⟨hnn2, hnc2, hnb2, hnr2⟩
              · exact Or.inl (HeadSafeStepCf.of_locFrame ih')
            | timeOut | error | exception _ _ | finalFfi _ =>
              rcases ih with hloc | ⟨_, _, _, hnr⟩
              · dsimp only at hloc
                have ih' : LocFrame state st := by unfold LocFrame at hloc ⊢; rw [hloc]; rfl
                exact Or.inl ((HeadSafeStepCf.of_locFrame ih').with_locals_clock _ _)
              · exact Or.inr ⟨by simp, by simp, by simp, hnr⟩
            | «break» | «continue» =>
              rcases ih with hloc | _
              · dsimp only at hloc
                have ih' : LocFrame state st := by unfold LocFrame at hloc ⊢; rw [hloc]; rfl
                exact Or.inl (HeadSafeStepCf.of_locFrame ih')
              · exact Or.inr ⟨by simp, by simp, by simp,
                  by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h⟩
  | store dst val =>
    have hdst : HeadSafeStoreProgCf dst val = true := by simpa [shape, headSafeProgCf] using supported
    cases dst with
    | op op es =>
      cases op <;> try simp [HeadSafeStoreProgCf] at hdst
      rcases es with _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩ <;> try simp [HeadSafeStoreProgCf] at hdst
      cases e1 with
      | var vk g =>
        cases vk <;> try simp [HeadSafeStoreProgCf] at hdst
        cases e2 with
        | const k =>
          simp only [HeadSafeStoreProgCf, beq_iff_eq, decide_eq_true_eq, Bool.and_eq_true] at hdst
          obtain ⟨⟨rfl, hk_le, hk8, hk24, hk32, hk40⟩, hval_sh⟩ := hdst
          have hk24' : k.toNat ≠ 24 := by simpa using hk24
          have hk32' : k.toNat ≠ 32 := by simpa using hk32
          have hk40' : k.toNat ≠ 40 := by simpa using hk40
          obtain ⟨evw, hevw⟩ : ∃ w : BitVec 64, state.globals.lookup (ofString "ev") = some (.val (.word w)) :=
            globalWord_of_globN_pos state "ev" hev_pos
          have hevw_nat : evw.toNat = globN state "ev" := by unfold globN; simp [hevw]
          rcases hst : evaluateHOLFiniteState state (.store (.op .add [.var .global (ofString "ev"), .const k]) val) with ⟨r, post⟩
          cases r with
          | some res =>
            have herr := store_some_eq_error' hst; subst herr
            exact Or.inr ⟨by simp, by simp, by simp, by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h⟩
          | none =>
            rw [evaluateHOLFiniteState_store] at hst
            have had_ev : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
                (.op .add [.var .global (ofString "ev"), .const k]) = some (.val (.word (evw + k))) := by
              simp [evalHOLExact, evalListHOLExact, hevw, wordOpHOL, wordOp, valueIsWord, valueWord]
            rw [had_ev] at hst; dsimp only at hst
            rcases hv : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) val with _ | vv
            · rw [hv] at hst; simp at hst
            · obtain ⟨vw, rfl⟩ := headSafeValProgCf_word state val hval_sh vv hv
              rw [hv] at hst; dsimp only at hst
              have hfl_vw : flattenHOL (.val (.word vw) : ValueHOL 64) = [.word vw] := by
                simp [flattenHOL]
              rw [hfl_vw] at hst
              simp only [panMemStoresHOL, panMemStoreHOL] at hst
              by_cases hdom : state.memaddrs (evw + k)
              · simp only [hdom, ↓reduceIte] at hst
                injection hst with _ hp_eq; subst hp_eq
                refine Or.inl ⟨rfl, rfl, fun a ha => ?_⟩
                have hk_nat : (evw + k).toNat = globN state "ev" + k.toNat := by
                  rw [BitVec.toNat_add, hevw_nat, Nat.mod_eq_of_lt (by omega)]
                have hne : a ≠ evw + k := by
                  rintro rfl
                  exact ha (Or.inl ⟨k.toNat, hk_nat, by omega, hk24', hk32', hk40'⟩)
                dsimp only; rw [if_neg hne]
              · simp only [hdom, ↓reduceIte] at hst; simp at hst
        | _ => simp [HeadSafeStoreProgCf] at hdst
      | _ => simp [HeadSafeStoreProgCf] at hdst
    | _ => simp [HeadSafeStoreProgCf] at hdst
  | _ => simp [shape, headSafeProgCf] at supported
termination_by (state.clock, sizeOf program)
decreasing_by
  all_goals
    simp_wf
    apply InitECandidate.Solver.GuestGlobalKeep.lex_of
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite,
      ProgHOL.seq.sizeOf_spec, ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec,
      ProgHOL.decCall.sizeOf_spec, true_and]
    first
      | exact Or.inl smallR
      | exact Or.inl small
      | (rcases Nat.lt_or_eq_of_le mclock with h | h
         · exact Or.inl h
         · exact Or.inr (And.intro h (by simp +arith)))
      | exact Or.inr (by simp +arith)

private theorem cfStep_of_eps_call0 {F : Type}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} (hf : EvmPreservingSpec (fun _ => True) Qc fname)
    (honly : ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, rs) →
      ∃ good, (∀ f, good f = true → ∀ vs b c r,
        lookupCodeHOLFinite originalRuntimeCode.lookup f vs = some (b, c, r) →
        onlyEvmOrTrapRaise good b = true) ∧ onlyEvmOrTrapRaise good body = true)
    (hsafe : ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, rs) →
      headSafeProgCf opRoCallees body = true)
    (hret1 : ∀ params body retShape,
      originalRuntimeCode.lookup fname = some (params, body, retShape) → retShape = .one)
    (args : List (ExpHOL 64))
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode) (hInv : EvmInv s)
    (hnt : (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1) :
    CfStep s (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).2 ∧
    ((evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = none →
      (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).2.locals = s.locals ∧
      (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).2.code = originalRuntimeCode) := by
  obtain ⟨params_f, body_f, ret_f, hlook_f, hspec_f⟩ := hf
  have hrf1 : ret_f = .one := hret1 params_f body_f ret_f hlook_f
  subst hrf1
  obtain ⟨hev_pos, hev_bnd⟩ := evmInv_head_ev_bounds_cf hInv
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname vs = some (body', callee, ret') := by
          rwa [← hc]
        have hsame := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup fname
          params_f body_f body' .one ret' vs callee hlook_f hl_orig
        have hret_eq := lookupCodeHOLFinite_installed_return s fname
          params_f body_f body' .one ret' vs callee (by rw [hc]; exact hlook_f) hl
        subst hsame; subst hret_eq
        let ent := callEntryStateHOLFinite s callee
        have hInv_ent : EvmInv ent := localsFree_evmInv s callee (s.clock - 1) hInv
        have hent_code : ent.code = originalRuntimeCode := hc
        have hhs_body := evaluate_headSafeProgCf opRoCallees opRoCallees_good body'
          (hsafe vs body' callee .one hl_orig) ent hent_code hev_pos hev_bnd
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata ent body').1
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨cres, cpost⟩
        simp only [ent] at hrun hmeta hhs_body
        simp only [hrun] at hmeta hhs_body hnt hfr ⊢
        have hnt_ent : (evaluateHOLFiniteState ent body').1 ≠ some .timeOut := by
          simp only [ent, hrun]; rintro rfl; simp at hnt
        have hsp := hspec_f ent hent_code hInv_ent trivial ⟨vs, hl_orig⟩ hnt_ent
        simp only [ent, hrun] at hsp
        cases cres with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some r =>
          cases r with
          | timeOut => simp at hnt
          | «break» | «continue» | error => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : shapeEqHOL (shapeOfHOLExact v) .one = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              obtain ⟨hInv_cp, hch_cp, hR_cp, _⟩ := hsp.1 v rfl
              have hstep_hs := hhs_body.to_resumes (Or.inl ⟨v, rfl⟩)
              have hg_cp : cpost.globals = s.globals := hstep_hs.2.1
              have hcells := headSafeAddr_preserves_cells_cf hInv hstep_hs.2.2
              have hInv_out : EvmInv { cpost with locals := s.locals } :=
                localsFree_evmInv cpost s.locals cpost.clock hInv_cp
              have hhp_eq : globN { cpost with locals := s.locals } "heap_ptr" = globN s "heap_ptr" := by
                simp [globN, hg_cp]
              have hgk : GlobalsKept ["heap_ptr", "journal_n", "scratch_ptr"] s { cpost with locals := s.locals } := by
                intro g _; simp [hg_cp]
              have hch_out : evmChain { cpost with locals := s.locals } = evmChain s := by
                rw [evmChain_with_locals cpost s.locals cpost.clock, hch_cp]
                exact evmChain_with_locals s callee (s.clock - 1)
              have hR_out : OpDispatchSpec.evmR { cpost with locals := s.locals } ≤ OpDispatchSpec.evmR s := by
                change OpDispatchSpec.evmR { cpost with locals := s.locals, clock := cpost.clock } ≤ OpDispatchSpec.evmR s
                rw [evmR_lc_fc cpost s.locals cpost.clock]
                have hR_ent : OpDispatchSpec.evmR ent = OpDispatchSpec.evmR s :=
                  evmR_lc_fc s callee (s.clock - 1)
                exact hR_cp.trans (le_of_eq hR_ent)
              exact ⟨⟨⟨hInv_out, le_of_eq hhp_eq.symm, hgk, hch_out⟩, hR_out, hcells.1, hcells.2⟩,
                fun _ => ⟨by simp, hmeta.trans hc⟩⟩
            · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hnt_trap : eid ≠ ofString "TrapErr" := by
              rcases hfr with h | h | h | (⟨_, hc'⟩ | ⟨e', v', hc', hnt_e⟩)
              · simp at h
              · simp at h
              · simp at h
              · simp at hc'
              · injection hc' with hc'; injection hc' with he _; subst he; exact hnt_e
            obtain ⟨good, hgood, hbody_only⟩ := honly vs body' callee .one hl_orig
            have hevm : eid = ofString "EvmErr" := by
              by_contra hneE
              have habs := evaluate_onlyEvmOrTrapRaise good hgood body' hbody_only ent hent_code eid ev hnt_trap hneE
              simp only [ent, hrun] at habs; exact habs rfl
            subst hevm
            obtain ⟨hInv_cp, hch_cp, hR_cp⟩ := hsp.2 ⟨ev, rfl⟩
            have hstep_hs := hhs_body.to_resumes (Or.inr ⟨ofString "EvmErr", ev, rfl, by decide⟩)
            have hg_cp : cpost.globals = s.globals := hstep_hs.2.1
            have hcells := headSafeAddr_preserves_cells_cf hInv hstep_hs.2.2
            have hInv_out : EvmInv cpost.emptyLocalsHOLFinite :=
              localsFree_evmInv cpost cpost.emptyLocalsHOLFinite.locals cpost.clock hInv_cp
            have hhp_eq : globN cpost.emptyLocalsHOLFinite "heap_ptr" = globN s "heap_ptr" := by
              simp [emptyLocalsHOLFinite, globN, hg_cp]
            have hgk : GlobalsKept ["heap_ptr", "journal_n", "scratch_ptr"] s cpost.emptyLocalsHOLFinite := by
              intro g _; simp [emptyLocalsHOLFinite, hg_cp]
            have hch_out : evmChain cpost.emptyLocalsHOLFinite = evmChain s := by
              change evmChain { cpost with locals := cpost.emptyLocalsHOLFinite.locals, clock := cpost.clock } = evmChain s
              rw [evmChain_with_locals cpost cpost.emptyLocalsHOLFinite.locals cpost.clock, hch_cp]
              exact evmChain_with_locals s callee (s.clock - 1)
            have hR_out : OpDispatchSpec.evmR cpost.emptyLocalsHOLFinite ≤ OpDispatchSpec.evmR s := by
              change OpDispatchSpec.evmR { cpost with locals := cpost.emptyLocalsHOLFinite.locals, clock := cpost.clock } ≤ OpDispatchSpec.evmR s
              rw [evmR_lc_fc cpost cpost.emptyLocalsHOLFinite.locals cpost.clock]
              have hR_ent : OpDispatchSpec.evmR ent = OpDispatchSpec.evmR s :=
                evmR_lc_fc s callee (s.clock - 1)
              exact hR_cp.trans (le_of_eq hR_ent)
            exact ⟨⟨⟨hInv_out, le_of_eq hhp_eq.symm, hgk, hch_out⟩, hR_out, hcells.1, hcells.2⟩,
              fun h => by simp at h⟩

private theorem cfStep_call0_charge_gas {F : Type}
    (args : List (ExpHOL 64)) (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hInv : EvmInv s)
    (hnt : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_gas") args)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_gas") args)).1) :
    CfStep s (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_gas") args)).2 ∧
    ((evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_gas") args)).1 = none →
      (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_gas") args)).2.locals = s.locals ∧
      (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_gas") args)).2.code = originalRuntimeCode) :=
  cfStep_of_eps_call0 eps_charge_gas_any
    (fun values body callee rs hl => by
      obtain ⟨_, _, hinst⟩ := lookupCode_installed hl
      rw [M21.lookup_charge_gas] at hinst
      rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]
      exact ⟨fun _ => false, fun _ h => by simp at h, by decide⟩)
    (fun values body callee rs hl => by
      obtain ⟨_, _, hinst⟩ := lookupCode_installed hl
      rw [M21.lookup_charge_gas] at hinst
      rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]
      decide)
    (fun _ _ _ hlk => by rw [M21.lookup_charge_gas] at hlk; exact (Prod.mk.inj (Prod.mk.inj (Option.some.inj hlk)).2).2.symm)
    args s hc hInv hnt hfr

private theorem cfStep_call0_charge_state_gas {F : Type}
    (args : List (ExpHOL 64)) (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hInv : EvmInv s)
    (hnt : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_state_gas") args)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_state_gas") args)).1) :
    CfStep s (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_state_gas") args)).2 ∧
    ((evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_state_gas") args)).1 = none →
      (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_state_gas") args)).2.locals = s.locals ∧
      (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_state_gas") args)).2.code = originalRuntimeCode) :=
  cfStep_of_eps_call0 eps_charge_state_gas
    (fun values body callee rs hl => by
      obtain ⟨_, _, hinst⟩ := lookupCode_installed hl
      rw [lookup_charge_state_gas_b] at hinst
      rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]
      exact ⟨fun g => g == ofString "add_sat", addSatOnlyCallees_good, by decide⟩)
    (fun values body callee rs hl => by
      obtain ⟨_, _, hinst⟩ := lookupCode_installed hl
      rw [lookup_charge_state_gas_b] at hinst
      rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]
      decide)
    (fun _ _ _ hlk => by rw [lookup_charge_state_gas_b] at hlk; exact (Prod.mk.inj (Prod.mk.inj (Option.some.inj hlk)).2).2.symm)
    args s hc hInv hnt hfr

private theorem globalBuffers_sz_pos_cf : ∀ gn ∈ globalBuffers, gn.2 ≠ 0 := by decide

private theorem cfStep_of_worldStepSc {F : Type}
    {B : R16WkAcctWs.BufList} {keep : List (String × List Nat)}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hB : R16WkAcctWs.ValidBufList B)
    (hAs : ArenaReady s)
    (hInv : ∃ S, InitECandidate.Solver.Wave8GuestInv.EvmInvAt s S)
    (hstep : R16WkAcctWs.WorldStepSc (R16WkAcctWs.bufRegions B)
      ["heap_ptr", "journal_n", "scratch_ptr"] keep NoExtra s r post) :
    CfStep s post := by
  have hevm : EvmStep ["heap_ptr", "journal_n", "scratch_ptr"] s post :=
    evmStep_of_worldStepSc hB safeStepGlobals_hp_jn_sp hAs hInv hstep
  obtain ⟨S, hW_s, hch_ne, _, _, hFW_all, _, _, _, hFO_disj, hAT_fo, _, _, _⟩ := hInv
  obtain ⟨Nd_at, hTr_at, hAT_at⟩ := hAT_fo
  have hWT_at_s : WorldTypedWith s S Nd_at := ⟨hW_s.1, hW_s.2.1, hW_s.2.2.1, hTr_at⟩
  obtain ⟨⟨hAp, hhp, _, _, hWS⟩, _⟩ := hstep
  obtain ⟨_, _, _, _, hog, hfr, _⟩ :=
    hWS S Nd_at hWT_at_s (R16WkAcctWs.validBufList_disj hB hWT_at_s)
  have hkeep_shape : ∀ j ∈ worldOwned s S Nd_at ++ R16WkAcctWs.bufRegions B s ++ [freeGap s],
      j = (0, 0) ∨ j.1 % 8 = 0 ∨ j.2 ≠ 0 := by
    intro j hj
    rcases List.mem_append.1 hj with hj12 | hfg
    · rcases List.mem_append.1 hj12 with hj_ow | hj_R
      · exact worldOwned_well_shaped hWT_at_s j hj_ow
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj_R
        unfold Wave8GuestInv.bufferRegion
        by_cases hz : globN s p.1 = 0
        · exact Or.inl (by simp [hz])
        · by_cases hp2 : p.2 = 0
          · right; left
            obtain ⟨sz, hgb, _⟩ := hB p hp
            have hfix : (globN s p.1, if globN s p.1 = 0 then 0 else sz) ∈ fixedObjects s := by
              unfold fixedObjects
              apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
              exact List.mem_map.2 ⟨(p.1, sz), hgb, rfl⟩
            rcases hWT_at_s.2.2.1.1 _ hfix with h0 | ⟨_, hw⟩
            · simp [hz] at h0; exact absurd h0 (globalBuffers_sz_pos_cf (p.1, sz) hgb)
            · exact hw.1
          · exact Or.inr (Or.inr (by simp [hz, hp2]))
    · rw [List.mem_singleton] at hfg; subst hfg
      exact Or.inr (Or.inl hAs.2.2.2.2.2.2.2.1)
  have hdisj_bufs_of_fixed : ∀ b : Ivl, (∀ j ∈ fixedObjects s, Disj b j) →
      ∀ j ∈ R16WkAcctWs.bufRegions B s, Disj b j := by
    intro b hbfix j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj
    obtain ⟨sz, hgb, _, hle⟩ := hB p hp
    have hfix : Wave8GuestInv.bufferRegion s (p.1, sz) ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.2 ⟨(p.1, sz), hgb, rfl⟩
    have hd := hbfix _ hfix
    by_cases hz : globN s p.1 = 0
    · exact Or.inr (Or.inl (by simp [Wave8GuestInv.bufferRegion, hz]))
    · simp only [Wave8GuestInv.bufferRegion, hz, ↓reduceIte] at hd ⊢
      rcases hd with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (by dsimp only at h ⊢; omega))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (by dsimp only at h ⊢; omega)))
  have hu_fo : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, o.2 ≠ 0 →
      InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post o := by
    intro ec hec o ho hnz
    have ho_fl : o ∈ ((evmChain s).map (frameObjects s)).flatten :=
      List.mem_flatten.2 ⟨frameObjects s ec, List.mem_map.2 ⟨ec, hec, rfl⟩, ho⟩
    have harena := (frameObject_zero_or_allocated hAs.2 (hFW_all ec hec) ho).resolve_left hnz
    have ho_ow : ∀ j ∈ worldOwned s S Nd_at, Disj o j := by
      intro j hj
      unfold worldOwned at hj
      rcases List.mem_append.1 hj with h1 | hnd
      · rcases List.mem_append.1 h1 with htab | hfix
        · obtain ⟨u, hu, hj_fp⟩ := List.mem_flatMap.1 htab
          exact (hFO_disj ec hec o ho).1 u hu j hj_fp
        · exact (hFO_disj ec hec o ho).2 j hfix
      · exact hAT_at o ho_fl j hnd
    exact (arena_survives_world_frame hAs.2 hAp.2 hhp harena ho_ow
      (hdisj_bufs_of_fixed o (hFO_disj ec hec o ho).2) hkeep_shape hfr hog).1
  have hrec_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨hb1, hb2, _, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hAs.2 hFW
    have he1_8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
    have he2_8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
    exact ⟨fun k hk hk8 => InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
            (hu_fo ec hec (ec.1, 280) (by simp [frameObjects]) (by simp)) (by omega) hb1 ⟨by omega, by omega⟩,
           fun k hk hk8 => InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
            (hu_fo ec hec (ec.2, 104) (by simp [frameObjects]) (by simp)) (by omega) hb2 ⟨by omega, by omega⟩⟩
  have hmap_gas : ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)) =
      ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)) := by
    apply List.map_congr_left; intro ec hec
    rw [(hrec_eq ec hec).1 64 (by decide) (by decide), (hrec_eq ec hec).1 192 (by decide) (by decide)]
  have hR_eq : OpDispatchSpec.evmR post = OpDispatchSpec.evmR s := by
    unfold OpDispatchSpec.evmR
    rw [hevm.2.2.2, hmap_gas]
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    unfold evmChain
    have hmc : 0 < maxChain := by decide
    obtain ⟨m, hm⟩ : ∃ m, maxChain = m + 1 := ⟨maxChain - 1, by omega⟩
    rw [hm]; simp [evmChainFrom]
  refine ⟨hevm, le_of_eq hR_eq, (hrec_eq _ hhead).2 48 (by decide) (by decide), ?_⟩
  intro ec hec
  exact ⟨(hrec_eq ec hec).1 24 (by decide) (by decide),
         (hrec_eq ec hec).1 32 (by decide) (by decide),
         (hrec_eq ec hec).1 40 (by decide) (by decide),
         (hrec_eq ec hec).2 56 (by decide) (by decide)⟩

private theorem call0_or_resumes_cf {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fname : MlS) (args : List (ExpHOL 64))
    (hcr : ContOrRes (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = none ∨
    InitECandidate.Solver.Wave8Contracts.M23.Resumes (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 := by
  rcases hcr with h | h | h | hr
  · exact Or.inl h
  · exfalso
    rw [evaluateHOLFiniteState_call] at h
    revert h; split <;> [simp; (split <;> [simp; (split <;> [simp; skip])])]
    rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨rc, _⟩
    rcases rc with _ | (_ | _ | _ | _ | _ | _ | _) <;> dsimp only <;> (repeat' split) <;> simp
  · exfalso
    rw [evaluateHOLFiniteState_call] at h
    revert h; split <;> [simp; (split <;> [simp; (split <;> [simp; skip])])]
    rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨rc, _⟩
    rcases rc with _ | (_ | _ | _ | _ | _ | _ | _) <;> dsimp only <;> (repeat' split) <;> simp
  · exact Or.inr hr

private theorem call0_none_locals_cf {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fn : MlS) (args : List (ExpHOL 64))
    (hnone : (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).1 = none) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).2.locals = s.locals := by
  rw [evaluateHOLFiniteState_call] at hnone ⊢
  unfold evalListHOLFinite at hnone ⊢
  rcases h1 : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [h1] at hnone
  · simp only [h1] at hnone ⊢
    rcases h2 : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fn vs with _ | ⟨b, c, r⟩
    · simp [h2] at hnone
    · simp only [h2] at hnone ⊢
      split at hnone
      · simp at hnone
      · rename_i hcz; rw [if_neg hcz]
        rcases h3 : evaluateHOLFiniteState (callEntryStateHOLFinite s c) b with ⟨rb, sb⟩
        simp only [h3] at hnone ⊢
        rcases rb with _ | rb'
        · simp at hnone
        · cases rb' with
          | returned rv =>
            dsimp only at hnone ⊢
            split at hnone
            · rename_i hsh; rw [if_pos hsh]
            · simp at hnone
          | _ => simp at hnone

private theorem contOrRes_of_flowingOrResumes_cf {r : Option (PanSemResultExact 64)}
    (hfr : FlowingOrResumes r) : ContOrRes r := by
  rcases hfr with h | h | h | hr
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr hr))

private theorem worldEff_to_worldStepSc_wsAcct_cf {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hW : WorldOK s)
    (heff : WorldEff s post [] wsAcctBufs ["heap_ptr", "scratch_ptr"]) :
    WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] R10Shards.P26_P28.stdKeep NoExtra s r post := by
  have heff' : WorldEff s post (bufRegions wsAcctBufs s) wsAcctBufs ["heap_ptr", "scratch_ptr"] :=
    heff.mono (fun _ hiv => by cases hiv) (fun _ h => h) (fun _ h => h)
  have hws0 : WorldStep (bufRegions wsAcctBufs) ["heap_ptr", "scratch_ptr"] R10Shards.P26_P28.stdKeep NoExtra s r post :=
    heff'.to_worldStep_Q hW (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial)
  exact WorldStepSc.mono_bufs
    (fun p hp => by simp [wsAcctBufs] at hp; rcases hp with rfl | rfl | rfl <;> simp [acctMutBufs])
    (fun g hg => by simp at hg; rcases hg with rfl | rfl <;> simp)
    ⟨hws0, heff.sp_hi⟩

private def cfMul6W : ExpHOL 64 :=
  FrontendCodecComputation.expToHOLStructural
    (Exp.panOp PanOp.mul [(Exp.const (BitVec.ofNat 64 6)), (Exp.var VarKind.local "w")])

private def cfMulN1530 : ExpHOL 64 :=
  FrontendCodecComputation.expToHOLStructural
    (Exp.panOp PanOp.mul [(Exp.var VarKind.local "n"), (Exp.const (BitVec.ofNat 64 1530))])

private def cfAllocTail : ProgHOL 64 :=
  .decCall (ofString "stored_code") .one (ofString "alloc")
    [.op .add [.var .local (ofString "n"), .const 8#64]]
    (.seq
      (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "stored_code"), .var .local (ofString "code"), .var .local (ofString "n")])
      (.seq
        (.call (some (none, none)) (ofString "set_code")
          [.load .one (.op .add [.var .local (ofString "msg"), .const 32#64]),
           .var .local (ofString "stored_code"), .var .local (ofString "n")])
        (.return (.const 0#64))))

private def cfChargesProg : ProgHOL 64 :=
  .seq
    (.call (some (none, none)) (ofString "charge_gas") [cfMul6W])
    (.seq
      (.call (some (none, none)) (ofString "charge_state_gas") [cfMulN1530])
      cfAllocTail)

private def cfGuardsProg : ProgHOL 64 :=
  .seq
    (.ite (.cmp .lower (.const 65536#64) (.var .local (ofString "n")))
      (.raise (ofString "EvmErr") (.const 4#64))
      .skip)
    (.decCall (ofString "w") .one (ofString "words_of") [.var .local (ofString "n")]
      cfChargesProg)

private def cfIte1Prog : ProgHOL 64 :=
  .ite (.cmp .lower (.const 0#64) (.var .local (ofString "n")))
    (.ite (.cmp .equal (.loadByte (.var .local (ofString "code"))) (.const 239#64))
      (.raise (ofString "EvmErr") (.const 11#64))
      .skip)
    .skip

private def cfBody2Prog : ProgHOL 64 :=
  .seq cfIte1Prog cfGuardsProg

private theorem cf_body_eq :
    sourceFnBody Guest.Software.guestFn_create_finish =
      .dec (ofString "code") .one (.load .one (.op .add [.var .local (ofString "child"), .const 120#64]))
        (.dec (ofString "n") .one (.load .one (.op .add [.var .local (ofString "child"), .const 128#64]))
          cfBody2Prog) := rfl

private theorem create_finish_tail_worldStepSc_cf {F : Type}
    {s : PanSemStateFiniteExact 64 F} {nw codew msgw : BitVec 64}
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hn_le : nw.toNat ≤ 65536)
    (hs_n : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hs_code : s.locals.lookup (ofString "code") = some (.val (.word codew)))
    (hs_msg : s.locals.lookup (ofString "msg") = some (.val (.word msgw)))
    (hnt : (evaluateHOLFiniteState s cfAllocTail).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s cfAllocTail).1) :
    WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] R10Shards.P26_P28.stdKeep NoExtra
      s (evaluateHOLFiniteState s cfAllocTail).1 (evaluateHOLFiniteState s cfAllocTail).2 := by
  let pRest : ProgHOL 64 :=
    .seq
      (.call (some (none, none)) (ofString "set_code")
        [.load .one (.op .add [.var .local (ofString "msg"), .const 32#64]),
         .var .local (ofString "stored_code"), .var .local (ofString "n")])
      (.return (.const 0#64))
  let pMc : ProgHOL 64 :=
    .call (some (none, none)) (ofString "memcpy")
      [.var .local (ofString "stored_code"), .var .local (ofString "code"), .var .local (ofString "n")]
  have hB := validBufList_acctMutBufs
  have hgw := safeStepGlobals_hp_jn_sp
  dsimp only [cfAllocTail] at hnt hfr ⊢
  change WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] R10Shards.P26_P28.stdKeep NoExtra s
    (evaluateHOLFiniteState s
      (.decCall (ofString "stored_code") .one (ofString "alloc")
        [.op .add [.var .local (ofString "n"), .const 8#64]] (.seq pMc pRest))).1
    (evaluateHOLFiniteState s
      (.decCall (ofString "stored_code") .one (ofString "alloc")
        [.op .add [.var .local (ofString "n"), .const 8#64]] (.seq pMc pRest))).2
  set sz : BitVec 64 := nw + 8#64
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.op .add [.var .local (ofString "n"), .const 8#64]] = some [.val (.word sz)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact, evalHOLExact, hs_n, wordOpHOL, wordOp, valueIsWord, valueWord, sz]
  simp only [hargs] at hnt hfr ⊢
  rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "alloc") [.val (.word sz)] with
    _ | ⟨body', callee, ret'⟩
  · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hl] at hnt hfr ⊢
    by_cases hz : s.clock = 0
    · simp [hz] at hnt
    · rw [if_neg hz] at hnt hfr ⊢
      have hlk_alloc_explicit : originalRuntimeCode.lookup (ofString "alloc") =
          some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_alloc, .one) :=
        lookup_alloc_r16
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "alloc") _ _ body'
        _ ret' [.val (.word sz)] callee (by rw [hc]; exact hlk_alloc_explicit) hl
      subst hsame
      have hret_eq := lookupCodeHOLFinite_installed_return s (ofString "alloc") _ _ _
        _ ret' [.val (.word sz)] callee (by rw [hc]; exact hlk_alloc_explicit) hl
      subst hret_eq
      obtain ⟨nw_a, hnw_eq, hnw_callee⟩ := Fast_C08WkShard03.lookupCode_one_word hlk_alloc_explicit (by rw [← hc]; exact hl)
      injection hnw_eq with hnw_eq'; injection hnw_eq' with hnw_eq'; injection hnw_eq' with hnw_eq'; subst hnw_eq'
      obtain ⟨pw, hpw_lk⟩ : ∃ pw : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word pw)) :=
        globalWord_of_globN_pos s "heap_ptr" (by have := hW.1.2.1; rw [R11Shards.sourceBase_val] at this; omega)
      rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) (sourceFnBody Guest.Software.guestFn_alloc) with ⟨res, pa⟩
      simp only [hrun] at hnt hfr ⊢
      have hcr_outer := contOrRes_of_flowingOrResumes_cf hfr
      have hres_a : InitECandidate.Solver.Wave8Contracts.M23.Resumes res := by
        cases res with
        | none => rcases hcr_outer with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
        | some r1 =>
          cases r1 with
          | returned rv => exact Or.inl ⟨rv, rfl⟩
          | exception eid ev =>
            rcases hcr_outer with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨e', v', hc0, hne⟩⟩
            · simp at hc0
            · simp at hc0
            · simp at hc0
            · simp at hc0
            · change some (PanSemResultExact.exception eid ev) = some (PanSemResultExact.exception e' v') at hc0
              injection hc0 with hc0'; injection hc0' with he1 he2; subst he1 he2
              exact Or.inr ⟨eid, ev, rfl, hne⟩
          | timeOut => simp at hnt
          | _ => rcases hcr_outer with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
      have hal := R13.alloc_body_resumes (callEntryStateHOLFinite s callee) pw hc hpw_lk
        (by rw [hrun]; exact hres_a)
      rw [hrun] at hal
      obtain ⟨nw', hnw'_lk, hrv_eq, hcmp1, hcmp2, hpa_eq⟩ := hal
      have hnw_eq2 : sz = nw' := by
        have : (callEntryStateHOLFinite s callee).locals.lookup (ofString "n") = some (.val (.word sz)) := hnw_callee
        rw [this] at hnw'_lk; injection hnw'_lk with h'; injection h' with h'; injection h'
      subst hnw_eq2
      dsimp only at hrv_eq hpa_eq
      subst hrv_eq
      dsimp only at hnt hfr ⊢
      have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one &&
          shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one) = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      rw [if_pos hsh] at hnt hfr ⊢
      dsimp only at hnt hfr ⊢
      set m1 := setVarHOLFinite (ofString "stored_code") (.val (.word pw)) { pa with locals := s.locals }
      have hm1_next : m1 = { s with
          globals := s.globals.update (ofString "heap_ptr", .val (.word ((pw + (sz + 7)) &&& ((0 : BitVec 64) - 8)))),
          locals := m1.locals, clock := m1.clock } := by
        dsimp only [m1, setVarHOLFinite]; rw [hpa_eq]; rfl
      have heff_s : WorldEff s s [] wsAcctBufs ["heap_ptr", "scratch_ptr"] :=
        WorldEff.refl s [] wsAcctBufs ["heap_ptr", "scratch_ptr"] hW.1 hc
      obtain ⟨heff_m1, _, _, _, hp_lo_s, hp_add, hp_hi, _⟩ :=
        R16Shards.worldEff_alloc_step heff_s (by decide) hpw_lk hcmp1 hcmp2 hm1_next
      have hm1_loc : m1.locals = s.locals.update (ofString "stored_code", .val (.word pw)) := rfl
      have hnw8 : sz.toNat = nw.toNat + 8 := create_finish_alloc_add_no_wrap nw hn_le
      have hpw_hi : pw.toNat + nw.toNat ≤ heapLimit := by rw [hnw8] at hp_add; omega
      have hm1_sc : m1.locals.lookup (ofString "stored_code") = some (.val (.word pw)) := by
        rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have hm1_code : m1.locals.lookup (ofString "code") = some (.val (.word codew)) := by
        rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs_code,
          show ofString "stored_code" ≠ ofString "code" by decide]
      have hm1_n : m1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
        rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs_n,
          show ofString "stored_code" ≠ ofString "n" by decide]
      have hargs_mc : evalListHOLFinite m1 (h := fun a => Classical.propDecidable (m1.memaddrs a))
          [.var .local (ofString "stored_code"), .var .local (ofString "code"), .var .local (ofString "n")] =
          some [.val (.word pw), .val (.word codew), .val (.word nw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hm1_sc, hm1_code, hm1_n]
      have hmc_eff : (evaluateHOLFiniteState m1 pMc).1 ≠ some .timeOut →
          ContOrRes (evaluateHOLFiniteState m1 pMc).1 →
          WorldEff s (evaluateHOLFiniteState m1 pMc).2 [] wsAcctBufs ["heap_ptr", "scratch_ptr"] := by
        intro hnt_mc hcr_mc
        have hb := Fast_C08WkShard03.call0_byteEff Fast_C08WkShard03.funByteEff_memcpy m1
          [.var .local (ofString "stored_code"), .var .local (ofString "code"), .var .local (ofString "n")]
          [(pw.toNat, nw.toNat)] heff_m1.code heff_m1.arena.1
          (fun vals ha i hi _ => by
            rw [hargs_mc] at ha; injection ha with ha_eq; subst ha_eq
            simp only [List.mem_singleton, Fast_C08WkShard03.valWordNat] at hi
            subst hi; exact ⟨(pw.toNat, nw.toNat), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
          hnt_mc (call0_or_resumes_cf m1 (ofString "memcpy") _ hcr_mc)
        exact heff_m1.of_byteEff hb (fun iv hiv _ => by
          simp only [List.mem_singleton] at hiv; subst hiv
          exact Or.inr (Or.inr (Or.inr ⟨hp_lo_s, hpw_hi⟩)))
      rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
      rcases hrw : evaluateHOLFiniteState m1 pMc with ⟨rw1, m2⟩
      dsimp only [pMc, pRest] at hrw hmc_eff ⊢
      simp only [hrw] at hnt hfr ⊢
      cases rw1 with
      | none =>
        have heff_m2 := hmc_eff (by rw [hrw]; simp) (by rw [hrw]; exact Or.inl rfl)
        rw [hrw] at heff_m2; dsimp only at heff_m2
        have hs12 : WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] R10Shards.P26_P28.stdKeep NoExtra s none m2 :=
          worldEff_to_worldStepSc_wsAcct_cf hW heff_m2
        have hW_m2 : WorldOK m2 := hs12.worldOK_bufs hB hW
        have hs23 : WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] R10Shards.P26_P28.stdKeep NoExtra
            m2 (evaluateHOLFiniteState m2 pRest).1 (evaluateHOLFiniteState m2 pRest).2 :=
          progWStep_seq hB hgw
            (progWStep_call0 (fun _ h => h) (fun _ h => h) wkSc_set_code)
            (progWStep_return _ _ _)
            m2 heff_m2.code hW_m2 hnt hfr
        have hs23' := hs23.with_locals_clock (r' := (evaluateHOLFiniteState m2 pRest).1)
          (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState m2 pRest).2.locals (ofString "stored_code", s.locals.lookup (ofString "stored_code")))
          (evaluateHOLFiniteState m2 pRest).2.clock
        exact WorldStepSc.trans hB hgw hs12 hs23'
      | some r =>
        have heff_m2 := hmc_eff (by rw [hrw]; exact hnt) (by rw [hrw]; exact contOrRes_of_flowingOrResumes_cf hfr)
        rw [hrw] at heff_m2; dsimp only at heff_m2
        have hs12 : WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] R10Shards.P26_P28.stdKeep NoExtra s (some r) m2 :=
          worldEff_to_worldStepSc_wsAcct_cf hW heff_m2
        exact hs12.with_locals_clock (r' := some r)
          (HolFiniteMapExact.resVarEq m2.locals (ofString "stored_code", s.locals.lookup (ofString "stored_code")))
          m2.clock

private theorem create_finish_after_charges_cf {F : Type}
    {s4 : PanSemStateFiniteExact 64 F} {nw codew msgw : BitVec 64}
    (hc4 : s4.code = originalRuntimeCode) (hInv4 : EvmInv s4)
    (hn_le : nw.toNat ≤ 65536)
    (hs4_msg : s4.locals.lookup (ofString "msg") = some (.val (.word msgw)))
    (hs4_code : s4.locals.lookup (ofString "code") = some (.val (.word codew)))
    (hs4_n : s4.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hnt : (evaluateHOLFiniteState s4 cfChargesProg).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s4 cfChargesProg).1) :
    CfStep s4 (evaluateHOLFiniteState s4 cfChargesProg).2 := by
  dsimp only [cfChargesProg] at hnt hfr ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases hcg : evaluateHOLFiniteState s4
      (.call (some (none, none)) (ofString "charge_gas") [cfMul6W]) with ⟨rcg, s5⟩
  simp only [hcg] at hnt hfr ⊢
  cases rcg with
  | some _ =>
    have hs_cg := (cfStep_call0_charge_gas [cfMul6W] s4 hc4 hInv4 (by rw [hcg]; exact hnt) (by rw [hcg]; exact hfr)).1
    rw [hcg] at hs_cg; exact hs_cg
  | none =>
    dsimp only at hnt hfr ⊢
    obtain ⟨hs_cg, hnone_cg⟩ := cfStep_call0_charge_gas [cfMul6W] s4 hc4 hInv4 (by rw [hcg]; simp) (by rw [hcg]; exact Or.inl rfl)
    rw [hcg] at hs_cg hnone_cg
    obtain ⟨hs5_loc, hc5⟩ := hnone_cg rfl
    have hInv5 : EvmInv s5 := hs_cg.1.1
    have hs5_msg : s5.locals.lookup (ofString "msg") = some (.val (.word msgw)) := by rw [hs5_loc]; exact hs4_msg
    have hs5_code : s5.locals.lookup (ofString "code") = some (.val (.word codew)) := by rw [hs5_loc]; exact hs4_code
    have hs5_n : s5.locals.lookup (ofString "n") = some (.val (.word nw)) := by rw [hs5_loc]; exact hs4_n
    refine cfStep_trans hs_cg ?_
    rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
    rcases hcsg : evaluateHOLFiniteState s5
        (.call (some (none, none)) (ofString "charge_state_gas") [cfMulN1530]) with ⟨rcsg, s6⟩
    simp only [hcsg] at hnt hfr ⊢
    cases rcsg with
    | some _ =>
      have hs_csg := (cfStep_call0_charge_state_gas [cfMulN1530] s5 hc5 hInv5 (by rw [hcsg]; exact hnt) (by rw [hcsg]; exact hfr)).1
      rw [hcsg] at hs_csg; exact hs_csg
    | none =>
      dsimp only at hnt hfr ⊢
      obtain ⟨hs_csg, hnone_csg⟩ := cfStep_call0_charge_state_gas [cfMulN1530] s5 hc5 hInv5 (by rw [hcsg]; simp) (by rw [hcsg]; exact Or.inl rfl)
      rw [hcsg] at hs_csg hnone_csg
      obtain ⟨hs6_loc, hc6⟩ := hnone_csg rfl
      have hInv6 : EvmInv s6 := hs_csg.1.1
      have hs6_msg : s6.locals.lookup (ofString "msg") = some (.val (.word msgw)) := by rw [hs6_loc]; exact hs5_msg
      have hs6_code : s6.locals.lookup (ofString "code") = some (.val (.word codew)) := by rw [hs6_loc]; exact hs5_code
      have hs6_n : s6.locals.lookup (ofString "n") = some (.val (.word nw)) := by rw [hs6_loc]; exact hs5_n
      refine cfStep_trans hs_csg ?_
      have hAv6 : EvmAvoids createFinishAvoids s6 := evm_createFinishAvoids s6 hInv6
      obtain ⟨hAs6, S6, hInvAt6, _⟩ := hAv6
      have hW6 : WorldOK s6 := ⟨hAs6, S6, hInvAt6.1⟩
      have hws6 := create_finish_tail_worldStepSc_cf hc6 hW6 hn_le hs6_n hs6_code hs6_msg hnt hfr
      exact cfStep_of_worldStepSc validBufList_acctMutBufs hAs6 ⟨S6, hInvAt6⟩ hws6

private theorem create_finish_after_guards_cf {F : Type}
    {s3 : PanSemStateFiniteExact 64 F} {nw codew msgw : BitVec 64}
    (hc3 : s3.code = originalRuntimeCode) (hInv3 : EvmInv s3)
    (hs3_msg : s3.locals.lookup (ofString "msg") = some (.val (.word msgw)))
    (hs3_code : s3.locals.lookup (ofString "code") = some (.val (.word codew)))
    (hs3_n : s3.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hnt0 : (evaluateHOLFiniteState s3 cfGuardsProg).1 ≠ some .timeOut)
    (hfr0 : FlowingOrResumes (evaluateHOLFiniteState s3 cfGuardsProg).1) :
    CfStep s3 (evaluateHOLFiniteState s3 cfGuardsProg).2 := by
  dsimp only [cfGuardsProg] at hnt0 hfr0 ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hnt0 hfr0 ⊢
  rw [evaluateHOLFiniteState_ite] at hnt0 hfr0 ⊢
  have hcmp2 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
      (.cmp .lower (.const 65536#64) (.var .local (ofString "n"))) =
      some (.val (.word (if 65536#64 < nw then 1#64 else 0#64))) := by
    simp [evalHOLExact, hs3_n, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp2] at hnt0 hfr0 ⊢; dsimp only at hnt0 hfr0 ⊢
  by_cases hgt : 65536#64 < nw
  · have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
    simp only [hgt, ↓reduceIte, h10] at hnt0 hfr0 ⊢
    rw [evaluateHOLFiniteState_raise] at hnt0 hfr0 ⊢
    dsimp only [evalHOLExact] at hnt0 hfr0 ⊢
    cases s3.eshapes.lookup (ofString "EvmErr") with
    | none => dsimp only; exact cfStep_refl hInv3
    | some sh =>
      by_cases hshape : shapeOfHOLExact (.val (.word 4#64) : ValueHOL 64) = sh ∧
          sizeOfShapeWithContextHOL s3.structs (shapeOfHOLExact (.val (.word 4#64) : ValueHOL 64)) ≤ 32
      · simp only [if_pos hshape] at hnt0 hfr0 ⊢
        exact cfStep_with_locals_clock (cfStep_refl hInv3) _ s3.clock
      · simp only [if_neg hshape] at hnt0 hfr0 ⊢
        exact cfStep_refl hInv3
  · have hn_le : nw.toNat ≤ 65536 := by
      rw [BitVec.lt_def] at hgt; change ¬ (65536 < nw.toNat) at hgt; omega
    have h00 : (0#64 : BitVec 64) = 0 := rfl
    simp only [hgt, ↓reduceIte, h00, evaluateHOLFiniteState_skip] at hnt0 hfr0 ⊢
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt0 hfr0 ⊢
    have hargs_w : evalListHOLFinite s3 (h := fun a => Classical.propDecidable (s3.memaddrs a))
        [.var .local (ofString "n")] = some [.val (.word nw)] := by
      rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, evalHOLExact, hs3_n]
    rw [hargs_w] at hnt0 hfr0 ⊢; dsimp only at hnt0 hfr0 ⊢
    rcases hl_w : lookupCodeHOLFinite s3.code.lookup (ofString "words_of") [.val (.word nw)] with
      _ | ⟨body_w, callee_w, ret_w⟩
    · simp [hl_w] at hfr0; exact absurd hfr0 not_flowingOrResumes_error
    · simp only [hl_w] at hnt0 hfr0 ⊢
      by_cases hz3 : s3.clock = 0
      · simp [hz3] at hnt0
      · rw [if_neg hz3] at hnt0 hfr0 ⊢
        have hlk_wo : originalRuntimeCode.lookup (ofString "words_of") =
            some ((sourceFunctionEntry Guest.Software.guestFn_words_of).2) :=
          lookup_of_guestAst_getElem 443 (by rw [guestAst_len]; decide)
            (extractFn Guest.Software.guestFn_words_of) rfl
        have hbw_eq := lookupCodeHOLFinite_installed_body s3.code.lookup (ofString "words_of")
          _ (sourceFnBody Guest.Software.guestFn_words_of) body_w _ ret_w [.val (.word nw)] callee_w
          (by rw [hc3]; exact hlk_wo) hl_w
        subst body_w
        let ent_w := callEntryStateHOLFinite s3 callee_w
        have hlfr_w : LocFrameR16 ent_w (evaluateHOLFiniteState ent_w (sourceFnBody Guest.Software.guestFn_words_of)).2 :=
          evaluate_roProgR16 wordsOfCallees wordsOfCallees_good
            (sourceFnBody Guest.Software.guestFn_words_of) (by decide) ent_w hc3
        rcases hrw : evaluateHOLFiniteState ent_w (sourceFnBody Guest.Software.guestFn_words_of) with ⟨rw0, pw0⟩
        dsimp only [ent_w] at hrw hlfr_w
        simp only [hrw] at hlfr_w hnt0 hfr0 ⊢
        cases rw0 with
        | none => exact absurd hfr0 not_flowingOrResumes_error
        | some crw =>
          cases crw with
          | timeOut => simp at hnt0
          | «break» | «continue» | error => exact absurd hfr0 not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr0 not_flowingOrResumes_finalFfi
          | exception _ _ =>
            dsimp only
            have hpw0_eq : pw0 = { s3 with locals := pw0.locals, clock := pw0.clock } := by
              unfold LocFrameR16 at hlfr_w; rw [hlfr_w]; rfl
            rw [hpw0_eq]
            exact cfStep_with_locals_clock (cfStep_refl hInv3) _ pw0.clock
          | returned vw =>
            dsimp only at hnt0 hfr0 ⊢
            by_cases hsh_vw : (shapeEqHOL (shapeOfHOLExact vw) .one && shapeEqHOL (shapeOfHOLExact vw) ret_w) = true
            · simp only [hsh_vw, ↓reduceIte] at hnt0 hfr0 ⊢
              set s4 := setVarHOLFinite (ofString "w") vw { pw0 with locals := s3.locals }
              have hs4_eq : s4 = { s3 with locals := s3.locals.update (ofString "w", vw), clock := pw0.clock } := by
                dsimp only [s4, setVarHOLFinite]
                unfold LocFrameR16 at hlfr_w; rw [hlfr_w]; rfl
              have hInv4 : EvmInv s4 := by rw [hs4_eq]; exact localsFree_evmInv s3 (s3.locals.update (ofString "w", vw)) pw0.clock hInv3
              have hc4 : s4.code = originalRuntimeCode := by rw [hs4_eq]; exact hc3
              have hs4_msg : s4.locals.lookup (ofString "msg") = some (.val (.word msgw)) := by
                rw [hs4_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs3_msg,
                  show ofString "w" ≠ ofString "msg" by decide]
              have hs4_code : s4.locals.lookup (ofString "code") = some (.val (.word codew)) := by
                rw [hs4_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs3_code,
                  show ofString "w" ≠ ofString "code" by decide]
              have hs4_n : s4.locals.lookup (ofString "n") = some (.val (.word nw)) := by
                rw [hs4_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs3_n,
                  show ofString "w" ≠ ofString "n" by decide]
              have hstep34 : CfStep s3 s4 := by
                rw [hs4_eq]; exact cfStep_with_locals_clock (cfStep_refl hInv3) (s3.locals.update (ofString "w", vw)) pw0.clock
              have hbody4 := create_finish_after_charges_cf hc4 hInv4 hn_le hs4_msg hs4_code hs4_n hnt0 hfr0
              rcases hr4 : evaluateHOLFiniteState s4 cfChargesProg with ⟨r4, p4⟩
              simp only [hr4] at hnt0 hfr0 hbody4 ⊢
              exact cfStep_trans hstep34 (cfStep_with_locals_clock hbody4 _ p4.clock)
            · simp [hsh_vw] at hfr0; exact absurd hfr0 not_flowingOrResumes_error

private theorem create_finish_body2_cf {F : Type}
    {s2 : PanSemStateFiniteExact 64 F} {nw codew msgw : BitVec 64}
    (hc2 : s2.code = originalRuntimeCode) (hInv2 : EvmInv s2)
    (hs2_msg : s2.locals.lookup (ofString "msg") = some (.val (.word msgw)))
    (hs2_code : s2.locals.lookup (ofString "code") = some (.val (.word codew)))
    (hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hnt0 : (evaluateHOLFiniteState s2 cfBody2Prog).1 ≠ some .timeOut)
    (hfr0 : FlowingOrResumes (evaluateHOLFiniteState s2 cfBody2Prog).1) :
    CfStep s2 (evaluateHOLFiniteState s2 cfBody2Prog).2 := by
  dsimp only [cfBody2Prog] at hnt0 hfr0 ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hnt0 hfr0 ⊢
  have hlfr1 : LocFrameR16 s2 (evaluateHOLFiniteState s2 cfIte1Prog).2 :=
    evaluate_roProgR16 (fun _ => false) (fun _ h => by simp at h) cfIte1Prog (by decide) s2 hc2
  have hav1 : ∀ k, avoidsLocal k cfIte1Prog = true := fun _ => rfl
  rcases hr_i1 : evaluateHOLFiniteState s2 cfIte1Prog with ⟨ri1, s3⟩
  have hflow1 : ri1 = none → ∀ k, s3.locals.lookup k = s2.locals.lookup k := by
    intro hri1 k
    have hk := evaluate_avoidsLocal_flowing k cfIte1Prog (hav1 k) s2 (by rw [hr_i1, hri1]; exact Or.inl rfl)
    rw [hr_i1] at hk; exact hk
  simp only [hr_i1] at hlfr1 hnt0 hfr0 ⊢
  cases ri1 with
  | some _ =>
    dsimp only
    have hs3_eq : s3 = { s2 with locals := s3.locals, clock := s3.clock } := hlfr1
    rw [hs3_eq]; exact cfStep_with_locals_clock (cfStep_refl hInv2) s3.locals s3.clock
  | none =>
    dsimp only at hnt0 hfr0 ⊢
    have hs3_loc : s3.locals = s2.locals := by
      apply HolFiniteMapExact.ext; funext k
      exact hflow1 rfl k
    have hs3_eq : s3 = { s2 with clock := s3.clock } := by
      unfold LocFrameR16 at hlfr1; rw [hlfr1, hs3_loc]
    have hInv3 : EvmInv s3 := by rw [hs3_eq]; exact localsFree_evmInv s2 s2.locals s3.clock hInv2
    have hc3 : s3.code = originalRuntimeCode := by rw [hs3_eq]; exact hc2
    have hs3_msg : s3.locals.lookup (ofString "msg") = some (.val (.word msgw)) := by rw [hs3_loc]; exact hs2_msg
    have hs3_code : s3.locals.lookup (ofString "code") = some (.val (.word codew)) := by rw [hs3_loc]; exact hs2_code
    have hs3_n : s3.locals.lookup (ofString "n") = some (.val (.word nw)) := by rw [hs3_loc]; exact hs2_n
    have hstep23 : CfStep s2 s3 := by
      rw [hs3_eq]; exact cfStep_with_locals_clock (cfStep_refl hInv2) s2.locals s3.clock
    exact cfStep_trans hstep23 (create_finish_after_guards_cf hc3 hInv3 hs3_msg hs3_code hs3_n hnt0 hfr0)

theorem create_finish_specs : CreateFinishSpecs where
  ek_create_finish := by
    obtain ⟨params, body, retShape, hlk, hrun⟩ := ek_create_finish_proof
    refine ⟨params, body, retShape, hlk, ?_⟩
    intro F s hc hAv hex hnt hres
    have hInv : EvmInv s := ⟨hAv.1, hAv.2.elim fun S hS => ⟨S, hS.1⟩⟩
    exact hrun s hc (evm_createFinishAvoids s hInv) hex hnt hres
  gas_mark_cells_create_finish := by
    have hlk_cf : originalRuntimeCode.lookup (ofString "create_finish") =
        some ([(ofString "msg", .one), (ofString "child", .one)],
          sourceFnBody Guest.Software.guestFn_create_finish, .one) :=
      lookup_create_finish
    refine ⟨[(ofString "msg", .one), (ofString "child", .one)],
      sourceFnBody Guest.Software.guestFn_create_finish, .one, hlk_cf, ?_⟩
    intro F s0 hc0 hAv0 hex0 hnt0 hres0
    have hInv0 : EvmInv s0 := ⟨hAv0.1, hAv0.2.elim fun S hS => ⟨S, hS.1⟩⟩
    obtain ⟨vs0, hlk0⟩ := hex0
    obtain ⟨msgw, childw, _, hs0_msg, hs0_child⟩ :=
      Fast_C08WkShard03.lookupCode_two_words (by decide) hlk_cf hlk0
    have hfr0 : FlowingOrResumes (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_create_finish)).1 :=
      Or.inr (Or.inr (Or.inr hres0))
    suffices hcf : CfStep s0 (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_create_finish)).2 by
      exact ⟨hcf.2.1, hcf.2.2.1, hcf.2.2.2⟩
    rw [cf_body_eq] at hnt0 hfr0 ⊢
    rw [evaluateHOLFiniteState_dec_total] at hnt0 hfr0 ⊢; dsimp only at hnt0 hfr0 ⊢
    rcases hcode_ev : @evalHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "child"), .const 120#64])) with _ | codev
    · simp [hcode_ev] at hfr0; exact absurd hfr0 not_flowingOrResumes_error
    · simp only [hcode_ev] at hnt0 hfr0 ⊢
      rcases codev with ⟨⟨codew⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hfr0; exact absurd hfr0 not_flowingOrResumes_error)
      have hsh_code : shapeEqHOL .one (shapeOfHOLExact (.val (.word codew) : ValueHOL 64)) = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      rw [if_pos hsh_code] at hnt0 hfr0 ⊢; dsimp only at hnt0 hfr0 ⊢
      set s1 := setVarHOLFinite (ofString "code") (.val (.word codew)) s0
      have hInv1 : EvmInv s1 := localsFree_evmInv s0 s1.locals s0.clock hInv0
      have hc1 : s1.code = originalRuntimeCode := hc0
      have hs1_msg : s1.locals.lookup (ofString "msg") = some (.val (.word msgw)) := by
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs0_msg,
          show ofString "code" ≠ ofString "msg" by decide]
      have hs1_code : s1.locals.lookup (ofString "code") = some (.val (.word codew)) := by
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      rw [evaluateHOLFiniteState_dec_total] at hnt0 hfr0 ⊢; dsimp only at hnt0 hfr0 ⊢
      rcases hn_ev : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
          (.load .one (.op .add [.var .local (ofString "child"), .const 128#64])) with _ | nv
      · simp [hn_ev] at hfr0; exact absurd hfr0 not_flowingOrResumes_error
      · simp only [hn_ev] at hnt0 hfr0 ⊢
        rcases nv with ⟨⟨nw⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hfr0; exact absurd hfr0 not_flowingOrResumes_error)
        have hsh_n : shapeEqHOL .one (shapeOfHOLExact (.val (.word nw) : ValueHOL 64)) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hsh_n] at hnt0 hfr0 ⊢; dsimp only at hnt0 hfr0 ⊢
        set s2 := setVarHOLFinite (ofString "n") (.val (.word nw)) s1
        have hInv2 : EvmInv s2 := localsFree_evmInv s1 s2.locals s1.clock hInv1
        have hc2 : s2.code = originalRuntimeCode := hc1
        have hs2_msg : s2.locals.lookup (ofString "msg") = some (.val (.word msgw)) := by
          simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_msg,
            show ofString "n" ≠ ofString "msg" by decide]
        have hs2_code : s2.locals.lookup (ofString "code") = some (.val (.word codew)) := by
          simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_code,
            show ofString "n" ≠ ofString "code" by decide]
        have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word nw)) := by
          simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hstep02 : CfStep s0 s2 :=
          cfStep_with_locals_clock (cfStep_refl hInv0) s2.locals s0.clock
        have hbody2 := create_finish_body2_cf hc2 hInv2 hs2_msg hs2_code hs2_n hnt0 hfr0
        rcases hr2 : evaluateHOLFiniteState s2 cfBody2Prog with ⟨r2, p2⟩
        simp only [hr2] at hbody2 ⊢
        exact cfStep_trans hstep02 (cfStep_with_locals_clock hbody2 _ p2.clock)

end CreateFinishSpecsProof
end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
