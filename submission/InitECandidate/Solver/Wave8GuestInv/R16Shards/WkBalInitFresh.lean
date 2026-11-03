import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalBase

/-! Zero-sorry proofs of `wk_bal_init` and `wk_state_fresh_tx` (`ContractParts/C08.lean`). -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBal

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. `noCatchableRaise` and `keepsG "scratch_ptr"` for `htab_new` and `alloc` -/

def initAllocCallees (f : MlS) : Bool :=
  f == ofString "trap_with" || f == ofString "alloc" || f == ofString "htab_new"

theorem initAllocCallees_good :
    ∀ f, initAllocCallees f = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      noCatchableRaise initAllocCallees body = true := by
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ :=
    InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
  simp only [initAllocCallees, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with (rfl | rfl) | rfl
  · have hl := lookup_of_guestAst_getElem 3 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_trap_with) rfl
    change originalRuntimeCode.lookup (ofString "trap_with") = _ at hl
    rw [hl] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_alloc) rfl
    change originalRuntimeCode.lookup (ofString "alloc") = _ at hl
    rw [hl] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [R10Shards.SoloHtabNew.lookup_htab_new] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl

theorem initAllocCallees_keeps_sp :
    ∀ f, initAllocCallees f = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      InitECandidate.Solver.GuestGlobalKeep.keepsG (ofString "scratch_ptr") initAllocCallees body = true := by
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ :=
    InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
  simp only [initAllocCallees, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with (rfl | rfl) | rfl
  · have hl := lookup_of_guestAst_getElem 3 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_trap_with) rfl
    change originalRuntimeCode.lookup (ofString "trap_with") = _ at hl
    rw [hl] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_alloc) rfl
    change originalRuntimeCode.lookup (ofString "alloc") = _ at hl
    rw [hl] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · rw [R10Shards.SoloHtabNew.lookup_htab_new] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl

theorem htab_new_no_catchable_exn {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (e : MlS) (v : ValueHOL 64)
    (hne : e ≠ ofString "TrapErr") :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_new)).1 ≠
      some (.exception e v) :=
  evaluate_noCatchableRaise initAllocCallees initAllocCallees_good
    (sourceFnBody Guest.Software.guestFn_htab_new) rfl s hcode e v hne

theorem alloc_no_catchable_exn {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (e : MlS) (v : ValueHOL 64)
    (hne : e ≠ ofString "TrapErr") :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).1 ≠
      some (.exception e v) :=
  evaluate_noCatchableRaise initAllocCallees initAllocCallees_good
    (sourceFnBody Guest.Software.guestFn_alloc) rfl s hcode e v hne

/-! ## 2. Exact heap-only `htab_new` and `alloc` steppers -/

theorem htab_new_heap_props {F : Type}
    (s : PanSemStateFiniteExact 64 F) (kw capw : BitVec 64)
    (hAR : ArenaReady s)
    (hkl : kw.toNat ∈ htabKeyLens)
    (hcl : capw.toNat ≤ htabCapMax)
    (hk : s.locals.lookup (ofString "key_len") = some (.val (.word kw)))
    (hc : s.locals.lookup (ofString "cap") = some (.val (.word capw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_new)).1 =
      some (.returned v)) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_new)).2
    ∃ tw : BitVec 64,
      v = .val (.word tw) ∧
      globN s "heap_ptr" ≤ tw.toNat ∧
      tw.toNat + 88 ≤ globN post "heap_ptr" ∧
      ArenaReady post ∧
      post.be = s.be ∧
      globN post "scratch_ptr" = globN s "scratch_ptr" ∧
      globN post "frame_mem_ptr" = globN s "frame_mem_ptr" ∧
      HtabWF post tw.toNat ∧
      hdr post tw.toNat 3 = 0 ∧
      hdr post tw.toNat 0 = kw.toNat ∧
      (∀ i ∈ htabFootprint post tw.toNat,
        Allocated post i ∧ Inside i (globN s "heap_ptr") (globN post "heap_ptr")) ∧
      FrameOutside s post [(globN s "scratch_ptr", 0)]
        (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = post.globals.lookup k) := by
  dsimp only
  have hpos : 0 < globN s "heap_ptr" := by
    have := hAR.2.1; rw [M13.sourceBase_val] at this; omega
  obtain ⟨p0, hp, _⟩ := R10Shards.SoloHtabNew.global_word_of_pos s "heap_ptr" hpos
  have hnp := R10Shards.SoloHtabNew.htab_new_run s hAR.1.code kw capw p0 hk hc hp hAR hkl hcl v hret
  obtain ⟨tw, rfl, hAp, hAG, hwf, hcnt0, hhdr0, hfp, hfr, hgl⟩ := hnp
  set post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_new)).2
  have hbe : post.be = s.be :=
    (M13.evaluateHOLFiniteState_guestInv_be s (sourceFnBody Guest.Software.guestFn_htab_new) hAR.1).2
  have hsp_lk : s.globals.lookup (ofString "scratch_ptr") = post.globals.lookup (ofString "scratch_ptr") :=
    (InitECandidate.Solver.GuestGlobalKeep.evaluate_keepsG
      (ofString "scratch_ptr") initAllocCallees initAllocCallees_keeps_sp
      (sourceFnBody Guest.Software.guestFn_htab_new) rfl s hAR.1.code).symm
  have hsp_eq : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    globN_eq_of_lookup hsp_lk
  have hfmp_eq : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" :=
    globN_eq_of_lookup (hgl (ofString "frame_mem_ptr") (by decide))
  have hfp_heap : ∀ i ∈ htabFootprint post tw.toNat,
      Allocated post i ∧ Inside i (globN s "heap_ptr") (globN post "heap_ptr") := by
    intro i hi
    obtain ⟨hal_i, hin_or⟩ := hfp i hi
    rcases hin_or with hin_h | hin_s
    · exact ⟨hal_i, hin_h⟩
    · rw [hsp_eq] at hin_s
      have hi0 : i.2 = 0 := by dsimp [Inside] at hin_s; omega
      have hpos_i : 0 < i.2 := by
        simp only [htabFootprint, List.mem_cons, List.not_mem_nil, or_false] at hi
        have hc2 : 2 ≤ hdr post tw.toNat 10 := hwf.2.2.2.2.2.1
        have hst1 : 1 ≤ hdr post tw.toNat 0 := hwf.2.2.1
        have hst_eq : hdr post tw.toNat 1 = (hdr post tw.toNat 0 + 7) / 8 * 8 := hwf.2.2.2.2.1
        rcases hi with rfl | rfl | rfl | rfl
        · dsimp; omega
        · dsimp; rw [hst_eq]
          exact Nat.mul_pos (by omega) (by omega)
        · dsimp; omega
        · dsimp; omega
      omega
  have ht_fp : (tw.toNat, 88) ∈ htabFootprint post tw.toNat := by simp [htabFootprint]
  have ht_in := (hfp_heap _ ht_fp).2
  have hfr_sp0 : FrameOutside s post [(globN s "scratch_ptr", 0)]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
    intro a hk0 hnhf
    apply hfr a
    · intro i hi hch
      simp only [List.mem_singleton] at hi; subst hi
      rw [hsp_eq, Nat.sub_self] at hch
      exact hk0 _ (List.mem_singleton.2 rfl) hch
    · exact hnhf
  have hgl' : ∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = post.globals.lookup k := by
    intro k hk_ne
    by_cases hsp : k = ofString "scratch_ptr"
    · subst hsp; exact hsp_lk
    · apply hgl k
      simp [List.mem_cons, hk_ne, hsp]
  exact ⟨tw, rfl, ht_in.1, ht_in.2, hAp, hbe, hsp_eq, hfmp_eq,
    hwf, hcnt0, by simpa [locN, hk] using hhdr0, hfp_heap, hfr_sp0, hgl'⟩

/-- Call stepper for `ProgHOL.call (some (some (vk, vname), none)) "htab_new" [.const kw, .const capw]`
followed by `cont`. -/
theorem seq_call_htab_new_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (vk : VarKind) (vname : MlS) (kw capw : BitVec 64) (cont : ProgHOL 64)
    (hAR : ArenaReady s)
    (hkl : kw.toNat ∈ htabKeyLens)
    (hcl : capw.toNat ≤ htabCapMax)
    (hdest_not_arena : vk = .global →
      vname ≠ ofString "heap_ptr" ∧ vname ≠ ofString "scratch_ptr" ∧ vname ≠ ofString "frame_mem_ptr")
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (some (vk, vname), none)) (ofString "htab_new") [.const kw, .const capw])
        cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq (.call (some (some (vk, vname), none)) (ofString "htab_new") [.const kw, .const capw])
        cont)).1) :
    ∃ (tw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      globN s "heap_ptr" ≤ tw.toNat ∧
      tw.toNat + 88 ≤ globN mid "heap_ptr" ∧
      ArenaReady mid ∧
      mid.be = s.be ∧
      globN mid "scratch_ptr" = globN s "scratch_ptr" ∧
      globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" ∧
      HtabWF mid tw.toNat ∧
      hdr mid tw.toNat 3 = 0 ∧
      hdr mid tw.toNat 0 = kw.toNat ∧
      (∀ i ∈ htabFootprint mid tw.toNat,
        Allocated mid i ∧ Inside i (globN s "heap_ptr") (globN mid "heap_ptr")) ∧
      FrameOutside s mid [(globN s "scratch_ptr", 0)] (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") ∧
      (vk = .local → mid.locals.lookup vname = some (.val (.word tw)) ∧
        (∀ x, x ≠ vname → mid.locals.lookup x = s.locals.lookup x) ∧
        (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = mid.globals.lookup k)) ∧
      (vk = .global → mid.globals.lookup vname = some (.val (.word tw)) ∧
        mid.locals = s.locals ∧
        (∀ k : MlS, k ≠ ofString "heap_ptr" → k ≠ vname → s.globals.lookup k = mid.globals.lookup k)) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      evaluateHOLFiniteState s
        (.seq (.call (some (some (vk, vname), none)) (ofString "htab_new") [.const kw, .const capw])
          cont) = evaluateHOLFiniteState mid cont := by
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres
  set cprog := ProgHOL.call (some (some (vk, vname), none)) (ofString "htab_new") [.const kw, .const capw]
  rcases hc_eval : evaluateHOLFiniteState s cprog with ⟨rc, mid⟩
  have hc_eval_orig := hc_eval
  rw [hc_eval] at hnt hres
  dsimp only [cprog] at hc_eval
  rw [evaluateHOLFiniteState_call] at hc_eval
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const kw, .const capw] = some [.val (.word kw), .val (.word capw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "htab_new")
    (ofString "key_len") (ofString "cap") (sourceFnBody Guest.Software.guestFn_htab_new) kw capw
    (by decide) (by rw [hAR.1.code]; exact R10Shards.SoloHtabNew.lookup_htab_new)
  rw [hargs] at hc_eval; dsimp only at hc_eval; rw [hlk] at hc_eval; dsimp only at hc_eval
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz] at hc_eval; injection hc_eval with hr _; subst hr; simp at hnt
  · rw [if_neg hcz] at hc_eval
    let cmap := (HolFiniteMapExact.empty.update (ofString "key_len", ValueHOL.val (.word kw))).update
      (ofString "cap", ValueHOL.val (.word capw))
    let ent := callEntryStateHOLFinite s cmap
    have hent_AR : ArenaReady ent := (arenaReady_with_locals s cmap (s.clock - 1)).2 hAR
    have hent_k : ent.locals.lookup (ofString "key_len") = some (.val (.word kw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "cap" ≠ ofString "key_len" by decide]
    have hent_c : ent.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_htab_new) with ⟨rb, sb⟩
    have hrun' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_htab_new) = (rb, sb) := hrun
    rw [hrun'] at hc_eval
    cases rb with
    | none =>
      injection hc_eval with hr _; subst hr; exact absurd hres not_resumes_error
    | some rb' =>
      cases rb' with
      | timeOut =>
        injection hc_eval with hr _; subst hr; simp at hnt
      | «break» | «continue» | error =>
        injection hc_eval with hr _; subst hr; exact absurd hres not_resumes_error
      | finalFfi _ =>
        injection hc_eval with hr _; subst hr
        exfalso; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      | exception e ev =>
        injection hc_eval with hr _; subst hr
        exfalso
        rcases hres with ⟨_, h⟩ | ⟨e', ev', h, hne⟩
        · simp at h
        · dsimp only at h; injection h with h'; injection h' with he1 he2; subst he1 he2
          exact htab_new_no_catchable_exn ent hAR.1.code e ev hne (congrArg Prod.fst hrun)
      | returned vb =>
        have hprops := htab_new_heap_props ent kw capw hent_AR hkl hcl hent_k hent_c vb
          (congrArg Prod.fst hrun)
        have hrun_snd : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_htab_new)).2 = sb :=
          congrArg Prod.snd hrun
        dsimp only at hprops
        rw [hrun_snd] at hprops
        obtain ⟨tw, rfl, htw_lo, htw_hi, hAsb, hbe_sb, hsp_sb, hfmp_sb,
          hwf_sb, hcnt0, hhdr0, hfp_sb, hfr_sb, hgl_sb⟩ := hprops
        dsimp only at hc_eval
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word tw) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hsh] at hc_eval
        by_cases hval : isValidValueHOLExact s.toExact vk vname (.val (.word tw)) = true
        · rw [if_pos hval] at hc_eval
          injection hc_eval with hr hmid
          subst hr
          have hmid_mem : mid.memory = sb.memory := by
            rw [← hmid]; cases vk <;> rfl
          have hmid_be : mid.be = s.be := by
            rw [← hmid]; cases vk <;> exact hbe_sb
          have hmid_hp : globN mid "heap_ptr" = globN sb "heap_ptr" := by
            rw [← hmid]
            cases vk with
            | «local» => rfl
            | global =>
              have hne := (hdest_not_arena rfl).1
              dsimp only [setKvarHOLFinite]
              simp [setGlobalHOLFinite, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne]
          have hmid_sp : globN mid "scratch_ptr" = globN s "scratch_ptr" := by
            rw [← hmid]
            cases vk with
            | «local» => exact hsp_sb
            | global =>
              have hne := (hdest_not_arena rfl).2.1
              dsimp only [setKvarHOLFinite]
              have h1 : globN (setGlobalHOLFinite vname (.val (.word tw)) { sb with locals := s.locals }) "scratch_ptr" =
                  globN sb "scratch_ptr" := by
                simp [setGlobalHOLFinite, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne]
              exact h1.trans hsp_sb
          have hmid_fmp : globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" := by
            rw [← hmid]
            cases vk with
            | «local» => exact hfmp_sb
            | global =>
              have hne := (hdest_not_arena rfl).2.2
              dsimp only [setKvarHOLFinite]
              have h1 : globN (setGlobalHOLFinite vname (.val (.word tw)) { sb with locals := s.locals }) "frame_mem_ptr" =
                  globN sb "frame_mem_ptr" := by
                simp [setGlobalHOLFinite, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne]
              exact h1.trans hfmp_sb
          have hmid_AR : ArenaReady mid := by
            rw [← hmid]
            cases vk with
            | «local» =>
              exact (arenaReady_with_locals sb _ sb.clock).2 hAsb
            | global =>
              dsimp only [setKvarHOLFinite]
              obtain ⟨hne1, hne2, hne3⟩ := hdest_not_arena rfl
              have hAsb' : ArenaReady { sb with locals := s.locals } :=
                (arenaReady_with_locals sb s.locals sb.clock).2 hAsb
              refine ⟨guestInv_congr (s := { sb with locals := s.locals }) rfl rfl rfl rfl hAsb'.1, ?_⟩
              unfold ArenaOK
              have e1 : globN (setGlobalHOLFinite vname (.val (.word tw)) { sb with locals := s.locals }) "heap_ptr" =
                  globN sb "heap_ptr" := by
                simp [setGlobalHOLFinite, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne1]
              have e2 : globN (setGlobalHOLFinite vname (.val (.word tw)) { sb with locals := s.locals }) "frame_mem_ptr" =
                  globN sb "frame_mem_ptr" := by
                simp [setGlobalHOLFinite, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne3]
              have e3 : globN (setGlobalHOLFinite vname (.val (.word tw)) { sb with locals := s.locals }) "scratch_ptr" =
                  globN sb "scratch_ptr" := by
                simp [setGlobalHOLFinite, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne2]
              rw [e1, e2, e3]
              refine ⟨hAsb.2.1, hAsb.2.2.1, hAsb.2.2.2.1, hAsb.2.2.2.2.1, hAsb.2.2.2.2.2.1,
                hAsb.2.2.2.2.2.2.1, hAsb.2.2.2.2.2.2.2.1, hAsb.2.2.2.2.2.2.2.2.1, ?_⟩
              intro g hg
              by_cases hgv : ofString g = vname
              · exact ⟨tw, by simp [GlobalWord, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hgv]⟩
              · obtain ⟨wg, hwg⟩ := hAsb.2.2.2.2.2.2.2.2.2 g hg
                exact ⟨wg, by simp [GlobalWord, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hgv, Ne.symm hgv]; exact hwg⟩
          have hmid_wf : HtabWF mid tw.toNat := by
            have hmid_eq_mem : mid = { sb with locals := mid.locals, globals := mid.globals, clock := mid.clock } := by
              rw [← hmid]; cases vk <;> rfl
            rw [hmid_eq_mem]
            have h1 : HtabWF { sb with locals := mid.locals, globals := mid.globals, clock := mid.clock } tw.toNat ↔
                HtabWF sb tw.toNat := by
              have hfc : ∀ nodes Fr head,
                  FreeChain { sb with locals := mid.locals, globals := mid.globals, clock := mid.clock } nodes head Fr ↔
                  FreeChain sb nodes head Fr := by
                intro nodes Fr
                induction Fr with
                | nil => intro _; exact Iff.rfl
                | cons f rest ih =>
                  intro head; simp only [FreeChain]; exact and_congr Iff.rfl (ih _)
              simp only [HtabWF, htabFootprint, hdr, nodeF, memW, WordsOK, WordAt, hfc]
            exact h1.2 hwf_sb
          have hmid_fp_eq : htabFootprint mid tw.toNat = htabFootprint sb tw.toNat := by
            simp [htabFootprint, hdr, memW, hmid_mem]
          have hseq_eq : evaluateHOLFiniteState s (.seq cprog cont) = evaluateHOLFiniteState mid cont := by
            rw [evaluateHOLFiniteState_seq_line780, hc_eval_orig]
          have hent_hp : globN ent "heap_ptr" = globN s "heap_ptr" := rfl
          refine ⟨tw, mid, htw_lo, by rw [hmid_hp]; exact htw_hi, hmid_AR, hmid_be, hmid_sp, hmid_fmp,
            hmid_wf, by simpa [hdr, memW, hmid_mem] using hcnt0,
            by simpa [hdr, memW, hmid_mem] using hhdr0, ?_, ?_, ?_, ?_, hnt, hres, hseq_eq⟩
          · intro i hi
            rw [hmid_fp_eq] at hi
            obtain ⟨_, hin_i⟩ := hfp_sb i hi
            rw [← hmid_hp] at hin_i
            exact ⟨Or.inl ⟨le_trans hAR.2.1 hin_i.1, hin_i.2⟩, hin_i⟩
          · intro a hk_nil hnhf
            rw [hmid_mem]
            have hnhf' : ¬ CellHits a.toNat (globN ent "heap_ptr", globN sb "heap_ptr" - globN ent "heap_ptr") := by
              rw [hent_hp, ← hmid_hp]; exact hnhf
            exact hfr_sb a hk_nil hnhf'
          · rintro rfl
            rw [← hmid]
            dsimp only [setKvarHOLFinite, setVarHOLFinite]
            refine ⟨by simp [HolFiniteMapExact.lookup_update, FUPDATE],
              fun x hx => by simp [HolFiniteMapExact.lookup_update, FUPDATE, hx, Ne.symm hx],
              fun k hk1 => hgl_sb k hk1⟩
          · rintro rfl
            rw [← hmid]
            dsimp only [setKvarHOLFinite, setGlobalHOLFinite]
            refine ⟨by simp [HolFiniteMapExact.lookup_update, FUPDATE], rfl, fun k hk1 hk2 => ?_⟩
            have h1 : s.globals.lookup k = sb.globals.lookup k := hgl_sb k hk1
            simp [HolFiniteMapExact.lookup_update, FUPDATE, hk2, Ne.symm hk2, h1]
        · rw [if_neg hval] at hc_eval
          injection hc_eval with hr _; subst hr
          exact absurd hres not_resumes_error

/-- Call stepper for `ProgHOL.decCall x .one "htab_new" [.const kw, .const capw] cont`. -/
theorem decCall_htab_new_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (x : MlS) (kw capw : BitVec 64) (cont : ProgHOL 64)
    (hAR : ArenaReady s)
    (hkl : kw.toNat ∈ htabKeyLens)
    (hcl : capw.toNat ≤ htabCapMax)
    (hnt : (evaluateHOLFiniteState s
      (.decCall x .one (ofString "htab_new") [.const kw, .const capw] cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall x .one (ofString "htab_new") [.const kw, .const capw] cont)).1) :
    ∃ (tw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      globN s "heap_ptr" ≤ tw.toNat ∧
      tw.toNat + 88 ≤ globN mid "heap_ptr" ∧
      ArenaReady mid ∧
      mid.be = s.be ∧
      globN mid "scratch_ptr" = globN s "scratch_ptr" ∧
      globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" ∧
      HtabWF mid tw.toNat ∧
      hdr mid tw.toNat 3 = 0 ∧
      hdr mid tw.toNat 0 = kw.toNat ∧
      (∀ i ∈ htabFootprint mid tw.toNat,
        Allocated mid i ∧ Inside i (globN s "heap_ptr") (globN mid "heap_ptr")) ∧
      FrameOutside s mid [(globN s "scratch_ptr", 0)] (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") ∧
      mid.locals.lookup x = some (.val (.word tw)) ∧
      (∀ y, y ≠ x → mid.locals.lookup y = s.locals.lookup y) ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = mid.globals.lookup k) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x .one (ofString "htab_new") [.const kw, .const capw] cont)).1 =
        (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x .one (ofString "htab_new") [.const kw, .const capw] cont)).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) } := by
  have hdc_nt := hnt
  have hdc_res := hres
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const kw, .const capw] = some [.val (.word kw), .val (.word capw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "htab_new")
    (ofString "key_len") (ofString "cap") (sourceFnBody Guest.Software.guestFn_htab_new) kw capw
    (by decide) (by rw [hAR.1.code]; exact R10Shards.SoloHtabNew.lookup_htab_new)
  rw [hargs] at hnt hres; dsimp only at hnt hres
  rw [hlk] at hnt hres; dsimp only at hnt hres
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz] at hnt; exact absurd rfl hnt
  · rw [if_neg hcz] at hnt hres
    let cmap := (HolFiniteMapExact.empty.update (ofString "key_len", ValueHOL.val (.word kw))).update
      (ofString "cap", ValueHOL.val (.word capw))
    let ent := callEntryStateHOLFinite s cmap
    have hent_AR : ArenaReady ent := (arenaReady_with_locals s cmap (s.clock - 1)).2 hAR
    have hent_k : ent.locals.lookup (ofString "key_len") = some (.val (.word kw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "cap" ≠ ofString "key_len" by decide]
    have hent_c : ent.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_htab_new) with ⟨rb, sb⟩
    have hrun' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_htab_new) = (rb, sb) := hrun
    rw [hrun'] at hnt hres
    cases rb with
    | none => exact absurd hres not_resumes_error
    | some rb' =>
      cases rb' with
      | timeOut => exact absurd rfl hnt
      | «break» | «continue» | error => exact absurd hres not_resumes_error
      | finalFfi _ =>
        exfalso; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      | exception e ev =>
        exfalso
        rcases hres with ⟨_, h⟩ | ⟨e', ev', h, hne⟩
        · simp at h
        · dsimp only at h; injection h with h'; injection h' with he1 he2; subst he1 he2
          exact htab_new_no_catchable_exn ent hAR.1.code e ev hne (congrArg Prod.fst hrun)
      | returned vb =>
        have hprops := htab_new_heap_props ent kw capw hent_AR hkl hcl hent_k hent_c vb
          (congrArg Prod.fst hrun)
        have hrun_snd : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_htab_new)).2 = sb :=
          congrArg Prod.snd hrun
        dsimp only at hprops
        rw [hrun_snd] at hprops
        obtain ⟨tw, rfl, htw_lo, htw_hi, hAsb, hbe_sb, hsp_sb, hfmp_sb,
          hwf_sb, hcnt0, hhdr0, hfp_sb, hfr_sb, hgl_sb⟩ := hprops
        dsimp only at hnt hres
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word tw) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word tw) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hsh] at hnt hres
        let mid := setVarHOLFinite x (.val (.word tw)) { sb with locals := s.locals }
        have hmid_AR : ArenaReady mid := (arenaReady_with_locals sb _ sb.clock).2 hAsb
        have hmid_wf : HtabWF mid tw.toNat := (htabWF_with_locals sb _ sb.clock tw.toNat).2 hwf_sb
        have heval_eq : evaluateHOLFiniteState s
            (.decCall x .one (ofString "htab_new") [.const kw, .const capw] cont) =
            ((evaluateHOLFiniteState mid cont).1,
              { (evaluateHOLFiniteState mid cont).2 with
                locals := HolFiniteMapExact.resVarEq
                  (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) }) := by
          rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs]
          dsimp only; rw [hlk]; dsimp only
          rw [if_neg hcz, hrun']; dsimp only
          rw [if_pos hsh]
        refine ⟨tw, mid, htw_lo, htw_hi, hmid_AR, hbe_sb, hsp_sb, hfmp_sb,
          hmid_wf, hcnt0, hhdr0, ?_, hfr_sb,
          by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
          fun y hy => by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hy, Ne.symm hy],
          fun k hk1 => hgl_sb k hk1,
          by intro hto; rw [hto] at hnt; exact hnt rfl,
          hres, by rw [heval_eq], by rw [heval_eq]⟩
        intro i hi
        have hfp_eq : htabFootprint mid tw.toNat = htabFootprint sb tw.toNat := rfl
        rw [hfp_eq] at hi
        exact hfp_sb i hi

/-- Call stepper for `ProgHOL.call (some (some (.global, gname), none)) "alloc" [.const nw]`
followed by `cont`. -/
theorem seq_call_alloc_global_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (gname : MlS) (nw : BitVec 64) (cont : ProgHOL 64)
    (hAR : ArenaReady s)
    (hnot_arena : gname ≠ ofString "heap_ptr" ∧ gname ≠ ofString "scratch_ptr" ∧ gname ≠ ofString "frame_mem_ptr")
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (some (.global, gname), none)) (ofString "alloc") [.const nw])
        cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq (.call (some (some (.global, gname), none)) (ofString "alloc") [.const nw])
        cont)).1) :
    ∃ (pw qw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      pw.toNat = globN s "heap_ptr" ∧
      qw.toNat = pw.toNat + (nw.toNat + 7) / 8 * 8 ∧
      globN mid "heap_ptr" = qw.toNat ∧
      pw.toNat ≤ qw.toNat ∧
      pw.toNat % 8 = 0 ∧
      ArenaReady mid ∧
      mid.memory = s.memory ∧
      mid.memaddrs = s.memaddrs ∧
      mid.be = s.be ∧
      mid.locals = s.locals ∧
      globN mid "scratch_ptr" = globN s "scratch_ptr" ∧
      globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" ∧
      mid.globals.lookup gname = some (.val (.word pw)) ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → k ≠ gname → s.globals.lookup k = mid.globals.lookup k) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      evaluateHOLFiniteState s
        (.seq (.call (some (some (.global, gname), none)) (ofString "alloc") [.const nw])
          cont) = evaluateHOLFiniteState mid cont := by
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres
  set cprog := ProgHOL.call (some (some (.global, gname), none)) (ofString "alloc") [.const nw]
  rcases hc_eval : evaluateHOLFiniteState s cprog with ⟨rc, mid⟩
  have hc_eval_orig := hc_eval
  rw [hc_eval] at hnt hres
  dsimp only [cprog] at hc_eval
  rw [evaluateHOLFiniteState_call] at hc_eval
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const nw] = some [.val (.word nw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_alloc) nw
    (by rw [hAR.1.code]; exact R13Shards.lookup_alloc_r13)
  rw [hargs] at hc_eval; dsimp only at hc_eval; rw [hlk] at hc_eval; dsimp only at hc_eval
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz] at hc_eval; injection hc_eval with hr _; subst hr; simp at hnt
  · rw [if_neg hcz] at hc_eval
    let cmap := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word nw))
    let ent := callEntryStateHOLFinite s cmap
    have hent_AR : ArenaReady ent := (arenaReady_with_locals s cmap (s.clock - 1)).2 hAR
    have hent_n : locN ent "n" = nw.toNat := by
      simp [locN, ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_alloc) with ⟨rb, sb⟩
    have hrun' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_alloc) = (rb, sb) := hrun
    rw [hrun'] at hc_eval
    cases rb with
    | none => injection hc_eval with hr _; subst hr; exact absurd hres not_resumes_error
    | some rb' =>
      cases rb' with
      | timeOut => injection hc_eval with hr _; subst hr; simp at hnt
      | «break» | «continue» | error =>
        injection hc_eval with hr _; subst hr; exact absurd hres not_resumes_error
      | finalFfi _ =>
        injection hc_eval with hr _; subst hr
        exfalso; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      | exception e ev =>
        injection hc_eval with hr _; subst hr
        exfalso
        rcases hres with ⟨_, h⟩ | ⟨e', ev', h, hne⟩
        · simp at h
        · dsimp only at h; injection h with h'; injection h' with he1 he2; subst he1 he2
          exact alloc_no_catchable_exn ent hAR.1.code e ev hne (congrArg Prod.fst hrun)
      | returned vb =>
        have hres_ent : Wave8Contracts.M12.Resumes
            (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_alloc)).1 :=
          Or.inl ⟨vb, congrArg Prod.fst hrun⟩
        obtain ⟨pw, qw, hrv_ent, hpw_eq, hqw_eq, _, _, hpw_le_qw, hsb_g, hsb_m, hsb_be, hsb_ma, hAsb, hsb_hp, hsb_sp⟩ :=
          R13Shards.alloc_body_resumes_props ent hAR.1.code hent_AR hres_ent
        rw [hrun] at hrv_ent hsb_g hsb_m hsb_be hsb_ma hAsb hsb_hp hsb_sp
        dsimp only at hrv_ent hsb_g hsb_m hsb_be hsb_ma hAsb hsb_hp hsb_sp
        injection hrv_ent with hvb; injection hvb with hvb'; subst hvb'
        rw [hent_n] at hqw_eq
        dsimp only at hc_eval
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word pw) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hsh] at hc_eval
        by_cases hval : isValidValueHOLExact s.toExact .global gname (.val (.word pw)) = true
        · rw [if_pos hval] at hc_eval
          injection hc_eval with hr hmid
          subst hr
          obtain ⟨hne1, hne2, hne3⟩ := hnot_arena
          have hmid_hp : globN mid "heap_ptr" = qw.toNat := by
            rw [← hmid]; dsimp only [setKvarHOLFinite]
            have e1 : globN (setGlobalHOLFinite gname (.val (.word pw)) { sb with locals := s.locals }) "heap_ptr" =
                globN sb "heap_ptr" := by
              simp [setGlobalHOLFinite, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne1]
            exact e1.trans hsb_hp
          have hmid_sp : globN mid "scratch_ptr" = globN s "scratch_ptr" := by
            rw [← hmid]; dsimp only [setKvarHOLFinite]
            have e1 : globN (setGlobalHOLFinite gname (.val (.word pw)) { sb with locals := s.locals }) "scratch_ptr" =
                globN sb "scratch_ptr" := by
              simp [setGlobalHOLFinite, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne2]
            exact e1.trans hsb_sp
          have hmid_fmp : globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" := by
            rw [← hmid]; dsimp only [setKvarHOLFinite]
            have hsb_fmp : globN sb "frame_mem_ptr" = globN s "frame_mem_ptr" := by
              unfold globN; rw [hsb_g]
              simp [ent, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
            have e1 : globN (setGlobalHOLFinite gname (.val (.word pw)) { sb with locals := s.locals }) "frame_mem_ptr" =
                globN sb "frame_mem_ptr" := by
              simp [setGlobalHOLFinite, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne3]
            exact e1.trans hsb_fmp
          have hmid_AR : ArenaReady mid := by
            rw [← hmid]; dsimp only [setKvarHOLFinite]
            have hAsb' : ArenaReady { sb with locals := s.locals } :=
              (arenaReady_with_locals sb s.locals sb.clock).2 hAsb
            refine ⟨guestInv_congr (s := { sb with locals := s.locals }) rfl rfl rfl rfl hAsb'.1, ?_⟩
            unfold ArenaOK
            have e1 : globN (setGlobalHOLFinite gname (.val (.word pw)) { sb with locals := s.locals }) "heap_ptr" =
                globN sb "heap_ptr" := by
              simp [setGlobalHOLFinite, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne1]
            have e2 : globN (setGlobalHOLFinite gname (.val (.word pw)) { sb with locals := s.locals }) "frame_mem_ptr" =
                globN sb "frame_mem_ptr" := by
              simp [setGlobalHOLFinite, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne3]
            have e3 : globN (setGlobalHOLFinite gname (.val (.word pw)) { sb with locals := s.locals }) "scratch_ptr" =
                globN sb "scratch_ptr" := by
              simp [setGlobalHOLFinite, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne2]
            rw [e1, e2, e3]
            refine ⟨hAsb.2.1, hAsb.2.2.1, hAsb.2.2.2.1, hAsb.2.2.2.2.1, hAsb.2.2.2.2.2.1,
              hAsb.2.2.2.2.2.2.1, hAsb.2.2.2.2.2.2.2.1, hAsb.2.2.2.2.2.2.2.2.1, ?_⟩
            intro g hg
            by_cases hgv : ofString g = gname
            · exact ⟨pw, by simp [GlobalWord, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hgv]⟩
            · obtain ⟨wg, hwg⟩ := hAsb.2.2.2.2.2.2.2.2.2 g hg
              exact ⟨wg, by simp [GlobalWord, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hgv, Ne.symm hgv]; exact hwg⟩
          have hpw8 : pw.toNat % 8 = 0 := by
            rw [hpw_eq]; exact hAR.2.2.2.2.2.2.1
          have hseq_eq : evaluateHOLFiniteState s (.seq cprog cont) = evaluateHOLFiniteState mid cont := by
            rw [evaluateHOLFiniteState_seq_line780, hc_eval_orig]
          refine ⟨pw, qw, mid, hpw_eq, hqw_eq, hmid_hp, hpw_le_qw, hpw8, hmid_AR,
            by rw [← hmid]; exact hsb_m,
            by rw [← hmid]; exact hsb_ma,
            by rw [← hmid]; exact hsb_be,
            by rw [← hmid]; rfl,
            hmid_sp, hmid_fmp,
            by rw [← hmid]; simp [setKvarHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
            fun k hk1 hk2 => ?_,
            hnt, hres, hseq_eq⟩
          rw [← hmid]
          simp [ent, callEntryStateHOLFinite, setKvarHOLFinite, setGlobalHOLFinite, hsb_g,
            HolFiniteMapExact.lookup_update, FUPDATE, hk1, Ne.symm hk1, hk2, Ne.symm hk2]
        · rw [if_neg hval] at hc_eval
          injection hc_eval with hr _; subst hr
          exact absurd hres not_resumes_error

/-! ## 3. Heap-only frame & `bal_init` / `state_fresh_tx` world-typing helpers -/

theorem mem0_8_16_eq_of_heap_sp_frame {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {keep : List Ivl}
    (hAs : ArenaOK s)
    (hk_lo : ∀ j ∈ keep, sourceBase ≤ j.1)
    (hfr : FrameOutside s post keep (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")) :
    memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 := by
  have hsb : sourceBase = 2701131776 := rfl
  have hhp_lo := hAs.1
  have hlow : ∀ a : Nat, a + 8 ≤ sourceBase → memW post a = memW s a := fun a ha => by
    have ha_lt : a < 2 ^ 64 := by rw [hsb] at ha; omega
    have hm := hfr (BitVec.ofNat 64 a)
      (fun j hj hcj => by
        have hj_lo := hk_lo j hj
        obtain ⟨c1, _⟩ := hcj
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at c1
        omega)
      (fun hcf => by
        obtain ⟨c1, _⟩ := hcf
        dsimp only at c1
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at c1
        omega)
    unfold memW; rw [hm]
  exact ⟨hlow 0 (by rw [hsb]; omega), hlow 8 (by rw [hsb]; omega), hlow 16 (by rw [hsb]; omega)⟩

theorem ivlUnhit_of_allocated_heap_sp0 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {keep : List Ivl} {i : Ivl}
    (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hal : Allocated s i)
    (hk_sp : ∀ j ∈ keep, ∃ sp, j = (sp, 0) ∧ sp % 8 = 0)
    (hfr : FrameOutside s post keep (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")) :
    M08IvlUnhit s post i := by
  intro a ha8 h1 h2
  have hd_hf : Disj i (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
    by_cases hle : globN s "heap_ptr" ≤ globN post "heap_ptr"
    · exact disj_flip (InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap hAs hAp hal
        ⟨le_rfl, by omega⟩)
    · exact Or.inr (Or.inl (by dsimp; omega))
  apply hfr a
  · intro j hj hcj
    obtain ⟨sp, rfl, hsp8⟩ := hk_sp j hj
    exact InitECandidate.Solver.Wave8Contracts.M08.not_cellHits_of_disj ha8 hsp8 ⟨h1, h2⟩
      (Or.inr (Or.inl rfl)) hcj
  · exact InitECandidate.Solver.Wave8Contracts.M08.not_cellHits_of_disj ha8 hAs.2.2.2.2.2.1 ⟨h1, h2⟩
      hd_hf

theorem ivlUnhit_trans {F : Type} {a b c : PanSemStateFiniteExact 64 F} {i : Ivl}
    (h1 : M08IvlUnhit a b i) (h2 : M08IvlUnhit b c i) : M08IvlUnhit a c i :=
  fun x hx8 hx1 hx2 => (h2 x hx8 hx1 hx2).trans (h1 x hx8 hx1 hx2)

theorem frameOutside_seq_heap_sp0 {F : Type} {a b c : PanSemStateFiniteExact 64 F}
    {ks kb : List Ivl}
    (hha : globN a "heap_ptr" ≤ globN b "heap_ptr")
    (hhb : globN b "heap_ptr" ≤ globN c "heap_ptr")
    (h1 : FrameOutside a b ks (globN a "heap_ptr", globN b "heap_ptr" - globN a "heap_ptr"))
    (h2 : FrameOutside b c kb (globN b "heap_ptr", globN c "heap_ptr" - globN b "heap_ptr")) :
    FrameOutside a c (ks ++ kb) (globN a "heap_ptr", globN c "heap_ptr" - globN a "heap_ptr") := by
  intro x hno hnhf
  have hnhf1 : ¬ CellHits x.toNat (globN a "heap_ptr", globN b "heap_ptr" - globN a "heap_ptr") := by
    intro ⟨c1, c2⟩; dsimp only at c1 c2
    exact hnhf ⟨c1, by dsimp only; omega⟩
  have hnhf2 : ¬ CellHits x.toNat (globN b "heap_ptr", globN c "heap_ptr" - globN b "heap_ptr") := by
    intro ⟨c1, c2⟩; dsimp only at c1 c2
    exact hnhf ⟨by dsimp only; omega, by dsimp only; omega⟩
  exact (h2 x (fun j hj => hno j (List.mem_append_right _ hj)) hnhf2).trans
    (h1 x (fun j hj => hno j (List.mem_append_left _ hj)) hnhf1)

theorem lookup_bal_init :
    originalRuntimeCode.lookup (ofString "bal_init") =
      some ([], sourceFnBody Guest.Software.guestFn_bal_init, .one) :=
  lookup_of_guestAst_getElem 411 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bal_init) rfl

theorem lookup_state_fresh_tx :
    originalRuntimeCode.lookup (ofString "state_fresh_tx") =
      some ([], sourceFnBody Guest.Software.guestFn_state_fresh_tx, .one) :=
  lookup_of_guestAst_getElem 355 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_state_fresh_tx) rfl

theorem disj_fresh_sub {i j : Ivl} {a b c d : Nat}
    (hi : Inside i a b) (hj : Inside j c d) (hbc : b ≤ c) : Disj i j :=
  Or.inr (Or.inr (Or.inl (le_trans hi.2 (le_trans hbc hj.1))))

theorem htab_nonzero_of_wf {F : Type} {s : PanSemStateFiniteExact 64 F} {t : Nat}
    (hW : HtabWF s t) : t ≠ 0 := by
  have hlo := (hW.1 (t, 88) (by simp [htabFootprint])).1.1
  have hsb : 0 < sourceBase := by decide
  dsimp at hlo; omega

theorem zero_not_mem_S_of_tables {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hT : TablesTyped s S) : 0 ∉ S :=
  fun h0 => htab_nonzero_of_wf (hT.2.1 0 h0).1 rfl

theorem htabWF_transfer_unhit {F : Type} {a b : PanSemStateFiniteExact 64 F} {t : Nat}
    (ha : ArenaReady a) (hb : ArenaReady b)
    (hW : HtabWF a t)
    (hu : ∀ i ∈ htabFootprint a t, M08IvlUnhit a b i)
    (halloc : ∀ i ∈ htabFootprint a t, Allocated b i) :
    HtabWF b t ∧ htabFootprint b t = htabFootprint a t ∧ (∀ k, k < 11 → hdr b t k = hdr a t k) := by
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have ht_fp : (t, 88) ∈ htabFootprint a t := by simp [htabFootprint]
  have ht8 : t % 8 = 0 := (hW.1 _ ht_fp).2.1
  have hhi : t + 88 ≤ 2 ^ 64 := by have := (hW.1 _ ht_fp).1.2; dsimp at this; omega
  obtain ⟨hhdr, hfp_eq⟩ :=
    InitECandidate.Solver.Wave8Contracts.M08.htabFootprint_eq_of_hdr_unhit ht8 hhi (hu _ ht_fp)
  exact ⟨InitECandidate.Solver.Wave8Contracts.M08.htabWF_congr_unhit ha.1 hb.1 hW hu, hfp_eq, hhdr⟩

theorem seq_assign_global_zero_return_zero {F : Type}
    (s : PanSemStateFiniteExact 64 F) (gname : MlS)
    (hAR : ArenaReady s)
    (hg_mem : ∃ gn ∈ guestGlobalNames, ofString gn = gname)
    (hnot_arena : gname ≠ ofString "heap_ptr" ∧ gname ≠ ofString "scratch_ptr" ∧ gname ≠ ofString "frame_mem_ptr") :
    let post := emptyLocalsHOLFinite (setGlobalHOLFinite gname (.val (.word 0)) s)
    evaluateHOLFiniteState s
      (.seq (.assign .global gname (.const 0)) (.return (.const 0))) =
      (some (.returned (.val (.word 0))), post) ∧
    ArenaReady post ∧
    post.memory = s.memory ∧
    post.memaddrs = s.memaddrs ∧
    post.be = s.be ∧
    globN post "heap_ptr" = globN s "heap_ptr" ∧
    globN post "scratch_ptr" = globN s "scratch_ptr" ∧
    globN post "frame_mem_ptr" = globN s "frame_mem_ptr" ∧
    post.globals.lookup gname = some (.val (.word 0)) ∧
    (∀ k : MlS, k ≠ gname → s.globals.lookup k = post.globals.lookup k) := by
  dsimp only
  obtain ⟨gn, hgn_in, hgn_eq⟩ := hg_mem
  obtain ⟨w0, hw0⟩ := hAR.2.2.2.2.2.2.2.2.2 gn hgn_in
  unfold GlobalWord at hw0
  rw [hgn_eq] at hw0
  have heval : evaluateHOLFiniteState s
      (.seq (.assign .global gname (.const 0)) (.return (.const 0))) =
      (some (.returned (.val (.word 0))),
        emptyLocalsHOLFinite (setGlobalHOLFinite gname (.val (.word 0)) s)) := by
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
    simp [evalHOLExact, isValidValueHOLFinite, isValidValueHOLExact,
      lookupKvarHOLFinite, lookupKvarHOLExact, hw0,
      shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
      evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
  obtain ⟨hne1, hne2, hne3⟩ := hnot_arena
  set post := emptyLocalsHOLFinite (setGlobalHOLFinite gname (.val (.word 0)) s)
  have e1 : globN post "heap_ptr" = globN s "heap_ptr" := by
    simp [post, emptyLocalsHOLFinite, setGlobalHOLFinite, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne1]
  have e2 : globN post "scratch_ptr" = globN s "scratch_ptr" := by
    simp [post, emptyLocalsHOLFinite, setGlobalHOLFinite, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne2]
  have e3 : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
    simp [post, emptyLocalsHOLFinite, setGlobalHOLFinite, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne3]
  have hAR_post : ArenaReady post := by
    refine ⟨guestInv_congr (s := s) rfl rfl rfl rfl hAR.1, ?_⟩
    unfold ArenaOK
    rw [e1, e3, e2]
    refine ⟨hAR.2.1, hAR.2.2.1, hAR.2.2.2.1, hAR.2.2.2.2.1, hAR.2.2.2.2.2.1,
      hAR.2.2.2.2.2.2.1, hAR.2.2.2.2.2.2.2.1, hAR.2.2.2.2.2.2.2.2.1, ?_⟩
    intro g hg
    by_cases hgv : ofString g = gname
    · exact ⟨0, by simp [post, emptyLocalsHOLFinite, GlobalWord, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hgv]⟩
    · obtain ⟨wg, hwg⟩ := hAR.2.2.2.2.2.2.2.2.2 g hg
      exact ⟨wg, by simp [post, emptyLocalsHOLFinite, GlobalWord, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hgv, Ne.symm hgv]; exact hwg⟩
  exact ⟨heval, hAR_post, rfl, rfl, rfl, e1, e2, e3,
    by simp [post, emptyLocalsHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
    fun k hk => by simp [post, emptyLocalsHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk, Ne.symm hk]⟩

/-- Notice `FrameOutside s post [(globN s "scratch_ptr", 0)] (hp0, hp1 - hp0)` implies
`FrameOutside s post [freeGap s] (heapFree s)` ONLY when `frame_mem_ptr < scratch_ptr`!
Wait: what if `frame_mem_ptr = scratch_ptr`? Then `freeGap s = (sp, 0)`, so `(sp, 0) ∈ [freeGap s]`!
And if `frame_mem_ptr < scratch_ptr`, then `sp - 8 ≥ frame_mem_ptr` (since both are `% 8 = 0`),
so ANY `a` hitting `(sp, 0)` (`sp < a + 8 ∧ a < sp`) satisfies `frame_mem_ptr ≤ sp - 8 < a + 8`
AND `a < sp = frame_mem_ptr + (sp - frame_mem_ptr)`, i.e. `CellHits a (freeGap s)`!
WHAT A GEM! `(globN s "scratch_ptr", 0)` is ALWAYS subsumed by `freeGap s` in `ArenaOK s`! -/
theorem cellHits_sp0_imp_freeGap {F : Type} {s : PanSemStateFiniteExact 64 F} {a : Nat}
    (hA : ArenaOK s) (hch : CellHits a (globN s "scratch_ptr", 0)) :
    CellHits a (freeGap s) := by
  obtain ⟨c1, c2⟩ := hch
  dsimp only at c1 c2
  have hle := hA.2.2.2.1
  have hfm8 := hA.2.2.2.2.2.2.1
  have hsp8 := hA.2.2.2.2.2.2.2.1
  unfold freeGap M13.freeGap CellHits
  dsimp only
  omega

theorem frameOutside_sp0_to_world {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {keep : List Ivl} { extra : List Ivl }
    (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hk_sp : ∀ j ∈ keep, j = (globN s "scratch_ptr", 0))
    (hfr : FrameOutside s post keep (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")) :
    FrameOutside s post (extra ++ [freeGap s]) (heapFree s) := by
  intro a hno hnhf
  apply hfr a
  · intro j hj hcj
    rw [hk_sp j hj] at hcj
    exact hno (freeGap s) (List.mem_append_right _ (List.mem_singleton.2 rfl))
      (cellHits_sp0_imp_freeGap hAs hcj)
  · intro ⟨c1, c2⟩
    dsimp only at c1 c2
    have hp_lim := hAp.2.1
    exact hnhf ⟨c1, by unfold heapFree M13.heapFree; dsimp only; omega⟩

/-! ## 4. `wk_bal_init` -/

theorem pairwise_disj_globalBuffers_rebind {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hF : FixedTyped s)
    {rebound : List String}
    (hkept : ∀ gn ∈ globalBuffers, gn.1 ∉ rebound → globN post gn.1 = globN s gn.1)
    (hfresh : ∀ gn ∈ globalBuffers, gn.1 ∈ rebound →
      globN post gn.1 = 0 ∨ Inside (globN post gn.1, gn.2) (globN s "heap_ptr") (globN post "heap_ptr"))
    (hrebound_pw : rebound.Pairwise (fun g1 g2 =>
      ∀ sz1 sz2, (g1, sz1) ∈ globalBuffers → (g2, sz2) ∈ globalBuffers →
        Disj (globN post g1, if globN post g1 = 0 then 0 else sz1)
             (globN post g2, if globN post g2 = 0 then 0 else sz2))) :
    (globalBuffers.map fun gn => (globN post gn.1, if globN post gn.1 = 0 then 0 else gn.2)).Pairwise Disj := by
  have hpw_s : (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)).Pairwise Disj := by
    have hpw := hF.2
    unfold fixedObjects at hpw
    exact (List.pairwise_append.1 (List.pairwise_append.1 (List.pairwise_append.1 hpw).1).1).1
  have hal_s : ∀ gn ∈ globalBuffers,
      (if globN s gn.1 = 0 then 0 else gn.2) = 0 ∨
        Allocated s (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2) := by
    intro gn hgn
    have hm : (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2) ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.2 ⟨gn, hgn, rfl⟩
    rcases hF.1 _ hm with h0 | ⟨hal, _⟩
    · exact Or.inl h0
    · exact Or.inr hal
  have hgb_nodup : (globalBuffers.map Prod.fst).Nodup := by decide
  rw [List.pairwise_map] at hpw_s ⊢
  rw [List.pairwise_iff_getElem] at hpw_s ⊢
  intro i j hi hj hij
  let gni := globalBuffers[i]
  let gnj := globalBuffers[j]
  have hmem_i : gni ∈ globalBuffers := List.getElem_mem hi
  have hmem_j : gnj ∈ globalBuffers := List.getElem_mem hj
  have hne_name : gni.1 ≠ gnj.1 := by
    intro heq
    have hinj := List.nodup_iff_injective_getElem.1 hgb_nodup
    have hij_fin : (⟨i, by simpa using hi⟩ : Fin (globalBuffers.map Prod.fst).length) =
        ⟨j, by simpa using hj⟩ :=
      hinj (by simpa [gni, gnj] using heq)
    have hij_val : i = j := congrArg Fin.val hij_fin
    omega
  change Disj (globN post gni.1, if globN post gni.1 = 0 then 0 else gni.2)
    (globN post gnj.1, if globN post gnj.1 = 0 then 0 else gnj.2)
  by_cases hri : gni.1 ∈ rebound <;> by_cases hrj : gnj.1 ∈ rebound
  · obtain ⟨ki, hki, heqi⟩ := List.mem_iff_getElem.1 hri
    obtain ⟨kj, hkj, heqj⟩ := List.mem_iff_getElem.1 hrj
    have hkne : ki ≠ kj := by intro h; subst h; rw [heqi] at heqj; exact hne_name heqj
    have hget := List.pairwise_iff_getElem.1 hrebound_pw
    rcases Nat.lt_or_gt_of_ne hkne with hlt | hgt
    · have hd := hget ki kj hki hkj hlt gni.2 gnj.2
        (by rw [heqi]; exact hmem_i) (by rw [heqj]; exact hmem_j)
      rw [← heqi, ← heqj]; exact hd
    · have hd := hget kj ki hkj hki hgt gnj.2 gni.2
        (by rw [heqj]; exact hmem_j) (by rw [heqi]; exact hmem_i)
      rw [← heqi, ← heqj]; exact disj_flip hd
  · rw [hkept gnj hmem_j hrj]
    rcases hfresh gni hmem_i hri with hz | hfr_i
    · rw [hz]; exact Or.inl rfl
    · by_cases hiz : globN post gni.1 = 0
      · rw [hiz]; exact Or.inl rfl
      · rw [if_neg hiz]
        rcases hal_s gnj hmem_j with hj0 | hal_j
        · exact Or.inr (Or.inl hj0)
        · exact InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap hAs hAp hal_j hfr_i
  · rw [hkept gni hmem_i hri]
    rcases hfresh gnj hmem_j hrj with hz | hfr_j
    · rw [hz]; exact Or.inr (Or.inl rfl)
    · by_cases hjz : globN post gnj.1 = 0
      · rw [hjz]; exact Or.inr (Or.inl rfl)
      · rw [if_neg hjz]
        rcases hal_s gni hmem_i with hi0 | hal_i
        · exact Or.inl hi0
        · exact disj_flip (InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap hAs hAp hal_i hfr_j)
  · rw [hkept gni hmem_i hri, hkept gnj hmem_j hrj]
    exact hpw_s i j hi hj hij

/-- General `FixedTyped` reconstruction when `rebound` is a singleton `[g0]` rebound to a fresh
word-aligned block `(p, sz0)` inside `[heap_ptr s, heap_ptr post)`, `blockOutObjects post = blockOutObjects s`,
and `balObjects post ⊆ balObjects s` (specifically `balObjects post = []` or `balObjects post = balObjects s`). -/
theorem fixedTyped_rebind_one_fresh {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hag : AllocatorGrows s post)
    (hF : FixedTyped s)
    (g0 : String) (sz0 : Nat)
    (hg0_mem : (g0, sz0) ∈ globalBuffers)
    (hg0_nz : globN post g0 ≠ 0)
    (hg0_8 : (globN post g0) % 8 = 0)
    (hsz0_8 : sz0 % 8 = 0)
    (hg0_in : Inside (globN post g0, sz0) (globN s "heap_ptr") (globN post "heap_ptr"))
    (hgb_kept : ∀ gn ∈ globalBuffers, gn.1 ≠ g0 → globN post gn.1 = globN s gn.1)
    (hj_eq : globN post "journal" = globN s "journal")
    (hjc_eq : globN post "journal_cap" = globN s "journal_cap")
    (hbo_eq : blockOutObjects post = blockOutObjects s)
    (hbal_sub : ∀ x ∈ balObjects post, x ∈ balObjects s)
    (hbal_pw : (balObjects post).Pairwise Disj) :
    FixedTyped post ∧
    (∀ o ∈ fixedObjects post, o ∈ fixedObjects s ∨ o = (0, 0) ∨
      Inside o (globN s "heap_ptr") (globN post "heap_ptr")) := by
  have hal_g0 : Allocated post (globN post g0, sz0) :=
    Or.inl ⟨le_trans hAs.2.1 hg0_in.1, hg0_in.2⟩
  have hw_g0 : WordsOK post (globN post g0, sz0) :=
    M13.wordsOK_of_allocated hAp hal_g0 hg0_8 hsz0_8
  have hmem_classify : ∀ o ∈ fixedObjects post,
      o ∈ fixedObjects s ∨ o = (globN post g0, sz0) := by
    intro o ho
    unfold fixedObjects at ho
    rcases List.mem_append.1 ho with ho123 | ho_bal
    · rcases List.mem_append.1 ho123 with ho12 | ho_bo
      · rcases List.mem_append.1 ho12 with ho_gb | ho_jr
        · obtain ⟨gn, hgn, rfl⟩ := List.mem_map.1 ho_gb
          by_cases hname : gn.1 = g0
          · have hsz_eq : gn.2 = sz0 := by
              have hnodup : (globalBuffers.map Prod.fst).Nodup := by decide
              obtain ⟨i1, hi1, he1⟩ := List.mem_iff_getElem.1 hgn
              obtain ⟨i2, hi2, he2⟩ := List.mem_iff_getElem.1 hg0_mem
              have hinj := List.nodup_iff_injective_getElem.1 hnodup
              have hfin : (⟨i1, by simpa using hi1⟩ : Fin (globalBuffers.map Prod.fst).length) =
                  ⟨i2, by simpa using hi2⟩ := by
                apply hinj
                simp only [List.getElem_map]
                rw [he1, he2]; exact hname
              have hi_eq : i1 = i2 := congrArg Fin.val hfin
              subst hi_eq; rw [he1] at he2; exact congrArg Prod.snd he2
            right; rw [hname, hsz_eq, if_neg hg0_nz]
          · left
            rw [hgb_kept gn hgn hname]
            unfold fixedObjects
            apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
            exact List.mem_map.2 ⟨gn, hgn, rfl⟩
        · left
          simp only [List.mem_singleton] at ho_jr; subst ho_jr
          rw [hjc_eq, hj_eq]
          unfold fixedObjects
          apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
          exact List.mem_singleton.2 rfl
      · left; rw [hbo_eq] at ho_bo; exact M13.blockOut_in_fixedObjects ho_bo
    · left; exact M13.bal_in_fixedObjects (hbal_sub o ho_bal)
  have halloc_post : ∀ o ∈ fixedObjects post, o.2 = 0 ∨ (Allocated post o ∧ WordsOK post o) := by
    intro o ho
    rcases hmem_classify o ho with ho_old | rfl
    · rcases hF.1 o ho_old with h0 | ⟨hal, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hag.allocated hal,
          InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hAs.1 hAp.1 hw⟩
    · exact Or.inr ⟨hal_g0, hw_g0⟩
  have hpw_gb_post :
      (globalBuffers.map fun gn => (globN post gn.1, if globN post gn.1 = 0 then 0 else gn.2)).Pairwise Disj := by
    refine pairwise_disj_globalBuffers_rebind hAs.2 hAp.2 hF (rebound := [g0])
      (fun gn hgn hnin => hgb_kept gn hgn (fun h => hnin (List.mem_singleton.2 h)))
      (fun gn hgn hin => ?_) (List.pairwise_singleton _ _)
    have hname := List.mem_singleton.1 hin
    have hsz_eq : gn.2 = sz0 := by
      have hnodup : (globalBuffers.map Prod.fst).Nodup := by decide
      obtain ⟨i1, hi1, he1⟩ := List.mem_iff_getElem.1 hgn
      obtain ⟨i2, hi2, he2⟩ := List.mem_iff_getElem.1 hg0_mem
      have hinj := List.nodup_iff_injective_getElem.1 hnodup
      have hfin : (⟨i1, by simpa using hi1⟩ : Fin (globalBuffers.map Prod.fst).length) =
          ⟨i2, by simpa using hi2⟩ :=
        hinj (by simp only [List.getElem_map]; rw [he1, he2]; exact hname)
      have hi_eq : i1 = i2 := congrArg Fin.val hfin
      subst hi_eq; rw [he1] at he2; exact congrArg Prod.snd he2
    rw [hname, hsz_eq]; exact Or.inr hg0_in
  have hpw_s := hF.2
  unfold fixedObjects at hpw_s
  obtain ⟨hpw_123, _, hcross_123_bal⟩ := List.pairwise_append.1 hpw_s
  obtain ⟨hpw_12, hpw_bo, hcross_12_bo⟩ := List.pairwise_append.1 hpw_123
  obtain ⟨_, hpw_jr, hcross_gb_jr⟩ := List.pairwise_append.1 hpw_12
  have hdisj_g0_old : ∀ x ∈ fixedObjects s, Disj (globN post g0, sz0) x := by
    intro x hx
    rcases hF.1 x hx with hx0 | ⟨hal_x, _⟩
    · exact Or.inr (Or.inl hx0)
    · exact InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_x hg0_in
  have hgb_post_in : ∀ x ∈ (globalBuffers.map fun gn => (globN post gn.1, if globN post gn.1 = 0 then 0 else gn.2)),
      x ∈ (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) ∨
        x = (globN post g0, sz0) := by
    intro x hx
    obtain ⟨gn, hgn, rfl⟩ := List.mem_map.1 hx
    by_cases hname : gn.1 = g0
    · have hsz_eq : gn.2 = sz0 := by
        have hnodup : (globalBuffers.map Prod.fst).Nodup := by decide
        obtain ⟨i1, hi1, he1⟩ := List.mem_iff_getElem.1 hgn
        obtain ⟨i2, hi2, he2⟩ := List.mem_iff_getElem.1 hg0_mem
        have hinj := List.nodup_iff_injective_getElem.1 hnodup
        have hfin : (⟨i1, by simpa using hi1⟩ : Fin (globalBuffers.map Prod.fst).length) =
            ⟨i2, by simpa using hi2⟩ :=
          hinj (by simp only [List.getElem_map]; rw [he1, he2]; exact hname)
        have hi_eq : i1 = i2 := congrArg Fin.val hfin
        subst hi_eq; rw [he1] at he2; exact congrArg Prod.snd he2
      right; rw [hname, hsz_eq, if_neg hg0_nz]
    · left; rw [hgb_kept gn hgn hname]; exact List.mem_map.2 ⟨gn, hgn, rfl⟩
  have hpw_post : (fixedObjects post).Pairwise Disj := by
    unfold fixedObjects
    rw [hjc_eq, hj_eq, hbo_eq]
    apply List.pairwise_append.2
    refine ⟨List.pairwise_append.2 ⟨List.pairwise_append.2 ⟨hpw_gb_post, hpw_jr, ?_⟩, hpw_bo, ?_⟩, hbal_pw, ?_⟩
    · intro x hx y hy
      rcases hgb_post_in x hx with hx_s | rfl
      · exact hcross_gb_jr x hx_s y hy
      · simp only [List.mem_singleton] at hy; subst hy
        apply hdisj_g0_old
        unfold fixedObjects
        apply List.mem_append_left; apply List.mem_append_left; exact List.mem_append_right _ (List.mem_singleton.2 rfl)
    · intro x hx y hy
      rcases List.mem_append.1 hx with hx_gb | hx_jr
      · rcases hgb_post_in x hx_gb with hx_s | rfl
        · exact hcross_12_bo x (List.mem_append_left _ hx_s) y hy
        · exact hdisj_g0_old y (M13.blockOut_in_fixedObjects hy)
      · exact hcross_12_bo x (List.mem_append_right _ hx_jr) y hy
    · intro x hx y hy
      have hy_s := hbal_sub y hy
      rcases List.mem_append.1 hx with hx_12 | hx_bo
      · rcases List.mem_append.1 hx_12 with hx_gb | hx_jr
        · rcases hgb_post_in x hx_gb with hx_s | rfl
          · exact hcross_123_bal x (List.mem_append_left _ (List.mem_append_left _ hx_s)) y hy_s
          · exact hdisj_g0_old y (M13.bal_in_fixedObjects hy_s)
        · exact hcross_123_bal x (List.mem_append_left _ (List.mem_append_right _ hx_jr)) y hy_s
      · exact hcross_123_bal x (List.mem_append_right _ hx_bo) y hy_s
  refine ⟨⟨halloc_post, hpw_post⟩, fun o ho => ?_⟩
  rcases hmem_classify o ho with ho_old | rfl
  · exact Or.inl ho_old
  · exact Or.inr (Or.inr hg0_in)

/-- Adding fresh pairwise-disjoint tables `T_new` (each with a fresh non-shared role `r` not
appearing in `jr`, and disjoint from `S` and `fixedObjects post` and `nodeExtents post Nd`). -/
theorem rolesOK_adjoin_fresh_slots {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S T_new : List Nat}
    {old_sl new_sl jr : List (Nat × String)}
    (hroles_s : RolesOK s S old_sl jr)
    (hhdr0_S : ∀ t ∈ S, hdr post t 0 = hdr s t 0)
    (hnew_decomp : ∃ prefix_sl added_sl suffix_sl,
      new_sl = prefix_sl ++ added_sl ++ suffix_sl ∧
      (∀ a ∈ prefix_sl ++ suffix_sl, a ∈ old_sl) ∧
      (prefix_sl ++ suffix_sl).Pairwise (fun a b => a.1 = b.1 → a.2 = b.2 ∧ a.2 ∈ sharedRoles) ∧
      (∀ a ∈ added_sl, a.1 ∈ T_new ∧ hdr post a.1 0 = roleKeyLen a.2) ∧
      added_sl.Pairwise (fun a b => a.1 ≠ b.1))
    (hT_disj_S : ∀ t ∈ T_new, t ∉ S) :
    RolesOK post (S ++ T_new) new_sl jr := by
  obtain ⟨prefix_sl, added_sl, suffix_sl, rfl, hps_old, hps_pw, hadd_ok, hadd_pw⟩ := hnew_decomp
  have hsub_S : ∀ t ∈ S, t ∈ S ++ T_new := fun t ht => List.mem_append_left _ ht
  have hsub_T : ∀ t ∈ T_new, t ∈ S ++ T_new := fun t ht => List.mem_append_right _ ht
  have hne_ST : ∀ u ∈ S, ∀ v ∈ T_new, u ≠ v := by
    intro u hu v hv rfl; exact hT_disj_S u hv hu
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.1 ha with ha_sl | ha_jr
    · rcases List.mem_append.1 ha_sl with ha_pa | ha_suf
      · rcases List.mem_append.1 ha_pa with ha_pre | ha_add
        · have ho := hps_old a (List.mem_append_left _ ha_pre)
          obtain ⟨haS, hkl⟩ := hroles_s.1 a (List.mem_append_left _ ho)
          exact ⟨hsub_S _ haS, (hhdr0_S _ haS).trans hkl⟩
        · obtain ⟨haT, hkl⟩ := hadd_ok a ha_add
          exact ⟨hsub_T _ haT, hkl⟩
      · have ho := hps_old a (List.mem_append_right _ ha_suf)
        obtain ⟨haS, hkl⟩ := hroles_s.1 a (List.mem_append_left _ ho)
        exact ⟨hsub_S _ haS, (hhdr0_S _ haS).trans hkl⟩
    · obtain ⟨haS, hkl⟩ := hroles_s.1 a (List.mem_append_right _ ha_jr)
      exact ⟨hsub_S _ haS, (hhdr0_S _ haS).trans hkl⟩
  · -- Pairwise on `prefix_sl ++ added_sl ++ suffix_sl`
    obtain ⟨hpw_pre, hpw_suf, hcross_ps⟩ := List.pairwise_append.1 hps_pw
    apply List.pairwise_append.2
    refine ⟨List.pairwise_append.2 ⟨hpw_pre, ?_, ?_⟩, hpw_suf, ?_⟩
    · exact hadd_pw.imp (fun hne heq => absurd heq hne)
    · intro a ha b hb heq
      have haS := (hroles_s.1 a (List.mem_append_left _ (hps_old a (List.mem_append_left _ ha)))).1
      have hbT := (hadd_ok b hb).1
      exact absurd heq (hne_ST a.1 haS b.1 hbT)
    · intro a ha b hb heq
      have hbS := (hroles_s.1 b (List.mem_append_left _ (hps_old b (List.mem_append_right _ hb)))).1
      rcases List.mem_append.1 ha with ha_pre | ha_add
      · exact hcross_ps a ha_pre b hb heq
      · have haT := (hadd_ok a ha_add).1
        exact absurd heq.symm (hne_ST b.1 hbS a.1 haT)
  · intro a ha b hb heq
    have haS := (hroles_s.1 a (List.mem_append_right _ ha)).1
    rcases List.mem_append.1 hb with hb_sl | hb_jr
    · rcases List.mem_append.1 hb_sl with hb_pa | hb_suf
      · rcases List.mem_append.1 hb_pa with hb_pre | hb_add
        · exact hroles_s.2.2 a ha b (List.mem_append_left _ (hps_old b (List.mem_append_left _ hb_pre))) heq
        · exact absurd heq (hne_ST a.1 haS b.1 (hadd_ok b hb_add).1)
      · exact hroles_s.2.2 a ha b (List.mem_append_left _ (hps_old b (List.mem_append_right _ hb_suf))) heq
    · exact hroles_s.2.2 a ha b (List.mem_append_right _ hb_jr) heq

theorem memB_eq_of_allocated_heap_sp0 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {keep : List Ivl} {i : Ivl} {a : Nat}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hbe : post.be = s.be)
    (hal : Allocated s i)
    (hk_sp : ∀ j ∈ keep, ∃ sp, j = (sp, 0) ∧ sp % 8 = 0)
    (hfr : FrameOutside s post keep (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    (hin : i.1 ≤ a ∧ a < i.1 + i.2) :
    memB post a = memB s a := by
  have hhi := (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hAs hal).2
  have ha_lt : a < 2 ^ 64 := by omega
  let c := panByteAlignHOL (BitVec.ofNat 64 a)
  have hc_nat : c.toNat = a / 8 * 8 := by
    have hal8 : 2 ^ ((64 : Nat) / 8).log2 = 8 := by decide
    change (BitVec.ofNat 64 ((BitVec.ofNat 64 a).toNat / 2 ^ ((64 : Nat) / 8).log2 *
      2 ^ ((64 : Nat) / 8).log2)).toNat = a / 8 * 8
    rw [hal8, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt,
      Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self a 8) ha_lt)]
  have hmem : post.memory c = s.memory c := by
    apply hfr c
    · intro j hj ⟨c1, c2⟩
      obtain ⟨sp, rfl, hsp8⟩ := hk_sp j hj
      dsimp only at c1 c2; rw [hc_nat] at c1 c2; omega
    · intro ⟨c1, c2⟩
      change globN s "heap_ptr" < c.toNat + 8 at c1
      change c.toNat < globN s "heap_ptr" + (globN post "heap_ptr" - globN s "heap_ptr") at c2
      rw [hc_nat] at c1 c2
      have hhp8 := hAs.2.2.2.2.2.1
      rcases hal with ⟨_, hi_hp⟩ | ⟨hi_sc, _⟩
      · change i.1 + i.2 ≤ globN s "heap_ptr" at hi_hp
        omega
      · have hsep : heapLimit ≤ scratchStart := by decide
        have h1 := hAp.2.1; have h2 := hAs.2.2.1; have h3 := hAs.2.2.2.1
        have hsp8 := hAs.2.2.2.2.2.2.2.1
        change globN s "scratch_ptr" ≤ i.1 at hi_sc
        omega
  unfold memB
  change (match post.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 a) v post.be).toNat) =
         (match s.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 a) v s.be).toNat)
  rw [hmem, hbe]

/-- General `TablesTyped`, `JournalTyped`, `TriesTypedWith`, and `OwnedGrows` extension when:
1. `T_new` are pairwise distinct fresh well-formed tables whose footprints are allocated in `post`
   and lie inside `[heap_ptr s, heap_ptr post)`, and are pairwise footprint-disjoint among `T_new`.
2. `FixedTyped post` holds and every `o ∈ fixedObjects post` is either in `fixedObjects s`, `(0, 0)`,
   or inside `[heap_ptr s, heap_ptr post)`, AND disjoint from every `t ∈ T_new`'s footprint.
3. All old tables `t ∈ S`, `ws`, `bs`, `bo` list headers, and `Nd` nodes/paths are unhit. -/
theorem tables_tries_adjoin_fresh {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S T_new Nd : List Nat}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hag : AllocatorGrows s post)
    (hW : WorldTypedWith s S Nd)
    (hF_post : FixedTyped post)
    (hfix_from : ∀ o ∈ fixedObjects post, o ∈ fixedObjects s ∨ o = (0, 0) ∨
      Inside o (globN s "heap_ptr") (globN post "heap_ptr"))
    (hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, M08IvlUnhit s post i)
    (hu_ws : globN s "ws" ≠ 0 → M08IvlUnhit s post (globN s "ws", 40))
    (hu_bs : globN s "bs" ≠ 0 → M08IvlUnhit s post (globN s "bs", 80))
    (hu_bo : globN s "bo" ≠ 0 → M08IvlUnhit s post (globN s "bo", 88))
    (hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → M08IvlUnhit s post i)
    (hu_nd_rec : ∀ n ∈ Nd, M08IvlUnhit s post (nodeIvl s n))
    (hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k))
    (hm0 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16)
    (hws_g : globN post "ws" = globN s "ws")
    (hbs_g : globN post "bs" = globN s "bs")
    (hbo_g : globN post "bo" = globN s "bo")
    (hT_nd : T_new.Nodup)
    (hT_wf : ∀ t ∈ T_new, HtabWF post t ∧
      ∀ i ∈ htabFootprint post t, Allocated post i ∧
        Inside i (globN s "heap_ptr") (globN post "heap_ptr") ∧
        (∀ j ∈ fixedObjects post, Disj i j))
    (hT_pw : ∀ t ∈ T_new, ∀ u ∈ T_new, t ≠ u →
      ∀ i ∈ htabFootprint post t, ∀ j ∈ htabFootprint post u, Disj i j)
    (hts_post : ∀ k ∈ tsTableSlots, globN post "ts" ≠ 0 → RootIn (S ++ T_new) (memW post (globN post "ts" + k)))
    (hgr_post : ∀ g ∈ globalTableRoots, RootIn (S ++ T_new) (globN post g))
    (htsN_post : globN post "ts" ≠ 0 → memW post (globN post "ts" + 32) ∈ S ++ T_new →
      HtabValuesIn post (memW post (globN post "ts" + 32)) (S ++ T_new))
    (hbal_post : ∀ ad ∈ balRecords post, memW post ad ∈ S ++ T_new ∧ memW post (ad + 8) ∈ S ++ T_new ∧
      (∀ k ∈ ([16, 24, 32] : List Nat), LstOK post (memW post (ad + k))) ∧
      (∀ l ∈ htabValues post (memW post ad), LstOK post l))
    (hroles_post : (∀ t ∈ S, hdr post t 0 = hdr s t 0) → (∀ t ∈ T_new, t ∉ S) →
      RolesOK post (S ++ T_new) (worldRoleSlots post) (journalRoleSlots post))
    (hJ_post : JournalTyped post (S ++ T_new)) :
    (∀ t ∈ T_new, t ∉ S) ∧
    WorldTypedWith post (S ++ T_new) Nd ∧
    OwnedGrows s post (worldOwned s S Nd) (worldOwned post (S ++ T_new) Nd) := by
  obtain ⟨hT, _, hF, hTr⟩ := hW
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have hT_disj_S : ∀ t ∈ T_new, t ∉ S := by
    intro t ht htS
    have ht_in := ((hT_wf t ht).2 (t, 88) (by simp [htabFootprint])).2.1
    have hal_s := ((hT.2.1 t htS).2 (t, 88) (by simp [htabFootprint])).1
    have hd := InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_s ht_in
    rcases hd with h | h | h | h <;> dsimp at h <;> omega
  have hsub_S : ∀ u ∈ S, u ∈ S ++ T_new := fun u hu => List.mem_append_left _ hu
  have hroot_S : ∀ {v}, RootIn S v → RootIn (S ++ T_new) v := by
    rintro v (rfl | hv); exact Or.inl rfl; exact Or.inr (hsub_S v hv)
  have htab_fp_hdr : ∀ t ∈ S, (∀ k, k < 11 → hdr post t k = hdr s t k) ∧ htabFootprint post t = htabFootprint s t := by
    intro t ht
    have hwf := (hT.2.1 t ht).1
    have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
    have ht8 : t % 8 = 0 := (hwf.1 _ ht_fp).2.1
    have hhi : t + 88 ≤ 2 ^ 64 := by have := (hwf.1 _ ht_fp).1.2; dsimp at this; omega
    exact InitECandidate.Solver.Wave8Contracts.M08.htabFootprint_eq_of_hdr_unhit ht8 hhi (hu_tab t ht _ ht_fp)
  have hbo_words : globN s "bo" ≠ 0 → ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := fun hnz k hk => by
    have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    simpa [hbo_g] using InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
      hAs.2 hF "bo" 88 (by decide) hbo_g hnz (hu_bo hnz) hk_in.1 hk_in.2
  have hbo_part := InitECandidate.Solver.Wave8Contracts.M08.blockOutObjects_eq_of_bo_unhit
    hAs.2 hF hbo_g hT.2.2.2.2.2.2.2.2.2.2.1
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
  have hnd_part := InitECandidate.Solver.Wave8Contracts.M08.nodeHeap_congr_bytes
    hAs.1 hAp.1 hag hTr.1 hu_nd_rec hu_nd_byte
  obtain ⟨hndS, hTt, hTp, hwsR, hbsR, _, _, hbsN, _, _, _, _⟩ := hT
  have hT_post : TablesTyped post (S ++ T_new) := by
    refine ⟨List.nodup_append.2 ⟨hndS, hT_nd, fun u hu v hv heq => by subst heq; exact hT_disj_S u hv hu⟩,
      ?_, ?_, ?_, ?_, hts_post, hgr_post, ?_, htsN_post, hbal_post, hbo_part.2,
      hroles_post (fun t ht => (htab_fp_hdr t ht).1 0 (by omega)) hT_disj_S⟩
    · intro t ht
      rcases List.mem_append.1 ht with htS | htN
      · rw [(htab_fp_hdr t htS).2]
        refine ⟨InitECandidate.Solver.Wave8Contracts.M08.htabWF_congr_unhit hAs.1 hAp.1 (hTt t htS).1 (hu_tab t htS),
          fun i hi => ⟨hag.allocated ((hTt t htS).2 i hi).1, fun j hj => ?_⟩⟩
        rcases hfix_from j hj with hj_s | rfl | hj_fr
        · exact ((hTt t htS).2 i hi).2 j hj_s
        · exact Or.inr (Or.inl rfl)
        · exact disj_flip (InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap
            hAs.2 hAp.2 ((hTt t htS).2 i hi).1 hj_fr)
      · exact ⟨(hT_wf t htN).1, fun i hi => ⟨((hT_wf t htN).2 i hi).1, ((hT_wf t htN).2 i hi).2.2⟩⟩
    · intro t ht u hu_mem hne i hi j hj
      rcases List.mem_append.1 ht with htS | htN <;> rcases List.mem_append.1 hu_mem with huS | huN
      · rw [(htab_fp_hdr t htS).2] at hi; rw [(htab_fp_hdr u huS).2] at hj
        exact hTp t htS u huS hne i hi j hj
      · rw [(htab_fp_hdr t htS).2] at hi
        exact disj_flip (InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap
          hAs.2 hAp.2 ((hTt t htS).2 i hi).1 ((hT_wf u huN).2 j hj).2.1)
      · rw [(htab_fp_hdr u huS).2] at hj
        exact InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap
          hAs.2 hAp.2 ((hTt u huS).2 j hj).1 ((hT_wf t htN).2 i hi).2.1
      · exact hT_pw t htN u huN hne i hi j hj
    · intro k hk hnz
      rw [hws_g] at hnz
      have hwk : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      rw [InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
        hAs.2 hF "ws" 40 (by decide) hws_g hnz (hu_ws hnz) hwk.1 hwk.2]
      exact hroot_S (hwsR k hk hnz)
    · intro k hk hnz
      rw [hbs_g] at hnz
      have hbk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
        hAs.2 hF "bs" 80 (by decide) hbs_g hnz (hu_bs hnz) hbk.1 hbk.2]
      exact hroot_S (hbsR k hk hnz)
    · intro hnz hm
      rw [hbs_g] at hnz
      have hw32 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
        hAs.2 hF "bs" 80 (by decide) hbs_g hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [hw32] at hm ⊢
      rcases List.mem_append.1 hm with hmS | hmN
      · exact InitECandidate.Solver.Wave8Contracts.M08.htabValuesIn_congr_unhit
          (hTt _ hmS).1 (hu_tab _ hmS) hsub_S (hbsN hnz hmS)
      · rcases hbsR 32 (by simp [bsTableSlots]) hnz with h0 | hmS
        · exact absurd (h0 ▸ hmN) (fun h0N => htab_nonzero_of_wf (hT_wf 0 h0N).1 rfl)
        · exact absurd hmS (hT_disj_S _ hmN)
  have hTr_post : TriesTypedWith post (S ++ T_new) Nd := by
    refine ⟨hnd_part.1, ?_, ?_⟩
    · intro o ho
      rw [hnd_part.2] at ho
      have ho_alloc : o = (0, 0) ∨ Allocated s o := by
        unfold nodeExtents at ho
        obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
        rcases hno with rfl | rfl
        · exact Or.inr (hTr.1.1 n hn).2.1
        · unfold nodePath
          split_ifs with hp
          · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hp.1 with h0 | ⟨_, hal, _, _⟩
            · exact absurd h0 hp.2
            · exact Or.inr hal
          · exact Or.inl rfl
      refine ⟨fun t ht i hi => ?_, fun j hj => ?_⟩
      · rcases List.mem_append.1 ht with htS | htN
        · rw [(htab_fp_hdr t htS).2] at hi
          exact (hTr.2.1 o ho).1 t htS i hi
        · rcases ho_alloc with rfl | hal_o
          · exact Or.inl rfl
          · exact disj_flip (InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap
              hAs.2 hAp.2 hal_o ((hT_wf t htN).2 i hi).2.1)
      · rcases hfix_from j hj with hj_s | rfl | hj_fr
        · exact (hTr.2.1 o ho).2 j hj_s
        · exact Or.inr (Or.inl rfl)
        · rcases ho_alloc with rfl | hal_o
          · exact Or.inl rfl
          · exact disj_flip (InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap
              hAs.2 hAp.2 hal_o hj_fr)
    · intro hnz
      rw [hws_g] at hnz
      have hw24 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
        hAs.2 hF "ws" 40 (by decide) hws_g hnz (hu_ws hnz) (k := 24) (by omega) (by omega)
      have hw32 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
        hAs.2 hF "ws" 40 (by decide) hws_g hnz (hu_ws hnz) (k := 32) (by omega) (by omega)
      rw [hw24, hw32]
      obtain ⟨hr24, hr32⟩ := hTr.2.2 hnz
      refine ⟨hr24, fun hm i hi => ?_⟩
      rcases List.mem_append.1 hm with hmS | hmN
      · have hwf32 := (hTt _ hmS).1
        have hu32 := hu_tab _ hmS
        have hh32 := htab_fp_hdr _ hmS
        rw [hh32.1 3 (by omega)] at hi
        have hvals := InitECandidate.Solver.Wave8Contracts.M08.htabValues_eq_of_unhit hwf32 hu32
        have hget : (htabValues post (memW s (globN s "ws" + 32)))[i]? =
            (htabValues s (memW s (globN s "ws" + 32)))[i]? := by rw [hvals]
        simp only [htabValues, List.getElem?_map, List.getElem?_range, hh32.1 3 (by omega), hi,
          Option.map_some, Option.some.injEq] at hget
        rw [hget]; exact hr32 hmS i hi
      · rcases hwsR 32 (by simp [wsTableSlots]) hnz with h0 | hmS
        · exact absurd (h0 ▸ hmN) (fun h0N => htab_nonzero_of_wf (hT_wf 0 h0N).1 rfl)
        · exact absurd hmS (hT_disj_S _ hmN)
  have hOG : OwnedGrows s post (worldOwned s S Nd) (worldOwned post (S ++ T_new) Nd) := by
    intro o ho
    unfold worldOwned M13.worldOwned at ho
    rcases List.mem_append.1 ho with ho12 | ho_nd
    · rcases List.mem_append.1 ho12 with ho_tab | ho_fix
      · rw [List.flatMap_append] at ho_tab
        rcases List.mem_append.1 ho_tab with ho_S | ho_N
        · obtain ⟨t, htS, hi⟩ := List.mem_flatMap.1 ho_S
          rw [(htab_fp_hdr t htS).2] at hi
          refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
          unfold worldOwned M13.worldOwned
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨t, htS, hi⟩))
        · obtain ⟨t, htN, hi⟩ := List.mem_flatMap.1 ho_N
          exact Or.inr (Or.inr ((hT_wf t htN).2 o hi).2.1)
      · rcases hfix_from o ho_fix with ho_s | rfl | ho_fr
        · refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
          unfold worldOwned M13.worldOwned
          exact List.mem_append_left _ (List.mem_append_right _ ho_s)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr ho_fr)
    · rw [hnd_part.2] at ho_nd
      refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
      unfold worldOwned M13.worldOwned
      exact List.mem_append_right _ ho_nd
  exact ⟨hT_disj_S, ⟨hT_post, hJ_post, hF_post, hTr_post⟩, hOG⟩

theorem list_sublist_pairwise {α : Type} {R : α → α → Prop} {l1 l2 : List α}
    (hsub : List.Sublist l1 l2) (hpw : l2.Pairwise R) : l1.Pairwise R :=
  hpw.sublist hsub

/-- Zero-sorry proof of `wk_bal_init` (`ContractParts/C08.lean`). -/
theorem wk_bal_init :
    WorldKeeps WorldOK (fun _ => [])
    ["bal_accounts", "bal_idx_accts", "bal_idx_stor", "bal_index", "bal_key_buf", "heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
     ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "bal_init") := by
  refine ⟨_, _, _, lookup_bal_init, ?_⟩
  intro F s hcode hWOK _ hnt hres
  have hAR0 : ArenaReady s := hWOK.1
  have hbody_eq : sourceFnBody Guest.Software.guestFn_bal_init =
      .seq (.call (some (some (.global, ofString "bal_accounts"), none)) (ofString "htab_new") [.const 20, .const 64])
      (.seq (.call (some (some (.global, ofString "bal_idx_accts"), none)) (ofString "htab_new") [.const 28, .const 64])
      (.seq (.call (some (some (.global, ofString "bal_idx_stor"), none)) (ofString "htab_new") [.const 60, .const 64])
      (.seq (.call (some (some (.global, ofString "bal_key_buf"), none)) (ofString "alloc") [.const 64])
      (.seq (.assign .global (ofString "bal_index") (.const 0))
            (.return (.const 0)))))) := rfl
  rw [hbody_eq] at hnt hres ⊢
  obtain ⟨t1, s1, ht1_lo, ht1_hi, hAR1, hbe1, hsp1, hfmp1, hwf1, hcnt1, hhdr1, hfp1, hfr1, _, hg1, hnt1, hres1, heq1⟩ :=
    seq_call_htab_new_resumes s .global (ofString "bal_accounts") 20 64 _ hAR0
      (by decide) (by decide) (fun _ => ⟨by decide, by decide, by decide⟩) hnt hres
  obtain ⟨hs1_ba, _, hg1_other⟩ := hg1 rfl
  obtain ⟨t2, s2, ht2_lo, ht2_hi, hAR2, hbe2, hsp2, hfmp2, hwf2, hcnt2, hhdr2, hfp2, hfr2, _, hg2, hnt2, hres2, heq2⟩ :=
    seq_call_htab_new_resumes s1 .global (ofString "bal_idx_accts") 28 64 _ hAR1
      (by decide) (by decide) (fun _ => ⟨by decide, by decide, by decide⟩) hnt1 hres1
  obtain ⟨hs2_bia, _, hg2_other⟩ := hg2 rfl
  obtain ⟨t3, s3, ht3_lo, ht3_hi, hAR3, hbe3, hsp3, hfmp3, hwf3, hcnt3, hhdr3, hfp3, hfr3, _, hg3, hnt3, hres3, heq3⟩ :=
    seq_call_htab_new_resumes s2 .global (ofString "bal_idx_stor") 60 64 _ hAR2
      (by decide) (by decide) (fun _ => ⟨by decide, by decide, by decide⟩) hnt2 hres2
  obtain ⟨hs3_bis, _, hg3_other⟩ := hg3 rfl
  obtain ⟨pk, qk, s4, hpk_eq, hqk_eq, hs4_hp, hpk_le_qk, hpk8, hAR4, hs4_m, hs4_ma, hs4_be, _,
      hsp4, hfmp4, hs4_bkb, hg4_other, _, _, heq4⟩ :=
    seq_call_alloc_global_resumes s3 (ofString "bal_key_buf") 64 _ hAR3
      ⟨by decide, by decide, by decide⟩ hnt3 hres3
  obtain ⟨heq5, hAR5, hs5_m, hs5_ma, hs5_be, hs5_hp, hsp5, hfmp5, hs5_bi, hg5_other⟩ :=
    seq_assign_global_zero_return_zero s4 (ofString "bal_index") hAR4
      ⟨"bal_index", by decide, rfl⟩ ⟨by decide, by decide, by decide⟩
  rw [heq1, heq2, heq3, heq4, heq5]
  dsimp only
  set post := emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "bal_index") (.val (.word 0)) s4)
  have hhp_01 : globN s "heap_ptr" ≤ globN s1 "heap_ptr" := by omega
  have hhp_12 : globN s1 "heap_ptr" ≤ globN s2 "heap_ptr" := by omega
  have hhp_23 : globN s2 "heap_ptr" ≤ globN s3 "heap_ptr" := by omega
  have hhp_34 : globN s3 "heap_ptr" ≤ globN s4 "heap_ptr" := by omega
  have hhp_05 : globN s "heap_ptr" ≤ globN post "heap_ptr" := by omega
  have hsp_post : globN post "scratch_ptr" = globN s "scratch_ptr" := by
    rw [hsp5, hsp4, hsp3, hsp2, hsp1]
  have hag : AllocatorGrows s post := ⟨hhp_05, by rw [hsp_post]⟩
  have hbe_post : post.be = s.be := by rw [hs5_be, hs4_be, hbe3, hbe2, hbe1]
  have hgk : GlobalsKept ["bal_accounts", "bal_idx_accts", "bal_idx_stor", "bal_index", "bal_key_buf", "heap_ptr"] s post := by
    intro k hk
    simp only [List.map, List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    obtain ⟨hne_ba, hne_bia, hne_bis, hne_bi, hne_bkb, hne_hp⟩ := hk
    exact (hg1_other k hne_hp hne_ba).trans
      ((hg2_other k hne_hp hne_bia).trans
      ((hg3_other k hne_hp hne_bis).trans
      ((hg4_other k hne_hp hne_bkb).trans
      (hg5_other k hne_bi))))
  -- Compose `FrameOutside` across `s -> s1 -> s2 -> s3 -> post`:
  have hfr_02 := frameOutside_seq_heap_sp0 hhp_01 hhp_12 hfr1 (by rw [hsp1] at hfr2; exact hfr2)
  have hfr_03 := frameOutside_seq_heap_sp0 (le_trans hhp_01 hhp_12) hhp_23 hfr_02 (by rw [hsp2, hsp1] at hfr3; exact hfr3)
  have hfr_05 : FrameOutside s post
      ([(globN s "scratch_ptr", 0)] ++ [(globN s "scratch_ptr", 0)] ++ [(globN s "scratch_ptr", 0)])
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
    intro a hk0 hnhf
    rw [hs5_m, hs4_m]
    exact hfr_03 a hk0 (fun ⟨c1, c2⟩ => hnhf ⟨c1, by dsimp only at c2 ⊢; omega⟩)
  have hk_sp0 : ∀ j ∈ ([(globN s "scratch_ptr", 0)] ++ [(globN s "scratch_ptr", 0)] ++ [(globN s "scratch_ptr", 0)]),
      j = (globN s "scratch_ptr", 0) := by
    intro j hj; simp at hj; exact hj
  have hfr_world_nil : FrameOutside s post (([] : List Ivl) ++ [freeGap s]) (heapFree s) :=
    frameOutside_sp0_to_world hAR0.2 hAR5.2 hhp_05 hk_sp0 hfr_05
  have hRK : RecordsKept (fun _ => []) stdKeep s post :=
    InitECandidate.Solver.Wave8Contracts.M08.recordsKept_of_free_writes
      (R := fun _ => []) hWOK hfr_world_nil
  refine ⟨hAR5, hhp_05, hgk, hRK, fun S Nd hWT _ => ?_⟩
  have hsp8_s : globN s "scratch_ptr" % 8 = 0 := hAR0.2.2.2.2.2.2.2.2.1
  -- Unhit on any `Allocated s i`:
  have hunhit_alloc : ∀ i : Ivl, Allocated s i → M08IvlUnhit s post i := fun i hal =>
    ivlUnhit_of_allocated_heap_sp0 hAR0.2 hAR5.2 hal
      (fun j hj => ⟨globN s "scratch_ptr", hk_sp0 j hj, hsp8_s⟩) hfr_05
  have hm0 := mem0_8_16_eq_of_heap_sp_frame hAR0.2
    (fun j hj => by rw [hk_sp0 j hj]; dsimp only; have := hAR0.2.2.2.1; have := hAR0.2.2.2.2.1; rw [M13.sourceBase_val]; rw [M13.scratchStart_val] at *; omega)
    hfr_05
  -- Transfer `t1`, `t2`, `t3` to `post`:
  have hpost_ba : globN post "bal_accounts" = t1.toNat := by
    have h1 : s1.globals.lookup (ofString "bal_accounts") = post.globals.lookup (ofString "bal_accounts") :=
      (hg2_other _ (by decide) (by decide)).trans
        ((hg3_other _ (by decide) (by decide)).trans
        ((hg4_other _ (by decide) (by decide)).trans (hg5_other _ (by decide))))
    rw [globN, ← h1, hs1_ba]
  have hpost_bia : globN post "bal_idx_accts" = t2.toNat := by
    have h1 : s2.globals.lookup (ofString "bal_idx_accts") = post.globals.lookup (ofString "bal_idx_accts") :=
      (hg3_other _ (by decide) (by decide)).trans
        ((hg4_other _ (by decide) (by decide)).trans (hg5_other _ (by decide)))
    rw [globN, ← h1, hs2_bia]
  have hpost_bis : globN post "bal_idx_stor" = t3.toNat := by
    have h1 : s3.globals.lookup (ofString "bal_idx_stor") = post.globals.lookup (ofString "bal_idx_stor") :=
      (hg4_other _ (by decide) (by decide)).trans (hg5_other _ (by decide))
    rw [globN, ← h1, hs3_bis]
  have hpost_bkb : globN post "bal_key_buf" = pk.toNat := by
    have h1 : s4.globals.lookup (ofString "bal_key_buf") = post.globals.lookup (ofString "bal_key_buf") :=
      hg5_other _ (by decide)
    rw [globN, ← h1, hs4_bkb]
  -- Transfer `t1` from `s1` to `post`:
  have hfr_15 : FrameOutside s1 post ([(globN s "scratch_ptr", 0)] ++ [(globN s "scratch_ptr", 0)])
      (globN s1 "heap_ptr", globN post "heap_ptr" - globN s1 "heap_ptr") := by
    have hfr_13 := frameOutside_seq_heap_sp0 hhp_12 hhp_23
      (by rw [hsp1] at hfr2; exact hfr2) (by rw [hsp2, hsp1] at hfr3; exact hfr3)
    intro a hk0 hnhf
    rw [hs5_m, hs4_m]
    exact hfr_13 a hk0 (fun ⟨c1, c2⟩ => hnhf ⟨c1, by dsimp only at c2 ⊢; omega⟩)
  have hu_t1 : ∀ i ∈ htabFootprint s1 t1.toNat, M08IvlUnhit s1 post i := fun i hi =>
    ivlUnhit_of_allocated_heap_sp0 hAR1.2 hAR5.2 (hfp1 i hi).1
      (fun j hj => ⟨globN s "scratch_ptr", by simp at hj; exact hj, hsp8_s⟩) hfr_15
  obtain ⟨hwf1_p, hfp1_eq, hhdr1_eq⟩ := htabWF_transfer_unhit hAR1 hAR5 hwf1 hu_t1
    (fun i hi => AllocatorGrows.allocated ⟨by omega, by rw [hsp_post, hsp1]⟩ (hfp1 i hi).1)
  -- Transfer `t2` from `s2` to `post`:
  have hfr_25 : FrameOutside s2 post [(globN s "scratch_ptr", 0)]
      (globN s2 "heap_ptr", globN post "heap_ptr" - globN s2 "heap_ptr") := by
    intro a hk0 hnhf
    rw [hs5_m, hs4_m]
    have hfr3' : FrameOutside s2 s3 [(globN s "scratch_ptr", 0)] (globN s2 "heap_ptr", globN s3 "heap_ptr" - globN s2 "heap_ptr") := by
      rw [hsp2, hsp1] at hfr3; exact hfr3
    exact hfr3' a hk0 (fun ⟨c1, c2⟩ => hnhf ⟨c1, by dsimp only at c2 ⊢; omega⟩)
  have hu_t2 : ∀ i ∈ htabFootprint s2 t2.toNat, M08IvlUnhit s2 post i := fun i hi =>
    ivlUnhit_of_allocated_heap_sp0 hAR2.2 hAR5.2 (hfp2 i hi).1
      (fun j hj => ⟨globN s "scratch_ptr", List.mem_singleton.1 hj, hsp8_s⟩) hfr_25
  obtain ⟨hwf2_p, hfp2_eq, hhdr2_eq⟩ := htabWF_transfer_unhit hAR2 hAR5 hwf2 hu_t2
    (fun i hi => AllocatorGrows.allocated ⟨by omega, by rw [hsp_post, hsp2, hsp1]⟩ (hfp2 i hi).1)
  -- Transfer `t3` from `s3` to `post` (`post.memory = s3.memory`!):
  have hu_t3 : ∀ i ∈ htabFootprint s3 t3.toNat, M08IvlUnhit s3 post i :=
    fun _ _ _ _ _ _ => by rw [hs5_m, hs4_m]
  obtain ⟨hwf3_p, hfp3_eq, hhdr3_eq⟩ := htabWF_transfer_unhit hAR3 hAR5 hwf3 hu_t3
    (fun i hi => AllocatorGrows.allocated ⟨by omega, by rw [hsp_post, hsp3, hsp2, hsp1]⟩ (hfp3 i hi).1)
  -- `balRecords post = []` and `balObjects post = []` because `hdr post t1 3 = 0`!
  have hcnt1_p : hdr post t1.toNat 3 = 0 := (hhdr1_eq 3 (by omega)).trans hcnt1
  have hbalRec_p : balRecords post = [] := by
    have heq : balRecords post = if globN post "bal_accounts" = 0 then []
        else (List.range (hdr post (globN post "bal_accounts") 3)).map
          (fun i => nodeF post (hdr post (globN post "bal_accounts") 5)
            (memW post (hdr post (globN post "bal_accounts") 6 + 8 * i)) 8) := rfl
    rw [heq, hpost_ba, hcnt1_p]
    split_ifs <;> rfl
  have hbalObj_p : balObjects post = [] := by
    unfold balObjects; rw [hbalRec_p]; rfl
  -- Globals kept for world records / buffers other than `bal_key_buf`:
  have hg_kept_nonbal : ∀ name : String,
      ofString name ∉ (["bal_accounts", "bal_idx_accts", "bal_idx_stor", "bal_index", "bal_key_buf", "heap_ptr"] : List String).map ofString →
      globN post name = globN s name :=
    fun name hnin => globN_eq_of_lookup (hgk (ofString name) hnin)
  have hws_g : globN post "ws" = globN s "ws" := hg_kept_nonbal "ws" (by decide)
  have hbs_g : globN post "bs" = globN s "bs" := hg_kept_nonbal "bs" (by decide)
  have hts_g : globN post "ts" = globN s "ts" := hg_kept_nonbal "ts" (by decide)
  have hbo_g : globN post "bo" = globN s "bo" := hg_kept_nonbal "bo" (by decide)
  have hj_g : globN post "journal" = globN s "journal" := hg_kept_nonbal "journal" (by decide)
  have hjc_g : globN post "journal_cap" = globN s "journal_cap" := hg_kept_nonbal "journal_cap" (by decide)
  have hjn_g : globN post "journal_n" = globN s "journal_n" := hg_kept_nonbal "journal_n" (by decide)
  have hgb_kept : ∀ gn ∈ globalBuffers, gn.1 ≠ "bal_key_buf" → globN post gn.1 = globN s gn.1 := by
    intro ⟨gn, sz⟩ hgn hne
    apply hg_kept_nonbal gn
    simp only [globalBuffers, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgn
    repeat' rcases hgn with ⟨rfl, _⟩ | hgn
    all_goals first | exact absurd rfl hne | decide
  obtain ⟨hT_s, hJ_s, hF_s, hTr_s⟩ := hWT
  have hu_rec : ∀ g sz, (g, sz) ∈ M13.typedRecords → globN s g ≠ 0 → M08IvlUnhit s post (globN s g, sz) := by
    intro g sz hr hnz
    have hmf := InitECandidate.Solver.Wave8Contracts.M08.typedRecord_mem_fixedObjects s hr
    simp only [hnz, ↓reduceIte] at hmf
    rcases hF_s.1 _ hmf with h0 | ⟨hal, _⟩
    · dsimp at h0; simp only [M13.typedRecords, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hr
      rcases hr with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
    · exact hunhit_alloc _ hal
  have hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → M08IvlUnhit s post i := by
    intro i hi h24
    rcases hF_s.1 i (M13.blockOut_in_fixedObjects hi) with h0 | ⟨hal, _⟩
    · omega
    · exact hunhit_alloc i hal
  have hbo_words : globN s "bo" ≠ 0 → ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := fun hnz k hk => by
    have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    simpa [hbo_g] using InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
      hAR0.2 hF_s "bo" 88 (by decide) hbo_g hnz (hu_rec "bo" 88 (by decide) hnz) hk_in.1 hk_in.2
  have hbo_part := InitECandidate.Solver.Wave8Contracts.M08.blockOutObjects_eq_of_bo_unhit
    hAR0.2 hF_s hbo_g hT_s.2.2.2.2.2.2.2.2.2.2.1
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
  -- `FixedTyped post`:
  have hpk_nz : pk.toNat ≠ 0 := by
    have := hAR3.2.1; rw [M13.sourceBase_val] at this; omega
  have hqk_64 : qk.toNat = pk.toNat + 64 := by
    have h64 : (64 : BitVec 64).toNat = 64 := rfl
    rw [h64] at hqk_eq; omega
  have hbkb_in : Inside (globN post "bal_key_buf", 64) (globN s "heap_ptr") (globN post "heap_ptr") := by
    rw [hpost_bkb, hs5_hp, hs4_hp]
    exact ⟨by dsimp; omega, by dsimp; omega⟩
  obtain ⟨hF_post, hfix_from⟩ := fixedTyped_rebind_one_fresh hAR0 hAR5 hag hF_s
    "bal_key_buf" 64 (by decide) (by rw [hpost_bkb]; exact hpk_nz) (by rw [hpost_bkb]; exact hpk8)
    (by omega) hbkb_in hgb_kept hj_g hjc_g hbo_part.1
    (fun x hx => by rw [hbalObj_p] at hx; cases hx)
    (by rw [hbalObj_p]; exact List.Pairwise.nil)
  -- Disjointness of `t1, t2, t3` from each other and from `fixedObjects post`:
  have ht12_ne : t1.toNat ≠ t2.toNat := by omega
  have ht13_ne : t1.toNat ≠ t3.toNat := by omega
  have ht23_ne : t2.toNat ≠ t3.toNat := by omega
  have hT_nd : [t1.toNat, t2.toNat, t3.toNat].Nodup := by
    simp [ht12_ne, ht13_ne, ht23_ne]
  have hfix_post_in : ∀ j ∈ fixedObjects post, j ∈ fixedObjects s ∨ j = (pk.toNat, 64) := by
    intro j hj
    unfold fixedObjects at hj
    rcases List.mem_append.1 hj with hj123 | hj_bal
    · rcases List.mem_append.1 hj123 with hj12 | hj_bo
      · rcases List.mem_append.1 hj12 with hj_gb | hj_jr
        · obtain ⟨gn, hgn, rfl⟩ := List.mem_map.1 hj_gb
          by_cases hn : gn.1 = "bal_key_buf"
          · have hsz : gn.2 = 64 := by
              simp only [globalBuffers, List.mem_cons, List.not_mem_nil, or_false] at hgn
              repeat' rcases hgn with rfl | hgn
              all_goals first | rfl | contradiction
            right; rw [hn, hsz, hpost_bkb, if_neg hpk_nz]
          · left; rw [hgb_kept gn hgn hn]
            unfold fixedObjects
            apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
            exact List.mem_map.2 ⟨gn, hgn, rfl⟩
        · left; simp only [List.mem_singleton] at hj_jr; subst hj_jr
          rw [hjc_g, hj_g]
          unfold fixedObjects
          apply List.mem_append_left; apply List.mem_append_left; exact List.mem_append_right _ (List.mem_singleton.2 rfl)
      · left; rw [hbo_part.1] at hj_bo; exact M13.blockOut_in_fixedObjects hj_bo
    · rw [hbalObj_p] at hj_bal; cases hj_bal
  have hfp_disj_fix : ∀ (t : Nat) (lo hi : Nat),
      globN s "heap_ptr" ≤ lo → hi ≤ pk.toNat →
      (∀ i ∈ htabFootprint post t, Allocated post i ∧ Inside i lo hi) →
      ∀ i ∈ htabFootprint post t, Allocated post i ∧
        Inside i (globN s "heap_ptr") (globN post "heap_ptr") ∧
        (∀ j ∈ fixedObjects post, Disj i j) := by
    intro t lo hi hlo hhi hfp i hi_mem
    obtain ⟨hal_i, hin_i⟩ := hfp i hi_mem
    have hin_full : Inside i (globN s "heap_ptr") (globN post "heap_ptr") :=
      ⟨le_trans hlo hin_i.1, le_trans hin_i.2 (by rw [hs5_hp, hs4_hp]; omega)⟩
    refine ⟨hal_i, hin_full, fun j hj => ?_⟩
    rcases hfix_post_in j hj with hj_s | rfl
    · rcases hF_s.1 j hj_s with hj0 | ⟨hal_j, _⟩
      · exact Or.inr (Or.inl hj0)
      · exact InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap hAR0.2 hAR5.2 hal_j hin_full
    · exact Or.inr (Or.inr (Or.inl (le_trans hin_i.2 hhi)))
  have hT_wf : ∀ t ∈ [t1.toNat, t2.toNat, t3.toNat], HtabWF post t ∧
      ∀ i ∈ htabFootprint post t, Allocated post i ∧
        Inside i (globN s "heap_ptr") (globN post "heap_ptr") ∧
        (∀ j ∈ fixedObjects post, Disj i j) := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact ⟨hwf1_p, hfp_disj_fix t1.toNat (globN s "heap_ptr") (globN s1 "heap_ptr") le_rfl (by omega)
        (fun i hi => by rw [hfp1_eq] at hi; exact ⟨AllocatorGrows.allocated ⟨by omega, by rw [hsp_post, hsp1]⟩ (hfp1 i hi).1, (hfp1 i hi).2⟩)⟩
    · exact ⟨hwf2_p, hfp_disj_fix t2.toNat (globN s1 "heap_ptr") (globN s2 "heap_ptr") hhp_01 (by omega)
        (fun i hi => by rw [hfp2_eq] at hi; exact ⟨AllocatorGrows.allocated ⟨by omega, by rw [hsp_post, hsp2, hsp1]⟩ (hfp2 i hi).1, (hfp2 i hi).2⟩)⟩
    · exact ⟨hwf3_p, hfp_disj_fix t3.toNat (globN s2 "heap_ptr") (globN s3 "heap_ptr") (le_trans hhp_01 hhp_12) (by omega)
        (fun i hi => by rw [hfp3_eq] at hi; exact ⟨AllocatorGrows.allocated ⟨by omega, by rw [hsp_post, hsp3, hsp2, hsp1]⟩ (hfp3 i hi).1, (hfp3 i hi).2⟩)⟩
  have hT_pw : ∀ t ∈ [t1.toNat, t2.toNat, t3.toNat], ∀ u ∈ [t1.toNat, t2.toNat, t3.toNat], t ≠ u →
      ∀ i ∈ htabFootprint post t, ∀ j ∈ htabFootprint post u, Disj i j := by
    intro t ht u hu hne i hi j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht hu
    rcases ht with rfl | rfl | rfl <;> rcases hu with rfl | rfl | rfl
    · exact absurd rfl hne
    · rw [hfp1_eq] at hi; rw [hfp2_eq] at hj
      exact disj_fresh_sub (hfp1 i hi).2 (hfp2 j hj).2 le_rfl
    · rw [hfp1_eq] at hi; rw [hfp3_eq] at hj
      exact disj_fresh_sub (hfp1 i hi).2 (hfp3 j hj).2 hhp_12
    · rw [hfp2_eq] at hi; rw [hfp1_eq] at hj
      exact disj_flip (disj_fresh_sub (hfp1 j hj).2 (hfp2 i hi).2 le_rfl)
    · exact absurd rfl hne
    · rw [hfp2_eq] at hi; rw [hfp3_eq] at hj
      exact disj_fresh_sub (hfp2 i hi).2 (hfp3 j hj).2 le_rfl
    · rw [hfp3_eq] at hi; rw [hfp1_eq] at hj
      exact disj_flip (disj_fresh_sub (hfp1 j hj).2 (hfp3 i hi).2 hhp_12)
    · rw [hfp3_eq] at hi; rw [hfp2_eq] at hj
      exact disj_flip (disj_fresh_sub (hfp2 j hj).2 (hfp3 i hi).2 le_rfl)
    · exact absurd rfl hne
  -- Journal & `ts` & `RolesOK` for `bal_init`:
  let gfix := s.globals.update (ofString "heap_ptr", .val (.word qk))
  let post_j : PanSemStateFiniteExact 64 F := { post with globals := gfix }
  have hpj_hp : globN post_j "heap_ptr" = globN post "heap_ptr" := by
    rw [hs5_hp, hs4_hp]
    simp [post_j, gfix, globN, HolFiniteMapExact.lookup_update, FUPDATE]
  have hpj_sp : globN post_j "scratch_ptr" = globN s "scratch_ptr" := by
    simp [post_j, gfix, globN, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
  have hwgs_pj : InitECandidate.Solver.Wave8Contracts.M08.WorldGlobalsSame s post_j := by
    refine ⟨fun ⟨gn, sz⟩ hgn => ?_, fun g hg => ?_, ?_, ?_, ?_⟩
    · have hne : ofString "heap_ptr" ≠ ofString gn := by
        simp only [globalBuffers, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgn
        repeat' rcases hgn with ⟨rfl, _⟩ | hgn
        all_goals decide
      simp [post_j, gfix, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne]
    · have hne : ofString "heap_ptr" ≠ ofString g := by
        simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl <;> decide
      simp [post_j, gfix, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne]
    · simp [post_j, gfix, globN, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "journal" by decide]
    · simp [post_j, gfix, globN, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "journal_cap" by decide]
    · simp [post_j, gfix, globN, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "journal_n" by decide]
  have hu_jr_pj : globN s "journal_cap" ≠ 0 → M08IvlUnhit s post_j (globN s "journal", 32 * globN s "journal_cap") := by
    intro hcnz
    rcases hJ_s.2.2.1 with h0 | ⟨hal, _⟩
    · exact absurd h0 hcnz
    · exact hunhit_alloc _ hal
  have hjr_pj := InitECandidate.Solver.Wave8Contracts.M08.journalRoleSlots_eq_of_unhit
    (post := post_j)
    hAR0.1 (guestInv_congr (s := post) rfl rfl rfl rfl hAR5.1) hAR0.2
    ⟨by rw [hpj_hp]; exact hhp_05, by rw [hpj_sp]⟩
    (S' := S ++ [t1.toNat, t2.toNat, t3.toNat]) (fun x hx => List.mem_append_left _ hx)
    hJ_s hF_s hwgs_pj
    (fun hnz => by change M08IvlUnhit s post _; exact hu_rec "ts" 72 (by decide) hnz) hu_jr_pj
  have hjr_eq : journalRoleSlots post = journalRoleSlots s := by
    have heq_jrs : journalRoleSlots post = journalRoleSlots post_j := by
      have hpj_ts : globN post_j "ts" = globN s "ts" := hwgs_pj.1 ("ts", 72) (by decide)
      have hpj_j : globN post_j "journal" = globN s "journal" := hwgs_pj.2.2.1
      have hpj_jn : globN post_j "journal_n" = globN s "journal_n" := hwgs_pj.2.2.2.2
      have hm_eq : ∀ off, memW post_j off = memW post off := fun _ => rfl
      simp only [journalRoleSlots, journalRole, hjn_g, hj_g, hts_g, hpj_jn, hpj_j, hpj_ts, hm_eq]
    exact heq_jrs.trans hjr_pj.1
  have hJ_post : JournalTyped post (S ++ [t1.toNat, t2.toNat, t3.toNat]) := by
    have hpj_j : globN post_j "journal" = globN s "journal" := hwgs_pj.2.2.1
    have hpj_jc : globN post_j "journal_cap" = globN s "journal_cap" := hwgs_pj.2.2.2.1
    have hpj_jn : globN post_j "journal_n" = globN s "journal_n" := hwgs_pj.2.2.2.2
    obtain ⟨c1, c2, c3, c4⟩ := hjr_pj.2
    rw [hpj_jn, hpj_jc] at c1; rw [hpj_jc] at c2; rw [hpj_jc, hpj_j] at c3; rw [hpj_jn, hpj_j] at c4
    refine ⟨by rw [hjn_g, hjc_g]; exact c1, by rw [hjc_g]; exact c2, ?_, ?_⟩
    · rw [hjc_g, hj_g]
      rcases c3 with h0 | ⟨hal_pj, hw_pj⟩
      · exact Or.inl h0
      · exact Or.inr ⟨by simpa [Allocated, hpj_hp, hpj_sp, hsp_post] using hal_pj, hw_pj⟩
    · rw [hjn_g, hj_g]; exact c4
  have hu_tab_s : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, M08IvlUnhit s post i :=
    fun t ht i hi => hunhit_alloc i (((hT_s.2.1 t ht).2 i hi).1)
  have hu_bal_s : ∀ i ∈ balObjects s, i.2 ≠ 0 → M08IvlUnhit s post i := by
    intro i hi hnz
    rcases hF_s.1 i (M13.bal_in_fixedObjects hi) with h0 | ⟨hal, _⟩
    · exact absurd h0 hnz
    · exact hunhit_alloc i hal
  have hwrs_pj : worldRoleSlots post_j = worldRoleSlots s :=
    InitECandidate.Solver.Wave8Contracts.M08.worldRoleSlots_eq_of_unhit (post := post_j)
      hAR0.2 hT_s hF_s hwgs_pj
      (fun t ht i hi => hu_tab_s t ht i hi)
      (fun hnz => hu_rec "ws" 40 (by decide) hnz)
      (fun hnz => hu_rec "bs" 80 (by decide) hnz)
      (fun hnz => hu_rec "ts" 72 (by decide) hnz)
      (fun i hi hnz => hu_bal_s i hi hnz)
      hm0
  have ht1_nz : t1.toNat ≠ 0 := htab_nonzero_of_wf hwf1_p
  have ht2_nz : t2.toNat ≠ 0 := htab_nonzero_of_wf hwf2_p
  have ht3_nz : t3.toNat ≠ 0 := htab_nonzero_of_wf hwf3_p
  have hroles_post : (∀ t ∈ S, hdr post t 0 = hdr s t 0) →
      (∀ t ∈ [t1.toNat, t2.toNat, t3.toNat], t ∉ S) →
      RolesOK post (S ++ [t1.toNat, t2.toNat, t3.toNat]) (worldRoleSlots post) (journalRoleSlots post) := by
    intro hhdr0_S hT_disj_S
    rw [hjr_eq]
    refine rolesOK_adjoin_fresh_slots hT_s.2.2.2.2.2.2.2.2.2.2.2 hhdr0_S ?_ hT_disj_S
    let pre_p := (recRoles post "ws" [(16, "ws+16"), (32, "ws+32")] ++
      recRoles post "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"), (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] ++
      recRoles post "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"), (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")]).filter (fun a => a.1 != 0)
    let add_p := [(t1.toNat, "bal_accounts"), (t2.toNat, "bal_idx_accts"), (t3.toNat, "bal_idx_stor")]
    let suf_p := (nestRoles post "bs" "bs.inner" ++ nestRoles post "ts" "ts.inner").filter (fun a => a.1 != 0)
    have hpre_eq : pre_p = (recRoles post_j "ws" [(16, "ws+16"), (32, "ws+32")] ++
        recRoles post_j "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"), (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] ++
        recRoles post_j "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"), (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")]).filter (fun a => a.1 != 0) := by
      have e1 : globN post_j "ws" = globN post "ws" := (hwgs_pj.1 ("ws", 40) (by decide)).trans hws_g.symm
      have e2 : globN post_j "bs" = globN post "bs" := (hwgs_pj.1 ("bs", 80) (by decide)).trans hbs_g.symm
      have e3 : globN post_j "ts" = globN post "ts" := (hwgs_pj.1 ("ts", 72) (by decide)).trans hts_g.symm
      have hm_eq : ∀ off, memW post_j off = memW post off := fun _ => rfl
      simp only [pre_p, recRoles, e1, e2, e3, hm_eq]
    have hsuf_eq : suf_p = (nestRoles post_j "bs" "bs.inner" ++ nestRoles post_j "ts" "ts.inner").filter (fun a => a.1 != 0) := by
      have e2 : globN post_j "bs" = globN post "bs" := (hwgs_pj.1 ("bs", 80) (by decide)).trans hbs_g.symm
      have e3 : globN post_j "ts" = globN post "ts" := (hwgs_pj.1 ("ts", 72) (by decide)).trans hts_g.symm
      have hm_eq : ∀ off, memW post_j off = memW post off := fun _ => rfl
      have htv_eq : ∀ t, htabValues post_j t = htabValues post t := fun _ => rfl
      simp only [suf_p, nestRoles, e2, e3, hm_eq, htv_eq]
    have hsub_pj : List.Sublist (pre_p ++ suf_p) (worldRoleSlots post_j) := by
      have hgen : ∀ (a b c d : List (Nat × String)),
          List.Sublist (a ++ c) (a ++ b ++ c ++ d) := by
        intro a b c d
        rw [List.append_assoc a b c, List.append_assoc a (b ++ c) d, List.append_assoc b c d]
        exact List.Sublist.append (List.Sublist.refl a)
          ((List.sublist_append_left c d).trans (List.sublist_append_right b (c ++ d)))
      unfold worldRoleSlots
      rw [hpre_eq, hsuf_eq]
      simp only [List.filter_append]
      rw [← List.append_assoc _ (List.filter _ (nestRoles post_j "bs" "bs.inner"))
            (List.filter _ (nestRoles post_j "ts" "ts.inner"))]
      have h1 := hgen
        (List.filter (fun a => a.1 != 0) (recRoles post_j "ws" [(16, "ws+16"), (32, "ws+32")]) ++
          List.filter (fun a => a.1 != 0) (recRoles post_j "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"), (40, "bs+40"), (48, "bs+48"), (72, "bs+72")]) ++
          List.filter (fun a => a.1 != 0) (recRoles post_j "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"), (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")]))
        (List.filter (fun a => a.1 != 0) [(globN post_j "bal_accounts", "bal_accounts"), (globN post_j "bal_idx_accts", "bal_idx_accts"), (globN post_j "bal_idx_stor", "bal_idx_stor")])
        (List.filter (fun a => a.1 != 0) (nestRoles post_j "bs" "bs.inner") ++
          List.filter (fun a => a.1 != 0) (nestRoles post_j "ts" "ts.inner"))
        (List.filter (fun a => a.1 != 0) ((balRecords post_j).flatMap fun ad => [(memW post_j ad, "bal.stor"), (memW post_j (ad + 8), "bal.reads")]))
      simpa only [List.append_assoc] using h1
    refine ⟨pre_p, add_p, suf_p, ?_, ?_, ?_, ?_, ?_⟩
    · unfold worldRoleSlots
      rw [hbalRec_p, hpost_ba, hpost_bia, hpost_bis]
      simp only [List.flatMap_nil, List.append_nil, List.filter_append]
      have hadd_f : ([(t1.toNat, "bal_accounts"), (t2.toNat, "bal_idx_accts"), (t3.toNat, "bal_idx_stor")] : List (Nat × String)).filter (fun a => a.1 != 0) = add_p := by
        simp [add_p, ht1_nz, ht2_nz, ht3_nz]
      rw [hadd_f]
      simp [pre_p, suf_p, List.append_assoc]
    · intro a ha
      rw [← hwrs_pj]
      exact hsub_pj.subset ha
    · have hpw_wrs : (worldRoleSlots post_j).Pairwise (fun a b => a.1 = b.1 → a.2 = b.2 ∧ a.2 ∈ sharedRoles) := by
        rw [hwrs_pj]; exact hT_s.2.2.2.2.2.2.2.2.2.2.2.2.1
      exact hpw_wrs.sublist hsub_pj
    · intro a ha
      simp only [add_p, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact ⟨by simp, (hhdr1_eq 0 (by omega)).trans (hhdr1.trans (show (20 : BitVec 64).toNat = roleKeyLen "bal_accounts" by decide))⟩
      · exact ⟨by simp, (hhdr2_eq 0 (by omega)).trans (hhdr2.trans (show (28 : BitVec 64).toNat = roleKeyLen "bal_idx_accts" by decide))⟩
      · exact ⟨by simp, (hhdr3_eq 0 (by omega)).trans (hhdr3.trans (show (60 : BitVec 64).toNat = roleKeyLen "bal_idx_stor" by decide))⟩
    · simp [add_p, ht12_ne, ht13_ne, ht23_ne]
  have hts_post : ∀ k ∈ tsTableSlots, globN post "ts" ≠ 0 →
      RootIn (S ++ [t1.toNat, t2.toNat, t3.toNat]) (memW post (globN post "ts" + k)) := by
    intro k hk hnz
    rw [hts_g] at hnz
    have htk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
      simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    rw [InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
      hAR0.2 hF_s "ts" 72 (by decide) hts_g hnz (hu_rec "ts" 72 (by decide) hnz) htk.1 htk.2]
    rcases hT_s.2.2.2.2.2.1 k hk hnz with h0 | hmS
    · exact Or.inl h0
    · exact Or.inr (List.mem_append_left _ hmS)
  have hgr_post : ∀ g ∈ globalTableRoots, RootIn (S ++ [t1.toNat, t2.toNat, t3.toNat]) (globN post g) := by
    intro g hg
    simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · rw [hpost_ba]; exact Or.inr (List.mem_append_right _ (by simp))
    · rw [hpost_bia]; exact Or.inr (List.mem_append_right _ (by simp))
    · rw [hpost_bis]; exact Or.inr (List.mem_append_right _ (by simp))
  have htsN_post : globN post "ts" ≠ 0 →
      memW post (globN post "ts" + 32) ∈ S ++ [t1.toNat, t2.toNat, t3.toNat] →
      HtabValuesIn post (memW post (globN post "ts" + 32)) (S ++ [t1.toNat, t2.toNat, t3.toNat]) := by
    intro hnz hm
    rw [hts_g] at hnz
    have hw32 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
      hAR0.2 hF_s "ts" 72 (by decide) hts_g hnz (hu_rec "ts" 72 (by decide) hnz) (k := 32) (by omega) (by omega)
    rw [hw32] at hm ⊢
    rcases List.mem_append.1 hm with hmS | hmN
    · exact InitECandidate.Solver.Wave8Contracts.M08.htabValuesIn_congr_unhit
        (hT_s.2.1 _ hmS).1 (hu_tab_s _ hmS) (fun u hu => List.mem_append_left _ hu)
        (hT_s.2.2.2.2.2.2.2.2.1 hnz hmS)
    · rcases hT_s.2.2.2.2.2.1 32 (by simp [tsTableSlots]) hnz with h0 | hmS
      · exfalso
        rw [h0] at hmN
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmN
        rcases hmN with h | h | h
        · exact ht1_nz h.symm
        · exact ht2_nz h.symm
        · exact ht3_nz h.symm
      · exfalso
        let tbl := memW s (globN s "ts" + 32)
        have ht_in := ((hT_wf tbl hmN).2 (tbl, 88) (by simp [htabFootprint])).2.1
        have hal_s := ((hT_s.2.1 tbl hmS).2 (tbl, 88) (by simp [htabFootprint])).1
        have hd := InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap hAR0.2 hAR5.2 hal_s ht_in
        rcases hd with h | h | h | h <;> dsimp at h <;> omega
  have hu_nd_rec : ∀ n ∈ Nd, M08IvlUnhit s post (nodeIvl s n) :=
    fun n hn => hunhit_alloc _ (hTr_s.1.1 n hn).2.1
  have hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k) := by
    intro n hn h12 hlen0 k hk
    rcases (hTr_s.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_p, _, _⟩
    · exact absurd h0 hlen0
    · exact memB_eq_of_allocated_heap_sp0 hAR0.2 hAR5.2 hbe_post hal_p
        (fun j hj => ⟨globN s "scratch_ptr", hk_sp0 j hj, hsp8_s⟩)
        hfr_05 ⟨by dsimp; omega, by dsimp; omega⟩
  obtain ⟨_, hWT_post, hOG_post⟩ := tables_tries_adjoin_fresh hAR0 hAR5 hag
    ⟨hT_s, hJ_s, hF_s, hTr_s⟩ hF_post hfix_from
    hu_tab_s
    (fun hnz => hu_rec "ws" 40 (by decide) hnz)
    (fun hnz => hu_rec "bs" 80 (by decide) hnz)
    (fun hnz => hu_rec "bo" 88 (by decide) hnz)
    hu_bo_lst hu_nd_rec hu_nd_byte hm0 hws_g hbs_g hbo_g
    hT_nd hT_wf hT_pw hts_post hgr_post htsN_post
    (fun ad had => by rw [hbalRec_p] at had; cases had)
    hroles_post hJ_post
  refine ⟨S ++ [t1.toNat, t2.toNat, t3.toNat], Nd, fun t ht => List.mem_append_left _ ht,
    hWT_post, hOG_post, ?_, trivial⟩
  exact frameOutside_sp0_to_world hAR0.2 hAR5.2 hhp_05 hk_sp0 hfr_05

/-! ## 5. `wk_state_fresh_tx` -/

/-- Exact word-store stepper for `ProgHOL.seq (.store (.op .add [.var .global "ts", .const off]) valExp) cont`
when `ts = pw`, `sourceBase ≤ pw`, `pw + 72 ≤ heapLimit`, `pw % 8 = 0`, `off % 8 = 0`, `off + 8 ≤ 72`,
and `valExp` evaluates to `.val (.word vw)`. -/
theorem seq_store_ts_slot {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (pw off vw : BitVec 64) (valExp : ExpHOL 64) (cont : ProgHOL 64)
    (hAR : ArenaReady s)
    (hts_lk : s.globals.lookup (ofString "ts") = some (.val (.word pw)))
    (hpw_lo : sourceBase ≤ pw.toNat)
    (hpw_hi : pw.toNat + 72 ≤ heapLimit)
    (hpw8 : pw.toNat % 8 = 0)
    (hoff8 : off.toNat % 8 = 0)
    (hoff_hi : off.toNat + 8 ≤ 72)
    (hval_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some (.val (.word vw))) :
    let addr : BitVec 64 := pw + off
    let mid : PanSemStateFiniteExact 64 F :=
      { s with memory := fun a => if a = addr then .word vw else s.memory a }
    evaluateHOLFiniteState s
      (.seq (.store (.op .add [.var .global (ofString "ts"), .const off]) valExp) cont) =
      evaluateHOLFiniteState mid cont ∧
    ArenaReady mid ∧
    mid.globals = s.globals ∧
    mid.locals = s.locals ∧
    mid.be = s.be ∧
    addr.toNat = pw.toNat + off.toNat ∧
    memW mid (pw.toNat + off.toNat) = vw.toNat ∧
    (∀ k : Nat, k ≠ pw.toNat + off.toNat → k < 2 ^ 64 → memW mid k = memW s k) ∧
    FrameOutside s mid [] (pw.toNat, 72) := by
  dsimp only
  have h264 : heapLimit < 2 ^ 64 ∧ heapLimit ≤ heapEnd := ⟨by decide, by decide⟩
  have haddr_nat : (pw + off).toNat = pw.toNat + off.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hdom : s.memaddrs (pw + off) := by
    rw [hAR.1.memaddrs, InitECandidate.Solver.Wave8Contracts.M08.ordinaryDomain_iff, haddr_nat]
    exact ⟨by omega, by omega, by omega⟩
  have hdst_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .global (ofString "ts"), .const off]) = some (.val (.word (pw + off))) := by
    simp [evalHOLExact, evalListHOLExact, hts_lk, wordOpHOL, wordOp, valueIsWord, valueWord]
  have hst_eval : evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "ts"), .const off]) valExp) =
      (none, { s with memory := fun a => if a = pw + off then .word vw else s.memory a }) := by
    rw [evaluateHOLFiniteState_store, hdst_ev, hval_ev]
    simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom, ↓reduceIte]
  set mid : PanSemStateFiniteExact 64 F :=
    { s with memory := fun a => if a = pw + off then .word vw else s.memory a }
  have hAR_mid : ArenaReady mid := ⟨guestInv_congr (s := s) rfl rfl rfl rfl hAR.1, hAR.2⟩
  have hmw_eq : memW mid (pw.toNat + off.toNat) = vw.toNat := by
    unfold memW
    have hb_eq : BitVec.ofNat 64 (pw.toNat + off.toNat) = pw + off := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), haddr_nat]
    simp [mid, hb_eq]
  have hmw_ne : ∀ k : Nat, k ≠ pw.toNat + off.toNat → k < 2 ^ 64 → memW mid k = memW s k := by
    intro k hne hk64
    unfold memW
    have hb_ne : BitVec.ofNat 64 k ≠ pw + off := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64, haddr_nat] at this
      exact hne this
    simp [mid, hb_ne]
  have hfr : FrameOutside s mid [] (pw.toNat, 72) := by
    intro a _ hno
    have hne : a ≠ pw + off := by
      rintro rfl
      exact hno ⟨by dsimp only; omega, by dsimp only; omega⟩
    simp [mid, hne]
  exact ⟨by rw [evaluateHOLFiniteState_seq_line780, hst_eval],
    hAR_mid, rfl, rfl, rfl, haddr_nat, hmw_eq, hmw_ne, hfr⟩

/-- Combined stepper for `.seq (.call (some (some (.local, "t"), none)) "htab_new" [.const kw, .const capw])
    (.seq (.store (.op .add [.var .global "ts", .const off]) (.var .local "t")) cont)`. -/
theorem seq_htab_new_store_ts_slot {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (pw off kw capw : BitVec 64) (cont : ProgHOL 64)
    (hAR : ArenaReady s)
    (hp0_le : pw.toNat + 72 ≤ globN s "heap_ptr")
    (hpw_lo : sourceBase ≤ pw.toNat)
    (hpw8 : pw.toNat % 8 = 0)
    (hoff8 : off.toNat % 8 = 0)
    (hoff_hi : off.toNat + 8 ≤ 72)
    (hts_lk : s.globals.lookup (ofString "ts") = some (.val (.word pw)))
    (hkl : kw.toNat ∈ htabKeyLens)
    (hcl : capw.toNat ≤ htabCapMax)
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const kw, .const capw])
      (.seq (.store (.op .add [.var .global (ofString "ts"), .const off]) (.var .local (ofString "t")))
        cont))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const kw, .const capw])
      (.seq (.store (.op .add [.var .global (ofString "ts"), .const off]) (.var .local (ofString "t")))
        cont))).1) :
    ∃ (tw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      globN s "heap_ptr" ≤ tw.toNat ∧
      tw.toNat + 88 ≤ globN mid "heap_ptr" ∧
      ArenaReady mid ∧
      mid.be = s.be ∧
      globN mid "scratch_ptr" = globN s "scratch_ptr" ∧
      globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" ∧
      HtabWF mid tw.toNat ∧
      hdr mid tw.toNat 3 = 0 ∧
      hdr mid tw.toNat 0 = kw.toNat ∧
      (∀ i ∈ htabFootprint mid tw.toNat,
        Allocated mid i ∧ Inside i (globN s "heap_ptr") (globN mid "heap_ptr")) ∧
      memW mid (pw.toNat + off.toNat) = tw.toNat ∧
      (∀ off' : Nat, off' + 8 ≤ 72 → off' ≠ off.toNat →
        memW mid (pw.toNat + off') = memW s (pw.toNat + off')) ∧
      FrameOutside s mid [(globN s "scratch_ptr", 0), (pw.toNat, 72)]
        (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") ∧
      mid.locals.lookup (ofString "t") = some (.val (.word tw)) ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = mid.globals.lookup k) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      evaluateHOLFiniteState s
        (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const kw, .const capw])
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const off]) (.var .local (ofString "t")))
          cont)) = evaluateHOLFiniteState mid cont := by
  obtain ⟨tw, m1, htw_lo, htw_hi, hAR1, hbe1, hsp1, hfmp1, hwf1, hcnt1, hhdr1, hfp1, hfr1, hl1, _, hnt1, hres1, heq1⟩ :=
    seq_call_htab_new_resumes s .local (ofString "t") kw capw _ hAR hkl hcl
      (fun h => by cases h) hnt hres
  obtain ⟨hm1_t, _, hm1_gl⟩ := hl1 rfl
  have hts_m1 : m1.globals.lookup (ofString "ts") = some (.val (.word pw)) :=
    (hm1_gl (ofString "ts") (by decide)).symm.trans hts_lk
  have hpw_hi : pw.toNat + 72 ≤ heapLimit := le_trans hp0_le hAR.2.2.1
  have ht_ev : @evalHOLExact 64 F _ m1.toExact (fun a => Classical.propDecidable (m1.memaddrs a))
      (.var .local (ofString "t")) = some (.val (.word tw)) := hm1_t
  obtain ⟨heq2, hAR2, hm2_g, hm2_l, hm2_be, haddr_nat, hmw_eq, hmw_ne, hfr2⟩ :=
    seq_store_ts_slot m1 pw off tw (.var .local (ofString "t")) cont hAR1 hts_m1
      hpw_lo hpw_hi hpw8 hoff8 hoff_hi ht_ev
  set mid : PanSemStateFiniteExact 64 F :=
    { m1 with memory := fun a => if a = pw + off then .word tw else m1.memory a }
  rw [heq2] at hnt1 hres1
  have hu_t : ∀ i ∈ htabFootprint m1 tw.toNat, M08IvlUnhit m1 mid i := by
    intro i hi a _ h1 _
    have hin := (hfp1 i hi).2
    have hne : a ≠ pw + off := by
      rintro rfl
      rw [haddr_nat] at h1
      dsimp only [Inside] at hin
      omega
    simp [mid, hne]
  obtain ⟨hwf2, hfp2_eq, hhdr2_eq⟩ := htabWF_transfer_unhit hAR1 hAR2 hwf1 hu_t
    (fun i hi => (hfp1 i hi).1)
  have hfr_comb : FrameOutside s mid [(globN s "scratch_ptr", 0), (pw.toNat, 72)]
      (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") := by
    intro a hno hnhf
    have hno_pw : ¬ CellHits a.toNat (pw.toNat, 72) :=
      hno (pw.toNat, 72) (by simp)
    have hno_sp : ∀ j ∈ [(globN s "scratch_ptr", 0)], ¬ CellHits a.toNat j :=
      fun j hj => hno j (by simp only [List.mem_singleton] at hj; subst hj; simp)
    have h1 := hfr2 a (fun _ h => by cases h) hno_pw
    have h2 := hfr1 a hno_sp hnhf
    exact h1.trans h2
  refine ⟨tw, mid, htw_lo, htw_hi, hAR2, hm2_be.trans hbe1, hsp1, hfmp1,
    hwf2, (hhdr2_eq 3 (by omega)).trans hcnt1, (hhdr2_eq 0 (by omega)).trans hhdr1,
    fun i hi => by rw [hfp2_eq] at hi; exact hfp1 i hi,
    hmw_eq, ?_, hfr_comb, hm1_t, hm1_gl, hnt1, hres1, heq1.trans heq2⟩
  intro off' hoff'_hi hoff'_ne
  have h264 : heapLimit < 2 ^ 64 := by decide
  have hk64 : pw.toNat + off' < 2 ^ 64 := by omega
  rw [hmw_ne (pw.toNat + off') (by omega) hk64]
  unfold memW
  have hm_eq := hfr1 (BitVec.ofNat 64 (pw.toNat + off'))
    (fun j hj ⟨c1, c2⟩ => by
      simp only [List.mem_singleton] at hj; subst hj
      dsimp only at c1 c2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at c1 c2
      have hsep : heapLimit ≤ scratchStart := by decide
      have := hAR.2.2.2.1; have := hAR.2.2.2.2.1
      omega)
    (fun ⟨c1, c2⟩ => by
      dsimp only at c1 c2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at c1 c2
      omega)
  rw [hm_eq]

/-- Combined stepper for `.decCall "t" .one "htab_new" [.const kw, .const capw]
    (.seq (.store (.op .add [.var .global "ts", .const off]) (.var .local "t")) cont)`. -/
theorem decCall_htab_new_store_ts_slot {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (pw off kw capw : BitVec 64) (cont : ProgHOL 64)
    (hAR : ArenaReady s)
    (hp0_le : pw.toNat + 72 ≤ globN s "heap_ptr")
    (hpw_lo : sourceBase ≤ pw.toNat)
    (hpw8 : pw.toNat % 8 = 0)
    (hoff8 : off.toNat % 8 = 0)
    (hoff_hi : off.toNat + 8 ≤ 72)
    (hts_lk : s.globals.lookup (ofString "ts") = some (.val (.word pw)))
    (hkl : kw.toNat ∈ htabKeyLens)
    (hcl : capw.toNat ≤ htabCapMax)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString "t") .one (ofString "htab_new") [.const kw, .const capw]
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const off]) (.var .local (ofString "t")))
          cont))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString "t") .one (ofString "htab_new") [.const kw, .const capw]
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const off]) (.var .local (ofString "t")))
          cont))).1) :
    ∃ (tw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      globN s "heap_ptr" ≤ tw.toNat ∧
      tw.toNat + 88 ≤ globN mid "heap_ptr" ∧
      ArenaReady mid ∧
      mid.be = s.be ∧
      globN mid "scratch_ptr" = globN s "scratch_ptr" ∧
      globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" ∧
      HtabWF mid tw.toNat ∧
      hdr mid tw.toNat 3 = 0 ∧
      hdr mid tw.toNat 0 = kw.toNat ∧
      (∀ i ∈ htabFootprint mid tw.toNat,
        Allocated mid i ∧ Inside i (globN s "heap_ptr") (globN mid "heap_ptr")) ∧
      memW mid (pw.toNat + off.toNat) = tw.toNat ∧
      (∀ off' : Nat, off' + 8 ≤ 72 → off' ≠ off.toNat →
        memW mid (pw.toNat + off') = memW s (pw.toNat + off')) ∧
      FrameOutside s mid [(globN s "scratch_ptr", 0), (pw.toNat, 72)]
        (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") ∧
      mid.locals.lookup (ofString "t") = some (.val (.word tw)) ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = mid.globals.lookup k) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString "t") .one (ofString "htab_new") [.const kw, .const capw]
          (.seq (.store (.op .add [.var .global (ofString "ts"), .const off]) (.var .local (ofString "t")))
            cont))).1 = (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString "t") .one (ofString "htab_new") [.const kw, .const capw]
          (.seq (.store (.op .add [.var .global (ofString "ts"), .const off]) (.var .local (ofString "t")))
            cont))).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
            (ofString "t", s.locals.lookup (ofString "t")) } := by
  obtain ⟨tw, m1, htw_lo, htw_hi, hAR1, hbe1, hsp1, hfmp1, hwf1, hcnt1, hhdr1, hfp1, hfr1, hm1_t, _, hm1_gl, hnt1, hres1, heq1_1, heq1_2⟩ :=
    decCall_htab_new_resumes s (ofString "t") kw capw _ hAR hkl hcl hnt hres
  have hts_m1 : m1.globals.lookup (ofString "ts") = some (.val (.word pw)) :=
    (hm1_gl (ofString "ts") (by decide)).symm.trans hts_lk
  have hpw_hi : pw.toNat + 72 ≤ heapLimit := le_trans hp0_le hAR.2.2.1
  have ht_ev : @evalHOLExact 64 F _ m1.toExact (fun a => Classical.propDecidable (m1.memaddrs a))
      (.var .local (ofString "t")) = some (.val (.word tw)) := hm1_t
  obtain ⟨heq2, hAR2, hm2_g, hm2_l, hm2_be, haddr_nat, hmw_eq, hmw_ne, hfr2⟩ :=
    seq_store_ts_slot m1 pw off tw (.var .local (ofString "t")) cont hAR1 hts_m1
      hpw_lo hpw_hi hpw8 hoff8 hoff_hi ht_ev
  set mid : PanSemStateFiniteExact 64 F :=
    { m1 with memory := fun a => if a = pw + off then .word tw else m1.memory a }
  rw [heq2] at hnt1 hres1 heq1_1 heq1_2
  have hu_t : ∀ i ∈ htabFootprint m1 tw.toNat, M08IvlUnhit m1 mid i := by
    intro i hi a _ h1 _
    have hin := (hfp1 i hi).2
    have hne : a ≠ pw + off := by
      rintro rfl
      rw [haddr_nat] at h1
      dsimp only [Inside] at hin
      omega
    simp [mid, hne]
  obtain ⟨hwf2, hfp2_eq, hhdr2_eq⟩ := htabWF_transfer_unhit hAR1 hAR2 hwf1 hu_t
    (fun i hi => (hfp1 i hi).1)
  have hfr_comb : FrameOutside s mid [(globN s "scratch_ptr", 0), (pw.toNat, 72)]
      (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") := by
    intro a hno hnhf
    have hno_pw : ¬ CellHits a.toNat (pw.toNat, 72) :=
      hno (pw.toNat, 72) (by simp)
    have hno_sp : ∀ j ∈ [(globN s "scratch_ptr", 0)], ¬ CellHits a.toNat j :=
      fun j hj => hno j (by simp only [List.mem_singleton] at hj; subst hj; simp)
    have h1 := hfr2 a (fun _ h => by cases h) hno_pw
    have h2 := hfr1 a hno_sp hnhf
    exact h1.trans h2
  refine ⟨tw, mid, htw_lo, htw_hi, hAR2, hm2_be.trans hbe1, hsp1, hfmp1,
    hwf2, (hhdr2_eq 3 (by omega)).trans hcnt1, (hhdr2_eq 0 (by omega)).trans hhdr1,
    fun i hi => by rw [hfp2_eq] at hi; exact hfp1 i hi,
    hmw_eq, ?_, hfr_comb, hm1_t, hm1_gl, hnt1, hres1, heq1_1, heq1_2⟩
  intro off' hoff'_hi hoff'_ne
  have h264 : heapLimit < 2 ^ 64 := by decide
  have hk64 : pw.toNat + off' < 2 ^ 64 := by omega
  rw [hmw_ne (pw.toNat + off') (by omega) hk64]
  unfold memW
  have hm_eq := hfr1 (BitVec.ofNat 64 (pw.toNat + off'))
    (fun j hj ⟨c1, c2⟩ => by
      simp only [List.mem_singleton] at hj; subst hj
      dsimp only at c1 c2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at c1 c2
      have hsep : heapLimit ≤ scratchStart := by decide
      have := hAR.2.2.2.1; have := hAR.2.2.2.2.1
      omega)
    (fun ⟨c1, c2⟩ => by
      dsimp only at c1 c2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at c1 c2
      omega)
  rw [hm_eq]

theorem frameOutside_collapse_pw_sp {F : Type} (s a b : PanSemStateFiniteExact 64 F)
    (pw : Nat)
    (hpw_lo : globN s "heap_ptr" ≤ pw)
    (hpw_hi : pw + 72 ≤ globN a "heap_ptr")
    (hh_ab : globN a "heap_ptr" ≤ globN b "heap_ptr")
    (h1 : FrameOutside s a [(globN s "scratch_ptr", 0)]
      (globN s "heap_ptr", globN a "heap_ptr" - globN s "heap_ptr"))
    (h2 : FrameOutside a b [(globN s "scratch_ptr", 0), (pw, 72)]
      (globN a "heap_ptr", globN b "heap_ptr" - globN a "heap_ptr")) :
    FrameOutside s b [(globN s "scratch_ptr", 0)]
      (globN s "heap_ptr", globN b "heap_ptr" - globN s "heap_ptr") := by
  intro x hno_sp hnhf
  have hno_sp_x : ¬ CellHits x.toNat (globN s "scratch_ptr", 0) :=
    hno_sp _ (List.mem_singleton.2 rfl)
  have hno_pw_x : ¬ CellHits x.toNat (pw, 72) := by
    intro ⟨c1, c2⟩; dsimp only at c1 c2
    exact hnhf ⟨by dsimp only; omega, by dsimp only; omega⟩
  have hnhf_ab : ¬ CellHits x.toNat (globN a "heap_ptr", globN b "heap_ptr" - globN a "heap_ptr") := by
    intro ⟨c1, c2⟩; dsimp only at c1 c2
    exact hnhf ⟨by dsimp only; omega, by dsimp only; omega⟩
  have hnhf_sa : ¬ CellHits x.toNat (globN s "heap_ptr", globN a "heap_ptr" - globN s "heap_ptr") := by
    intro ⟨c1, c2⟩; dsimp only at c1 c2
    exact hnhf ⟨c1, by dsimp only; omega⟩
  have hm2 := h2 x (fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact hno_sp_x
    · exact hno_pw_x) hnhf_ab
  exact hm2.trans (h1 x hno_sp hnhf_sa)

/-- Zero-sorry proof of `wk_state_fresh_tx` (`ContractParts/C08.lean`). -/
theorem wk_state_fresh_tx :
    WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr", "journal_n", "ts"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
     ("ts", []),
     ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "state_fresh_tx") := by
  refine ⟨_, _, _, lookup_state_fresh_tx, ?_⟩
  intro F s hcode hWOK _ hnt hres
  have hAR0 : ArenaReady s := hWOK.1
  have hbody_eq : sourceFnBody Guest.Software.guestFn_state_fresh_tx =
      .seq (.call (some (some (.global, ofString "ts"), none)) (ofString "alloc") [.const 72])
      (.seq (.store (.op .add [.var .global (ofString "ts"), .const 0]) (.var .global (ofString "bs")))
      (.decCall (ofString "t") .one (ofString "htab_new") [.const 20, .const 64]
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const 8]) (.var .local (ofString "t")))
        (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 20, .const 64])
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const 16]) (.var .local (ofString "t")))
        (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 52, .const 64])
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const 24]) (.var .local (ofString "t")))
        (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 20, .const 16])
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const 32]) (.var .local (ofString "t")))
        (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 52, .const 16])
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const 40]) (.var .local (ofString "t")))
        (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 32, .const 16])
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const 48]) (.var .local (ofString "t")))
        (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 20, .const 16])
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const 56]) (.var .local (ofString "t")))
        (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 52, .const 16])
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const 64]) (.var .local (ofString "t")))
        (.seq (.assign .global (ofString "journal_n") (.const 0))
              (.return (.const 0)))))))))))))))))))) := rfl
  rw [hbody_eq] at hnt hres ⊢
  -- Step 0a: `ts := alloc(72)`
  obtain ⟨pw, qw, s0a, hpw_eq, hqw_eq, hs0a_hp, hpw_le_qw, hpw8, hAR0a, hs0a_m, _, hs0a_be, _,
      hsp0a, hfmp0a, hts0a, hg0a_other, hnt0a, hres0a, heq0a⟩ :=
    seq_call_alloc_global_resumes s (ofString "ts") 72 _ hAR0
      ⟨by decide, by decide, by decide⟩ hnt hres
  have hqw_72 : qw.toNat = pw.toNat + 72 := by
    have h72 : (72 : BitVec 64).toNat = 72 := rfl
    rw [h72] at hqw_eq; omega
  have hpw_lo : sourceBase ≤ pw.toNat := by rw [hpw_eq]; exact hAR0.2.1
  have hpw_hi : pw.toNat + 72 ≤ heapLimit := by
    have := hAR0a.2.2.1; omega
  -- Step 0b: `store (ts + 0) bs`
  obtain ⟨bsw, hbsw_lk⟩ := hAR0a.2.2.2.2.2.2.2.2.2 "bs" (by decide)
  have hbs_ev : @evalHOLExact 64 F _ s0a.toExact (fun a => Classical.propDecidable (s0a.memaddrs a))
      (.var .global (ofString "bs")) = some (.val (.word bsw)) := hbsw_lk
  obtain ⟨heq0b, hAR0b, hs0b_g, _, hs0b_be, _, _, _, hfr0b⟩ :=
    seq_store_ts_slot s0a pw 0 bsw (.var .global (ofString "bs")) _ hAR0a hts0a
      hpw_lo hpw_hi hpw8 (by decide) (by decide) hbs_ev
  set s0 : PanSemStateFiniteExact 64 F :=
    { s0a with memory := fun a => if a = pw + 0 then .word bsw else s0a.memory a }
  rw [heq0b] at hnt0a hres0a
  have hts0 : s0.globals.lookup (ofString "ts") = some (.val (.word pw)) := hts0a
  have hhp0 : globN s0 "heap_ptr" = pw.toNat + 72 := by
    change globN s0a "heap_ptr" = pw.toNat + 72; omega
  have hsp0 : globN s0 "scratch_ptr" = globN s "scratch_ptr" := hsp0a
  have hfr_s_s0 : FrameOutside s s0 [(globN s "scratch_ptr", 0)]
      (globN s "heap_ptr", globN s0 "heap_ptr" - globN s "heap_ptr") := by
    intro a _ hnhf
    have hm1 := hfr0b a (fun _ h => by cases h) (fun ⟨c1, c2⟩ => by
      dsimp only at c1 c2
      exact hnhf ⟨by dsimp only; omega, by dsimp only; omega⟩)
    exact hm1.trans (by rw [hs0a_m])
  -- Step 1 (`off = 8`, `decCall` `htab_new(20, 64)`):
  obtain ⟨t1, s1, ht1_lo, ht1_hi, hAR1, hbe1, hsp1, _, hwf1, hcnt1, hhdr1, hfp1,
      hmw1, hkeep1, hfr1, _, hg1, hnt1, hres1, heq1_1, heq1_2⟩ :=
    decCall_htab_new_store_ts_slot s0 pw 8 20 64 _ hAR0b (by omega) hpw_lo hpw8
      (by decide) (by decide) hts0 (by decide) (by decide) hnt0a hres0a
  have hts1 : s1.globals.lookup (ofString "ts") = some (.val (.word pw)) :=
    (hg1 (ofString "ts") (by decide)).symm.trans hts0
  have hfr_s_s1 := frameOutside_collapse_pw_sp s s0 s1 pw.toNat (by omega) (by omega) (by omega) hfr_s_s0
    (by rw [hsp0] at hfr1; exact hfr1)
  -- Step 2 (`off = 16`, `htab_new(20, 64)`):
  obtain ⟨t2, s2, ht2_lo, ht2_hi, hAR2, hbe2, hsp2, _, hwf2, hcnt2, hhdr2, hfp2,
      hmw2, hkeep2, hfr2, _, hg2, hnt2, hres2, heq2⟩ :=
    seq_htab_new_store_ts_slot s1 pw 16 20 64 _ hAR1 (by omega) hpw_lo hpw8
      (by decide) (by decide) hts1 (by decide) (by decide) hnt1 hres1
  have hts2 : s2.globals.lookup (ofString "ts") = some (.val (.word pw)) :=
    (hg2 (ofString "ts") (by decide)).symm.trans hts1
  have hfr_s_s2 := frameOutside_collapse_pw_sp s s1 s2 pw.toNat (by omega) (by omega) (by omega) hfr_s_s1
    (by rw [hsp1, hsp0] at hfr2; exact hfr2)
  -- Step 3 (`off = 24`, `htab_new(52, 64)`):
  obtain ⟨t3, s3, ht3_lo, ht3_hi, hAR3, hbe3, hsp3, _, hwf3, hcnt3, hhdr3, hfp3,
      hmw3, hkeep3, hfr3, _, hg3, hnt3, hres3, heq3⟩ :=
    seq_htab_new_store_ts_slot s2 pw 24 52 64 _ hAR2 (by omega) hpw_lo hpw8
      (by decide) (by decide) hts2 (by decide) (by decide) hnt2 hres2
  have hts3 : s3.globals.lookup (ofString "ts") = some (.val (.word pw)) :=
    (hg3 (ofString "ts") (by decide)).symm.trans hts2
  have hfr_s_s3 := frameOutside_collapse_pw_sp s s2 s3 pw.toNat (by omega) (by omega) (by omega) hfr_s_s2
    (by rw [hsp2, hsp1, hsp0] at hfr3; exact hfr3)
  -- Step 4 (`off = 32`, `htab_new(20, 16)`):
  obtain ⟨t4, s4, ht4_lo, ht4_hi, hAR4, hbe4, hsp4, _, hwf4, hcnt4, hhdr4, hfp4,
      hmw4, hkeep4, hfr4, _, hg4, hnt4, hres4, heq4⟩ :=
    seq_htab_new_store_ts_slot s3 pw 32 20 16 _ hAR3 (by omega) hpw_lo hpw8
      (by decide) (by decide) hts3 (by decide) (by decide) hnt3 hres3
  have hts4 : s4.globals.lookup (ofString "ts") = some (.val (.word pw)) :=
    (hg4 (ofString "ts") (by decide)).symm.trans hts3
  have hfr_s_s4 := frameOutside_collapse_pw_sp s s3 s4 pw.toNat (by omega) (by omega) (by omega) hfr_s_s3
    (by rw [hsp3, hsp2, hsp1, hsp0] at hfr4; exact hfr4)
  -- Step 5 (`off = 40`, `htab_new(52, 16)`):
  obtain ⟨t5, s5, ht5_lo, ht5_hi, hAR5, hbe5, hsp5, _, hwf5, hcnt5, hhdr5, hfp5,
      hmw5, hkeep5, hfr5, _, hg5, hnt5, hres5, heq5⟩ :=
    seq_htab_new_store_ts_slot s4 pw 40 52 16 _ hAR4 (by omega) hpw_lo hpw8
      (by decide) (by decide) hts4 (by decide) (by decide) hnt4 hres4
  have hts5 : s5.globals.lookup (ofString "ts") = some (.val (.word pw)) :=
    (hg5 (ofString "ts") (by decide)).symm.trans hts4
  have hfr_s_s5 := frameOutside_collapse_pw_sp s s4 s5 pw.toNat (by omega) (by omega) (by omega) hfr_s_s4
    (by rw [hsp4, hsp3, hsp2, hsp1, hsp0] at hfr5; exact hfr5)
  -- Step 6 (`off = 48`, `htab_new(32, 16)`):
  obtain ⟨t6, s6, ht6_lo, ht6_hi, hAR6, hbe6, hsp6, _, hwf6, hcnt6, hhdr6, hfp6,
      hmw6, hkeep6, hfr6, _, hg6, hnt6, hres6, heq6⟩ :=
    seq_htab_new_store_ts_slot s5 pw 48 32 16 _ hAR5 (by omega) hpw_lo hpw8
      (by decide) (by decide) hts5 (by decide) (by decide) hnt5 hres5
  have hts6 : s6.globals.lookup (ofString "ts") = some (.val (.word pw)) :=
    (hg6 (ofString "ts") (by decide)).symm.trans hts5
  have hfr_s_s6 := frameOutside_collapse_pw_sp s s5 s6 pw.toNat (by omega) (by omega) (by omega) hfr_s_s5
    (by rw [hsp5, hsp4, hsp3, hsp2, hsp1, hsp0] at hfr6; exact hfr6)
  -- Step 7 (`off = 56`, `htab_new(20, 16)`):
  obtain ⟨t7, s7, ht7_lo, ht7_hi, hAR7, hbe7, hsp7, _, hwf7, hcnt7, hhdr7, hfp7,
      hmw7, hkeep7, hfr7, _, hg7, hnt7, hres7, heq7⟩ :=
    seq_htab_new_store_ts_slot s6 pw 56 20 16 _ hAR6 (by omega) hpw_lo hpw8
      (by decide) (by decide) hts6 (by decide) (by decide) hnt6 hres6
  have hts7 : s7.globals.lookup (ofString "ts") = some (.val (.word pw)) :=
    (hg7 (ofString "ts") (by decide)).symm.trans hts6
  have hfr_s_s7 := frameOutside_collapse_pw_sp s s6 s7 pw.toNat (by omega) (by omega) (by omega) hfr_s_s6
    (by rw [hsp6, hsp5, hsp4, hsp3, hsp2, hsp1, hsp0] at hfr7; exact hfr7)
  -- Step 8 (`off = 64`, `htab_new(52, 16)`):
  obtain ⟨t8, s8, ht8_lo, ht8_hi, hAR8, hbe8, hsp8, _, hwf8, hcnt8, hhdr8, hfp8,
      hmw8, hkeep8, hfr8, _, hg8, hnt8, hres8, heq8⟩ :=
    seq_htab_new_store_ts_slot s7 pw 64 52 16 _ hAR7 (by omega) hpw_lo hpw8
      (by decide) (by decide) hts7 (by decide) (by decide) hnt7 hres7
  have hts8 : s8.globals.lookup (ofString "ts") = some (.val (.word pw)) :=
    (hg8 (ofString "ts") (by decide)).symm.trans hts7
  have hfr_s_s8 := frameOutside_collapse_pw_sp s s7 s8 pw.toNat (by omega) (by omega) (by omega) hfr_s_s7
    (by rw [hsp7, hsp6, hsp5, hsp4, hsp3, hsp2, hsp1, hsp0] at hfr8; exact hfr8)
  -- Step 9: `journal_n := 0; return 0`
  obtain ⟨heq9, hAR9, hs9_m, _, hs9_be, hs9_hp, hsp9, _, hs9_jn, hg9_other⟩ :=
    seq_assign_global_zero_return_zero s8 (ofString "journal_n") hAR8
      ⟨"journal_n", by decide, rfl⟩ ⟨by decide, by decide, by decide⟩
  set inner_post := emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "journal_n") (.val (.word 0)) s8)
  have hchain2 : evaluateHOLFiniteState s1
      (ProgHOL.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 20, .const 64])
      (.seq (.store (.op .add [.var .global (ofString "ts"), .const 16]) (.var .local (ofString "t")))
      (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 52, .const 64])
      (.seq (.store (.op .add [.var .global (ofString "ts"), .const 24]) (.var .local (ofString "t")))
      (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 20, .const 16])
      (.seq (.store (.op .add [.var .global (ofString "ts"), .const 32]) (.var .local (ofString "t")))
      (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 52, .const 16])
      (.seq (.store (.op .add [.var .global (ofString "ts"), .const 40]) (.var .local (ofString "t")))
      (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 32, .const 16])
      (.seq (.store (.op .add [.var .global (ofString "ts"), .const 48]) (.var .local (ofString "t")))
      (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 20, .const 16])
      (.seq (.store (.op .add [.var .global (ofString "ts"), .const 56]) (.var .local (ofString "t")))
      (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 52, .const 16])
      (.seq (.store (.op .add [.var .global (ofString "ts"), .const 64]) (.var .local (ofString "t")))
      (.seq (.assign .global (ofString "journal_n") (.const 0))
            (.return (.const 0))))))))))))))))) =
      (some (.returned (.val (.word 0))), inner_post) := by
    rw [heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9]
  have hchain2_1 := congrArg Prod.fst hchain2
  have hchain2_2 := congrArg Prod.snd hchain2
  dsimp only at hchain2_1 hchain2_2
  rw [heq0a, heq0b]
  have hout_eq : evaluateHOLFiniteState s0
      (.decCall (ofString "t") .one (ofString "htab_new") [.const 20, .const 64]
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const 8]) (.var .local (ofString "t")))
        (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 20, .const 64])
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const 16]) (.var .local (ofString "t")))
        (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 52, .const 64])
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const 24]) (.var .local (ofString "t")))
        (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 20, .const 16])
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const 32]) (.var .local (ofString "t")))
        (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 52, .const 16])
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const 40]) (.var .local (ofString "t")))
        (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 32, .const 16])
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const 48]) (.var .local (ofString "t")))
        (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 20, .const 16])
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const 56]) (.var .local (ofString "t")))
        (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 52, .const 16])
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const 64]) (.var .local (ofString "t")))
        (.seq (.assign .global (ofString "journal_n") (.const 0))
              (.return (.const 0))))))))))))))))))) =
      (some (.returned (.val (.word 0))),
        { inner_post with locals :=
            HolFiniteMapExact.resVarEq inner_post.locals (ofString "t", s0.locals.lookup (ofString "t")) }) :=
    Prod.ext (heq1_1.trans hchain2_1) (heq1_2.trans (by rw [hchain2_2]))
  rw [hout_eq]
  dsimp only
  apply worldStep_with_locals_right _ inner_post.clock (fun _ _ h => h)
  -- Now prove `WorldStep (fun _ => []) ["heap_ptr", "journal_n", "ts"] keep_sft NoExtra s _ inner_post`!
  have hhp_09 : globN s "heap_ptr" ≤ globN inner_post "heap_ptr" := by omega
  have hsp_post : globN inner_post "scratch_ptr" = globN s "scratch_ptr" := by
    rw [hsp9, hsp8, hsp7, hsp6, hsp5, hsp4, hsp3, hsp2, hsp1, hsp0]
  have hag : AllocatorGrows s inner_post := ⟨hhp_09, by rw [hsp_post]⟩
  have hbe_post : inner_post.be = s.be := by
    rw [hs9_be, hbe8, hbe7, hbe6, hbe5, hbe4, hbe3, hbe2, hbe1, hs0b_be, hs0a_be]
  have hgk : GlobalsKept ["heap_ptr", "journal_n", "ts"] s inner_post := by
    intro k hk
    simp only [List.map, List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    obtain ⟨hne_hp, hne_jn, hne_ts⟩ := hk
    have h0 : s.globals.lookup k = s0.globals.lookup k := hg0a_other k hne_hp hne_ts
    exact h0.trans ((hg1 k hne_hp).trans ((hg2 k hne_hp).trans ((hg3 k hne_hp).trans
      ((hg4 k hne_hp).trans ((hg5 k hne_hp).trans ((hg6 k hne_hp).trans
      ((hg7 k hne_hp).trans ((hg8 k hne_hp).trans (hg9_other k hne_jn)))))))))
  have hfr_09 : FrameOutside s inner_post [(globN s "scratch_ptr", 0)]
      (globN s "heap_ptr", globN inner_post "heap_ptr" - globN s "heap_ptr") := by
    intro a hk0 hnhf
    rw [hs9_m]
    exact hfr_s_s8 a hk0 (fun ⟨c1, c2⟩ => hnhf ⟨c1, by rw [hs9_hp]; exact c2⟩)
  have hk_sp0 : ∀ j ∈ [(globN s "scratch_ptr", 0)], j = (globN s "scratch_ptr", 0) :=
    fun _ hj => List.mem_singleton.1 hj
  have hfr_world_nil : FrameOutside s inner_post (([] : List Ivl) ++ [freeGap s]) (heapFree s) :=
    frameOutside_sp0_to_world hAR0.2 hAR9.2 hhp_09 hk_sp0 hfr_09
  have hRK_std : RecordsKept (fun _ => []) stdKeep s inner_post :=
    InitECandidate.Solver.Wave8Contracts.M08.recordsKept_of_free_writes
      (R := fun _ => []) hWOK hfr_world_nil
  have hRK : RecordsKept (fun _ => [])
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])] s inner_post := by
    intro rec hrec hgnz k hk hnoR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrec
    rcases hrec with rfl | rfl | rfl | rfl
    · exact hRK_std ("ws", [0, 8, 16, 24, 32]) (by simp [stdKeep, M13.stdKeep]) hgnz k hk hnoR
    · exact hRK_std ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]) (by simp [stdKeep, M13.stdKeep]) hgnz k hk hnoR
    · cases hk
    · exact hRK_std ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp [stdKeep, M13.stdKeep]) hgnz k hk hnoR
  refine ⟨hAR9, hhp_09, hgk, hRK, fun S Nd hWT _ => ?_⟩
  have hsp8_s : globN s "scratch_ptr" % 8 = 0 := hAR0.2.2.2.2.2.2.2.2.1
  have hunhit_alloc : ∀ i : Ivl, Allocated s i → M08IvlUnhit s inner_post i := fun i hal =>
    ivlUnhit_of_allocated_heap_sp0 hAR0.2 hAR9.2 hal
      (fun j hj => ⟨globN s "scratch_ptr", hk_sp0 j hj, hsp8_s⟩) hfr_09
  have hm0 := mem0_8_16_eq_of_heap_sp_frame hAR0.2
    (fun j hj => by rw [hk_sp0 j hj]; dsimp only; have := hAR0.2.2.2.1; have := hAR0.2.2.2.2.1; rw [M13.sourceBase_val]; rw [M13.scratchStart_val] at *; omega)
    hfr_09
  -- Globals of `inner_post`:
  have hpost_ts : globN inner_post "ts" = pw.toNat := by
    have h1 : s8.globals.lookup (ofString "ts") = inner_post.globals.lookup (ofString "ts") :=
      hg9_other _ (by decide)
    rw [globN, ← h1, hts8]
  have hpost_jn : globN inner_post "journal_n" = 0 := by
    rw [globN, hs9_jn]; rfl
  have hg_kept_nonts : ∀ name : String,
      ofString name ∉ (["heap_ptr", "journal_n", "ts"] : List String).map ofString →
      globN inner_post name = globN s name :=
    fun name hnin => globN_eq_of_lookup (hgk (ofString name) hnin)
  have hws_g : globN inner_post "ws" = globN s "ws" := hg_kept_nonts "ws" (by decide)
  have hbs_g : globN inner_post "bs" = globN s "bs" := hg_kept_nonts "bs" (by decide)
  have hbo_g : globN inner_post "bo" = globN s "bo" := hg_kept_nonts "bo" (by decide)
  have hba_g : globN inner_post "bal_accounts" = globN s "bal_accounts" := hg_kept_nonts "bal_accounts" (by decide)
  have hbia_g : globN inner_post "bal_idx_accts" = globN s "bal_idx_accts" := hg_kept_nonts "bal_idx_accts" (by decide)
  have hbis_g : globN inner_post "bal_idx_stor" = globN s "bal_idx_stor" := hg_kept_nonts "bal_idx_stor" (by decide)
  have hj_g : globN inner_post "journal" = globN s "journal" := hg_kept_nonts "journal" (by decide)
  have hjc_g : globN inner_post "journal_cap" = globN s "journal_cap" := hg_kept_nonts "journal_cap" (by decide)
  have hgb_kept : ∀ gn ∈ globalBuffers, gn.1 ≠ "ts" → globN inner_post gn.1 = globN s gn.1 := by
    intro ⟨gn, sz⟩ hgn hne
    apply hg_kept_nonts gn
    simp only [globalBuffers, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgn
    repeat' rcases hgn with ⟨rfl, _⟩ | hgn
    all_goals first | exact absurd rfl hne | decide
  -- Slots of `ts` in `inner_post` (`memW inner_post = memW s8`):
  have hmw_p8 : memW inner_post (pw.toNat + 8) = t1.toNat := by
    unfold memW; rw [hs9_m]; change memW s8 (pw.toNat + 8) = t1.toNat
    rw [hkeep8 8 (by omega) (by decide), hkeep7 8 (by omega) (by decide),
        hkeep6 8 (by omega) (by decide), hkeep5 8 (by omega) (by decide),
        hkeep4 8 (by omega) (by decide), hkeep3 8 (by omega) (by decide),
        hkeep2 8 (by omega) (by decide)]
    exact hmw1
  have hmw_p16 : memW inner_post (pw.toNat + 16) = t2.toNat := by
    unfold memW; rw [hs9_m]; change memW s8 (pw.toNat + 16) = t2.toNat
    rw [hkeep8 16 (by omega) (by decide), hkeep7 16 (by omega) (by decide),
        hkeep6 16 (by omega) (by decide), hkeep5 16 (by omega) (by decide),
        hkeep4 16 (by omega) (by decide), hkeep3 16 (by omega) (by decide)]
    exact hmw2
  have hmw_p24 : memW inner_post (pw.toNat + 24) = t3.toNat := by
    unfold memW; rw [hs9_m]; change memW s8 (pw.toNat + 24) = t3.toNat
    rw [hkeep8 24 (by omega) (by decide), hkeep7 24 (by omega) (by decide),
        hkeep6 24 (by omega) (by decide), hkeep5 24 (by omega) (by decide),
        hkeep4 24 (by omega) (by decide)]
    exact hmw3
  have hmw_p32 : memW inner_post (pw.toNat + 32) = t4.toNat := by
    unfold memW; rw [hs9_m]; change memW s8 (pw.toNat + 32) = t4.toNat
    rw [hkeep8 32 (by omega) (by decide), hkeep7 32 (by omega) (by decide),
        hkeep6 32 (by omega) (by decide), hkeep5 32 (by omega) (by decide)]
    exact hmw4
  have hmw_p40 : memW inner_post (pw.toNat + 40) = t5.toNat := by
    unfold memW; rw [hs9_m]; change memW s8 (pw.toNat + 40) = t5.toNat
    rw [hkeep8 40 (by omega) (by decide), hkeep7 40 (by omega) (by decide),
        hkeep6 40 (by omega) (by decide)]
    exact hmw5
  have hmw_p48 : memW inner_post (pw.toNat + 48) = t6.toNat := by
    unfold memW; rw [hs9_m]; change memW s8 (pw.toNat + 48) = t6.toNat
    rw [hkeep8 48 (by omega) (by decide), hkeep7 48 (by omega) (by decide)]
    exact hmw6
  have hmw_p56 : memW inner_post (pw.toNat + 56) = t7.toNat := by
    unfold memW; rw [hs9_m]; change memW s8 (pw.toNat + 56) = t7.toNat
    rw [hkeep8 56 (by omega) (by decide)]
    exact hmw7
  have hmw_p64 : memW inner_post (pw.toNat + 64) = t8.toNat := by
    unfold memW; rw [hs9_m]; exact hmw8
  -- Transfer `t1..t8` to `inner_post`:
  -- Observe: for any `si` (`i ∈ 1..8`), `FrameOutside si s8 [(sp, 0), (pw, 72)] (hp si, hp s8 - hp si)` holds,
  -- and every `j ∈ htabFootprint si ti` has `Inside j (hp s_{i-1}) (hp si)` with `pw + 72 ≤ hp s0 ≤ hp s_{i-1}`,
  -- so `j` is disjoint from `(pw, 72)`, `(sp, 0)`, and `(hp si, hp s8 - hp si)`!
  have hfr_step : ∀ {a b c : PanSemStateFiniteExact 64 F}
      (hab : globN a "heap_ptr" ≤ globN b "heap_ptr")
      (hbc : globN b "heap_ptr" ≤ globN c "heap_ptr")
      (h1 : FrameOutside a b [(globN s "scratch_ptr", 0), (pw.toNat, 72)] (globN a "heap_ptr", globN b "heap_ptr" - globN a "heap_ptr"))
      (h2 : FrameOutside b c [(globN s "scratch_ptr", 0), (pw.toNat, 72)] (globN b "heap_ptr", globN c "heap_ptr" - globN b "heap_ptr")),
      FrameOutside a c [(globN s "scratch_ptr", 0), (pw.toNat, 72)] (globN a "heap_ptr", globN c "heap_ptr" - globN a "heap_ptr") := by
    intro a b c hab hbc h1 h2 x hno hnhf
    have hnhf1 : ¬ CellHits x.toNat (globN a "heap_ptr", globN b "heap_ptr" - globN a "heap_ptr") :=
      fun ⟨c1, c2⟩ => hnhf ⟨c1, by dsimp only at c2 ⊢; omega⟩
    have hnhf2 : ¬ CellHits x.toNat (globN b "heap_ptr", globN c "heap_ptr" - globN b "heap_ptr") :=
      fun ⟨c1, c2⟩ => hnhf ⟨by dsimp only at c1 ⊢; omega, by dsimp only at c2 ⊢; omega⟩
    exact (h2 x hno hnhf2).trans (h1 x hno hnhf1)
  have hfr2' : FrameOutside s1 s2 [(globN s "scratch_ptr", 0), (pw.toNat, 72)]
      (globN s1 "heap_ptr", globN s2 "heap_ptr" - globN s1 "heap_ptr") := by rw [hsp1, hsp0] at hfr2; exact hfr2
  have hfr3' : FrameOutside s2 s3 [(globN s "scratch_ptr", 0), (pw.toNat, 72)]
      (globN s2 "heap_ptr", globN s3 "heap_ptr" - globN s2 "heap_ptr") := by rw [hsp2, hsp1, hsp0] at hfr3; exact hfr3
  have hfr4' : FrameOutside s3 s4 [(globN s "scratch_ptr", 0), (pw.toNat, 72)]
      (globN s3 "heap_ptr", globN s4 "heap_ptr" - globN s3 "heap_ptr") := by rw [hsp3, hsp2, hsp1, hsp0] at hfr4; exact hfr4
  have hfr5' : FrameOutside s4 s5 [(globN s "scratch_ptr", 0), (pw.toNat, 72)]
      (globN s4 "heap_ptr", globN s5 "heap_ptr" - globN s4 "heap_ptr") := by rw [hsp4, hsp3, hsp2, hsp1, hsp0] at hfr5; exact hfr5
  have hfr6' : FrameOutside s5 s6 [(globN s "scratch_ptr", 0), (pw.toNat, 72)]
      (globN s5 "heap_ptr", globN s6 "heap_ptr" - globN s5 "heap_ptr") := by rw [hsp5, hsp4, hsp3, hsp2, hsp1, hsp0] at hfr6; exact hfr6
  have hfr7' : FrameOutside s6 s7 [(globN s "scratch_ptr", 0), (pw.toNat, 72)]
      (globN s6 "heap_ptr", globN s7 "heap_ptr" - globN s6 "heap_ptr") := by rw [hsp6, hsp5, hsp4, hsp3, hsp2, hsp1, hsp0] at hfr7; exact hfr7
  have hfr8' : FrameOutside s7 s8 [(globN s "scratch_ptr", 0), (pw.toNat, 72)]
      (globN s7 "heap_ptr", globN s8 "heap_ptr" - globN s7 "heap_ptr") := by rw [hsp7, hsp6, hsp5, hsp4, hsp3, hsp2, hsp1, hsp0] at hfr8; exact hfr8
  have hfr_78 := hfr8'
  have hfr_68 := hfr_step (by omega) (by omega) hfr7' hfr_78
  have hfr_58 := hfr_step (by omega) (by omega) hfr6' hfr_68
  have hfr_48 := hfr_step (by omega) (by omega) hfr5' hfr_58
  have hfr_38 := hfr_step (by omega) (by omega) hfr4' hfr_48
  have hfr_28 := hfr_step (by omega) (by omega) hfr3' hfr_38
  have hfr_18 := hfr_step (by omega) (by omega) hfr2' hfr_28
  have hu_from_step : ∀ {si : PanSemStateFiniteExact 64 F} {lo : Nat} {i : Ivl},
      ArenaOK si → pw.toNat + 72 ≤ lo → Inside i lo (globN si "heap_ptr") →
      FrameOutside si s8 [(globN s "scratch_ptr", 0), (pw.toNat, 72)] (globN si "heap_ptr", globN s8 "heap_ptr" - globN si "heap_ptr") →
      M08IvlUnhit si inner_post i := by
    intro si lo i hAsi hlo hin hfr_si a ha8 h1 h2
    rw [hs9_m]
    apply hfr_si a
    · intro j hj hcj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact InitECandidate.Solver.Wave8Contracts.M08.not_cellHits_of_disj ha8 hsp8_s ⟨h1, h2⟩ (Or.inr (Or.inl rfl)) hcj
      · exact InitECandidate.Solver.Wave8Contracts.M08.not_cellHits_of_disj ha8 hpw8 ⟨h1, h2⟩
          (Or.inr (Or.inr (Or.inr (le_trans hlo hin.1)))) hcj
    · exact InitECandidate.Solver.Wave8Contracts.M08.not_cellHits_of_disj ha8 hAsi.2.2.2.2.2.1 ⟨h1, h2⟩
        (Or.inr (Or.inr (Or.inl hin.2)))
  obtain ⟨hwf1_p, hfp1_eq, hhdr1_eq⟩ := htabWF_transfer_unhit hAR1 hAR9 hwf1
    (fun i hi => hu_from_step hAR1.2 (by omega) (hfp1 i hi).2 hfr_18)
    (fun i hi => AllocatorGrows.allocated ⟨by omega, by rw [hsp_post, hsp1, hsp0]⟩ (hfp1 i hi).1)
  obtain ⟨hwf2_p, hfp2_eq, hhdr2_eq⟩ := htabWF_transfer_unhit hAR2 hAR9 hwf2
    (fun i hi => hu_from_step hAR2.2 (by omega) (hfp2 i hi).2 hfr_28)
    (fun i hi => AllocatorGrows.allocated ⟨by omega, by rw [hsp_post, hsp2, hsp1, hsp0]⟩ (hfp2 i hi).1)
  obtain ⟨hwf3_p, hfp3_eq, hhdr3_eq⟩ := htabWF_transfer_unhit hAR3 hAR9 hwf3
    (fun i hi => hu_from_step hAR3.2 (by omega) (hfp3 i hi).2 hfr_38)
    (fun i hi => AllocatorGrows.allocated ⟨by omega, by rw [hsp_post, hsp3, hsp2, hsp1, hsp0]⟩ (hfp3 i hi).1)
  obtain ⟨hwf4_p, hfp4_eq, hhdr4_eq⟩ := htabWF_transfer_unhit hAR4 hAR9 hwf4
    (fun i hi => hu_from_step hAR4.2 (by omega) (hfp4 i hi).2 hfr_48)
    (fun i hi => AllocatorGrows.allocated ⟨by omega, by rw [hsp_post, hsp4, hsp3, hsp2, hsp1, hsp0]⟩ (hfp4 i hi).1)
  obtain ⟨hwf5_p, hfp5_eq, hhdr5_eq⟩ := htabWF_transfer_unhit hAR5 hAR9 hwf5
    (fun i hi => hu_from_step hAR5.2 (by omega) (hfp5 i hi).2 hfr_58)
    (fun i hi => AllocatorGrows.allocated ⟨by omega, by rw [hsp_post, hsp5, hsp4, hsp3, hsp2, hsp1, hsp0]⟩ (hfp5 i hi).1)
  obtain ⟨hwf6_p, hfp6_eq, hhdr6_eq⟩ := htabWF_transfer_unhit hAR6 hAR9 hwf6
    (fun i hi => hu_from_step hAR6.2 (by omega) (hfp6 i hi).2 hfr_68)
    (fun i hi => AllocatorGrows.allocated ⟨by omega, by rw [hsp_post, hsp6, hsp5, hsp4, hsp3, hsp2, hsp1, hsp0]⟩ (hfp6 i hi).1)
  obtain ⟨hwf7_p, hfp7_eq, hhdr7_eq⟩ := htabWF_transfer_unhit hAR7 hAR9 hwf7
    (fun i hi => hu_from_step hAR7.2 (by omega) (hfp7 i hi).2 hfr_78)
    (fun i hi => AllocatorGrows.allocated ⟨by omega, by rw [hsp_post, hsp7, hsp6, hsp5, hsp4, hsp3, hsp2, hsp1, hsp0]⟩ (hfp7 i hi).1)
  obtain ⟨hwf8_p, hfp8_eq, hhdr8_eq⟩ := htabWF_transfer_unhit hAR8 hAR9 hwf8
    (fun _ _ _ _ _ _ => by rw [hs9_m])
    (fun i hi => AllocatorGrows.allocated ⟨by omega, by rw [hsp_post, hsp8, hsp7, hsp6, hsp5, hsp4, hsp3, hsp2, hsp1, hsp0]⟩ (hfp8 i hi).1)
  -- `FixedTyped inner_post` and `balObjects inner_post = balObjects s`!
  obtain ⟨hT_s, hJ_s, hF_s, hTr_s⟩ := hWT
  have hu_tab_s : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, M08IvlUnhit s inner_post i :=
    fun t ht i hi => hunhit_alloc i (((hT_s.2.1 t ht).2 i hi).1)
  have hu_bal_s : ∀ i ∈ balObjects s, i.2 ≠ 0 → M08IvlUnhit s inner_post i := by
    intro i hi hnz
    rcases hF_s.1 i (M13.bal_in_fixedObjects hi) with h0 | ⟨hal, _⟩
    · exact absurd h0 hnz
    · exact hunhit_alloc i hal
  have hbal_part := InitECandidate.Solver.Wave8Contracts.M08.balObjects_eq_of_unhit
    hAR0.2 hT_s hF_s hba_g hu_tab_s hu_bal_s hm0
  have hu_rec : ∀ g sz, (g, sz) ∈ M13.typedRecords → globN s g ≠ 0 → M08IvlUnhit s inner_post (globN s g, sz) := by
    intro g sz hr hnz
    have hmf := InitECandidate.Solver.Wave8Contracts.M08.typedRecord_mem_fixedObjects s hr
    simp only [hnz, ↓reduceIte] at hmf
    rcases hF_s.1 _ hmf with h0 | ⟨hal, _⟩
    · dsimp at h0; simp only [M13.typedRecords, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hr
      rcases hr with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
    · exact hunhit_alloc _ hal
  have hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → M08IvlUnhit s inner_post i := by
    intro i hi h24
    rcases hF_s.1 i (M13.blockOut_in_fixedObjects hi) with h0 | ⟨hal, _⟩
    · omega
    · exact hunhit_alloc i hal
  have hbo_words : globN s "bo" ≠ 0 → ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW inner_post (globN s "bo" + k) = memW s (globN s "bo" + k) := fun hnz k hk => by
    have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    simpa [hbo_g] using InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
      hAR0.2 hF_s "bo" 88 (by decide) hbo_g hnz (hu_rec "bo" 88 (by decide) hnz) hk_in.1 hk_in.2
  have hbo_part := InitECandidate.Solver.Wave8Contracts.M08.blockOutObjects_eq_of_bo_unhit
    hAR0.2 hF_s hbo_g hT_s.2.2.2.2.2.2.2.2.2.2.1
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
  have hpw_nz : pw.toNat ≠ 0 := by rw [M13.sourceBase_val] at hpw_lo; omega
  have hts_in : Inside (globN inner_post "ts", 72) (globN s "heap_ptr") (globN inner_post "heap_ptr") := by
    rw [hpost_ts, hs9_hp]
    exact ⟨by dsimp; omega, by dsimp; omega⟩
  have hbal_pw_s : (balObjects s).Pairwise Disj := by
    have hpw := hF_s.2
    unfold fixedObjects at hpw
    exact (List.pairwise_append.1 hpw).2.1
  obtain ⟨hF_post, hfix_from⟩ := fixedTyped_rebind_one_fresh hAR0 hAR9 hag hF_s
    "ts" 72 (by decide) (by rw [hpost_ts]; exact hpw_nz) (by rw [hpost_ts]; exact hpw8)
    (by omega) hts_in hgb_kept hj_g hjc_g hbo_part.1
    (fun x hx => by rw [hbal_part.1] at hx; exact hx)
    (by rw [hbal_part.1]; exact hbal_pw_s)
  -- Classify `fixedObjects inner_post`: every `j ∈ fixedObjects inner_post` is in `fixedObjects s` OR `(pw.toNat, 72)`!
  have hfix_post_in : ∀ j ∈ fixedObjects inner_post, j ∈ fixedObjects s ∨ j = (pw.toNat, 72) := by
    intro j hj
    unfold fixedObjects at hj
    rcases List.mem_append.1 hj with hj123 | hj_bal
    · rcases List.mem_append.1 hj123 with hj12 | hj_bo
      · rcases List.mem_append.1 hj12 with hj_gb | hj_jr
        · obtain ⟨gn, hgn, rfl⟩ := List.mem_map.1 hj_gb
          by_cases hn : gn.1 = "ts"
          · have hsz : gn.2 = 72 := by
              simp only [globalBuffers, List.mem_cons, List.not_mem_nil, or_false] at hgn
              repeat' rcases hgn with rfl | hgn
              all_goals first | rfl | contradiction
            right; rw [hn, hsz, hpost_ts, if_neg hpw_nz]
          · left; rw [hgb_kept gn hgn hn]
            unfold fixedObjects
            apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
            exact List.mem_map.2 ⟨gn, hgn, rfl⟩
        · left; simp only [List.mem_singleton] at hj_jr; subst hj_jr
          rw [hjc_g, hj_g]
          unfold fixedObjects
          apply List.mem_append_left; apply List.mem_append_left; exact List.mem_append_right _ (List.mem_singleton.2 rfl)
      · left; rw [hbo_part.1] at hj_bo; exact M13.blockOut_in_fixedObjects hj_bo
    · left; rw [hbal_part.1] at hj_bal; exact M13.bal_in_fixedObjects hj_bal
  -- Now package `T_new = [t1.toNat, t2.toNat, t3.toNat, t4.toNat, t5.toNat, t6.toNat, t7.toNat, t8.toNat]`:
  have ht_chain : pw.toNat + 72 ≤ t1.toNat ∧ t1.toNat + 88 ≤ t2.toNat ∧
      t2.toNat + 88 ≤ t3.toNat ∧ t3.toNat + 88 ≤ t4.toNat ∧
      t4.toNat + 88 ≤ t5.toNat ∧ t5.toNat + 88 ≤ t6.toNat ∧
      t6.toNat + 88 ≤ t7.toNat ∧ t7.toNat + 88 ≤ t8.toNat := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact le_trans (le_of_eq hhp0.symm) ht1_lo
    · exact le_trans ht1_hi ht2_lo
    · exact le_trans ht2_hi ht3_lo
    · exact le_trans ht3_hi ht4_lo
    · exact le_trans ht4_hi ht5_lo
    · exact le_trans ht5_hi ht6_lo
    · exact le_trans ht6_hi ht7_lo
    · exact le_trans ht7_hi ht8_lo
  let T_new : List Nat := [t1.toNat, t2.toNat, t3.toNat, t4.toNat, t5.toNat, t6.toNat, t7.toNat, t8.toNat]
  have hT_nd : T_new.Nodup := by
    obtain ⟨c01, c12, c23, c34, c45, c56, c67, c78⟩ := ht_chain
    dsimp only [T_new]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    refine ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩,
            ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩,
            ⟨by omega, by omega, by omega, by omega, by omega⟩,
            ⟨by omega, by omega, by omega, by omega⟩,
            ⟨by omega, by omega, by omega⟩,
            ⟨by omega, by omega⟩,
            ⟨by omega, not_false⟩⟩
  have hfp_disj_fix : ∀ (t lo hi : Nat),
      pw.toNat + 72 ≤ lo → hi ≤ globN s8 "heap_ptr" →
      (∀ i ∈ htabFootprint inner_post t, Allocated inner_post i ∧ Inside i lo hi) →
      ∀ i ∈ htabFootprint inner_post t, Allocated inner_post i ∧
        Inside i (globN s "heap_ptr") (globN inner_post "heap_ptr") ∧
        (∀ j ∈ fixedObjects inner_post, Disj i j) := by
    intro t lo hi hlo hhi hfp i hi_mem
    obtain ⟨hal_i, hin_i⟩ := hfp i hi_mem
    have hin_full : Inside i (globN s "heap_ptr") (globN inner_post "heap_ptr") :=
      ⟨by dsimp [Inside] at hin_i ⊢; omega, by rw [hs9_hp]; exact le_trans hin_i.2 hhi⟩
    refine ⟨hal_i, hin_full, fun j hj => ?_⟩
    rcases hfix_post_in j hj with hj_s | rfl
    · rcases hF_s.1 j hj_s with hj0 | ⟨hal_j, _⟩
      · exact Or.inr (Or.inl hj0)
      · exact InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap hAR0.2 hAR9.2 hal_j hin_full
    · exact Or.inr (Or.inr (Or.inr (le_trans hlo hin_i.1)))
  have hT_bounds : ∀ t ∈ T_new, ∃ idx : Fin 8,
      t = [t1.toNat, t2.toNat, t3.toNat, t4.toNat, t5.toNat, t6.toNat, t7.toNat, t8.toNat][idx] := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ht
    exact ⟨⟨i, hi⟩, rfl⟩
  have hT_ivls : ∀ (idx : Fin 8),
      let t := [t1.toNat, t2.toNat, t3.toNat, t4.toNat, t5.toNat, t6.toNat, t7.toNat, t8.toNat][idx]
      let lo := [globN s0 "heap_ptr", globN s1 "heap_ptr", globN s2 "heap_ptr", globN s3 "heap_ptr",
                 globN s4 "heap_ptr", globN s5 "heap_ptr", globN s6 "heap_ptr", globN s7 "heap_ptr"][idx]
      let hi := [globN s1 "heap_ptr", globN s2 "heap_ptr", globN s3 "heap_ptr", globN s4 "heap_ptr",
                 globN s5 "heap_ptr", globN s6 "heap_ptr", globN s7 "heap_ptr", globN s8 "heap_ptr"][idx]
      HtabWF inner_post t ∧ pw.toNat + 72 ≤ lo ∧ hi ≤ globN s8 "heap_ptr" ∧
      (∀ i ∈ htabFootprint inner_post t, Allocated inner_post i ∧ Inside i lo hi) := by
    intro ⟨idx, hidx⟩
    match idx, hidx with
    | 0, _ => exact ⟨hwf1_p, by dsimp; omega, by dsimp; omega, fun i hi => by dsimp at hi ⊢; rw [hfp1_eq] at hi; exact ⟨AllocatorGrows.allocated ⟨by omega, by rw [hsp_post, hsp1, hsp0]⟩ (hfp1 i hi).1, (hfp1 i hi).2⟩⟩
    | 1, _ => exact ⟨hwf2_p, by dsimp; omega, by dsimp; omega, fun i hi => by dsimp at hi ⊢; rw [hfp2_eq] at hi; exact ⟨AllocatorGrows.allocated ⟨by omega, by rw [hsp_post, hsp2, hsp1, hsp0]⟩ (hfp2 i hi).1, (hfp2 i hi).2⟩⟩
    | 2, _ => exact ⟨hwf3_p, by dsimp; omega, by dsimp; omega, fun i hi => by dsimp at hi ⊢; rw [hfp3_eq] at hi; exact ⟨AllocatorGrows.allocated ⟨by omega, by rw [hsp_post, hsp3, hsp2, hsp1, hsp0]⟩ (hfp3 i hi).1, (hfp3 i hi).2⟩⟩
    | 3, _ => exact ⟨hwf4_p, by dsimp; omega, by dsimp; omega, fun i hi => by dsimp at hi ⊢; rw [hfp4_eq] at hi; exact ⟨AllocatorGrows.allocated ⟨by omega, by rw [hsp_post, hsp4, hsp3, hsp2, hsp1, hsp0]⟩ (hfp4 i hi).1, (hfp4 i hi).2⟩⟩
    | 4, _ => exact ⟨hwf5_p, by dsimp; omega, by dsimp; omega, fun i hi => by dsimp at hi ⊢; rw [hfp5_eq] at hi; exact ⟨AllocatorGrows.allocated ⟨by omega, by rw [hsp_post, hsp5, hsp4, hsp3, hsp2, hsp1, hsp0]⟩ (hfp5 i hi).1, (hfp5 i hi).2⟩⟩
    | 5, _ => exact ⟨hwf6_p, by dsimp; omega, by dsimp; omega, fun i hi => by dsimp at hi ⊢; rw [hfp6_eq] at hi; exact ⟨AllocatorGrows.allocated ⟨by omega, by rw [hsp_post, hsp6, hsp5, hsp4, hsp3, hsp2, hsp1, hsp0]⟩ (hfp6 i hi).1, (hfp6 i hi).2⟩⟩
    | 6, _ => exact ⟨hwf7_p, by dsimp; omega, by dsimp; omega, fun i hi => by dsimp at hi ⊢; rw [hfp7_eq] at hi; exact ⟨AllocatorGrows.allocated ⟨by omega, by rw [hsp_post, hsp7, hsp6, hsp5, hsp4, hsp3, hsp2, hsp1, hsp0]⟩ (hfp7 i hi).1, (hfp7 i hi).2⟩⟩
    | 7, _ => exact ⟨hwf8_p, by dsimp; omega, by dsimp; omega, fun i hi => by dsimp at hi ⊢; rw [hfp8_eq] at hi; exact ⟨AllocatorGrows.allocated ⟨by omega, by rw [hsp_post, hsp8, hsp7, hsp6, hsp5, hsp4, hsp3, hsp2, hsp1, hsp0]⟩ (hfp8 i hi).1, (hfp8 i hi).2⟩⟩
  have hT_wf : ∀ t ∈ T_new, HtabWF inner_post t ∧
      ∀ i ∈ htabFootprint inner_post t, Allocated inner_post i ∧
        Inside i (globN s "heap_ptr") (globN inner_post "heap_ptr") ∧
        (∀ j ∈ fixedObjects inner_post, Disj i j) := by
    intro t ht
    obtain ⟨idx, rfl⟩ := hT_bounds t ht
    obtain ⟨hwf_i, hlo_i, hhi_i, hfp_i⟩ := hT_ivls idx
    exact ⟨hwf_i, hfp_disj_fix _ _ _ hlo_i hhi_i hfp_i⟩
  have hT_pw : ∀ t ∈ T_new, ∀ u ∈ T_new, t ≠ u →
      ∀ i ∈ htabFootprint inner_post t, ∀ j ∈ htabFootprint inner_post u, Disj i j := by
    intro t ht u hu hne i hi j hj
    obtain ⟨idx1, rfl⟩ := hT_bounds t ht
    obtain ⟨idx2, rfl⟩ := hT_bounds u hu
    have hidx_ne : idx1 ≠ idx2 := fun h => hne (by rw [h])
    obtain ⟨_, _, _, hfp_1⟩ := hT_ivls idx1
    obtain ⟨_, _, _, hfp_2⟩ := hT_ivls idx2
    have hin1 := (hfp_1 i hi).2
    have hin2 := (hfp_2 j hj).2
    have hhi_le_lo : ∀ (a b : Fin 8), a.val < b.val →
        [globN s1 "heap_ptr", globN s2 "heap_ptr", globN s3 "heap_ptr", globN s4 "heap_ptr",
         globN s5 "heap_ptr", globN s6 "heap_ptr", globN s7 "heap_ptr", globN s8 "heap_ptr"][a] ≤
        [globN s0 "heap_ptr", globN s1 "heap_ptr", globN s2 "heap_ptr", globN s3 "heap_ptr",
         globN s4 "heap_ptr", globN s5 "heap_ptr", globN s6 "heap_ptr", globN s7 "heap_ptr"][b] := by
      have hh12 : globN s1 "heap_ptr" ≤ globN s2 "heap_ptr" := le_trans ht2_lo (by omega)
      have hh23 : globN s2 "heap_ptr" ≤ globN s3 "heap_ptr" := le_trans ht3_lo (by omega)
      have hh34 : globN s3 "heap_ptr" ≤ globN s4 "heap_ptr" := le_trans ht4_lo (by omega)
      have hh45 : globN s4 "heap_ptr" ≤ globN s5 "heap_ptr" := le_trans ht5_lo (by omega)
      have hh56 : globN s5 "heap_ptr" ≤ globN s6 "heap_ptr" := le_trans ht6_lo (by omega)
      have hh67 : globN s6 "heap_ptr" ≤ globN s7 "heap_ptr" := le_trans ht7_lo (by omega)
      intro ⟨a, ha⟩ ⟨b, hb⟩ hab
      dsimp only at hab
      match a, ha, b, hb with
      | 0, _, 1, _ | 0, _, 2, _ | 0, _, 3, _ | 0, _, 4, _ | 0, _, 5, _ | 0, _, 6, _ | 0, _, 7, _
      | 1, _, 2, _ | 1, _, 3, _ | 1, _, 4, _ | 1, _, 5, _ | 1, _, 6, _ | 1, _, 7, _
      | 2, _, 3, _ | 2, _, 4, _ | 2, _, 5, _ | 2, _, 6, _ | 2, _, 7, _
      | 3, _, 4, _ | 3, _, 5, _ | 3, _, 6, _ | 3, _, 7, _
      | 4, _, 5, _ | 4, _, 6, _ | 4, _, 7, _
      | 5, _, 6, _ | 5, _, 7, _
      | 6, _, 7, _ => change _ ≤ _; dsimp; omega
      | 0, _, 0, _ | 1, _, 0, _ | 1, _, 1, _ | 2, _, 0, _ | 2, _, 1, _ | 2, _, 2, _
      | 3, _, 0, _ | 3, _, 1, _ | 3, _, 2, _ | 3, _, 3, _
      | 4, _, 0, _ | 4, _, 1, _ | 4, _, 2, _ | 4, _, 3, _ | 4, _, 4, _
      | 5, _, 0, _ | 5, _, 1, _ | 5, _, 2, _ | 5, _, 3, _ | 5, _, 4, _ | 5, _, 5, _
      | 6, _, 0, _ | 6, _, 1, _ | 6, _, 2, _ | 6, _, 3, _ | 6, _, 4, _ | 6, _, 5, _ | 6, _, 6, _
      | 7, _, 0, _ | 7, _, 1, _ | 7, _, 2, _ | 7, _, 3, _ | 7, _, 4, _ | 7, _, 5, _ | 7, _, 6, _ | 7, _, 7, _ =>
        exfalso; omega
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hidx_ne) with hlt | hgt
    · exact disj_fresh_sub hin1 hin2 (hhi_le_lo idx1 idx2 hlt)
    · exact disj_flip (disj_fresh_sub hin2 hin1 (hhi_le_lo idx2 idx1 hgt))
  -- JournalTyped & journalRoleSlots on `inner_post` (trivial because `globN inner_post "journal_n" = 0`!):
  have hjrs_post : journalRoleSlots inner_post = [] := by
    unfold journalRoleSlots; rw [hpost_jn]; rfl
  have hJ_post : JournalTyped inner_post (S ++ T_new) := by
    refine ⟨by rw [hpost_jn]; omega, by rw [hjc_g]; exact hJ_s.2.1, ?_, ?_⟩
    · rw [hjc_g, hj_g]
      rcases hJ_s.2.2.1 with h0 | ⟨hal, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hag.allocated hal,
          InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hAR0.1 hAR9.1 hw⟩
    · intro i hi; rw [hpost_jn] at hi; omega
  -- `ts` slots, `ts+32` nested values (`hdr inner_post t4 3 = 0`!), `bal`, `globalTableRoots`, and `RolesOK`!
  have hcnt4_p : hdr inner_post t4.toNat 3 = 0 := (hhdr4_eq 3 (by omega)).trans hcnt4
  have hts_post : ∀ k ∈ tsTableSlots, globN inner_post "ts" ≠ 0 →
      RootIn (S ++ T_new) (memW inner_post (globN inner_post "ts" + k)) := by
    intro k hk _
    rw [hpost_ts]
    simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hmw_p8]; exact Or.inr (List.mem_append_right _ (by simp [T_new]))
    · rw [hmw_p16]; exact Or.inr (List.mem_append_right _ (by simp [T_new]))
    · rw [hmw_p24]; exact Or.inr (List.mem_append_right _ (by simp [T_new]))
    · rw [hmw_p32]; exact Or.inr (List.mem_append_right _ (by simp [T_new]))
    · rw [hmw_p40]; exact Or.inr (List.mem_append_right _ (by simp [T_new]))
    · rw [hmw_p48]; exact Or.inr (List.mem_append_right _ (by simp [T_new]))
    · rw [hmw_p56]; exact Or.inr (List.mem_append_right _ (by simp [T_new]))
    · rw [hmw_p64]; exact Or.inr (List.mem_append_right _ (by simp [T_new]))
  have hgr_post : ∀ g ∈ globalTableRoots, RootIn (S ++ T_new) (globN inner_post g) := by
    intro g hg
    have hg_eq : globN inner_post g = globN s g := by
      simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      · exact hba_g
      · exact hbia_g
      · exact hbis_g
    rw [hg_eq]
    rcases hT_s.2.2.2.2.2.2.1 g hg with h0 | hmS
    · exact Or.inl h0
    · exact Or.inr (List.mem_append_left _ hmS)
  have htsN_post : globN inner_post "ts" ≠ 0 →
      memW inner_post (globN inner_post "ts" + 32) ∈ S ++ T_new →
      HtabValuesIn inner_post (memW inner_post (globN inner_post "ts" + 32)) (S ++ T_new) := by
    intro _ _ i hi
    rw [hpost_ts, hmw_p32, hcnt4_p] at hi
    omega
  have hbal_post : ∀ ad ∈ balRecords inner_post,
      memW inner_post ad ∈ S ++ T_new ∧ memW inner_post (ad + 8) ∈ S ++ T_new ∧
      (∀ k ∈ ([16, 24, 32] : List Nat), LstOK inner_post (memW inner_post (ad + k))) ∧
      (∀ l ∈ htabValues inner_post (memW inner_post ad), LstOK inner_post l) := by
    have hbrec_eq : balRecords inner_post = balRecords s :=
      InitECandidate.Solver.Wave8Contracts.M08.balRecords_eq_of_unhit hT_s hba_g
        (fun hnz => by
          rcases hT_s.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
          · exact absurd h0 hnz
          · exact hu_tab_s _ hm)
    intro ad had
    obtain ⟨h0, h8, _, hkl, hll⟩ := hbal_part.2 ad had
    rw [hbrec_eq] at had
    have had_s := hT_s.2.2.2.2.2.2.2.2.2.1 ad had
    exact ⟨by rw [h0]; exact List.mem_append_left _ had_s.1,
           by rw [h8]; exact List.mem_append_left _ had_s.2.1, hkl, hll⟩
  -- `RolesOK inner_post (S ++ T_new) (worldRoleSlots inner_post) []`:
  let gfix := s.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (globN s8 "heap_ptr"))))
  let post_j : PanSemStateFiniteExact 64 F := { inner_post with globals := gfix }
  have hwgs_pj : InitECandidate.Solver.Wave8Contracts.M08.WorldGlobalsSame s post_j := by
    refine ⟨fun ⟨gn, sz⟩ hgn => ?_, fun g hg => ?_, ?_, ?_, ?_⟩
    · have hne : ofString "heap_ptr" ≠ ofString gn := by
        simp only [globalBuffers, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgn
        repeat' rcases hgn with ⟨rfl, _⟩ | hgn
        all_goals decide
      simp [post_j, gfix, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne]
    · have hne : ofString "heap_ptr" ≠ ofString g := by
        simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl <;> decide
      simp [post_j, gfix, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne]
    · simp [post_j, gfix, globN, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "journal" by decide]
    · simp [post_j, gfix, globN, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "journal_cap" by decide]
    · simp [post_j, gfix, globN, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "journal_n" by decide]
  have hwrs_pj : worldRoleSlots post_j = worldRoleSlots s :=
    InitECandidate.Solver.Wave8Contracts.M08.worldRoleSlots_eq_of_unhit (post := post_j)
      hAR0.2 hT_s hF_s hwgs_pj
      (fun t ht i hi => hu_tab_s t ht i hi)
      (fun hnz => hu_rec "ws" 40 (by decide) hnz)
      (fun hnz => hu_rec "bs" 80 (by decide) hnz)
      (fun hnz => hu_rec "ts" 72 (by decide) hnz)
      (fun i hi hnz => hu_bal_s i hi hnz)
      hm0
  have hroles_post : (∀ t ∈ S, hdr inner_post t 0 = hdr s t 0) →
      (∀ t ∈ T_new, t ∉ S) →
      RolesOK inner_post (S ++ T_new) (worldRoleSlots inner_post) (journalRoleSlots inner_post) := by
    intro hhdr0_S hT_disj_S
    rw [hjrs_post]
    have hroles_s_nil : RolesOK s S (worldRoleSlots s) [] := by
      obtain ⟨r1, r2, _⟩ := hT_s.2.2.2.2.2.2.2.2.2.2.2
      exact ⟨fun a ha => r1 a (List.mem_append_left _ (by simpa using ha)), r2, fun _ h => by cases h⟩
    refine rolesOK_adjoin_fresh_slots hroles_s_nil hhdr0_S ?_ hT_disj_S
    let pre_p := (recRoles inner_post "ws" [(16, "ws+16"), (32, "ws+32")] ++
      recRoles inner_post "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"), (40, "bs+40"), (48, "bs+48"), (72, "bs+72")]).filter (fun a => a.1 != 0)
    let add_p : List (Nat × String) :=
      [(t1.toNat, "ts+8"), (t2.toNat, "ts+16"), (t3.toNat, "ts+24"), (t4.toNat, "ts+32"),
       (t5.toNat, "ts+40"), (t6.toNat, "ts+48"), (t7.toNat, "ts+56"), (t8.toNat, "ts+64")]
    let suf_p := ([(globN inner_post "bal_accounts", "bal_accounts"),
        (globN inner_post "bal_idx_accts", "bal_idx_accts"),
        (globN inner_post "bal_idx_stor", "bal_idx_stor")] ++
      nestRoles inner_post "bs" "bs.inner" ++
      ((balRecords inner_post).flatMap fun ad => [(memW inner_post ad, "bal.stor"), (memW inner_post (ad + 8), "bal.reads")])).filter (fun a => a.1 != 0)
    have hnest_ts_p : nestRoles inner_post "ts" "ts.inner" = [] := by
      unfold nestRoles
      rw [hpost_ts, if_neg hpw_nz, hmw_p32]
      have ht4_nz : t4.toNat ≠ 0 := htab_nonzero_of_wf hwf4_p
      rw [if_neg ht4_nz]
      unfold htabValues
      rw [hcnt4_p]; rfl
    have hpre_eq : pre_p = (recRoles post_j "ws" [(16, "ws+16"), (32, "ws+32")] ++
        recRoles post_j "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"), (40, "bs+40"), (48, "bs+48"), (72, "bs+72")]).filter (fun a => a.1 != 0) := by
      have e1 : globN post_j "ws" = globN inner_post "ws" := (hwgs_pj.1 ("ws", 40) (by decide)).trans hws_g.symm
      have e2 : globN post_j "bs" = globN inner_post "bs" := (hwgs_pj.1 ("bs", 80) (by decide)).trans hbs_g.symm
      have hm_eq : ∀ off, memW post_j off = memW inner_post off := fun _ => rfl
      simp only [pre_p, recRoles, e1, e2, hm_eq]
    have hsuf_eq : suf_p = ([(globN post_j "bal_accounts", "bal_accounts"),
        (globN post_j "bal_idx_accts", "bal_idx_accts"),
        (globN post_j "bal_idx_stor", "bal_idx_stor")] ++
      nestRoles post_j "bs" "bs.inner" ++
      ((balRecords post_j).flatMap fun ad => [(memW post_j ad, "bal.stor"), (memW post_j (ad + 8), "bal.reads")])).filter (fun a => a.1 != 0) := by
      have eba : globN post_j "bal_accounts" = globN inner_post "bal_accounts" := (hwgs_pj.2.1 "bal_accounts" (by decide)).trans hba_g.symm
      have ebia : globN post_j "bal_idx_accts" = globN inner_post "bal_idx_accts" := (hwgs_pj.2.1 "bal_idx_accts" (by decide)).trans hbia_g.symm
      have ebis : globN post_j "bal_idx_stor" = globN inner_post "bal_idx_stor" := (hwgs_pj.2.1 "bal_idx_stor" (by decide)).trans hbis_g.symm
      have ebs : globN post_j "bs" = globN inner_post "bs" := (hwgs_pj.1 ("bs", 80) (by decide)).trans hbs_g.symm
      have hm_eq : ∀ off, memW post_j off = memW inner_post off := fun _ => rfl
      have htv_eq : ∀ t, htabValues post_j t = htabValues inner_post t := fun _ => rfl
      have hbr_eq : balRecords post_j = balRecords inner_post := by
        change (if globN post_j "bal_accounts" = 0 then _ else _) = (if globN inner_post "bal_accounts" = 0 then _ else _)
        rw [eba]; rfl
      simp only [suf_p, nestRoles, eba, ebia, ebis, ebs, hm_eq, htv_eq, hbr_eq]
    have hsub_pj : List.Sublist (pre_p ++ suf_p) (worldRoleSlots post_j) := by
      have hgen : ∀ (a b c d e : List (Nat × String)),
          List.Sublist (a ++ c ++ e) (a ++ b ++ c ++ d ++ e) := by
        intro a b c d e
        have h1 : List.Sublist (a ++ c) (a ++ b ++ c ++ d) := by
          rw [List.append_assoc a b c, List.append_assoc a (b ++ c) d, List.append_assoc b c d]
          exact List.Sublist.append (List.Sublist.refl a)
            ((List.sublist_append_left c d).trans (List.sublist_append_right b (c ++ d)))
        exact List.Sublist.append h1 (List.Sublist.refl e)
      unfold worldRoleSlots
      rw [hpre_eq, hsuf_eq]
      simp only [List.filter_append]
      have hinst := hgen
        (List.filter (fun a => a.1 != 0) (recRoles post_j "ws" [(16, "ws+16"), (32, "ws+32")]) ++
          List.filter (fun a => a.1 != 0) (recRoles post_j "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"), (40, "bs+40"), (48, "bs+48"), (72, "bs+72")]))
        (List.filter (fun a => a.1 != 0) (recRoles post_j "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"), (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")]))
        (List.filter (fun a => a.1 != 0) [(globN post_j "bal_accounts", "bal_accounts"), (globN post_j "bal_idx_accts", "bal_idx_accts"), (globN post_j "bal_idx_stor", "bal_idx_stor")] ++
          List.filter (fun a => a.1 != 0) (nestRoles post_j "bs" "bs.inner"))
        (List.filter (fun a => a.1 != 0) (nestRoles post_j "ts" "ts.inner"))
        (List.filter (fun a => a.1 != 0) ((balRecords post_j).flatMap fun ad => [(memW post_j ad, "bal.stor"), (memW post_j (ad + 8), "bal.reads")]))
      simpa only [List.append_assoc] using hinst
    refine ⟨pre_p, add_p, suf_p, ?_, ?_, ?_, ?_, ?_⟩
    · unfold worldRoleSlots
      rw [hnest_ts_p]
      have hts_roles_eq : (recRoles inner_post "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
          (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")]).filter (fun a => a.1 != 0) = add_p := by
        unfold recRoles
        rw [hpost_ts, if_neg hpw_nz]
        simp only [List.map, hmw_p8, hmw_p16, hmw_p24, hmw_p32, hmw_p40, hmw_p48, hmw_p56, hmw_p64]
        have hnz1 := htab_nonzero_of_wf hwf1_p
        have hnz2 := htab_nonzero_of_wf hwf2_p
        have hnz3 := htab_nonzero_of_wf hwf3_p
        have hnz4 := htab_nonzero_of_wf hwf4_p
        have hnz5 := htab_nonzero_of_wf hwf5_p
        have hnz6 := htab_nonzero_of_wf hwf6_p
        have hnz7 := htab_nonzero_of_wf hwf7_p
        have hnz8 := htab_nonzero_of_wf hwf8_p
        simp [add_p, hnz1, hnz2, hnz3, hnz4, hnz5, hnz6, hnz7, hnz8]
      simp only [List.filter_append, hts_roles_eq, List.filter_nil, List.append_nil]
      simp only [pre_p, suf_p, List.filter_append, List.append_assoc]
    · intro a ha; rw [← hwrs_pj]; exact hsub_pj.subset ha
    · have hpw_wrs : (worldRoleSlots post_j).Pairwise (fun a b => a.1 = b.1 → a.2 = b.2 ∧ a.2 ∈ sharedRoles) := by
        rw [hwrs_pj]; exact hT_s.2.2.2.2.2.2.2.2.2.2.2.2.1
      exact hpw_wrs.sublist hsub_pj
    · intro a ha
      simp only [add_p, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨by simp [T_new], (hhdr1_eq 0 (by omega)).trans (hhdr1.trans (show (20 : BitVec 64).toNat = roleKeyLen "ts+8" by decide))⟩
      · exact ⟨by simp [T_new], (hhdr2_eq 0 (by omega)).trans (hhdr2.trans (show (20 : BitVec 64).toNat = roleKeyLen "ts+16" by decide))⟩
      · exact ⟨by simp [T_new], (hhdr3_eq 0 (by omega)).trans (hhdr3.trans (show (52 : BitVec 64).toNat = roleKeyLen "ts+24" by decide))⟩
      · exact ⟨by simp [T_new], (hhdr4_eq 0 (by omega)).trans (hhdr4.trans (show (20 : BitVec 64).toNat = roleKeyLen "ts+32" by decide))⟩
      · exact ⟨by simp [T_new], (hhdr5_eq 0 (by omega)).trans (hhdr5.trans (show (52 : BitVec 64).toNat = roleKeyLen "ts+40" by decide))⟩
      · exact ⟨by simp [T_new], (hhdr6_eq 0 (by omega)).trans (hhdr6.trans (show (32 : BitVec 64).toNat = roleKeyLen "ts+48" by decide))⟩
      · exact ⟨by simp [T_new], (hhdr7_eq 0 (by omega)).trans (hhdr7.trans (show (20 : BitVec 64).toNat = roleKeyLen "ts+56" by decide))⟩
      · exact ⟨by simp [T_new], (hhdr8_eq 0 (by omega)).trans (hhdr8.trans (show (52 : BitVec 64).toNat = roleKeyLen "ts+64" by decide))⟩
    · have hpw_t : T_new.Pairwise (· ≠ ·) := List.nodup_iff_pairwise_ne.1 hT_nd
      have hmap_eq : T_new = add_p.map Prod.fst := rfl
      rw [hmap_eq] at hpw_t
      exact List.Pairwise.of_map Prod.fst (fun {a b} hne heq => absurd heq hne) hpw_t
  have hu_nd_rec : ∀ n ∈ Nd, M08IvlUnhit s inner_post (nodeIvl s n) :=
    fun n hn => hunhit_alloc _ (hTr_s.1.1 n hn).2.1
  have hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB inner_post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k) := by
    intro n hn h12 hlen0 k hk
    rcases (hTr_s.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_p, _, _⟩
    · exact absurd h0 hlen0
    · exact memB_eq_of_allocated_heap_sp0 hAR0.2 hAR9.2 hbe_post hal_p
        (fun j hj => ⟨globN s "scratch_ptr", hk_sp0 j hj, hsp8_s⟩)
        hfr_09 ⟨by dsimp; omega, by dsimp; omega⟩
  obtain ⟨_, hWT_post, hOG_post⟩ := tables_tries_adjoin_fresh hAR0 hAR9 hag
    ⟨hT_s, hJ_s, hF_s, hTr_s⟩ hF_post hfix_from
    hu_tab_s
    (fun hnz => hu_rec "ws" 40 (by decide) hnz)
    (fun hnz => hu_rec "bs" 80 (by decide) hnz)
    (fun hnz => hu_rec "bo" 88 (by decide) hnz)
    hu_bo_lst hu_nd_rec hu_nd_byte hm0 hws_g hbs_g hbo_g
    hT_nd hT_wf hT_pw hts_post hgr_post htsN_post hbal_post
    hroles_post hJ_post
  refine ⟨S ++ T_new, Nd, fun t ht => List.mem_append_left _ ht,
    hWT_post, hOG_post, ?_, trivial⟩
  exact frameOutside_sp0_to_world hAR0.2 hAR9.2 hhp_09 hk_sp0 hfr_09
  
end InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBal
