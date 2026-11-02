import InitECandidate.Solver.Wave8GuestInv.Deliveries.M23.EvmLemmas

/-! `ek_stack_pop`: `stack_pop` keeps `EvmInv`, `heap_ptr`, all globals (`gw = []`), and `evmChain`.
Checked against frozen spec revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`). -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace InitECandidate.Solver.Wave8Contracts.M23

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

private theorem lookup_stack_pop :
    originalRuntimeCode.lookup (ofString "stack_pop") =
      some ([], sourceFnBody Guest.Software.guestFn_stack_pop,
        .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 453 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_stack_pop) rfl

private theorem evalAt_loadG {F : Type} (t : PanSemStateFiniteExact 64 F) (g : String) (k : BitVec 64)
    (v : ValueHOL 64)
    (h : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.load .one (.op .add [.var .global (ofString g), .const k])) = some v) :
    ∃ a : BitVec 64, v = .val (.word a) ∧ a.toNat = memW t (globN t g + k.toNat) := by
  have hv : ∃ a : BitVec 64, v = .val (.word a) := by
    simp [evalHOLExact, evalListHOLExact] at h
    rcases hg : t.globals.lookup (ofString g) with _ | w
    · simp [hg] at h
    · rcases w with x | fs | ⟨nm, fs⟩
      · cases x with
        | word x =>
          simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
          rcases hm : t.memory (x + k) with ⟨y⟩
          exact ⟨y, by rw [← h.2, hm]⟩
      · simp [hg, valueIsWord] at h
      · simp [hg, valueIsWord] at h
  obtain ⟨a, rfl⟩ := hv
  refine ⟨a, rfl, ?_⟩
  simp [evalHOLExact, evalListHOLExact] at h
  rcases hg : t.globals.lookup (ofString g) with _ | w
  · simp [hg] at h
  · rcases w with x | fs | ⟨nm, fs⟩
    · cases x with
      | word x =>
        simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
        have hadd : BitVec.ofNat 64 (x.toNat + k.toNat) = x + k := by rw [BitVec.add_def]
        simp only [globN, memW, hg, hadd, h.2]
    · simp [hg, valueIsWord] at h
    · simp [hg, valueIsWord] at h

private theorem not_resumes_error : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

private theorem evmStep_refl_locals_clock {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s)
    (hpost : post = { s with locals := post.locals, clock := post.clock }) :
    EvmStep [] s post := by
  obtain ⟨hAs, S, hW, hrest⟩ := hInv
  have hInvAt : EvmInvAt s S := ⟨hW, hrest⟩
  obtain ⟨Nd_at, hTr_at, hAT_at⟩ := hInvAt.2.2.2.2.2.2.2.2.2.1
  have heff : ByteRegionEffect s post [] := by
    rw [hpost]
    exact (ByteRegionEffect.refl s []).with_locals_clock post.locals post.clock
  exact ByteRegionEffect.to_evmStep_nil_with hAs hInvAt hTr_at hAT_at
    (fun x hx => by simp at hx) heff

/-- `stack_pop` (AST line 15046): EVM step: `EvmInv`, `ev`/`cur_cont` and the frame chain kept. -/
theorem «ek_stack_pop» : EvmKeeps EvmInv [] (ofString "stack_pop") := by
  refine ⟨_, _, _, lookup_stack_pop, ?_⟩
  intro F s _hcode hInv _hlookup _hnt hres
  let retExp : ExpHOL 64 :=
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural
      (Exp.load (Shape.comb [Shape.one, Shape.one, Shape.one, Shape.one])
        (Exp.op BinOp.add [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.global "ev"), (Exp.const (BitVec.ofNat 64 8))])),
          (Exp.panOp PanOp.mul [(Exp.var VarKind.local "sp"), (Exp.const (BitVec.ofNat 64 32))])]))
  have hb : sourceFnBody Guest.Software.guestFn_stack_pop =
      .dec (ofString "sp") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 16]))
        (.seq
          (.ite (.cmp .equal (.var .local (ofString "sp")) (.const 0))
            (.raise (ofString "EvmErr") (.const 2))
            .skip)
          (.seq
            (.assign .local (ofString "sp") (.op .sub [.var .local (ofString "sp"), .const 1]))
            (.seq
              (.store (.op .add [.var .global (ofString "ev"), .const 16]) (.var .local (ofString "sp")))
              (.return retExp)))) := rfl
  rw [hb] at hres ⊢
  -- Extract `ev` global word from `EvmInv s` (`ev` is in `[scratch_ptr, scratchEnd)` so `> 0`!):
  have hev_pos : 0 < globN s "ev" := by
    obtain ⟨hAs, S, _, _, _, _, hFW_all, _⟩ := hInv
    have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
      unfold evmChain
      have hpos : ∃ m, Wave8GuestInv.maxChain + 1 = m + 1 := ⟨Wave8GuestInv.maxChain, rfl⟩
      obtain ⟨m, hm⟩ := hpos; rw [hm, evmChainFrom]; exact List.mem_cons_self
    have hin := ((hFW_all _ hhead_mem).1 (globN s "ev", 280) (by simp)).1
    have hsc := hAs.2.2.2.1
    have hgap := hAs.2.2.2.2.1
    rw [scratchStart_val] at hsc
    obtain ⟨hin1, _⟩ := hin
    dsimp only at hin1
    omega
  obtain ⟨ev, hev, hev_nat⟩ := global_word_of_pos s "ev" hev_pos
  -- Step 1: evaluate `.dec "sp"`
  rw [evaluateHOLFiniteState_dec_total] at hres ⊢
  dsimp only at hres ⊢
  revert hres
  split
  · intro hres; exact absurd hres not_resumes_error
  · rename_i vsp hload
    intro hres
    obtain ⟨sp, rfl, hsp_memW⟩ := evalAt_loadG s "ev" 16 vsp hload
    have h16_nat : (16 : BitVec 64).toNat = 16 := rfl
    rw [h16_nat] at hsp_memW
    have hsh_sp : shapeEqHOL .one (shapeOfHOLExact (ValueHOL.val (HolWordLab.word sp))) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hsh_sp] at hres ⊢
    dsimp only at hres ⊢
    set s1 := setVarHOLFinite (ofString "sp") (.val (.word sp)) s with hs1
    have hs1_sp : s1.locals.lookup (ofString "sp") = some (.val (.word sp)) := by
      simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    -- Step 2: `.seq (.ite (sp == 0) (raise EvmErr 2) skip) ...`
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres ⊢
    have hcmp_eval : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.cmp .equal (.var .local (ofString "sp")) (.const 0)) =
        some (.val (.word (if sp = 0 then 1 else 0))) := by
      simp [evalHOLExact, hs1_sp, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcmp_eval] at hres ⊢
    dsimp only at hres ⊢
    by_cases hsp0 : sp = 0
    · -- `sp = 0`: raises `EvmErr` (or errors), memory and globals are unchanged!
      subst hsp0
      have h10 : ((1 : BitVec 64) = 0) = False := by decide
      simp only [↓reduceIte, h10] at hres ⊢
      rcases hraise : evaluateHOLFiniteState s1 (.raise (ofString "EvmErr") (.const 2)) with ⟨rr, sr⟩
      have hraise_info : rr ≠ none ∧ sr = { s with locals := sr.locals, clock := sr.clock } := by
        rw [evaluateHOLFiniteState_raise] at hraise
        have he2 : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
            (.const 2) = some (.val (.word 2)) := rfl
        rw [he2] at hraise
        dsimp only at hraise
        split at hraise
        · split at hraise
          · injection hraise with hrr hsr; subst hrr hsr; exact ⟨by simp, rfl⟩
          · injection hraise with hrr hsr; subst hrr hsr; exact ⟨by simp, rfl⟩
        · injection hraise with hrr hsr; subst hrr hsr; exact ⟨by simp, rfl⟩
      cases rr with
      | none => exact absurd rfl hraise_info.1
      | some r' =>
        dsimp only
        refine evmStep_refl_locals_clock hInv ?_
        rcases hsr_eq : hraise_info.2 with _
        rw [hraise_info.2]
    · -- `sp ≠ 0`: falls through `.skip`, decrements `sp`, stores `sp - 1` at `ev + 16`, returns load!
      have hsp_pos : 0 < memW s (globN s "ev" + 16) := by
        rw [← hsp_memW]
        exact Nat.pos_of_ne_zero (fun hz => hsp0 (BitVec.eq_of_toNat_eq hz))
      have hif_cond : (if sp = 0 then (1 : BitVec 64) else 0) = 0 := if_neg hsp0
      rw [hif_cond] at hres ⊢
      simp only [↓reduceIte, evaluateHOLFiniteState_skip] at hres ⊢
      -- `.seq (.assign .local "sp" (sp - 1)) ...`
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hres ⊢
      have hsub_eval : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
          (.op .sub [.var .local (ofString "sp"), .const 1]) = some (.val (.word (sp - 1))) := by
        simp [evalHOLExact, evalListHOLExact, hs1_sp, valueIsWord, valueWord, wordOpHOL, wordOp]
      have hvalid_sp : s1.isValidValueHOLFinite .local (ofString "sp") (.val (.word (sp - 1))) = true := by
        simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hs1_sp, shapeOfHOLExact, shapeEqHOL]
      rw [hsub_eval] at hres ⊢
      dsimp only at hres ⊢
      rw [if_pos hvalid_sp] at hres ⊢
      dsimp only at hres ⊢
      set s2 := setKvarHOLFinite .local (ofString "sp") (.val (.word (sp - 1))) s1 with hs2
      have hs2_sp : s2.locals.lookup (ofString "sp") = some (.val (.word (sp - 1))) := by
        simp [hs2, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hs2_ev : s2.globals.lookup (ofString "ev") = some (.val (.word ev)) := hev
      -- `.seq (.store (ev + 16) sp) (.return ...)`
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store] at hres ⊢
      have hdst_eval : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
          (.op .add [.var .global (ofString "ev"), .const 16]) = some (.val (.word (ev + 16))) := by
        simp [evalHOLExact, evalListHOLExact, hs2_ev, valueIsWord, valueWord, wordOpHOL, wordOp]
      have hsrc_eval : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
          (.var .local (ofString "sp")) = some (.val (.word (sp - 1))) := hs2_sp
      rw [hdst_eval, hsrc_eval] at hres ⊢
      simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hres ⊢
      by_cases hdom : s.memaddrs (ev + 16)
      · have hs2_dom : s2.memaddrs (ev + 16) := hdom
        simp only [hs2_dom, ↓reduceIte] at hres ⊢
        set s3 : PanSemStateFiniteExact 64 F :=
          { s2 with memory := fun a => if a = ev + 16 then .word (sp - 1) else s2.memory a }
        have hret_mem_glob :
            let rpair := evaluateHOLFiniteState s3 (.return retExp)
            rpair.2 = { s with
              memory := fun a => if a = ev + 16 then .word (sp - 1) else s.memory a,
              locals := rpair.2.locals,
              clock := rpair.2.clock } := by
          dsimp only
          rw [evaluateHOLFiniteState_return]
          split
          · rfl
          · split <;> rfl
        have hsp1_nat : (sp - 1).toNat = memW s (globN s "ev" + 16) - 1 := by
          rw [BitVec.toNat_sub, hsp_memW]
          have : (1 : BitVec 64).toNat = 1 := rfl
          rw [this]; omega
        refine evmStep_of_head_sp_dec hInv hev hsp_pos hsp1_nat ?_
        change { (evaluateHOLFiniteState s3 (.return retExp)).2 with
            locals := (evaluateHOLFiniteState s3 (.return retExp)).2.locals.resVarEq
              (ofString "sp", s.locals.lookup (ofString "sp")) } = _
        rcases hrpair : evaluateHOLFiniteState s3 (.return retExp) with ⟨rr, sr⟩
        have hsr : sr = { s with
            memory := fun a => if a = ev + 16 then .word (sp - 1) else s.memory a,
            locals := sr.locals, clock := sr.clock } := by
          simpa [hrpair] using hret_mem_glob
        dsimp only
        conv_lhs => rw [hsr]
      · have hs2_dom : ¬ s2.memaddrs (ev + 16#64) := hdom
        simp [hs2_dom] at hres
        exact absurd hres not_resumes_error

end InitECandidate.Solver.Wave8Contracts.M23
