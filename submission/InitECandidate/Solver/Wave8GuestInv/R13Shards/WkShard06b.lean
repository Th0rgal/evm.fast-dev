import InitECandidate.Solver.Wave8GuestInv.ContractParts.C03
import InitECandidate.Solver.GuestTrapOutcomes
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M08.wk_memzero
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.RlpMemcpyLemmas
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.WorldFrame
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.StoreAllocHelpers
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.Common
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.TeNewSupport

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

namespace R13Wk06b

/-! ## 1. Master W1 lemma for fresh heap constructors (`R = []`, `gw = ["heap_ptr"]`) -/

private theorem mem_eq_of_bytes_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {a : BitVec 64}
    (ha_dom : ordinaryDomain a) (hbe : post.be = s.be)
    (hb : ∀ k : Nat, k < 8 → memB post (a.toNat + k) = memB s (a.toNat + k)) :
    post.memory a = s.memory a := by
  have hdom' := (M13.ordinaryDomain_iff a).mp ha_dom
  have ha_ord : a.toNat % 8 = 0 ∧ sourceBase ≤ a.toNat ∧ a.toNat < heapEnd := by
    rw [M13.sourceBase_val, M13.heapEnd_val]; omega
  have hhe_lt : heapEnd ≤ 2 ^ 64 := by rw [M13.heapEnd_val]; decide
  have ha_hi : a.toNat + 8 ≤ 2 ^ 64 := by omega
  rcases hp_m : post.memory a with ⟨wp⟩
  rcases hs_m : s.memory a with ⟨ws⟩
  congr 1
  apply BitVec.eq_of_toNat_eq
  have hbyte_val : ∀ k : Nat, k < 8 →
      (panGetByteHOL (BitVec.ofNat 64 (a.toNat + k)) wp s.be).toNat =
      (panGetByteHOL (BitVec.ofNat 64 (a.toNat + k)) ws s.be).toNat := by
    intro k hk
    have hal_eq : panByteAlignHOL (BitVec.ofNat 64 (a.toNat + k)) = a := by
      apply BitVec.eq_of_toNat_eq
      rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hbk := hb k hk
    unfold memB at hbk
    rw [hal_eq, hp_m, hs_m, hbe] at hbk
    exact hbk
  have hshift : ∀ (w : BitVec 64) (idx : Nat), idx < 8 →
      w.toNat / 256 ^ idx % 256 =
      (panGetByteHOL (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))) w s.be).toNat := by
    intro w idx hidx
    unfold panGetByteHOL
    change w.toNat / 256 ^ idx % 256 =
      (UInt8.ofNat (w.toNat / 256 ^ (if s.be then 8 - 1 - (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8
        else (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8) % 256)).toNat
    have hexp : (if s.be then 8 - 1 - (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8
        else (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8) = idx := by
      have hmod_lt : (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat =
          a.toNat + (if s.be then 7 - idx else idx) :=
        Nat.mod_eq_of_lt (by cases s.be <;> simp <;> omega)
      rw [hmod_lt]
      cases s.be <;> simp <;> omega
    rw [hexp, UInt8.toNat_ofNat']
    have h256 : (2 ^ 8 : Nat) = 256 := by decide
    rw [h256, Nat.mod_mod]
  have hpow_eq : ∀ idx : Nat, idx < 8 → wp.toNat / 256 ^ idx % 256 = ws.toNat / 256 ^ idx % 256 := by
    intro idx hidx
    rw [hshift wp idx hidx, hshift ws idx hidx]
    exact hbyte_val (if s.be then 7 - idx else idx) (by cases s.be <;> simp <;> omega)
  have hdecomp : ∀ n : Nat, n < 2 ^ 64 →
      n = (n / 256 ^ 0 % 256) +
          (n / 256 ^ 1 % 256) * 256 ^ 1 +
          (n / 256 ^ 2 % 256) * 256 ^ 2 +
          (n / 256 ^ 3 % 256) * 256 ^ 3 +
          (n / 256 ^ 4 % 256) * 256 ^ 4 +
          (n / 256 ^ 5 % 256) * 256 ^ 5 +
          (n / 256 ^ 6 % 256) * 256 ^ 6 +
          (n / 256 ^ 7 % 256) * 256 ^ 7 := by
    intro n hn; omega
  rw [hdecomp wp.toNat wp.isLt, hdecomp ws.toNat ws.isLt]
  rw [hpow_eq 0 (by omega), hpow_eq 1 (by omega), hpow_eq 2 (by omega), hpow_eq 3 (by omega),
      hpow_eq 4 (by omega), hpow_eq 5 (by omega), hpow_eq 6 (by omega), hpow_eq 7 (by omega)]

theorem worldOwned_in_old_or_fresh {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat}
    (_hs : ArenaOK s) (_hp : ArenaOK post)
    (hWT : WorldTypedWith s S Nd)
    (hOG : OwnedGrows s post (worldOwned s S Nd) (worldOwned post S Nd))
    {f : Ivl}
    (hf_disj_alloc : ∀ i : Ivl, Allocated s i → Disj f i)
    (hf_disj_owned : ∀ o ∈ worldOwned post S Nd,
      Inside o (globN s "heap_ptr") (globN post "heap_ptr") → Disj f o) :
    ∀ o ∈ worldOwned post S Nd, Disj f o := by
  intro o ho
  rcases hOG o ho with rfl | ⟨j, hj, hin_j⟩ | hfr
  · exact Or.inr (Or.inl rfl)
  · rcases InitECandidate.Solver.Wave8Contracts.M08.worldOwned_allocated hWT hj with hj0 | hal_j
    · exact Or.inr (Or.inl (by unfold Inside at hin_j; omega))
    · exact InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_right hin_j (hf_disj_alloc j hal_j)
  · exact hf_disj_owned o ho hfr

theorem worldStep_of_fresh_heap {F : Type}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hW : WorldOK s)
    (hA_post : ArenaReady post)
    (hh : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hG : GlobalsKept ["heap_ptr"] s post)
    (hbe : post.be = s.be)
    (hout_dom : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a)
    (hfr_heap : ∀ a : BitVec 64, ¬ CellHits a.toNat (heapFree s) → post.memory a = s.memory a)
    (hbyte_heap : ∀ b : Nat, b < 2 ^ 64 → ¬ InIvl b (heapFree s) → memB post b = memB s b)
    (hQ : ∀ S Nd, WorldTypedWith s S Nd →
      WorldTypedWith post S Nd →
      worldOwned post S Nd = worldOwned s S Nd →
      Q s r post S Nd) :
    WorldStep (fun _ => []) ["heap_ptr"] M13.stdKeep Q s r post := by
  have hglob_nhp : ∀ nm : String, ofString nm ≠ ofString "heap_ptr" →
      s.globals.lookup (ofString nm) = post.globals.lookup (ofString nm) := by
    intro nm hne
    apply hG
    simp only [List.map, List.mem_cons, List.not_mem_nil, or_false]
    exact hne
  have hsc_eq : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    (M13.globN_eq_of_lookup_eq (hglob_nhp "scratch_ptr" (by decide))).symm
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := le_of_eq hsc_eq
  have hfr_ext : FrameOutside s post (([] : List Ivl) ++ [InitECandidate.Solver.Wave8Contracts.M08.freeGap s])
      (InitECandidate.Solver.Wave8Contracts.M08.heapFree s) :=
    fun a _ hno_hf => hfr_heap a hno_hf
  have hRK : RecordsKept (fun _ => []) M13.stdKeep s post :=
    InitECandidate.Solver.Wave8Contracts.M08.recordsKept_of_free_writes
      (R := fun {F} (_ : PanSemStateFiniteExact 64 F) => []) hW hfr_ext
  refine ⟨hA_post, hh, hG, hRK, fun S Nd hWT _ => ?_⟩
  have hcell : M13.SameTypedCells s post S Nd := by
    refine ⟨hbe, hA_post.1.memaddrs.trans hW.1.1.memaddrs.symm, hW.1.1.memaddrs, ?_, ?_, ?_⟩
    · intro a hna
      apply hout_dom a
      rwa [hW.1.1.memaddrs]
    · intro a ha ha8 ⟨i, hi, ha1, ha2⟩
      by_cases hdom : ordinaryDomain (BitVec.ofNat 64 a)
      · have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
        apply mem_eq_of_bytes_eq hdom hbe
        intro k hk
        rw [hbit]
        apply hbyte_heap (a + k) (by omega)
        intro hbh
        rcases M13.worldTypedIvls_allocated hWT hi with hi0 | hal_i
        · omega
        · have hdj : Disj i (heapFree s) := M13.allocated_disj_heapFree hW.1.2 hal_i
          obtain ⟨_, _⟩ := hbh
          rcases hdj with h0 | h0 | h | h <;> omega
      · apply hout_dom
        rwa [hW.1.1.memaddrs]
    · intro b hb ⟨i, hi, hb1, hb2⟩
      apply hbyte_heap b hb
      intro hbh
      rcases M13.worldTypedIvls_allocated hWT hi with hi0 | hal_i
      · omega
      · have hdj : Disj i (heapFree s) := M13.allocated_disj_heapFree hW.1.2 hal_i
        obtain ⟨_, _⟩ := hbh
        rcases hdj with h0 | h0 | h | h <;> omega
  have hg_core : ∀ g ∈ M13.coreWorldGlobals, globN post g = globN s g := by
    intro g hg
    have hne : ofString g ≠ ofString "heap_ptr" := by revert g hg; decide
    exact (M13.globN_eq_of_lookup_eq (hglob_nhp g hne)).symm
  have hfeq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [M13.blockOutObjects_eq hW.1.2 hWT.2.2.1 hcell (hg_core "bo" (by decide)),
        M13.balObjects_eq hW.1.2 hWT.1 hWT.2.2.1 hcell (hg_core "bal_accounts" (by decide)),
        hg_core "journal" (by decide),
        hg_core "journal_cap" (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "heap_ptr" := by revert gn hgn; decide
    rw [(M13.globN_eq_of_lookup_eq (hglob_nhp gn.1 hne)).symm]
  have hFT_post := M13.fixedTyped_of_eq hA_post hWT.2.2.1 hh hsc hfeq
  obtain ⟨hWT_post, hOG⟩ := M13.worldTypedWith_congr_w1 hW.1 hA_post hh hsc hg_core hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hwo_eq : worldOwned post S Nd = worldOwned s S Nd := by
    unfold worldOwned
    have hfp_eq : S.flatMap (htabFootprint post) = S.flatMap (htabFootprint s) := by
      apply List.flatMap_congr
      intro t ht
      exact M13.htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1
    rw [hfp_eq, hfeq, M13.nodeExtents_eq hWT.2.2.2.1 hcell]
  refine ⟨S, Nd, fun _ h => h, hWT_post, hOG, ?_, hQ S Nd hWT hWT_post hwo_eq⟩
  intro a _ hno_hf
  exact hfr_heap a hno_hf

/-! ## 2. Allocator + `memzero` constructors: `wk_msg_new` and `wk_te_new` -/

theorem evaluate_call_trap_with_no_resumes {F : Type}
    (state : PanSemStateFiniteExact 64 F) (codeVal : BitVec 64)
    (hcode : state.code = originalRuntimeCode) :
    ¬ Resumes (evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "trap_with") [.const codeVal])).1 := by
  rw [evaluateHOLFiniteState_call]
  have hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const codeVal] =
      some [.val (.word codeVal)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hlookup := pan_one_word_lookup state.code.lookup (ofString "trap_with") (ofString "code")
    (sourceFnBody Guest.Software.guestFn_trap_with) codeVal (by rw [hcode]; exact lookup_trap_with)
  rw [hargs]; dsimp only; rw [hlookup]; dsimp only
  split
  · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h
  · have hout := evaluate_trap_with_body_outcomes
      (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
    rcases hbody : evaluateHOLFiniteState
      (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
      (sourceFnBody Guest.Software.guestFn_trap_with) with ⟨res, st⟩
    rw [hbody] at hout
    cases res with
    | none => exact absurd rfl hout.1
    | some r =>
      cases r with
      | returned v => exact absurd rfl (hout.2.1 v)
      | exception eid ev =>
        rintro (⟨_, h⟩ | ⟨e', v', h, hne⟩)
        · simp at h
        · simp at h; obtain ⟨rfl, rfl⟩ := h; exact hout.2.2 eid ev hne rfl
      | «break» | «continue» | error | timeOut | finalFfi _ =>
        rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h

theorem alloc_body_resumes {F : Type}
    (state : PanSemStateFiniteExact 64 F) (p n : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hp_lookup : state.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (hres : Resumes (evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_alloc)).1) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_alloc)
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    out.1 = some (.returned (.val (.word p))) ∧
    ¬ ((cMax - p).toNat < n.toNat) ∧ ¬ (cMax.toNat < q.toNat) ∧
    out.2 = { state with
      globals := state.globals.update (ofString "heap_ptr", .val (.word q))
      locals := out.2.locals
      clock := out.2.clock } := by
  dsimp only
  have hbody_eq : sourceFnBody Guest.Software.guestFn_alloc =
      .dec (ofString "p") .one (.var .global (ofString "heap_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1])
                .skip)
              (.seq
                (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "p"))))))) := rfl
  rw [hbody_eq, evaluateHOLFiniteState_dec_total] at hres ⊢
  have hp_eval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp_lookup
  dsimp only at hres ⊢; rw [hp_eval] at hres ⊢
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only at hres ⊢; rw [if_pos hsh_p] at hres ⊢; dsimp only at hres ⊢
  let pState := setVarHOLFinite (ofString "p") (.val (.word p)) state
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "p" ≠ ofString "n" by decide]
  rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
  have hev1 : @evalHOLExact 64 F _ pState.toExact
      (fun a => Classical.propDecidable (pState.memaddrs a))
      (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
        (.var .local (ofString "n"))) =
      some (.val (.word (if (cMax - p).toNat < n.toNat then 1 else 0))) := by
    simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
      Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]; rfl
  by_cases hcmp1 : (cMax - p).toNat < n.toNat
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) =
        evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1]; simp
    rw [hite1] at hres
    have hno_none := evaluate_call_trap_with_no_none pState 1 hcode
    have hno_res := evaluate_call_trap_with_no_resumes pState 1 hcode
    rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r1, s1⟩
    rw [htr] at hno_none hno_res hres
    cases r1 with
    | none => exact absurd rfl hno_none
    | some _ => exact False.elim (hno_res hres)
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) = (none, pState) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
    rw [hite1] at hres ⊢; dsimp only at hres ⊢
    rw [evaluateHOLFiniteState_dec_total] at hres ⊢
    let q : BitVec 64 := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    have hq_eval : @evalHOLExact 64 F _ pState.toExact
        (fun a => Classical.propDecidable (pState.memaddrs a))
        (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
          .op .sub [.const 0, .const 8]]) = some (.val (.word q)) := by
      simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
        wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
      exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w))) (alloc_q_word_eq p n)
    dsimp only at hres ⊢; rw [hq_eval] at hres ⊢
    have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word q))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    dsimp only at hres ⊢; rw [if_pos hsh_q] at hres ⊢; dsimp only at hres ⊢
    let qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
    have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hp_loc_q : qState.locals.lookup (ofString "p") = some (.val (.word p)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_loc,
        show ofString "q" ≠ ofString "p" by decide]
    rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
    have hev2 : @evalHOLExact 64 F _ qState.toExact
        (fun a => Classical.propDecidable (qState.memaddrs a))
        (.cmp .lower (.const cMax) (.var .local (ofString "q"))) =
        some (.val (.word (if cMax.toNat < q.toNat then 1 else 0))) := by
      simp only [evalHOLExact, hq_loc, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    by_cases hcmp2 : cMax.toNat < q.toNat
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) =
          evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_pos hcmp2]; simp
      rw [hite2] at hres
      have hno_none := evaluate_call_trap_with_no_none qState 1 hcode
      have hno_res := evaluate_call_trap_with_no_resumes qState 1 hcode
      rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r2, s2⟩
      rw [htr] at hno_none hno_res hres
      cases r2 with
      | none => exact absurd rfl hno_none
      | some _ => exact False.elim (hno_res hres)
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) = (none, qState) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_neg hcmp2]; simp [evaluateHOLFiniteState_skip]
      rw [hite2]; dsimp only
      have hp_g : qState.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) := hp_lookup
      have heval_end : evaluateHOLFiniteState qState
          (.seq (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
            (.return (.var .local (ofString "p")))) =
          (some (.returned (.val (.word p))),
            emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word q)) qState)) := by
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
        simp [evalHOLExact, hq_loc, hp_loc_q, isValidValueHOLExact, lookupKvarHOLExact, hp_g,
          shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
          evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
      rw [heval_end]
      exact ⟨rfl, hcmp1, hcmp2, rfl⟩

theorem decCall_alloc_resumes {F : Type}
    {s : PanSemStateFiniteExact 64 F} {x : MlS} {arg : ExpHOL 64} {cont : ProgHOL 64}
    (hcode : s.code = originalRuntimeCode)
    (hp nv : BitVec 64)
    (hhp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word hp)))
    (harg : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [arg] =
      some [.val (.word nv)])
    (hres : Resumes (evaluateHOLFiniteState s (.decCall x .one (ofString "alloc") [arg] cont)).1) :
    let q := (hp + (nv + 7)) &&& ((0 : BitVec 64) - 8)
    ¬ ((cMax - hp).toNat < nv.toNat) ∧ ¬ (cMax.toNat < q.toNat) ∧
    ∃ (pa : PanSemStateFiniteExact 64 F),
      pa = { s with
        globals := s.globals.update (ofString "heap_ptr", .val (.word q))
        locals := pa.locals
        clock := pa.clock } ∧
      let s1 := setVarHOLFinite x (.val (.word hp)) { pa with locals := s.locals }
      Resumes (evaluateHOLFiniteState s1 cont).1 ∧
      (evaluateHOLFiniteState s (.decCall x .one (ofString "alloc") [arg] cont)).1 =
        (evaluateHOLFiniteState s1 cont).1 ∧
      (evaluateHOLFiniteState s (.decCall x .one (ofString "alloc") [arg] cont)).2 =
        { (evaluateHOLFiniteState s1 cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s1 cont).2.locals (x, s.locals.lookup x) } := by
  dsimp only
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite, harg] at hres ⊢
  dsimp only at hres ⊢
  have hlk := pan_one_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_alloc) nv
    (by rw [hcode]; exact InitECandidate.Solver.Wave8Contracts.M27.lookup_alloc_te)
  rw [hlk] at hres ⊢; dsimp only at hres ⊢
  by_cases hclk : s.clock = 0
  · rw [if_pos hclk] at hres; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
  · rw [if_neg hclk] at hres ⊢
    let entry := callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv)))
    have hn_ent : entry.locals.lookup (ofString "n") = some (.val (.word nv)) := by
      simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases haRun : evaluateHOLFiniteState (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv))))
        (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ra, pa⟩
    simp only [haRun] at hres ⊢
    have hra_res : Resumes ra := by
      cases ra with
      | none => rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      | some r =>
        cases r with
        | returned v => exact Or.inl ⟨v, rfl⟩
        | exception eid ev =>
          rcases hres with ⟨_, h⟩ | ⟨e', v', h, hne⟩
          · simp at h
          · simp at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨eid, ev, rfl, hne⟩
        | _ => rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
    obtain ⟨hra_eq, hcmp1, hcmp2, hpa_eq⟩ := alloc_body_resumes entry hp nv hcode hhp hn_ent
      (by dsimp only [entry]; rw [haRun]; exact hra_res)
    dsimp only [entry] at hra_eq hpa_eq
    rw [haRun] at hra_eq hpa_eq
    dsimp only at hra_eq hpa_eq
    subst hra_eq
    dsimp only at hres ⊢
    have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word hp) : ValueHOL 64)) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word hp) : ValueHOL 64)) .one) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hsh] at hres ⊢
    refine ⟨hcmp1, hcmp2, pa, ?_, ?_⟩
    · rw [hpa_eq]; rfl
    · rcases hcont : evaluateHOLFiniteState (setVarHOLFinite x (.val (.word hp)) { pa with locals := s.locals }) cont with ⟨rc, inner⟩
      simp only [hcont] at hres ⊢
      exact ⟨hres, trivial, trivial⟩

/-- Shared constructor `WorldStep` for `x := alloc(sz); memzero(x, sz); return x` where `sz % 8 = 0`. -/
theorem alloc_memzero_return_worldStep {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x : MlS) (sz : BitVec 64)
    (hsz8 : sz.toNat % 8 = 0) (_hsz_pos : 0 < sz.toNat) (_hsz_lt : sz.toNat < 1024)
    (hcode : s.code = originalRuntimeCode) (hWOK : WorldOK s)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall x .one (ofString "alloc") [.const sz]
        (.seq (.call (some (none, none)) (ofString "memzero") [.var .local x, .const sz])
          (.return (.var .local x))))).1) :
    let out := evaluateHOLFiniteState s
      (.decCall x .one (ofString "alloc") [.const sz]
        (.seq (.call (some (none, none)) (ofString "memzero") [.var .local x, .const sz])
          (.return (.var .local x))))
    WorldStep (fun _ => []) ["heap_ptr"] M13.stdKeep
      (RetAvoids (fun _ _ w => [(w, sz.toNat)])) s out.1 out.2 := by
  dsimp only
  obtain ⟨hp, _, _, hhp, hhp_eq, _, _, _, _⟩ := Wave8Contracts.M26.arenaOK_globals s hWOK.1.2
  have harg : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.const sz] =
      some [.val (.word sz)] := by
    rw [evalListHOLFinite_eq_toExact]; rfl
  obtain ⟨hcmp1, hcmp2, pa, hpa_eq, hres1, heq_r, heq_p⟩ :=
    decCall_alloc_resumes (x := x) hcode hp sz hhp harg hres
  set q : BitVec 64 := (hp + (sz + 7)) &&& ((0 : BitVec 64) - 8)
  have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hWOK.1.2.2.1
  have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hWOK.1.2.2.2.2.2.2.1
  obtain ⟨hq_eq, hq_hi, hq_al, hp_le_q⟩ := Wave8Contracts.M26.alloc_arith hp sz hhp_hi hhp_al hcmp1 hcmp2
  change q.toNat = _ at hq_eq
  change q.toNat ≤ heapLimit at hq_hi
  change q.toNat % 8 = 0 at hq_al
  change hp.toNat ≤ q.toNat at hp_le_q
  have hround : (sz.toNat + 7) / 8 * 8 = sz.toNat := by omega
  rw [hround] at hq_eq
  let s1 := setVarHOLFinite x (.val (.word hp)) { pa with locals := s.locals }
  have hs1_x : s1.locals.lookup x = some (.val (.word hp)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_code : s1.code = originalRuntimeCode := by
    have : pa.code = s.code := by rw [hpa_eq]
    exact this.trans hcode
  have hs1_G : GuestInv s1 := by
    have hpa_G : GuestInv pa := guestInv_congr (by rw [hpa_eq]) (by rw [hpa_eq]) (by rw [hpa_eq]) (by rw [hpa_eq]) hWOK.1.1
    exact guestInv_setVar x _ _ (guestInv_with_locals_clock pa s.locals pa.clock hpa_G)
  rw [evaluateHOLFiniteState_seq_line780] at hres1
  rcases hmzCall : evaluateHOLFiniteState s1
      (.call (some (none, none)) (ofString "memzero") [.var .local x, .const sz]) with ⟨rmz, pmz⟩
  rw [hmzCall] at hres1
  -- Unpack `memzero` call: if `rmz = some _`, since `memzero` never raises a non-TrapErr exception and void call never returns `returned`, `Resumes rmz` is impossible!
  have hargs_mz : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
      [.var .local x, .const sz] = some [.val (.word hp), .val (.word sz)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact, evalHOLExact, hs1_x]
  have hmzCall' := hmzCall
  rw [evaluateHOLFiniteState_call, hargs_mz] at hmzCall'
  dsimp only at hmzCall'
  have hl_mz := pan_two_word_lookup s1.code.lookup (ofString "memzero")
    (ofString "dst") (ofString "n") (sourceFnBody Guest.Software.guestFn_memzero)
    hp sz (by decide) (by rw [hs1_code]; exact InitECandidate.Solver.Wave8Contracts.M27.lookup_memzero)
  rw [hl_mz] at hmzCall'; dsimp only at hmzCall'
  split at hmzCall'
  · injection hmzCall' with hr_eq _
    subst hr_eq
    rcases hres1 with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
  · let mzEntry := callEntryStateHOLFinite s1
      ((HolFiniteMapExact.empty.update (ofString "dst", .val (.word hp))).update (ofString "n", .val (.word sz)))
    have hmz_G : GuestInv mzEntry := guestInv_callEntry s1 _ hs1_G
    have hmz_dst : locN mzEntry "dst" = hp.toNat := by
      simp [locN, mzEntry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "dst" by decide]
    have hmz_n : locN mzEntry "n" = sz.toNat := by
      simp [locN, mzEntry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hmzBody : evaluateHOLFiniteState mzEntry (sourceFnBody Guest.Software.guestFn_memzero) with ⟨rb, smz⟩
    have hmzBody' : evaluateHOLFiniteState
        (callEntryStateHOLFinite s1
          ((HolFiniteMapExact.empty.update (ofString "dst", .val (.word hp))).update (ofString "n", .val (.word sz))))
        (sourceFnBody Guest.Software.guestFn_memzero) = (rb, smz) := hmzBody
    rw [hmzBody'] at hmzCall'
    have hrb_res : Resumes rb := by
      cases rb with
      | none =>
        dsimp only at hmzCall'
        injection hmzCall' with hr_eq _
        subst hr_eq
        rcases hres1 with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      | some r =>
        cases r with
        | returned v => exact Or.inl ⟨v, rfl⟩
        | exception eid ev =>
          dsimp only at hmzCall'; injection hmzCall' with hr_eq _
          subst hr_eq
          rcases hres1 with ⟨_, h⟩ | ⟨e', v', h, hne⟩
          · simp at h
          · simp at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨eid, ev, rfl, hne⟩
        | _ =>
          dsimp only at hmzCall'
          injection hmzCall' with hr_eq _
          subst hr_eq
          rcases hres1 with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
    have hframe := InitECandidate.Solver.Wave8Contracts.M08.memzero_body_frame mzEntry hs1_code hmz_G
      (by rw [hmzBody]; exact hrb_res)
    rw [hmzBody, hmz_dst, hmz_n] at hframe
    dsimp only [InitECandidate.Solver.Wave8Contracts.M08.RegionWriteFrame] at hframe
    -- Extract common post-state properties from `hframe : RegionWriteFrame mzEntry smz (hp.toNat, sz.toNat)`
    have hsmz_pa : smz.globals = pa.globals ∧ smz.be = s.be ∧
        smz.code = s.code ∧ smz.memaddrs = s.memaddrs ∧
        smz.shMemaddrs = s.shMemaddrs ∧ smz.baseAddr = s.baseAddr ∧
        (∀ a : BitVec 64, ¬ s.memaddrs a → smz.memory a = s.memory a) ∧
        (∀ a : BitVec 64, ¬ CellHits a.toNat (heapFree s) → smz.memory a = s.memory a) ∧
        (∀ b : Nat, b < 2 ^ 64 → ¬ InIvl b (heapFree s) → memB smz b = memB s b) := by
      obtain ⟨hc_mz, hma_mz, hsh_mz, hba_mz, hbe_mz, hg_mz, hfr_mz, hby_mz, hdwr_mz⟩ := hframe
      have hm_ent : mzEntry.memory = s.memory := by dsimp [mzEntry, callEntryStateHOLFinite, s1, setVarHOLFinite]; rw [hpa_eq]
      have hma_ent : mzEntry.memaddrs = s.memaddrs := by dsimp [mzEntry, callEntryStateHOLFinite, s1, setVarHOLFinite]; rw [hpa_eq]
      have hbe_ent : mzEntry.be = s.be := by dsimp [mzEntry, callEntryStateHOLFinite, s1, setVarHOLFinite]; rw [hpa_eq]
      refine ⟨hg_mz, hbe_mz.trans hbe_ent,
        hc_mz.trans (by dsimp [mzEntry, callEntryStateHOLFinite, s1, setVarHOLFinite]; rw [hpa_eq]),
        hma_mz.trans hma_ent,
        hsh_mz.trans (by dsimp [mzEntry, callEntryStateHOLFinite, s1, setVarHOLFinite]; rw [hpa_eq]),
        hba_mz.trans (by dsimp [mzEntry, callEntryStateHOLFinite, s1, setVarHOLFinite]; rw [hpa_eq]),
        ?_, ?_, ?_⟩
      · intro a hna
        by_contra hne
        rw [← hm_ent] at hne
        have := hdwr_mz a hne
        rw [hma_ent] at this
        exact hna this
      · intro a hno_hf
        rw [← hm_ent]
        apply hfr_mz a
        · intro i hi hch
          simp only [List.mem_singleton] at hi; subst hi
          apply hno_hf
          unfold heapFree CellHits at *
          dsimp only at *
          omega
        · intro hch; unfold CellHits at hch; omega
      · intro b hb_lt hno_hf
        have h1 := hby_mz b hb_lt (fun hin => hno_hf (by
          unfold heapFree InIvl at *; dsimp only at *; omega))
        have h2 : memB mzEntry b = memB s b := by unfold memB; rw [hm_ent, hbe_ent]
        exact h1.trans h2
    -- Now extract `(r_fin, post)` of `evaluateHOLFiniteState s1 (seq (call ...) (return ...))`
    have hfin : (∃ e v, (evaluateHOLFiniteState s1
        (.seq (.call (some (none, none)) (ofString "memzero") [.var .local x, .const sz])
          (.return (.var .local x)))).1 = some (.exception e v)) ∨
        (evaluateHOLFiniteState s1
        (.seq (.call (some (none, none)) (ofString "memzero") [.var .local x, .const sz])
          (.return (.var .local x)))).1 = some (.returned (.val (.word hp))) := by
      rw [evaluateHOLFiniteState_seq_line780, hmzCall]
      cases rmz with
      | some rmz_val =>
        dsimp only
        rcases hres1 with ⟨v, hv⟩ | ⟨e, v, hv, _⟩
        · exfalso
          have hnr := InitECandidate.Solver.Wave8Contracts.M27.call_void_noret_te s1 (ofString "memzero") [.var .local x, .const sz] v
          rw [hmzCall] at hnr; exact hnr hv
        · exact Or.inl ⟨e, v, hv⟩
      | none =>
        dsimp only
        have hpmz_x : pmz.locals.lookup x = some (.val (.word hp)) := by
          cases rb with
          | none => simp at hmzCall'
          | some r =>
            cases r with
            | returned v =>
              dsimp only at hmzCall'; split at hmzCall'
              · injection hmzCall' with _ hp_eq; subst hp_eq; exact hs1_x
              · simp at hmzCall'
            | _ => simp at hmzCall'
        rw [evaluateHOLFiniteState_return]
        simp [evalHOLExact, hpmz_x, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    have hpost_smz :
        let post := (evaluateHOLFiniteState s
          (.decCall x .one (ofString "alloc") [.const sz]
            (.seq (.call (some (none, none)) (ofString "memzero") [.var .local x, .const sz])
              (.return (.var .local x))))).2
        post.memory = smz.memory ∧ post.globals = pa.globals ∧ post.be = s.be ∧
        post.code = s.code ∧ post.memaddrs = s.memaddrs ∧
        post.shMemaddrs = s.shMemaddrs ∧ post.baseAddr = s.baseAddr := by
      dsimp only
      rw [heq_p]
      have hinner :
          let inner := (evaluateHOLFiniteState s1
            (.seq (.call (some (none, none)) (ofString "memzero") [.var .local x, .const sz])
              (.return (.var .local x)))).2
          inner.memory = smz.memory ∧ inner.globals = smz.globals ∧ inner.be = smz.be ∧
          inner.code = smz.code ∧ inner.memaddrs = smz.memaddrs ∧
          inner.shMemaddrs = smz.shMemaddrs ∧ inner.baseAddr = smz.baseAddr := by
        dsimp only
        rw [evaluateHOLFiniteState_seq_line780, hmzCall]
        have hpmz : pmz.memory = smz.memory ∧ pmz.globals = smz.globals ∧ pmz.be = smz.be ∧
            pmz.code = smz.code ∧ pmz.memaddrs = smz.memaddrs ∧
            pmz.shMemaddrs = smz.shMemaddrs ∧ pmz.baseAddr = smz.baseAddr := by
          cases rb with
          | none =>
            dsimp only at hmzCall'
            injection hmzCall' with hr_eq _
            subst hr_eq
            rcases hres1 with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
          | some r =>
            cases r with
            | returned v =>
              dsimp only at hmzCall'; split at hmzCall'
              · injection hmzCall' with _ hp_eq; subst hp_eq; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
              · injection hmzCall' with _ hp_eq; subst hp_eq; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            | _ =>
              dsimp only at hmzCall'; injection hmzCall' with _ hp_eq; subst hp_eq
              exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        cases rmz with
        | some _ => exact hpmz
        | none =>
          dsimp only
          have hpmz_x : pmz.locals.lookup x = some (.val (.word hp)) := by
            cases rb with
            | none => simp at hmzCall'
            | some r =>
              cases r with
              | returned v =>
                dsimp only at hmzCall'; split at hmzCall'
                · injection hmzCall' with _ hp_eq; subst hp_eq; exact hs1_x
                · simp at hmzCall'
              | _ => simp at hmzCall'
          rw [evaluateHOLFiniteState_return]
          simp only [evalHOLExact, hpmz_x, shapeOfHOLExact, sizeOfShapeWithContextHOL,
            Nat.reduceLeDiff, ↓reduceIte, emptyLocalsHOLFinite]
          exact hpmz
      dsimp only at hinner ⊢
      exact ⟨hinner.1, hinner.2.1.trans hsmz_pa.1, hinner.2.2.1.trans hsmz_pa.2.1,
        hinner.2.2.2.1.trans hsmz_pa.2.2.1, hinner.2.2.2.2.1.trans hsmz_pa.2.2.2.1,
        hinner.2.2.2.2.2.1.trans hsmz_pa.2.2.2.2.1, hinner.2.2.2.2.2.2.trans hsmz_pa.2.2.2.2.2.1⟩
    set out := evaluateHOLFiniteState s
      (.decCall x .one (ofString "alloc") [.const sz]
        (.seq (.call (some (none, none)) (ofString "memzero") [.var .local x, .const sz])
          (.return (.var .local x))))
    have hpa_glob : pa.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) := by
      rw [hpa_eq]
    have hout_glob : out.2.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) :=
      hpost_smz.2.1.trans hpa_glob
    have hhp_post : globN out.2 "heap_ptr" = q.toNat := by
      unfold globN; rw [hout_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hfp_post : globN out.2 "frame_mem_ptr" = globN s "frame_mem_ptr" := by
      unfold globN; rw [hout_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
    have hsp_post : globN out.2 "scratch_ptr" = globN s "scratch_ptr" := by
      unfold globN; rw [hout_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
    have hG_post : GuestInv out.2 :=
      guestInv_congr hpost_smz.2.2.2.1 hpost_smz.2.2.2.2.1 hpost_smz.2.2.2.2.2.1 hpost_smz.2.2.2.2.2.2 hWOK.1.1
    have hA_post : ArenaReady out.2 := by
      refine ⟨hG_post, ?_⟩
      unfold ArenaOK
      rw [hhp_post, hfp_post, hsp_post]
      have hAs := hWOK.1.2
      have hsb_lo : sourceBase ≤ hp.toNat := by rw [hhp_eq]; exact hAs.1
      exact ⟨by omega, hq_hi, hAs.2.2.1, hAs.2.2.2.1, hAs.2.2.2.2.1,
        hq_al, hAs.2.2.2.2.2.2.1, hAs.2.2.2.2.2.2.2.1,
        globalsWord_update (ofString "heap_ptr") q hout_glob hAs.2.2.2.2.2.2.2.2⟩
    have hGK : GlobalsKept ["heap_ptr"] s out.2 := by
      intro k hk
      simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hk
      have hbeq : (ofString "heap_ptr" == k) = false := beq_eq_false_iff_ne.2 (Ne.symm hk)
      simp [hout_glob, HolFiniteMapExact.lookup_update, FUPDATE, hbeq]
    refine worldStep_of_fresh_heap hWOK hA_post (by rw [hhp_post, ← hhp_eq]; exact hp_le_q)
      hGK hpost_smz.2.2.1
      (fun a hna => by rw [hpost_smz.1]; exact hsmz_pa.2.2.2.2.2.2.1 a hna)
      (fun a hno => by rw [hpost_smz.1]; exact hsmz_pa.2.2.2.2.2.2.2.1 a hno)
      (fun b hb hno => by
        have hmb : memB out.2 b = memB smz b := by unfold memB; rw [hpost_smz.1, hpost_smz.2.2.1, hsmz_pa.2.1]
        rw [hmb]; exact hsmz_pa.2.2.2.2.2.2.2.2 b hb hno)
      (fun S Nd hWT _ hwo_eq => ?_)
    intro v hv
    have hout1_eq : out.1 = (evaluateHOLFiniteState s1
        (.seq (.call (some (none, none)) (ofString "memzero") [.var .local x, .const sz])
          (.return (.var .local x)))).1 := heq_r
    rw [hout1_eq] at hv
    rcases hfin with ⟨e, ve, hexn⟩ | hret_hp
    · rw [hexn] at hv; simp at hv
    · rw [hret_hp] at hv
      injection hv with hv'; injection hv' with hv''; subst hv''
      refine ⟨hp, rfl, fun ivl hivl o ho => ?_⟩
      simp only [List.mem_singleton] at hivl; subst hivl
      rw [hwo_eq] at ho
      rcases InitECandidate.Solver.Wave8Contracts.M08.worldOwned_allocated hWT ho with ho0 | hal_o
      · exact Or.inr (Or.inl ho0)
      · exact InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap hWOK.1.2 hA_post.2 hal_o
          ⟨by dsimp; omega, by dsimp; rw [hhp_post]; omega⟩

theorem store_word_resumes_step {F : Type}
    {s : PanSemStateFiniteExact 64 F} {d e : ExpHOL 64} {rest : ProgHOL 64}
    (a w : BitVec 64)
    (hd : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) d = some (.val (.word a)))
    (he : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e = some (.val (.word w)))
    (hres : Resumes (evaluateHOLFiniteState s (.seq (.store d e) rest)).1) :
    s.memaddrs a ∧
    evaluateHOLFiniteState s (.seq (.store d e) rest) =
      evaluateHOLFiniteState { s with memory := Wave8Contracts.M26.updW s.memory a w } rest := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store, hd, he] at hres ⊢
  by_cases hdom : s.memaddrs a
  · refine ⟨hdom, ?_⟩
    simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom, ↓reduceIte]
    rfl
  · exfalso
    simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom, ↓reduceIte] at hres
    rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

theorem decCall_arg_some_resumes {F : Type} (s : PanSemStateFiniteExact 64 F)
    (x fname : MlS) (arg : ExpHOL 64) (cont : ProgHOL 64)
    (hres : Resumes (evaluateHOLFiniteState s (.decCall x .one fname [arg] cont)).1) :
    ∃ vals, evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [arg] =
      some vals := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hres
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [arg] with _ | vals
  · rw [ha] at hres; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
  · exact ⟨vals, rfl⟩

theorem eval_panop_mul_words {F : Type}
    (s : PanSemStateFiniteExact 64 F) (e1 e2 : ExpHOL 64)
    (hret_or_some : ∃ vals, evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) [.panop .mul [e1, e2]] = some vals) :
    ∃ w1 w2 : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 = some (.val (.word w1)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 = some (.val (.word w2)) ∧
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.panop .mul [e1, e2]] =
        some [.val (.word (w1 * w2))] := by
  obtain ⟨vals, hvals⟩ := hret_or_some
  rw [evalListHOLFinite_eq_toExact] at hvals
  simp only [evalListHOLExact] at hvals
  rcases hev : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) (.panop .mul [e1, e2]) with _ | mv
  · rw [hev] at hvals; cases hvals
  · simp only [evalHOLExact, evalListHOLExact] at hev
    rcases he1 : @evalHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
    · rw [he1] at hev; cases hev
    · rcases he2 : @evalHOLExact 64 F _ s.toExact
          (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | v2
      · rw [he1, he2] at hev; cases hev
      · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _
        · exact ⟨w1, w2, rfl, rfl, by
            rw [evalListHOLFinite_eq_toExact]
            simp [evalListHOLExact, evalHOLExact, he1, he2, valueIsWord, valueWord, panOpHOL]⟩
        all_goals (rw [he1, he2] at hev; simp [List.all, valueIsWord] at hev)

theorem lst_new_worldStep {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hWOK : WorldOK s)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_lst_new)).1) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_lst_new)
    WorldStep (fun _ => []) ["heap_ptr"] M13.stdKeep
      (RetAvoidsIf (fun s => locN s "esz" * locN s "cap" < 2 ^ 64)
        (fun s post w => [(w, 24), (memW post w, locN s "esz" * locN s "cap")])) s out.1 out.2 := by
  dsimp only
  obtain ⟨hp, _, _, hhp, hhp_eq, _, _, _, _⟩ := Wave8Contracts.M26.arenaOK_globals s hWOK.1.2
  have hbody : sourceFnBody Guest.Software.guestFn_lst_new =
      .decCall (ofString "l") .one (ofString "alloc") [.const 24]
        (.decCall (ofString "p") .one (ofString "alloc")
          [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")]]
          (.seq (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "p")))
            (.seq (.store (.op .add [.var .local (ofString "l"), .const 8]) (.const 0))
              (.seq (.store (.op .add [.var .local (ofString "l"), .const 16]) (.var .local (ofString "cap")))
                (.return (.var .local (ofString "l"))))))) := rfl
  rw [hbody] at hres ⊢
  have harg1 : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.const 24] =
      some [.val (.word 24)] := by
    rw [evalListHOLFinite_eq_toExact]; rfl
  obtain ⟨hcmp1_1, hcmp2_1, pa1, hpa1_eq, hres1, heq_r1, heq_p1⟩ :=
    decCall_alloc_resumes (x := ofString "l") hcode hp 24 hhp harg1 hres
  set q1 : BitVec 64 := (hp + (24 + 7)) &&& ((0 : BitVec 64) - 8)
  have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hWOK.1.2.2.1
  have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hWOK.1.2.2.2.2.2.2.1
  obtain ⟨hq1_eq, hq1_hi, hq1_al, hp_le_q1⟩ := Wave8Contracts.M26.alloc_arith hp 24 hhp_hi hhp_al hcmp1_1 hcmp2_1
  change q1.toNat = _ at hq1_eq
  change q1.toNat ≤ heapLimit at hq1_hi
  change q1.toNat % 8 = 0 at hq1_al
  change hp.toNat ≤ q1.toNat at hp_le_q1
  have h24 : ((24 : BitVec 64).toNat + 7) / 8 * 8 = 24 := by decide
  rw [h24] at hq1_eq
  let s1 := setVarHOLFinite (ofString "l") (.val (.word hp)) { pa1 with locals := s.locals }
  have hs1_code : s1.code = originalRuntimeCode := by
    have : pa1.code = s.code := by rw [hpa1_eq]
    exact this.trans hcode
  have hs1_hp : s1.globals.lookup (ofString "heap_ptr") = some (.val (.word q1)) := by
    change pa1.globals.lookup _ = _; rw [hpa1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨w_esz, w_cap, hesz1, hcap1, harg2⟩ :=
    eval_panop_mul_words s1 (.var .local (ofString "esz")) (.var .local (ofString "cap"))
      (decCall_arg_some_resumes s1 _ _ _ _ hres1)
  have hesz_s : s.locals.lookup (ofString "esz") = some (.val (.word w_esz)) := by
    simp [s1, setVarHOLFinite, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "l" ≠ ofString "esz" by decide] at hesz1
    exact hesz1
  have hcap_s : s.locals.lookup (ofString "cap") = some (.val (.word w_cap)) := by
    simp [s1, setVarHOLFinite, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "l" ≠ ofString "cap" by decide] at hcap1
    exact hcap1
  obtain ⟨hcmp1_2, hcmp2_2, pa2, hpa2_eq, hres2, heq_r2, heq_p2⟩ :=
    decCall_alloc_resumes (x := ofString "p") hs1_code q1 (w_esz * w_cap) hs1_hp harg2 hres1
  set q2 : BitVec 64 := (q1 + (w_esz * w_cap + 7)) &&& ((0 : BitVec 64) - 8)
  obtain ⟨hq2_eq, hq2_hi, hq2_al, hq1_le_q2⟩ :=
    Wave8Contracts.M26.alloc_arith q1 (w_esz * w_cap) hq1_hi hq1_al hcmp1_2 hcmp2_2
  change q2.toNat = _ at hq2_eq
  change q2.toNat ≤ heapLimit at hq2_hi
  change q2.toNat % 8 = 0 at hq2_al
  change q1.toNat ≤ q2.toNat at hq1_le_q2
  let s2 := setVarHOLFinite (ofString "p") (.val (.word q1)) { pa2 with locals := s1.locals }
  have hs2_l : s2.locals.lookup (ofString "l") = some (.val (.word hp)) := by
    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "p" ≠ ofString "l" by decide]
  have hs2_p : s2.locals.lookup (ofString "p") = some (.val (.word q1)) := by
    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs2_cap : s2.locals.lookup (ofString "cap") = some (.val (.word w_cap)) := by
    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "p" ≠ ofString "cap" by decide,
      show ofString "l" ≠ ofString "cap" by decide, hcap_s]
  have hev_l0 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
      (.op .add [.var .local (ofString "l"), .const 0]) = some (.val (.word (hp + 0))) := by
    simp [evalHOLExact, evalListHOLExact, hs2_l, valueIsWord, valueWord, wordOpHOL, wordOp]
  have hev_p : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
      (.var .local (ofString "p")) = some (.val (.word q1)) := by
    simp [evalHOLExact, hs2_p]
  obtain ⟨hdom0, hst0⟩ := store_word_resumes_step (hp + 0) q1 hev_l0 hev_p hres2
  rw [hst0] at hres2
  set m1 := Wave8Contracts.M26.updW s2.memory (hp + 0) q1
  let st1 := { s2 with memory := m1 }
  have hev_l8 : @evalHOLExact 64 F _ st1.toExact (fun a => Classical.propDecidable (st1.memaddrs a))
      (.op .add [.var .local (ofString "l"), .const 8]) = some (.val (.word (hp + 8))) := by
    simp [st1, evalHOLExact, evalListHOLExact, hs2_l, valueIsWord, valueWord, wordOpHOL, wordOp]
  obtain ⟨hdom8, hst8⟩ := store_word_resumes_step (hp + 8) 0 hev_l8 rfl hres2
  rw [hst8] at hres2
  set m2 := Wave8Contracts.M26.updW m1 (hp + 8) 0
  let st2 := { st1 with memory := m2 }
  have hev_l16 : @evalHOLExact 64 F _ st2.toExact (fun a => Classical.propDecidable (st2.memaddrs a))
      (.op .add [.var .local (ofString "l"), .const 16]) = some (.val (.word (hp + 16))) := by
    simp [st2, st1, evalHOLExact, evalListHOLExact, hs2_l, valueIsWord, valueWord, wordOpHOL, wordOp]
  have hev_cap : @evalHOLExact 64 F _ st2.toExact (fun a => Classical.propDecidable (st2.memaddrs a))
      (.var .local (ofString "cap")) = some (.val (.word w_cap)) := by
    simp [st2, st1, evalHOLExact, hs2_cap]
  obtain ⟨hdom16, hst16⟩ := store_word_resumes_step (hp + 16) w_cap hev_l16 hev_cap hres2
  have hret_st3 : evaluateHOLFiniteState { st2 with memory := Wave8Contracts.M26.updW m2 (hp + 16) w_cap }
      (.return (.var .local (ofString "l"))) =
      (some (.returned (.val (.word hp))),
        emptyLocalsHOLFinite { st2 with memory := Wave8Contracts.M26.updW m2 (hp + 16) w_cap }) := by
    rw [evaluateHOLFiniteState_return]
    simp [st2, st1, evalHOLExact, hs2_l, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  have hs2_eval : evaluateHOLFiniteState s2
      (.seq (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "p")))
        (.seq (.store (.op .add [.var .local (ofString "l"), .const 8]) (.const 0))
          (.seq (.store (.op .add [.var .local (ofString "l"), .const 16]) (.var .local (ofString "cap")))
            (.return (.var .local (ofString "l")))))) =
      (some (.returned (.val (.word hp))),
        emptyLocalsHOLFinite { st2 with memory := Wave8Contracts.M26.updW m2 (hp + 16) w_cap }) := by
    rw [hst0, hst8, hst16, hret_st3]
  set m3 := Wave8Contracts.M26.updW m2 (hp + 16) w_cap
  have hs2_mem : s2.memory = s.memory := by
    change pa2.memory = s.memory
    rw [hpa2_eq]; change pa1.memory = s.memory; rw [hpa1_eq]
  have hs2_ma : s2.memaddrs = s.memaddrs := by
    change pa2.memaddrs = s.memaddrs
    rw [hpa2_eq]; change pa1.memaddrs = s.memaddrs; rw [hpa1_eq]
  have hs2_be : s2.be = s.be := by
    change pa2.be = s.be
    rw [hpa2_eq]; change pa1.be = s.be; rw [hpa1_eq]
  have hs2_code : s2.code = s.code := by
    change pa2.code = s.code
    rw [hpa2_eq]; change pa1.code = s.code; rw [hpa1_eq]
  have hs2_sh : s2.shMemaddrs = s.shMemaddrs := by
    change pa2.shMemaddrs = s.shMemaddrs
    rw [hpa2_eq]; change pa1.shMemaddrs = s.shMemaddrs; rw [hpa1_eq]
  have hs2_ba : s2.baseAddr = s.baseAddr := by
    change pa2.baseAddr = s.baseAddr
    rw [hpa2_eq]; change pa1.baseAddr = s.baseAddr; rw [hpa1_eq]
  have hpa2_glob : pa2.globals = (s.globals.update (ofString "heap_ptr", .val (.word q1))).update
      (ofString "heap_ptr", .val (.word q2)) := by
    rw [hpa2_eq]; change (pa1.globals.update _) = _; rw [hpa1_eq]
  set out := evaluateHOLFiniteState s
    (.decCall (ofString "l") .one (ofString "alloc") [.const 24]
      (.decCall (ofString "p") .one (ofString "alloc")
        [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")]]
        (.seq (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "p")))
          (.seq (.store (.op .add [.var .local (ofString "l"), .const 8]) (.const 0))
            (.seq (.store (.op .add [.var .local (ofString "l"), .const 16]) (.var .local (ofString "cap")))
              (.return (.var .local (ofString "l"))))))))
  have hout_r : out.1 = some (.returned (.val (.word hp))) := by
    rw [heq_r1, heq_r2, hs2_eval]
  have hout_mem : out.2.memory = m3 := by
    rw [heq_p1]; dsimp only; rw [heq_p2]; dsimp only; rw [hs2_eval]; rfl
  have hout_glob : out.2.globals = pa2.globals := by
    rw [heq_p1]; dsimp only; rw [heq_p2]; dsimp only; rw [hs2_eval]; rfl
  have hout_be : out.2.be = s.be := by
    rw [heq_p1]; dsimp only; rw [heq_p2]; dsimp only; rw [hs2_eval]; exact hs2_be
  have hout_code : out.2.code = s.code := by
    rw [heq_p1]; dsimp only; rw [heq_p2]; dsimp only; rw [hs2_eval]; exact hs2_code
  have hout_ma : out.2.memaddrs = s.memaddrs := by
    rw [heq_p1]; dsimp only; rw [heq_p2]; dsimp only; rw [hs2_eval]; exact hs2_ma
  have hout_sh : out.2.shMemaddrs = s.shMemaddrs := by
    rw [heq_p1]; dsimp only; rw [heq_p2]; dsimp only; rw [hs2_eval]; exact hs2_sh
  have hout_ba : out.2.baseAddr = s.baseAddr := by
    rw [heq_p1]; dsimp only; rw [heq_p2]; dsimp only; rw [hs2_eval]; exact hs2_ba
  have hhp_post : globN out.2 "heap_ptr" = q2.toNat := by
    unfold globN; rw [hout_glob, hpa2_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hfp_post : globN out.2 "frame_mem_ptr" = globN s "frame_mem_ptr" := by
    unfold globN; rw [hout_glob, hpa2_glob]
    simp [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
  have hsp_post : globN out.2 "scratch_ptr" = globN s "scratch_ptr" := by
    unfold globN; rw [hout_glob, hpa2_glob]
    simp [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
  have hG_post : GuestInv out.2 :=
    guestInv_congr hout_code hout_ma hout_sh hout_ba hWOK.1.1
  have hA_post : ArenaReady out.2 := by
    refine ⟨hG_post, ?_⟩
    unfold ArenaOK
    rw [hhp_post, hfp_post, hsp_post]
    have hAs := hWOK.1.2
    have hsb_lo : sourceBase ≤ hp.toNat := by rw [hhp_eq]; exact hAs.1
    have hpa1_g : pa1.globals = s.globals.update (ofString "heap_ptr", .val (.word q1)) := by rw [hpa1_eq]
    have hgw_pa1 : GlobalsWord pa1 :=
      globalsWord_update (ofString "heap_ptr") q1 hpa1_g hAs.2.2.2.2.2.2.2.2
    have hgw_post : GlobalsWord out.2 :=
      globalsWord_update (ofString "heap_ptr") q2 (by rw [hout_glob, hpa2_glob, ← hpa1_g]) hgw_pa1
    exact ⟨by omega, hq2_hi, hAs.2.2.1, hAs.2.2.2.1, hAs.2.2.2.2.1,
      hq2_al, hAs.2.2.2.2.2.2.1, hAs.2.2.2.2.2.2.2.1, hgw_post⟩
  have hGK : GlobalsKept ["heap_ptr"] s out.2 := by
    intro k hk
    simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hk
    have hbeq : (ofString "heap_ptr" == k) = false := beq_eq_false_iff_ne.2 (Ne.symm hk)
    simp [hout_glob, hpa2_glob, HolFiniteMapExact.lookup_update, FUPDATE, hbeq]
  -- Address bounds for `hp + 0`, `hp + 8`, `hp + 16`:
  have h264 : heapLimit < 2 ^ 64 := by decide
  have hp0_nat : (hp + 0).toNat = hp.toNat := by simp
  have hp8_nat : (hp + (8 : BitVec 64)).toNat = hp.toNat + 8 :=
    BitVec.toNat_add_of_lt (by change hp.toNat + 8 < 2 ^ 64; omega)
  have hp16_nat : (hp + (16 : BitVec 64)).toNat = hp.toNat + 16 :=
    BitVec.toNat_add_of_lt (by change hp.toNat + 16 < 2 ^ 64; omega)
  have hm3_frame : ∀ a : BitVec 64, a ≠ hp + 0 → a ≠ hp + 8 → a ≠ hp + 16 → m3 a = s.memory a := by
    intro a h0 h8 h16
    unfold m3 m2 m1 Wave8Contracts.M26.updW
    rw [if_neg h16, if_neg h8, if_neg h0, hs2_mem]
  refine worldStep_of_fresh_heap hWOK hA_post (by rw [hhp_post, ← hhp_eq]; omega)
    hGK hout_be
    (fun a hna => by
      rw [hout_mem]
      apply hm3_frame a
      · rintro rfl; exact hna (hs2_ma ▸ hdom0)
      · rintro rfl; exact hna (hs2_ma ▸ hdom8)
      · rintro rfl; exact hna (hs2_ma ▸ hdom16))
    (fun a hno => by
      rw [hout_mem]
      apply hm3_frame a
      · rintro rfl; apply hno; unfold heapFree CellHits; rw [hp0_nat, ← hhp_eq]; dsimp; omega
      · rintro rfl; apply hno; unfold heapFree CellHits; rw [hp8_nat, ← hhp_eq]; dsimp; omega
      · rintro rfl; apply hno; unfold heapFree CellHits; rw [hp16_nat, ← hhp_eq]; dsimp; omega)
    (fun b hb hno => by
      unfold memB
      rw [hout_mem, hout_be]
      have hc_nat := panByteAlign_toNat64 (BitVec.ofNat 64 b)
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb] at hc_nat
      have hm_eq : m3 (panByteAlignHOL (BitVec.ofNat 64 b)) = s.memory (panByteAlignHOL (BitVec.ofNat 64 b)) := by
        apply hm3_frame
        · intro heq; rw [heq, hp0_nat] at hc_nat; apply hno; unfold heapFree InIvl; dsimp; omega
        · intro heq; rw [heq, hp8_nat] at hc_nat; apply hno; unfold heapFree InIvl; dsimp; omega
        · intro heq; rw [heq, hp16_nat] at hc_nat; apply hno; unfold heapFree InIvl; dsimp; omega
      rw [hm_eq])
    (fun S Nd hWT _ hwo_eq => ?_)
  intro hmul_lt v hv
  dsimp only at hmul_lt ⊢
  rw [hout_r] at hv
  injection hv with hv'; injection hv' with hv''; subst hv''
  have hloc_esz : locN s "esz" = w_esz.toNat := by simp [locN, hesz_s]
  have hloc_cap : locN s "cap" = w_cap.toNat := by simp [locN, hcap_s]
  rw [hloc_esz, hloc_cap] at hmul_lt
  have hmul_toNat : (w_esz * w_cap).toNat = w_esz.toNat * w_cap.toNat := by
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hmul_lt]
  rw [hmul_toNat] at hq2_eq
  -- Read `memW out.2 hp.toNat = q1.toNat`
  have hp0_ne_8 : hp + 0 ≠ hp + 8 := by
    intro h; have := congrArg BitVec.toNat h; rw [hp0_nat, hp8_nat] at this; omega
  have hp0_ne_16 : hp + 0 ≠ hp + 16 := by
    intro h; have := congrArg BitVec.toNat h; rw [hp0_nat, hp16_nat] at this; omega
  have hp_eq_0 : BitVec.ofNat 64 hp.toNat = hp + 0 := by simp [BitVec.ofNat_toNat]
  have hmem0 : memW out.2 hp.toNat = q1.toNat := by
    unfold memW; rw [hout_mem, hp_eq_0]
    unfold m3 m2 m1 Wave8Contracts.M26.updW
    rw [if_neg hp0_ne_16, if_neg hp0_ne_8, if_pos rfl]
  refine ⟨hp, rfl, fun ivl hivl o ho => ?_⟩
  rw [hloc_esz, hloc_cap, hmem0] at hivl
  rw [hwo_eq] at ho
  rcases InitECandidate.Solver.Wave8Contracts.M08.worldOwned_allocated hWT ho with ho0 | hal_o
  · exact Or.inr (Or.inl ho0)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hivl
    rcases hivl with rfl | rfl
    · exact InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap hWOK.1.2 hA_post.2 hal_o
        ⟨by dsimp; omega, by dsimp; rw [hhp_post]; omega⟩
    · exact InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap hWOK.1.2 hA_post.2 hal_o
        ⟨by dsimp; omega, by dsimp; rw [hhp_post]; omega⟩

end R13Wk06b

theorem «wk_msg_new» :
    WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
     ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoids (fun _ _ w => [(w, 176)])) (ofString "msg_new") := by
  have hlook : originalRuntimeCode.lookup (ofString "msg_new") =
      some ([], sourceFnBody Guest.Software.guestFn_msg_new, .one) :=
    lookup_of_guestAst_getElem 465 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_msg_new) rfl
  refine ⟨_, _, _, hlook, fun {F} s hcode hWOK _ _ hres => ?_⟩
  exact R13Wk06b.alloc_memzero_return_worldStep s (ofString "m") 176
    (by decide) (by decide) (by decide) hcode hWOK hres

theorem «wk_te_new» :
    WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
     ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoids (fun _ _ w => [(w, 200)])) (ofString "te_new") := by
  have hlook : originalRuntimeCode.lookup (ofString "te_new") =
      some ([], sourceFnBody Guest.Software.guestFn_te_new, .one) :=
    lookup_of_guestAst_getElem 869 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_te_new) rfl
  refine ⟨_, _, _, hlook, fun {F} s hcode hWOK _ _ hres => ?_⟩
  exact R13Wk06b.alloc_memzero_return_worldStep s (ofString "te") 200
    (by decide) (by decide) (by decide) hcode hWOK hres

theorem «wk_lst_new» :
    WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
     ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoidsIf (fun s => locN s "esz" * locN s "cap" < 2 ^ 64)
      (fun s post w => [(w, 24), (memW post w, locN s "esz" * locN s "cap")])) (ofString "lst_new") := by
  have hlook : originalRuntimeCode.lookup (ofString "lst_new") =
      some ([(ofString "esz", .one), (ofString "cap", .one)],
        sourceFnBody Guest.Software.guestFn_lst_new, .one) :=
    lookup_of_guestAst_getElem 408 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_lst_new) rfl
  refine ⟨_, _, _, hlook, fun {F} s hcode hWOK _ _ hres => ?_⟩
  exact R13Wk06b.lst_new_worldStep s hcode hWOK hres
end InitECandidate.Solver.Wave8GuestInv
