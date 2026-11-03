import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.StackPushInv

/-! # `EvmPreservingSpec` for `stack_push`, `stack_push_word`, and `stack_push_bool` -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8Contracts.M23

/-! ## 1. `scratch_alloc` body non-EvmErr lemma and helper lookups -/

theorem scratch_alloc_lookup_pub :
    originalRuntimeCode.lookup (ofString "scratch_alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_scratch_alloc, .one) :=
  lookup_of_guestAst_getElem 13 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_scratch_alloc) rfl

theorem scratch_alloc_body_no_evmErr {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode) :
    ¬ IsEvmErr (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_scratch_alloc)).1 := by
  have hbody_eq : sourceFnBody Guest.Software.guestFn_scratch_alloc =
      .dec (ofString "p") .one (.var .global (ofString "scratch_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 7])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .sub [.var .local (ofString "p"), .var .local (ofString "n")],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr")))
                (.call (some (none, none)) (ofString "trap_with") [.const 7])
                .skip)
              (.seq
                (.assign .global (ofString "scratch_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "q"))))))) := rfl
  have htrap : ∀ (t : PanSemStateFiniteExact 64 F), t.code = originalRuntimeCode →
      let out := evaluateHOLFiniteState t (.call (some (none, none)) (ofString "trap_with") [.const 7])
      out.1 ≠ none ∧ ¬ IsEvmErr out.1 := by
    intro t htc; dsimp only
    rw [evaluateHOLFiniteState_call]
    rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) [.const 7] with _ | vals
    · exact ⟨by simp, by rintro ⟨_, h⟩; cases h⟩
    · dsimp only
      rcases hl : lookupCodeHOLFinite t.code.lookup (ofString "trap_with") vals with _ | ⟨body', callee, rs⟩
      · exact ⟨by simp, by rintro ⟨_, h⟩; cases h⟩
      · dsimp only
        have hbody_tr : body' = sourceFnBody Guest.Software.guestFn_trap_with :=
          lookupCodeHOLFinite_installed_body t.code.lookup (ofString "trap_with") _ _ _ _ _ vals callee
            (by rw [htc]; exact lookup_trap_with) hl
        subst hbody_tr
        split
        · exact ⟨by simp, by rintro ⟨_, h⟩; cases h⟩
        · have hout := evaluate_trap_with_body_outcomes (callEntryStateHOLFinite t callee)
          rcases hr : evaluateHOLFiniteState (callEntryStateHOLFinite t callee)
              (sourceFnBody Guest.Software.guestFn_trap_with) with ⟨res, st⟩
          rw [hr] at hout; dsimp only at hout ⊢
          cases res with
          | none => exact absurd rfl hout.1
          | some r0 =>
            cases r0 with
            | returned v => exact absurd rfl (hout.2.1 v)
            | exception eid v =>
              refine ⟨by simp, ?_⟩
              rintro ⟨_, h⟩; injection h with h'; injection h' with he hw
              subst he hw
              exact hout.2.2 (ofString "EvmErr") v (by decide) rfl
            | _ => exact ⟨by simp, by rintro ⟨_, h⟩; cases h⟩
  rw [hbody_eq, evaluateHOLFiniteState_dec_total]; dsimp only
  split
  · rintro ⟨_, h⟩; cases h
  · rename_i vp _
    split
    · dsimp only
      set s1 := setVarHOLFinite (ofString "p") vp s
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
      split
      · split
        · simp only [evaluateHOLFiniteState_skip]
          rw [evaluateHOLFiniteState_dec_total]; dsimp only
          split
          · rintro ⟨_, h⟩; cases h
          · rename_i vq _
            split
            · dsimp only
              set s2 := setVarHOLFinite (ofString "q") vq s1
              rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
              split
              · split
                · simp only [evaluateHOLFiniteState_skip]
                  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
                  split
                  · rintro ⟨_, h⟩; cases h
                  · split
                    · dsimp only; rw [evaluateHOLFiniteState_return]
                      split
                      · rintro ⟨_, h⟩; cases h
                      · split <;> (rintro ⟨_, h⟩; cases h)
                    · rintro ⟨_, h⟩; cases h
                · have ht2 := htrap s2 hcode
                  rcases htr2 : evaluateHOLFiniteState s2 (.call (some (none, none)) (ofString "trap_with") [.const 7]) with ⟨r2, t2⟩
                  rw [htr2] at ht2
                  cases r2 with
                  | none => exact absurd rfl ht2.1
                  | some _ => exact ht2.2
              · rintro ⟨_, h⟩; cases h
            · rintro ⟨_, h⟩; cases h
        · have ht1 := htrap s1 hcode
          rcases htr1 : evaluateHOLFiniteState s1 (.call (some (none, none)) (ofString "trap_with") [.const 7]) with ⟨r1, t1⟩
          rw [htr1] at ht1
          cases r1 with
          | none => exact absurd rfl ht1.1
          | some _ => exact ht1.2
      · rintro ⟨_, h⟩; cases h
    · rintro ⟨_, h⟩; cases h

theorem evalAt_loadG_word {F : Type} (t : PanSemStateFiniteExact 64 F) (g : String) (k : BitVec 64)
    (v : ValueHOL 64)
    (h : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.load .one (.op .add [.var .global (ofString g), .const k])) = some v) :
    ∃ a : BitVec 64, v = .val (.word a) ∧ a.toNat = memW t (globN t g + k.toNat) := by
  simp [evalHOLExact, evalListHOLExact] at h
  rcases hg : t.globals.lookup (ofString g) with _ | w
  · simp [hg] at h
  · rcases w with ⟨⟨x⟩⟩ | _ | _
    · simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
      rcases hm : t.memory (x + k) with ⟨y⟩
      rw [hm] at h
      have hadd : BitVec.ofNat 64 (x.toNat + k.toNat) = x + k := by rw [BitVec.add_def]
      exact ⟨y, h.2.symm, by simp only [globN, memW, hg, hadd, hm]⟩
    · simp [hg, valueIsWord] at h
    · simp [hg, valueIsWord] at h

theorem store_some_eq_error' {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {res : PanSemResultExact 64}
    (h : evaluateHOLFiniteState s (.store dst val) = (some res, post)) :
    res = .error := by
  rw [evaluateHOLFiniteState_store] at h; revert h
  rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst with _ | dv
  · intro h; injection h with h1; injection h1 with h2; exact h2.symm
  · rcases dv with ⟨⟨addr⟩⟩ | _ | _
    · rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val with _ | v
      · intro h; injection h with h1; injection h1 with h2; exact h2.symm
      · dsimp only; split
        · intro h; injection h with h1; cases h1
        · intro h; injection h with h1; injection h1 with h2; exact h2.symm
    · intro h; injection h with h1; injection h1 with h2; exact h2.symm
    · intro h; injection h with h1; injection h1 with h2; exact h2.symm

/-! ## 2. `eps_stack_push` -/

theorem lookup_stack_push :
    originalRuntimeCode.lookup (ofString "stack_push") =
      some ([(ofString "v", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_stack_push, .one) :=
  lookup_of_guestAst_getElem 454 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_stack_push) rfl

private theorem raise3_unchanged_post {F : Type}
    {s t : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s)
    (L_wrap : HolFiniteMapExact MlS (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64))
    (ht_eq : t = { s with locals := t.locals, clock := t.clock }) :
    let out := evaluateHOLFiniteState t (.raise (ofString "EvmErr") (.const 3#64))
    (∀ v, out.1 = some (.returned v) →
      EvmInv { out.2 with locals := L_wrap out.2.locals } ∧
      evmChain { out.2 with locals := L_wrap out.2.locals } = evmChain s ∧
      evmR { out.2 with locals := L_wrap out.2.locals } ≤ evmR s ∧
      (∀ g : String, ofString g ≠ ofString "scratch_ptr" → globN { out.2 with locals := L_wrap out.2.locals } g = globN s g)) ∧
    (IsEvmErr out.1 →
      EvmInv { out.2 with locals := L_wrap out.2.locals } ∧
      evmChain { out.2 with locals := L_wrap out.2.locals } = evmChain s ∧
      evmR { out.2 with locals := L_wrap out.2.locals } ≤ evmR s) := by
  dsimp only
  rw [evaluateHOLFiniteState_raise]; dsimp only [evalHOLExact]
  cases ht_esh : t.eshapes.lookup (ofString "EvmErr") with
    | none =>
      dsimp only
      constructor
      · intro _ h; cases h
      · rintro ⟨_, h⟩; cases h
    | some sh =>
      dsimp only
      by_cases hcond : shapeOfHOLExact (.val (.word 3#64)) = sh ∧
          sizeOfShapeWithContextHOL t.structs (shapeOfHOLExact (.val (.word 3#64))) ≤ 32
      · rw [if_pos hcond]; dsimp only
        let post := { t.emptyLocalsHOLFinite with locals := L_wrap t.emptyLocalsHOLFinite.locals }
        have hp_eq : post = { s with locals := post.locals, clock := t.clock } := by
          dsimp only [post, emptyLocalsHOLFinite]; conv_lhs => rw [ht_eq]
        have hInv_p : EvmInv post := by
          have h := localsFree_evmInv s post.locals t.clock hInv
          rwa [← hp_eq] at h
        have hm : post.memory = s.memory := by rw [hp_eq]
        have hg : post.globals = s.globals := by rw [hp_eq]
        have hc := evm_congr hm hg
        constructor
        · intro _ h; cases h
        · intro _; exact ⟨hInv_p, evmChain_congr hm hg, le_of_eq hc.2.1⟩
      · rw [if_neg hcond]; dsimp only
        constructor
        · intro _ h; cases h
        · rintro ⟨_, h⟩; cases h

theorem eps_stack_push :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => ∀ g : String, ofString g ≠ ofString "scratch_ptr" → globN post g = globN s g)
      (ofString "stack_push") := by
  refine ⟨_, _, _, lookup_stack_push, ?_⟩
  intro F s hcode hInv _ ⟨vals, hlk_entry⟩ hnt
  have hv_struct : ∃ w0 w1 w2 w3 : BitVec 64,
      s.locals.lookup (ofString "v") =
        some (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]) := by
    have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
      originalRuntimeCode.lookup (ofString "stack_push") vals
      (sourceFnBody Guest.Software.guestFn_stack_push) s.locals .one hlk_entry
    simp only [Flapjack.lookupCodeHOLExact, lookup_stack_push] at hx
    rcases vals with _ | ⟨v0, _ | _⟩
    · simp at hx
    · split at hx
      · rename_i hcond
        have heq := Option.some.inj hx
        rcases Prod.mk.inj heq with ⟨_, hrest⟩
        rcases Prod.mk.inj hrest with ⟨hloc, _⟩
        have hsh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v0) = true := by
          simpa [List.map] using hcond
        rw [shapeEqHOL_eq_true] at hsh
        have hfn : s.locals.lookup (ofString "v") = some v0 := by
          have := congrFun hloc.symm (ofString "v")
          simpa [FUPDATE_LIST, FUPDATE] using this
        rcases v0 with _ | fs | _
        · simp [shapeOfHOLExact] at hsh
        · simp only [shapeOfHOLExact, ShapeHOL.comb.injEq] at hsh
          rcases fs with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, _ | _⟩⟩⟩⟩
          · simp at hsh
          · simp at hsh
          · simp at hsh
          · simp at hsh
          · simp only [List.map, List.cons.injEq] at hsh
            obtain ⟨h0, h1, h2, h3, _⟩ := hsh
            rcases f0 with ⟨⟨w0⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h0
            rcases f1 with ⟨⟨w1⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h1
            rcases f2 with ⟨⟨w2⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h2
            rcases f3 with ⟨⟨w3⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h3
            exact ⟨w0, w1, w2, w3, hfn⟩
          · simp at hsh
        · simp [shapeOfHOLExact] at hsh
      · cases hx
    · simp at hx
  obtain ⟨vw0, vw1, vw2, vw3, hv_loc⟩ := hv_struct
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
  have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
  dsimp only at hb_ev
  have hev_pos : 0 < globN s "ev" := by
    obtain ⟨hin1, _⟩ := (hFW0.1 (globN s "ev", 280) (by simp)).1
    have h1 := hInv.1.2.2.2.1; have h2 := hInv.1.2.2.2.2.1
    rw [R11Shards.scratchStart_val] at h1; dsimp only at hin1; omega
  obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
  obtain ⟨hp_w, fp_w, sp_g_w, hhp_lk, hhp_nat, hfp_lk, hfp_nat, hsp_g_lk, hsp_g_nat⟩ :=
    Wave8Contracts.M26.arenaOK_globals s hInv.1.2
  have herr_triv : ∀ {P1 P2 : Prop},
      (∀ v, (some PanSemResultExact.error : Option (PanSemResultExact 64)) = some (.returned v) → P1) ∧
      (IsEvmErr (some PanSemResultExact.error) → P2) := by
    intro _ _; constructor
    · intro _ h; cases h
    · rintro ⟨_, h⟩; cases h
  let growBranch : ProgHOL 64 :=
    .seq
      (.ite (.cmp .notLower (.var .local (ofString "cap")) (.const 1024#64))
        (.raise (ofString "EvmErr") (.const 3#64))
        .skip)
      (.dec (ofString "ncap") .one (.panop .mul [.var .local (ofString "cap"), .const 2#64])
        (.seq
          (.ite (.cmp .lower (.const 1024#64) (.var .local (ofString "ncap")))
            (.assign .local (ofString "ncap") (.const 1024#64))
            .skip)
          (.decCall (ofString "ns") .one (ofString "scratch_alloc")
            [.panop .mul [.var .local (ofString "ncap"), .const 32#64]]
            (.seq
              (.call (some (none, none)) (ofString "memcpy")
                [.var .local (ofString "ns"),
                 .load .one (.op .add [.var .global (ofString "ev"), .const 8#64]),
                 .panop .mul [.var .local (ofString "sp"), .const 32#64]])
              (.seq
                (.store (.op .add [.var .global (ofString "ev"), .const 8#64]) (.var .local (ofString "ns")))
                (.store (.op .add [.var .global (ofString "ev"), .const 232#64]) (.var .local (ofString "ncap"))))))))
  let tailProg : ProgHOL 64 :=
    .seq
      (.ite (.cmp .equal (.var .local (ofString "sp")) (.const 1024#64))
        (.raise (ofString "EvmErr") (.const 3#64))
        .skip)
      (.seq
        (.store
          (.op .add
            [.load .one (.op .add [.var .global (ofString "ev"), .const 8#64]),
             .panop .mul [.var .local (ofString "sp"), .const 32#64]])
          (.var .local (ofString "v")))
        (.seq
          (.store (.op .add [.var .global (ofString "ev"), .const 16#64])
            (.op .add [.var .local (ofString "sp"), .const 1#64]))
          (.return (.const 0#64))))
  have hbody : sourceFnBody Guest.Software.guestFn_stack_push =
      .dec (ofString "sp") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 16#64]))
        (.dec (ofString "cap") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 232#64]))
          (.seq
            (.ite (.cmp .notLower (.var .local (ofString "sp")) (.var .local (ofString "cap")))
              growBranch
              .skip)
            tailProg)) := rfl
  dsimp only
  rw [hbody] at hnt ⊢
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
  rcases hload_sp : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ev"), .const 16#64])) with _ | vsp
  · exact herr_triv
  · simp only [hload_sp] at hnt ⊢
    obtain ⟨spw, rfl, hspw_eq⟩ := evalAt_loadG_word s "ev" 16#64 vsp hload_sp
    have h16_n : (16#64 : BitVec 64).toNat = 16 := rfl
    rw [h16_n] at hspw_eq
    have hsh_sp : shapeEqHOL .one (shapeOfHOLExact (.val (.word spw))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    rw [if_pos hsh_sp] at hnt ⊢; dsimp only at hnt ⊢
    set s1 := setVarHOLFinite (ofString "sp") (.val (.word spw)) s with hs1
    rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
    rcases hload_cap : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.load .one (.op .add [.var .global (ofString "ev"), .const 232#64])) with _ | vcap
    · exact herr_triv
    · simp only [hload_cap] at hnt ⊢
      obtain ⟨capw, rfl, hcapw_eq⟩ := evalAt_loadG_word s1 "ev" 232#64 vcap hload_cap
      have h232_n : (232#64 : BitVec 64).toNat = 232 := rfl
      have hs1_gm : memW s1 (globN s1 "ev" + 232) = memW s (globN s "ev" + 232) := rfl
      rw [h232_n, hs1_gm] at hcapw_eq
      have hsh_cap : shapeEqHOL .one (shapeOfHOLExact (.val (.word capw))) = true := by
        simp [shapeEqHOL, shapeOfHOLExact]
      rw [if_pos hsh_cap] at hnt ⊢; dsimp only at hnt ⊢
      set s2 := setVarHOLFinite (ofString "cap") (.val (.word capw)) s1 with hs2
      have hs2_sp : s2.locals.lookup (ofString "sp") = some (.val (.word spw)) := by
        simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "cap" ≠ ofString "sp" by decide]
      have hs2_cap : s2.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
        simp [hs2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hs2_v : s2.locals.lookup (ofString "v") =
          some (.rStruct [.val (.word vw0), .val (.word vw1), .val (.word vw2), .val (.word vw3)]) := by
        simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hv_loc,
          show ofString "cap" ≠ ofString "v" by decide, show ofString "sp" ≠ ofString "v" by decide]
      have hcap_ge1 : 1 ≤ capw.toNat := by rw [hcapw_eq]; exact hFW0.2.2.2.1
      have hsp_le_cap : spw.toNat ≤ capw.toNat := by rw [hspw_eq, hcapw_eq]; exact hFW0.2.2.2.2.1
      have hcap_le1024 : capw.toNat ≤ 1024 := by rw [hcapw_eq]; exact hFW0.2.2.2.2.2.1
      have run_tail : ∀ (m : PanSemStateFiniteExact 64 F) (freshIvl : Ivl),
          ArenaReady m →
          globN m "scratch_ptr" ≤ globN s "scratch_ptr" →
          (∀ g : String, ofString g ≠ ofString "scratch_ptr" → m.globals.lookup (ofString g) = s.globals.lookup (ofString g)) →
          ScratchByteEff s m [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))] →
          (freshIvl = (0, 0) ∨
            (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
              Inside freshIvl (globN m "scratch_ptr") (globN s "scratch_ptr"))) →
          (∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 8 → off ≠ 16 → off ≠ 232 →
            memW m (globN s "ev" + off) = memW s (globN s "ev" + off)) →
          ((freshIvl.2 = 0 ∧ memW m (globN s "ev" + 8) = memW s (globN s "ev" + 8) ∧
              memW m (globN s "ev" + 232) = memW s (globN s "ev" + 232)) ∨
            (freshIvl.2 ≠ 0 ∧ (memW m (globN s "ev" + 8), 32 * memW m (globN s "ev" + 232)) = freshIvl)) →
          spw.toNat < memW m (globN s "ev" + 232) →
          memW m (globN s "ev" + 232) ≤ 1024 →
          memW m (globN s "ev" + 16) = spw.toNat →
          m.locals.lookup (ofString "sp") = some (.val (.word spw)) →
          m.locals.lookup (ofString "v") =
            some (.rStruct [.val (.word vw0), .val (.word vw1), .val (.word vw2), .val (.word vw3)]) →
          let out := evaluateHOLFiniteState m tailProg
          let post := { out.2 with
            locals := (out.2.locals.resVarEq (ofString "cap", s1.locals.lookup (ofString "cap"))).resVarEq
              (ofString "sp", s.locals.lookup (ofString "sp")) }
          (∀ v, out.1 = some (.returned v) →
            EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s ∧
            (∀ g : String, ofString g ≠ ofString "scratch_ptr" → globN post g = globN s g)) ∧
          (IsEvmErr out.1 →
            EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s) := by
        intro m freshIvl hAm hsc_m hm_glob_other heff_m hfresh_m he0_m hnew_m hsp_lt_mcap hmcap_le _hm_sp16 hm_sp hm_v
        dsimp only [tailProg]
        have hm_ev : m.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
          rw [hm_glob_other "ev" (by decide)]; exact hevw
        have hsp_ne1024 : spw ≠ 1024#64 := by
          intro heq; subst heq
          have : (1024#64 : BitVec 64).toNat = 1024 := rfl
          omega
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
        have hcmp_sp : @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a))
            (.cmp .equal (.var .local (ofString "sp")) (.const 1024#64)) = some (.val (.word 0#64)) := by
          simp [evalHOLExact, hm_sp, Compiler.Encoders.Asm.wordCmpHOL, hsp_ne1024]
        rw [hcmp_sp]; simp only [↓reduceIte, evaluateHOLFiniteState_skip]
        have h0_eq : (0#64 : BitVec 64) = 0 := rfl
        simp only [h0_eq, ↓reduceIte, evaluateHOLFiniteState_skip]
        rw [evaluateHOLFiniteState_seq_line780]
        let dstStkExp : ExpHOL 64 :=
          .op .add
            [.load .one (.op .add [.var .global (ofString "ev"), .const 8#64]),
             .panop .mul [.var .local (ofString "sp"), .const 32#64]]
        rcases hst_v : evaluateHOLFiniteState m (.store dstStkExp (.var .local (ofString "v"))) with ⟨rv_st, m1⟩
        simp only [hst_v]
        cases rv_st with
        | some res_v =>
          have herr := store_some_eq_error' hst_v; subst herr; dsimp only; exact herr_triv
        | none =>
          dsimp only
          have hstk_ptr_bound : memW m (globN s "ev" + 8) + 32 * memW m (globN s "ev" + 232) ≤ 2 ^ 64 := by
            rcases hnew_m with ⟨_, h8_eq, h232_eq⟩ | ⟨hnz, hstk_eq⟩
            · rw [h8_eq, h232_eq]
              obtain ⟨_, hin2⟩ := (hFW0.1 (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232)) (by simp)).1
              rw [R11Shards.scratchEnd_val] at hin2; dsimp only at hin2; omega
            · rcases hfresh_m with rfl | ⟨_, _, _, hfin2⟩
              · exact absurd rfl hnz
              · have h4 := hInv.1.2.2.2.2.2.1; rw [R11Shards.scratchEnd_val] at h4
                rw [← hstk_eq] at hfin2; dsimp only at hfin2; omega
          have hd_v_stk := ScratchByteEff.of_store_struct4
            (Rl := [freshIvl, (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))])
            hAm.1.memaddrs hst_v
            (fun v hv => by
              change m.locals.lookup (ofString "v") = some v at hv
              rw [hm_v] at hv; injection hv with hv'; exact ⟨vw0, vw1, vw2, vw3, hv'.symm⟩)
            (fun addr hdst => by
              dsimp only [dstStkExp] at hdst
              have hmem_load8 : ∃ stkw : BitVec 64, m.memory (evw + 8#64) = .word stkw ∧
                  addr = stkw + spw * 32#64 := by
                rcases hm8 : m.memory (evw + 8#64) with ⟨stkw⟩
                refine ⟨stkw, rfl, ?_⟩
                simp [evalHOLExact, evalListHOLExact, hm_ev, hm_sp,
                  wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord, memLoadHOLExact, hm8] at hdst
                by_cases hdm8 : m.memaddrs (evw + 8#64)
                · simp [hdm8, valueIsWord, valueWord] at hdst; exact hdst.symm
                · simp [hdm8] at hdst
              obtain ⟨stkw, hm8, haddr_eq⟩ := hmem_load8
              have hev8_eq : evw + 8#64 = BitVec.ofNat 64 (globN s "ev" + 8) := by
                apply BitVec.eq_of_toNat_eq
                have : (8#64 : BitVec 64).toNat = 8 := rfl
                rw [BitVec.toNat_add, hevw_nat, this, BitVec.toNat_ofNat]
              have hstkw_nat : stkw.toNat = memW m (globN s "ev" + 8) := by
                unfold memW; rw [← hev8_eq, hm8]
              have hsp32_nat : (spw * 32#64).toNat = 32 * spw.toNat := by
                have : (32#64 : BitVec 64).toNat = 32 := rfl
                rw [BitVec.toNat_mul, this, Nat.mod_eq_of_lt (by omega)]; omega
              have haddr_nat : addr.toNat = memW m (globN s "ev" + 8) + 32 * spw.toNat := by
                rw [haddr_eq, BitVec.toNat_add, hstkw_nat, hsp32_nat, Nat.mod_eq_of_lt (by omega)]
              refine ⟨by omega, ?_⟩
              rcases hnew_m with ⟨_, h8_eq, h232_eq⟩ | ⟨_, hstk_eq⟩
              · exact ⟨(memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232)),
                  by simp, by dsimp only; omega, by dsimp only; omega⟩
              · refine ⟨freshIvl, by simp, ?_, ?_⟩
                · rw [← hstk_eq]; dsimp only; omega
                · rw [← hstk_eq]; dsimp only; omega)
          obtain ⟨heff_st_v_stk, hm1_loc, hm1_glob⟩ := hd_v_stk
          have heff_st_v : ScratchByteEff m m1
              [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))] :=
            heff_st_v_stk.mono (fun x hx => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              rcases hx with hx1 | hx2
              · rw [hx1]; exact ⟨_, List.mem_cons_self, le_refl _, le_refl _⟩
              · rw [hx2]; exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), le_refl _, le_refl _⟩)
          have hm1_e0_eq : ∀ off, off + 8 ≤ 280 → off % 8 = 0 →
              memW m1 (globN s "ev" + off) = memW m (globN s "ev" + off) := by
            intro off hoff hoff8
            unfold memW
            rw [heff_st_v_stk.cell_frame (BitVec.ofNat 64 (globN s "ev" + off))]
            intro x hx
            have htn : (BitVec.ofNat 64 (globN s "ev" + off)).toNat = globN s "ev" + off :=
              Nat.mod_eq_of_lt (by omega)
            rw [htn]
            have he0_8 : (globN s "ev") % 8 = 0 := (hFW0.1 (globN s "ev", 280) (by simp)).2.1
            have ha8 : (globN s "ev" + off) % 8 = 0 := by omega
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl
            · rcases hfresh_m with rfl | ⟨hf8, _, _, hfin2⟩
              · intro ⟨_, hc2⟩; dsimp only at hc2; omega
              · obtain ⟨he0_scr, _⟩ := (hFW0.1 (globN s "ev", 280) (by simp)).1
                exact not_cellHits_of_disj_aligned (i := (globN s "ev", 280)) ha8 hf8
                  (Nat.le_add_right _ off) (Nat.add_le_add_left hoff _)
                  (Or.inr (Or.inr (Or.inr (by dsimp only at he0_scr ⊢; omega))))
            · have hold_8 : (memW s (globN s "ev" + 8)) % 8 = 0 :=
                (hFW0.1 (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232)) (by simp)).2.1
              have hpw_fo := hInv.2.choose_spec.2.2.2.2.2.2.2.1
              have hch_s : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl := ⟨_, rfl⟩
              obtain ⟨tl_s, hch_s_eq⟩ := hch_s
              rw [hch_s_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw_fo
              have hd_stk : Disj (globN s "ev", 280) (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232)) := by
                have hp0 := hpw_fo.1; unfold frameObjects at hp0
                exact (List.pairwise_cons.1 hp0).1 _ (by simp)
              exact not_cellHits_of_disj_aligned (i := (globN s "ev", 280)) ha8 hold_8
                (Nat.le_add_right _ off) (Nat.add_le_add_left hoff _) hd_stk
          rw [evaluateHOLFiniteState_seq_line780]
          rcases hst_sp : evaluateHOLFiniteState m1
              (.store (.op .add [.var .global (ofString "ev"), .const 16#64])
                (.op .add [.var .local (ofString "sp"), .const 1#64])) with ⟨rsp_st, m2⟩
          simp only [hst_sp]
          cases rsp_st with
          | some res_sp =>
            have herr := store_some_eq_error' hst_sp; subst herr; dsimp only; exact herr_triv
          | none =>
            dsimp only
            have hm1_ev : m1.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
              rw [hm1_glob]; exact hm_ev
            have hm1_sp : m1.locals.lookup (ofString "sp") = some (.val (.word spw)) := by
              rw [hm1_loc]; exact hm_sp
            obtain ⟨w_sp1, hw_sp1_ev, hm2_eq⟩ := store_global_off_word (t := m1) (post := m2)
              (gname := "ev") (gbase := globN s "ev") (off := 16) hm1_ev hevw_nat (by omega)
              (fun v hv => by
                simp [evalHOLExact, evalListHOLExact, hm1_sp, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
                exact ⟨_, hv.symm⟩) hst_sp
            have hw_sp1_val : w_sp1 = spw + 1#64 := by
              simp [evalHOLExact, evalListHOLExact, hm1_sp, wordOpHOL, wordOp, valueIsWord, valueWord] at hw_sp1_ev
              exact hw_sp1_ev.symm
            subst hw_sp1_val
            have heff_st_sp := (ByteRegionEffect.of_store_word (Rl := [(globN s "ev", 280)])
              (heff_st_v.memaddrs.trans hAm.1.memaddrs) hst_sp
              (fun v hv => by
                simp [evalHOLExact, evalListHOLExact, hm1_sp, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
                exact ⟨_, hv.symm⟩)
              (fun addr hdst _ => by
                simp [evalHOLExact, evalListHOLExact, hm1_ev, wordOpHOL, wordOp, valueIsWord, valueWord] at hdst
                have h16_eq : (evw + 16#64).toNat = globN s "ev" + 16 := by
                  have : (16#64 : BitVec 64).toNat = 16 := rfl
                  rw [BitVec.toNat_add, hevw_nat, this, Nat.mod_eq_of_lt (by omega)]
                exact ⟨(globN s "ev", 280), by simp, by rw [← hdst, h16_eq]; dsimp only; omega,
                  by rw [← hdst, h16_eq]; dsimp only; omega⟩)).1
            have heff_st_sp_sbe : ScratchByteEff m1 m2
                [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))] :=
              (ScratchByteEff.of_bre heff_st_sp).mono (fun x hx => by
                simp at hx; subst hx; exact ⟨(globN s "ev", 280), by simp, le_refl _, le_refl _⟩)
            rw [evaluateHOLFiniteState_return]
            have hc0_m2 : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a)) (.const (0 : BitVec 64)) =
                some (.val (.word 0)) := rfl
            have hc0_m2' : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a)) (.const 0#64) =
                some (.val (.word 0#64)) := rfl
            simp only [hc0_m2, hc0_m2']
            have hsz0 : sizeOfShapeWithContextHOL m2.structs
                (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
              simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
            have hsz0' : sizeOfShapeWithContextHOL m2.structs
                (shapeOfHOLExact (.val (.word 0#64))) ≤ 32 := by
              simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
            simp only [hsz0, hsz0', ↓reduceIte]
            let post := { m2.emptyLocalsHOLFinite with
              locals := (m2.emptyLocalsHOLFinite.locals.resVarEq (ofString "cap", s1.locals.lookup (ofString "cap"))).resVarEq
                (ofString "sp", s.locals.lookup (ofString "sp")) }
            have heff_total : ScratchByteEff s post
                [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))] :=
              ((heff_m.trans heff_st_v).trans heff_st_sp_sbe).with_locals_clock post.locals m2.clock
            have hpost_glob_m : post.globals = m.globals := by
              simp [post, emptyLocalsHOLFinite, hm2_eq, hm1_glob]
            have hApost : ArenaReady post :=
              ⟨guestInv_congr (s := m) (by simp [post, emptyLocalsHOLFinite, hm2_eq, heff_st_v.code])
                (by simp [post, emptyLocalsHOLFinite, hm2_eq, heff_st_v.memaddrs])
                (by simp [post, emptyLocalsHOLFinite, hm2_eq, heff_st_v.shMemaddrs])
                (by simp [post, emptyLocalsHOLFinite, hm2_eq, heff_st_v.baseAddr]) hAm.1,
               arenaOK_congr hpost_glob_m hAm.2⟩
            have hsc_post : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by
              unfold globN; rw [hpost_glob_m]; exact hsc_m
            have hfresh_post : freshIvl = (0, 0) ∨
                (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
                  Inside freshIvl (globN post "scratch_ptr") (globN s "scratch_ptr")) := by
              unfold globN; rw [hpost_glob_m]; exact hfresh_m
            have hm2_memW_ne16 : ∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 16 →
                memW post (globN s "ev" + off) = memW m (globN s "ev" + off) := by
              intro off hoff hoff8 hne16
              change memW m2 (globN s "ev" + off) = memW m (globN s "ev" + off)
              rw [hm2_eq, memW_updW_ne m1 (globN s "ev" + 16) (globN s "ev" + off) _ (by omega) (by omega) (by omega),
                  hm1_e0_eq off hoff hoff8]
            have hm2_memW_16 : memW post (globN s "ev" + 16) = spw.toNat + 1 := by
              change memW m2 (globN s "ev" + 16) = spw.toNat + 1
              rw [hm2_eq, memW_updW_same m1 (globN s "ev" + 16) (spw + 1#64)]
              have : (1#64 : BitVec 64).toNat = 1 := rfl
              rw [BitVec.toNat_add, this, Nat.mod_eq_of_lt (by omega)]
            have he0_post : ∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 8 → off ≠ 16 → off ≠ 232 →
                memW post (globN s "ev" + off) = memW s (globN s "ev" + off) := by
              intro off hoff hoff8 h8 h16 h232
              rw [hm2_memW_ne16 off hoff hoff8 h16, he0_m off hoff hoff8 h8 h16 h232]
            have hnew_post :
                (freshIvl.2 = 0 ∧ memW post (globN s "ev" + 8) = memW s (globN s "ev" + 8) ∧
                  memW post (globN s "ev" + 232) = memW s (globN s "ev" + 232)) ∨
                (freshIvl.2 ≠ 0 ∧ (memW post (globN s "ev" + 8), 32 * memW post (globN s "ev" + 232)) = freshIvl) := by
              rw [hm2_memW_ne16 8 (by omega) (by omega) (by omega),
                  hm2_memW_ne16 232 (by omega) (by omega) (by omega)]
              exact hnew_m
            have hcap_post :
                1 ≤ memW post (globN s "ev" + 232) ∧
                memW post (globN s "ev" + 16) ≤ memW post (globN s "ev" + 232) ∧
                memW post (globN s "ev" + 232) ≤ 1024 := by
              rw [hm2_memW_ne16 232 (by omega) (by omega) (by omega), hm2_memW_16]
              exact ⟨by omega, by omega, hmcap_le⟩
            obtain ⟨hInv_p, hch_p, hR_p⟩ := evmInv_of_head_stack_push hInv hApost hsc_post
              heff_total hfresh_post he0_post hnew_post hcap_post
            constructor
            · intro _ _
              refine ⟨hInv_p, hch_p, le_of_eq hR_p, fun g hg => ?_⟩
              unfold globN; rw [hpost_glob_m, hm_glob_other g hg]
            · rintro ⟨_, h⟩; cases h
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
      have hcmp_grow : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
          (.cmp .notLower (.var .local (ofString "sp")) (.var .local (ofString "cap"))) =
          some (.val (.word (if capw ≤ spw then 1 else 0))) := by
        simp only [evalHOLExact, hs2_sp, hs2_cap, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, BitVec.le_def]
        by_cases hle : capw.toNat ≤ spw.toNat
        · have hnot : ¬ spw.toNat < capw.toNat := by omega
          simp [hle, hnot]
        · have hlt : spw.toNat < capw.toNat := by omega
          simp [hle, hlt]
      rw [hcmp_grow] at hnt ⊢; dsimp only at hnt ⊢
      by_cases hgrow : capw ≤ spw
      · have hsp_eq_cap : spw.toNat = capw.toNat := by
          rw [BitVec.le_def] at hgrow; omega
        have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
        simp only [hgrow, ↓reduceIte, h10] at hnt ⊢
        dsimp only [growBranch] at hnt ⊢
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
        have hcmp_cap1024 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
            (.cmp .notLower (.var .local (ofString "cap")) (.const 1024#64)) =
            some (.val (.word (if 1024 ≤ capw.toNat then 1 else 0))) := by
          have h1024 : (1024#64 : BitVec 64).toNat = 1024 := rfl
          simp only [evalHOLExact, hs2_cap, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, h1024]
          by_cases hle : 1024 ≤ capw.toNat
          · have hnot : ¬ capw.toNat < 1024 := by omega
            simp [hle, hnot]
          · have hlt : capw.toNat < 1024 := by omega
            simp [hle, hlt]
        rw [hcmp_cap1024] at hnt ⊢; dsimp only at hnt ⊢
        by_cases hcap1024 : 1024 ≤ capw.toNat
        · simp only [hcap1024, ↓reduceIte, h10] at hnt ⊢
          rcases hr3 : evaluateHOLFiniteState s2 (.raise (ofString "EvmErr") (.const 3#64)) with ⟨rr3, sr3⟩
          have hr3_nn : rr3 ≠ none := by
            intro h; subst h; exact raise_ne_none s2 _ (.const 3#64) (by rw [hr3])
          simp only [hr3]
          cases rr3 with
          | none => exact absurd rfl hr3_nn
          | some _ =>
            dsimp only
            have hru := raise3_unchanged_post (s := s) (t := s2) hInv
              (fun L => (L.resVarEq (ofString "cap", s1.locals.lookup (ofString "cap"))).resVarEq
                (ofString "sp", s.locals.lookup (ofString "sp")))
              (by cases s; rfl)
            dsimp only at hru; rw [hr3] at hru; exact hru
        · have hcap_lt1024 : capw.toNat < 1024 := by omega
          simp only [hcap1024, ↓reduceIte, evaluateHOLFiniteState_skip] at hnt ⊢
          rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
          have hmul2 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
              (.panop .mul [.var .local (ofString "cap"), .const 2#64]) =
              some (.val (.word (capw * 2#64))) := by
            simp [evalHOLExact, evalListHOLExact, hs2_cap, panOpHOL, valueIsWord, valueWord]
          rw [hmul2] at hnt ⊢; dsimp only at hnt ⊢
          have hsh_ncap : shapeEqHOL .one (shapeOfHOLExact (.val (.word (capw * 2#64)))) = true := by
            simp [shapeEqHOL, shapeOfHOLExact]
          rw [if_pos hsh_ncap] at hnt ⊢; dsimp only at hnt ⊢
          set s3 := setVarHOLFinite (ofString "ncap") (.val (.word (capw * 2#64))) s2 with hs3
          have hncap0_nat : (capw * 2#64).toNat = 2 * capw.toNat := by
            have : (2#64 : BitVec 64).toNat = 2 := rfl
            rw [BitVec.toNat_mul, this, Nat.mod_eq_of_lt (by omega)]; omega
          have hite_ncap : ∃ (s4 : PanSemStateFiniteExact 64 F) (ncapw : BitVec 64),
              evaluateHOLFiniteState s3
                (.ite (.cmp .lower (.const 1024#64) (.var .local (ofString "ncap")))
                  (.assign .local (ofString "ncap") (.const 1024#64))
                  .skip) = (none, s4) ∧
              s4 = { s with locals := s4.locals, clock := s.clock } ∧
              s4.locals.lookup (ofString "ncap") = some (.val (.word ncapw)) ∧
              s4.locals.lookup (ofString "sp") = some (.val (.word spw)) ∧
              s4.locals.lookup (ofString "v") =
                some (.rStruct [.val (.word vw0), .val (.word vw1), .val (.word vw2), .val (.word vw3)]) ∧
              capw.toNat < ncapw.toNat ∧ ncapw.toNat ≤ 1024 := by
            have hs3_ncap : s3.locals.lookup (ofString "ncap") = some (.val (.word (capw * 2#64))) := by
              simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            rw [evaluateHOLFiniteState_ite]
            have hcmp_nc : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
                (.cmp .lower (.const 1024#64) (.var .local (ofString "ncap"))) =
                some (.val (.word (if 1024#64 < capw * 2#64 then 1 else 0))) := by
              simp [evalHOLExact, hs3_ncap, Compiler.Encoders.Asm.wordCmpHOL]
            rw [hcmp_nc]; dsimp only
            by_cases hgt1024 : 1024#64 < capw * 2#64
            · simp only [hgt1024, ↓reduceIte, h10, evaluateHOLFiniteState_assign]
              have hev1024 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
                  (.const 1024#64) = some (.val (.word 1024#64)) := rfl
              have hval1024 : s3.isValidValueHOLFinite .local (ofString "ncap") (.val (.word 1024#64)) = true := by
                simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hs3_ncap, shapeOfHOLExact, shapeEqHOL]
              rw [hev1024]; dsimp only; rw [if_pos hval1024]
              let s4 := setKvarHOLFinite .local (ofString "ncap") (.val (.word 1024#64)) s3
              have h1024_n : (1024#64 : BitVec 64).toNat = 1024 := rfl
              refine ⟨s4, 1024#64, rfl, by cases s; rfl, ?_, ?_, ?_, by omega, by omega⟩
              · simp [s4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              · simp [s4, hs3, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_sp,
                  show ofString "ncap" ≠ ofString "sp" by decide]
              · simp [s4, hs3, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_v,
                  show ofString "ncap" ≠ ofString "v" by decide]
            · simp only [hgt1024, ↓reduceIte, evaluateHOLFiniteState_skip]
              have hle1024 : (capw * 2#64).toNat ≤ 1024 := by
                rw [BitVec.lt_def] at hgt1024
                have : (1024#64 : BitVec 64).toNat = 1024 := rfl
                omega
              refine ⟨s3, capw * 2#64, rfl, by cases s; rfl, hs3_ncap, ?_, ?_, by omega, hle1024⟩
              · simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_sp,
                  show ofString "ncap" ≠ ofString "sp" by decide]
              · simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_v,
                  show ofString "ncap" ≠ ofString "v" by decide]
          obtain ⟨s4, ncapw, hs4_run, hs4_eq, hs4_ncap, hs4_sp, hs4_v, hncap_gt, hncap_le1024⟩ := hite_ncap
          rw [evaluateHOLFiniteState_seq_line780, hs4_run] at hnt ⊢; dsimp only at hnt ⊢
          rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
          have hargs_sa : evalListHOLFinite s4 (h := fun a => Classical.propDecidable (s4.memaddrs a))
              [.panop .mul [.var .local (ofString "ncap"), .const 32#64]] =
              some [.val (.word (ncapw * 32#64))] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs4_ncap, panOpHOL, valueIsWord, valueWord]
          have hs4_code : s4.code = originalRuntimeCode := by rw [hs4_eq]; exact hcode
          have hlk_sa := pan_one_word_lookup s4.code.lookup (ofString "scratch_alloc") (ofString "n")
            (sourceFnBody Guest.Software.guestFn_scratch_alloc) (ncapw * 32#64)
            (by rw [hs4_code]; exact scratch_alloc_lookup_pub)
          rw [hargs_sa] at hnt ⊢; dsimp only at hnt ⊢
          rw [hlk_sa] at hnt ⊢; dsimp only at hnt ⊢
          by_cases hs4_clk0 : s4.clock = 0
          · rw [if_pos hs4_clk0] at hnt; simp at hnt
          · rw [if_neg hs4_clk0] at hnt ⊢
            let saCallee := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word (ncapw * 32#64)))
            let saEntry := callEntryStateHOLFinite s4 saCallee
            have hsa_code : saEntry.code = originalRuntimeCode := hs4_code
            have hsa_no_evmErr := scratch_alloc_body_no_evmErr saEntry hsa_code
            rcases hsa_run : evaluateHOLFiniteState saEntry
                (sourceFnBody Guest.Software.guestFn_scratch_alloc) with ⟨rsa, saPost⟩
            rw [hsa_run] at hsa_no_evmErr
            have hsa_run_raw : evaluateHOLFiniteState
                (callEntryStateHOLFinite s4 (HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word (ncapw * 32#64)))))
                (sourceFnBody Guest.Software.guestFn_scratch_alloc) = (rsa, saPost) := hsa_run
            simp only [hsa_run_raw] at hnt ⊢
            cases rsa with
            | none => exact herr_triv
            | some rsa0 =>
              cases rsa0 with
              | timeOut => simp at hnt
              | exception eid ev =>
                dsimp only at hnt ⊢
                by_cases heid : eid = ofString "EvmErr"
                · subst heid; exact absurd ⟨ev, rfl⟩ hsa_no_evmErr
                · constructor
                  · intro _ h; cases h
                  · rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact (heid h1).elim
              | «break» => exact herr_triv
              | «continue» => exact herr_triv
              | finalFfi _ =>
                constructor
                · intro _ h; cases h
                · rintro ⟨_, h⟩; cases h
              | error => exact herr_triv
              | returned vsa =>
                have hsa_sp_lk : saEntry.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp_g_w)) := by
                  change s4.globals.lookup _ = _; rw [hs4_eq]; exact hsp_g_lk
                have hsa_fp_lk : saEntry.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fp_w)) := by
                  change s4.globals.lookup _ = _; rw [hs4_eq]; exact hfp_lk
                have hsa_n_lk : saEntry.locals.lookup (ofString "n") = some (.val (.word (ncapw * 32#64))) := by
                  simp [saEntry, saCallee, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                obtain ⟨rfl, hcmp1_sa, hcmp2_sa, hsaPost_eq_raw⟩ :=
                  Wave8Contracts.M26.scratch_alloc_body_run saEntry sp_g_w fp_w (ncapw * 32#64)
                    hsa_code hsa_sp_lk hsa_fp_lk hsa_n_lk vsa (by rw [hsa_run])
                have hsaPost_eq : saPost = { saEntry with
                    globals := saEntry.globals.update (ofString "scratch_ptr", .val (.word ((sp_g_w - ncapw * 32#64) &&& ((0 : BitVec 64) - 8)))),
                    locals := saPost.locals } := by
                  rw [hsa_run] at hsaPost_eq_raw; exact hsaPost_eq_raw
                dsimp only [saEntry] at hsaPost_eq
                set nsw : BitVec 64 := (sp_g_w - ncapw * 32#64) &&& ((0 : BitVec 64) - 8)
                have hsh_ns : (shapeEqHOL (shapeOfHOLExact (.val (.word nsw) : ValueHOL 64)) .one &&
                    shapeEqHOL (shapeOfHOLExact (.val (.word nsw) : ValueHOL 64)) .one) = true := by
                  simp [shapeEqHOL, shapeOfHOLExact]
                have hsh_ns' : (shapeEqHOL (shapeOfHOLExact (.val (.word nsw) : ValueHOL 64)) .one &&
                    shapeEqHOL .one (shapeOfHOLExact (.val (.word nsw) : ValueHOL 64))) = true := by
                  simp [shapeEqHOL, shapeOfHOLExact]
                dsimp only at hnt ⊢
                simp only [hsh_ns, hsh_ns', ↓reduceIte] at hnt ⊢
                have hn_bytes : (ncapw * 32#64).toNat = 32 * ncapw.toNat := by
                  have : (32#64 : BitVec 64).toNat = 32 := rfl
                  rw [BitVec.toNat_mul, this, Nat.mod_eq_of_lt (by omega)]; omega
                have hsub_pf : (sp_g_w - fp_w).toNat = sp_g_w.toNat - fp_w.toNat := by
                  rw [BitVec.toNat_sub]
                  have hle_fp_sp : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hInv.1.2.2.2.2.1
                  omega
                have hsp_g_al : sp_g_w.toNat % 8 = 0 := by
                  have h8 : globN s "scratch_ptr" % 8 = 0 := hInv.1.2.2.2.2.2.2.2.2.1
                  rw [hsp_g_nat]; exact h8
                have hn_le_sp_g : (ncapw * 32#64).toNat ≤ sp_g_w.toNat := by
                  have := sp_g_w.isLt; have := fp_w.isLt; omega
                have hsub_pn : (sp_g_w - ncapw * 32#64).toNat = sp_g_w.toNat - 32 * ncapw.toNat := by
                  rw [BitVec.toNat_sub, hn_bytes]; omega
                have hnsw_nat : nsw.toNat = sp_g_w.toNat - 32 * ncapw.toNat := by
                  have hand := and_neg8_toNat (sp_g_w - ncapw * 32#64)
                  change nsw.toNat = (sp_g_w - ncapw * 32#64).toNat / 8 * 8 at hand
                  rw [hsub_pn] at hand; omega
                have hnsw_al : nsw.toNat % 8 = 0 := by omega
                have hnsw_ge_fp : globN s "frame_mem_ptr" ≤ nsw.toNat := by
                  rw [← hfp_nat]; exact Nat.le_of_not_lt hcmp2_sa
                have hnsw_end : nsw.toNat + 32 * ncapw.toNat = globN s "scratch_ptr" := by
                  rw [← hsp_g_nat]; omega
                set s5 := setVarHOLFinite (ofString "ns") (.val (.word nsw)) { saPost with locals := s4.locals } with hs5
                have hs5_ns : s5.locals.lookup (ofString "ns") = some (.val (.word nsw)) := by
                  simp [hs5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                have hs5_ncap : s5.locals.lookup (ofString "ncap") = some (.val (.word ncapw)) := by
                  simp [hs5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_ncap,
                    show ofString "ns" ≠ ofString "ncap" by decide]
                have hs5_sp : s5.locals.lookup (ofString "sp") = some (.val (.word spw)) := by
                  simp [hs5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_sp,
                    show ofString "ns" ≠ ofString "sp" by decide]
                have hs5_v : s5.locals.lookup (ofString "v") =
                    some (.rStruct [.val (.word vw0), .val (.word vw1), .val (.word vw2), .val (.word vw3)]) := by
                  simp [hs5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_v,
                    show ofString "ns" ≠ ofString "v" by decide]
                have hs5_mem : s5.memory = s.memory := by
                  change saPost.memory = s.memory; rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq]
                have hs5_glob : s5.globals = s.globals.update (ofString "scratch_ptr", .val (.word nsw)) := by
                  change saPost.globals = _; rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq]
                have hs5_code : s5.code = originalRuntimeCode := by
                  change saPost.code = _; rw [hsaPost_eq]; exact hsa_code
                have hs5_ma : s5.memaddrs = ordinaryDomain := by
                  change saPost.memaddrs = _; rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq]; exact hInv.1.1.memaddrs
                have hs5_ev : s5.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                  rw [hs5_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hevw,
                    show ofString "scratch_ptr" ≠ ofString "ev" by decide]
                let mcCall : ProgHOL 64 :=
                  .call (some (none, none)) (ofString "memcpy")
                    [.var .local (ofString "ns"),
                     .load .one (.op .add [.var .global (ofString "ev"), .const 8#64]),
                     .panop .mul [.var .local (ofString "sp"), .const 32#64]]
                let st8Prog : ProgHOL 64 :=
                  .store (.op .add [.var .global (ofString "ev"), .const 8#64]) (.var .local (ofString "ns"))
                let st232Prog : ProgHOL 64 :=
                  .store (.op .add [.var .global (ofString "ev"), .const 232#64]) (.var .local (ofString "ncap"))
                rcases hs5_m8 : s5.memory (evw + 8#64) with ⟨oldStkw⟩
                have hs5_dom8 : s5.memaddrs (evw + 8#64) := by
                  rw [hs5_ma, hInv.1.1.memaddrs.symm]
                  have hev8_eq : evw + 8#64 = BitVec.ofNat 64 (globN s "ev" + 8) := by
                    apply BitVec.eq_of_toNat_eq
                    have : (8#64 : BitVec 64).toNat = 8 := rfl
                    rw [BitVec.toNat_add, hevw_nat, this, BitVec.toNat_ofNat]
                  rw [hev8_eq]
                  exact ((hFW0.1 (globN s "ev", 280) (by simp)).2.2.2 1 (by omega)).choose_spec.1
                have hev_mc_src : @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a))
                    (.load .one (.op .add [.var .global (ofString "ev"), .const 8#64])) =
                    some (.val (.word oldStkw)) := by
                  simp [evalHOLExact, evalListHOLExact, hs5_ev, wordOpHOL, wordOp, valueIsWord, valueWord,
                    memLoadHOLExact, hs5_dom8, hs5_m8]
                have hev_mc_dst : @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a))
                    (.var .local (ofString "ns")) = some (.val (.word nsw)) := hs5_ns
                have hev_mc_n : @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a))
                    (.panop .mul [.var .local (ofString "sp"), .const 32#64]) =
                    some (.val (.word (spw * 32#64))) := by
                  simp [evalHOLExact, evalListHOLExact, hs5_sp, panOpHOL, valueIsWord, valueWord]
                have hsp32_nat : (spw * 32#64).toNat = 32 * spw.toNat := by
                  have : (32#64 : BitVec 64).toNat = 32 := rfl
                  rw [BitVec.toNat_mul, this, Nat.mod_eq_of_lt (by omega)]; omega
                let freshIvl : Ivl := (nsw.toNat, 32 * ncapw.toNat)
                have hnt_mc : (evaluateHOLFiniteState s5 mcCall).1 ≠ some .timeOut := by
                  intro hto
                  rcases hmc_to : evaluateHOLFiniteState s5
                      (.call (some (none, none)) (ofString "memcpy")
                        [.var .local (ofString "ns"),
                         .load .one (.op .add [.var .global (ofString "ev"), .const 8#64]),
                         .panop .mul [.var .local (ofString "sp"), .const 32#64]]) with ⟨rmc_to, smc_to⟩
                  have hto' : rmc_to = some .timeOut := by
                    dsimp only [mcCall] at hto; rw [hmc_to] at hto; exact hto
                  subst hto'
                  rw [evaluateHOLFiniteState_seq_line780] at hnt
                  simp [hmc_to] at hnt
                have hmc := M11.eval_call_memcpy_bre s5 _ _ _ nsw oldStkw (spw * 32#64) [freshIvl]
                  hs5_code hs5_ma hev_mc_dst hev_mc_src hev_mc_n
                  (fun _ => ⟨freshIvl, by simp, le_refl _, by dsimp only [freshIvl]; omega⟩) hnt_mc
                dsimp only at hmc
                rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
                rcases hmc_run : evaluateHOLFiniteState s5 mcCall with ⟨rmc, s6⟩
                rw [hmc_run] at hmc
                have hmc_run_raw : evaluateHOLFiniteState s5
                    (.call (some (none, none)) (ofString "memcpy")
                      [.var .local (ofString "ns"),
                       .load .one (.op .add [.var .global (ofString "ev"), .const 8#64]),
                       .panop .mul [.var .local (ofString "sp"), .const 32#64]]) = (rmc, s6) := hmc_run
                simp only [hmc_run_raw] at hnt ⊢
                cases rmc with
                | some rmc0 =>
                  dsimp only at hnt ⊢
                  have hnr := hmc.2 (by simp)
                  refine ⟨fun v hv => absurd (Or.inl ⟨v, hv⟩) hnr, ?_⟩
                  rintro ⟨ev, hv⟩
                  injection hv with hv'; subst hv'
                  exact absurd (Or.inr ⟨ofString "EvmErr", ev, rfl, by decide⟩) hnr
                | none =>
                  dsimp only at hnt ⊢
                  obtain ⟨heff_mc_m11, hs6_loc⟩ := hmc.1 rfl
                  have heff_mc : ScratchByteEff s5 s6 [freshIvl] := ScratchByteEff.of_m11_bre heff_mc_m11
                  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
                  rcases hst8 : evaluateHOLFiniteState s6 st8Prog with ⟨rst8, s7⟩
                  have hst8_raw : evaluateHOLFiniteState s6
                      (.store (.op .add [.var .global (ofString "ev"), .const 8#64]) (.var .local (ofString "ns"))) = (rst8, s7) := hst8
                  simp only [hst8_raw] at hnt ⊢
                  cases rst8 with
                  | some res8 =>
                    have herr := store_some_eq_error' hst8; subst herr; dsimp only; exact herr_triv
                  | none =>
                    dsimp only at hnt ⊢
                    have hs6_ev : s6.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                      rw [heff_mc_m11.globals]; exact hs5_ev
                    have hs6_ns : s6.locals.lookup (ofString "ns") = some (.val (.word nsw)) := by
                      rw [hs6_loc]; exact hs5_ns
                    obtain ⟨w_ns', hw_ns_ev, hs7_eq⟩ := store_global_off_word (t := s6) (post := s7)
                      (gname := "ev") (gbase := globN s "ev") (off := 8) hs6_ev hevw_nat (by omega)
                      (fun v hv => by
                        change s6.locals.lookup (ofString "ns") = some v at hv
                        rw [hs6_ns] at hv; injection hv with hv'; exact ⟨nsw, hv'.symm⟩) hst8
                    have hw_ns_val : nsw = w_ns' := by
                      change s6.locals.lookup (ofString "ns") = some (.val (.word w_ns')) at hw_ns_ev
                      rw [hs6_ns] at hw_ns_ev
                      injection hw_ns_ev with h1; injection h1 with h2; injection h2 with h3
                    subst w_ns'
                    have heff_st8 := (ByteRegionEffect.of_store_word (Rl := [(globN s "ev", 280)])
                      (heff_mc_m11.memaddrs.trans hs5_ma) hst8
                      (fun v hv => by
                        change s6.locals.lookup (ofString "ns") = some v at hv
                        rw [hs6_ns] at hv; injection hv with hv'; exact ⟨nsw, hv'.symm⟩)
                      (fun addr hdst _ => by
                        simp [evalHOLExact, evalListHOLExact, hs6_ev, wordOpHOL, wordOp, valueIsWord, valueWord] at hdst
                        have h8_eq : (evw + 8#64).toNat = globN s "ev" + 8 := by
                          have : (8#64 : BitVec 64).toNat = 8 := rfl
                          rw [BitVec.toNat_add, hevw_nat, this, Nat.mod_eq_of_lt (by omega)]
                        exact ⟨(globN s "ev", 280), by simp, by rw [← hdst, h8_eq]; dsimp only; omega,
                          by rw [← hdst, h8_eq]; dsimp only; omega⟩)).1
                    rcases hst232 : evaluateHOLFiniteState s7 st232Prog with ⟨rst232, s8⟩
                    have hst232_raw : evaluateHOLFiniteState s7
                        (.store (.op .add [.var .global (ofString "ev"), .const 232#64]) (.var .local (ofString "ncap"))) = (rst232, s8) := hst232
                    simp only [hst232_raw] at hnt ⊢
                    cases rst232 with
                    | some res232 =>
                      have herr := store_some_eq_error' hst232; subst herr; dsimp only; exact herr_triv
                    | none =>
                      dsimp only at hnt ⊢
                      have hs7_ev : s7.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                        rw [hs7_eq]; exact hs6_ev
                      have hs7_ncap : s7.locals.lookup (ofString "ncap") = some (.val (.word ncapw)) := by
                        rw [hs7_eq]; dsimp only; rw [hs6_loc]; exact hs5_ncap
                      obtain ⟨w_ncap', hw_ncap_ev, hs8_eq⟩ := store_global_off_word (t := s7) (post := s8)
                        (gname := "ev") (gbase := globN s "ev") (off := 232) hs7_ev hevw_nat (by omega)
                        (fun v hv => by
                          change s7.locals.lookup (ofString "ncap") = some v at hv
                          rw [hs7_ncap] at hv; injection hv with hv'; exact ⟨ncapw, hv'.symm⟩) hst232
                      have hw_ncap_val : ncapw = w_ncap' := by
                        change s7.locals.lookup (ofString "ncap") = some (.val (.word w_ncap')) at hw_ncap_ev
                        rw [hs7_ncap] at hw_ncap_ev
                        injection hw_ncap_ev with h1; injection h1 with h2; injection h2 with h3
                      subst w_ncap'
                      have heff_st232 := (ByteRegionEffect.of_store_word (Rl := [(globN s "ev", 280)])
                        (by rw [hs7_eq]; exact heff_mc_m11.memaddrs.trans hs5_ma) hst232
                        (fun v hv => by
                          change s7.locals.lookup (ofString "ncap") = some v at hv
                          rw [hs7_ncap] at hv; injection hv with hv'; exact ⟨ncapw, hv'.symm⟩)
                        (fun addr hdst _ => by
                          simp [evalHOLExact, evalListHOLExact, hs7_ev, wordOpHOL, wordOp, valueIsWord, valueWord] at hdst
                          have h232_eq : (evw + 232#64).toNat = globN s "ev" + 232 := by
                            have : (232#64 : BitVec 64).toNat = 232 := rfl
                            rw [BitVec.toNat_add, hevw_nat, this, Nat.mod_eq_of_lt (by omega)]
                          exact ⟨(globN s "ev", 280), by simp, by rw [← hdst, h232_eq]; dsimp only; omega,
                            by rw [← hdst, h232_eq]; dsimp only; omega⟩)).1
                      let m : PanSemStateFiniteExact 64 F :=
                        { s8 with
                          locals := (s8.locals.resVarEq (ofString "ns", s4.locals.lookup (ofString "ns"))).resVarEq
                            (ofString "ncap", s2.locals.lookup (ofString "ncap")) }
                      change (let out := evaluateHOLFiniteState m tailProg
                        let post := { out.2 with
                          locals := (out.2.locals.resVarEq (ofString "cap", s1.locals.lookup (ofString "cap"))).resVarEq
                            (ofString "sp", s.locals.lookup (ofString "sp")) }
                        (∀ v, out.1 = some (.returned v) →
                          EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s ∧
                          (∀ g : String, ofString g ≠ ofString "scratch_ptr" → globN post g = globN s g)) ∧
                        (IsEvmErr out.1 →
                          EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s))
                      have hm_glob : m.globals = s.globals.update (ofString "scratch_ptr", .val (.word nsw)) := by
                        dsimp only [m]; rw [hs8_eq, hs7_eq]; dsimp only; rw [heff_mc_m11.globals, hs5_glob]
                      have hm_sp_glob : globN m "scratch_ptr" = nsw.toNat := by
                        unfold globN; rw [hm_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
                      have hm_other_glob : ∀ g : String, ofString g ≠ ofString "scratch_ptr" →
                          m.globals.lookup (ofString g) = s.globals.lookup (ofString g) := by
                        intro g hg; rw [hm_glob]
                        simp [HolFiniteMapExact.lookup_update, FUPDATE, hg, Ne.symm hg]
                      have hm_G : GuestInv m := by
                        have hcode_m : m.code = s.code := by
                          dsimp only [m]; rw [hs8_eq, hs7_eq]; dsimp only
                          rw [heff_mc_m11.code, hs5_code, hcode]
                        have hma_m : m.memaddrs = s.memaddrs := by
                          dsimp only [m]; rw [hs8_eq, hs7_eq]; dsimp only
                          rw [heff_mc_m11.memaddrs, hs5_ma, hInv.1.1.memaddrs]
                        have hsh_m : m.shMemaddrs = s.shMemaddrs := by
                          dsimp only [m]; rw [hs8_eq, hs7_eq]; dsimp only
                          rw [heff_mc_m11.shMemaddrs]
                          change saPost.shMemaddrs = s.shMemaddrs
                          rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq]
                        have hba_m : m.baseAddr = s.baseAddr := by
                          dsimp only [m]; rw [hs8_eq, hs7_eq]; dsimp only
                          rw [heff_mc_m11.baseAddr]
                          change saPost.baseAddr = s.baseAddr
                          rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq]
                        exact guestInv_congr hcode_m hma_m hsh_m hba_m hInv.1.1
                      have hsc_m : globN m "scratch_ptr" ≤ globN s "scratch_ptr" := by
                        rw [hm_sp_glob]; omega
                      have hAm : ArenaReady m := by
                        refine ⟨hm_G, ?_⟩
                        unfold ArenaOK
                        have hhp_m : globN m "heap_ptr" = globN s "heap_ptr" :=
                          R16Shards.OpHandlers.globN_eq_of_lookup_eq (hm_other_glob "heap_ptr" (by decide))
                        have hfp_m : globN m "frame_mem_ptr" = globN s "frame_mem_ptr" :=
                          R16Shards.OpHandlers.globN_eq_of_lookup_eq (hm_other_glob "frame_mem_ptr" (by decide))
                        rw [hhp_m, hfp_m, hm_sp_glob]
                        have hA := hInv.1.2
                        exact ⟨hA.1, hA.2.1, hA.2.2.1, hnsw_ge_fp,
                          le_trans (by omega : nsw.toNat ≤ globN s "scratch_ptr") hA.2.2.2.2.1,
                          hA.2.2.2.2.2.1, hA.2.2.2.2.2.2.1, hnsw_al,
                          globalsWord_update (ofString "scratch_ptr") nsw hm_glob hA.2.2.2.2.2.2.2.2⟩
                      have heff_s_s5 : ScratchByteEff s s5 [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))] :=
                        ⟨hs5_code.trans hcode.symm,
                         hs5_ma.trans hInv.1.1.memaddrs.symm,
                         by change saPost.shMemaddrs = _; rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq],
                         by change saPost.baseAddr = _; rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq],
                         by change saPost.be = _; rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq],
                         fun g hg => by
                           change saPost.globals.lookup (ofString g) = _; rw [hsaPost_eq]
                           dsimp only [callEntryStateHOLFinite]; rw [hs4_eq]
                           simp [HolFiniteMapExact.lookup_update, FUPDATE, hg, Ne.symm hg],
                         fun a _ => by rw [hs5_mem],
                         fun a _ => by rw [hs5_mem],
                         fun b _ _ => by
                           unfold memB; rw [hs5_mem]
                           have hbe5 : s5.be = s.be := by
                             change saPost.be = _; rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq]
                           rw [hbe5]⟩
                      have heff_m : ScratchByteEff s m
                          [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))] := by
                        have h1 := heff_mc.mono (R2 := [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))])
                          (fun x hx => by simp at hx; subst hx; exact ⟨freshIvl, by simp, le_refl _, le_refl _⟩)
                        have h2 := (ScratchByteEff.of_bre heff_st8).mono
                          (R2 := [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))])
                          (fun x hx => by simp at hx; subst hx; exact ⟨(globN s "ev", 280), by simp, le_refl _, le_refl _⟩)
                        have h3 := (ScratchByteEff.of_bre heff_st232).mono
                          (R2 := [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))])
                          (fun x hx => by simp at hx; subst hx; exact ⟨(globN s "ev", 280), by simp, le_refl _, le_refl _⟩)
                        exact (((heff_s_s5.trans h1).trans h2).trans h3).with_locals_clock m.locals s8.clock
                      have hs6_e0_eq : ∀ off, off + 8 ≤ 280 → off % 8 = 0 →
                          memW s6 (globN s "ev" + off) = memW s (globN s "ev" + off) := by
                        intro off hoff hoff8
                        unfold memW
                        rw [heff_mc_m11.cell_frame (BitVec.ofNat 64 (globN s "ev" + off)), hs5_mem]
                        intro x hx; simp at hx; subst hx
                        have htn : (BitVec.ofNat 64 (globN s "ev" + off)).toNat = globN s "ev" + off :=
                          Nat.mod_eq_of_lt (by omega)
                        rw [htn]
                        have he0_8 : (globN s "ev") % 8 = 0 := (hFW0.1 (globN s "ev", 280) (by simp)).2.1
                        have ha8 : (globN s "ev" + off) % 8 = 0 := by omega
                        obtain ⟨he0_scr, _⟩ := (hFW0.1 (globN s "ev", 280) (by simp)).1
                        exact not_cellHits_of_disj_aligned (i := (globN s "ev", 280)) ha8 hnsw_al
                          (Nat.le_add_right _ off) (Nat.add_le_add_left hoff _)
                          (Or.inr (Or.inr (Or.inr (by dsimp only [freshIvl] at he0_scr ⊢; omega))))
                      have hm_e0_other : ∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 8 → off ≠ 232 →
                          memW m (globN s "ev" + off) = memW s (globN s "ev" + off) := by
                        intro off hoff hoff8 hne8 hne232
                        change memW s8 (globN s "ev" + off) = memW s (globN s "ev" + off)
                        rw [hs8_eq, memW_updW_ne s7 (globN s "ev" + 232) (globN s "ev" + off) _ (by omega) (by omega) (by omega),
                            hs7_eq, memW_updW_ne s6 (globN s "ev" + 8) (globN s "ev" + off) _ (by omega) (by omega) (by omega),
                            hs6_e0_eq off hoff hoff8]
                      have hm_e0_8 : memW m (globN s "ev" + 8) = nsw.toNat := by
                        change memW s8 (globN s "ev" + 8) = nsw.toNat
                        rw [hs8_eq, memW_updW_ne s7 (globN s "ev" + 232) (globN s "ev" + 8) _ (by omega) (by omega) (by omega),
                            hs7_eq, memW_updW_same s6 (globN s "ev" + 8) nsw]
                      have hm_e0_232 : memW m (globN s "ev" + 232) = ncapw.toNat := by
                        change memW s8 (globN s "ev" + 232) = ncapw.toNat
                        rw [hs8_eq, memW_updW_same s7 (globN s "ev" + 232) ncapw]
                      have hfresh_m : freshIvl = (0, 0) ∨
                          (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
                            Inside freshIvl (globN m "scratch_ptr") (globN s "scratch_ptr")) := by
                        right; refine ⟨hnsw_al, by dsimp only [freshIvl]; omega, ?_⟩
                        rw [hm_sp_glob]; exact ⟨le_refl _, le_of_eq hnsw_end⟩
                      have hnew_m :
                          (freshIvl.2 = 0 ∧ memW m (globN s "ev" + 8) = memW s (globN s "ev" + 8) ∧
                            memW m (globN s "ev" + 232) = memW s (globN s "ev" + 232)) ∨
                          (freshIvl.2 ≠ 0 ∧ (memW m (globN s "ev" + 8), 32 * memW m (globN s "ev" + 232)) = freshIvl) := by
                        right; refine ⟨by dsimp only [freshIvl]; omega, ?_⟩
                        rw [hm_e0_8, hm_e0_232]
                      have hm_loc_s4 : ∀ k, k ≠ ofString "ns" → k ≠ ofString "ncap" →
                          m.locals.lookup k = s4.locals.lookup k := by
                        intro k hk1 hk2
                        have hres_ne : ∀ (mp : HolFiniteMapExact MlS (ValueHOL 64)) (key q : MlS) (old : Option (ValueHOL 64)),
                            key ≠ q → (mp.resVarEq (key, old)).lookup q = mp.lookup q := by
                          intro mp key q old hne
                          unfold HolFiniteMapExact.resVarEq
                          cases old with
                          | none => simp [HolFiniteMapExact.eraseEq, FDOMSUB_HOL, hne.symm]
                          | some v => simp [HolFiniteMapExact.updateEq, FUPDATE_HOL, hne.symm]
                        have hs8_l : s8.locals = s5.locals := by
                          rw [hs8_eq, hs7_eq]; exact hs6_loc
                        dsimp only [m]
                        rw [hres_ne _ _ _ _ hk2.symm,
                            hres_ne _ _ _ _ hk1.symm,
                            hs8_l]
                        simp [hs5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk1, Ne.symm hk1]
                      exact run_tail m freshIvl hAm hsc_m hm_other_glob heff_m hfresh_m
                        (fun off hoff hoff8 h8 _ h232 => hm_e0_other off hoff hoff8 h8 h232)
                        hnew_m
                        (by rw [hm_e0_232]; omega)
                        (by rw [hm_e0_232]; exact hncap_le1024)
                        (by rw [hm_e0_other 16 (by omega) (by omega) (by omega) (by omega), ← hspw_eq])
                        (by rw [hm_loc_s4 (ofString "sp") (by decide) (by decide)]; exact hs4_sp)
                        (by rw [hm_loc_s4 (ofString "v") (by decide) (by decide)]; exact hs4_v)
      · have hsp_lt_cap : spw.toNat < capw.toNat := by
          rw [BitVec.le_def] at hgrow; omega
        simp only [hgrow, ↓reduceIte, evaluateHOLFiniteState_skip] at hnt ⊢
        exact run_tail s2 (0, 0)
          ⟨guestInv_congr (s := s) rfl rfl rfl rfl hInv.1.1, hInv.1.2⟩
          (le_refl _)
          (fun _ _ => rfl)
          ((ScratchByteEff.refl s _).with_locals_clock s2.locals s.clock)
          (Or.inl rfl)
          (fun _ _ _ _ _ _ => rfl)
          (Or.inl ⟨rfl, rfl, rfl⟩)
          (by change spw.toNat < memW s (globN s "ev" + 232); rw [← hcapw_eq]; exact hsp_lt_cap)
          (by change memW s (globN s "ev" + 232) ≤ 1024; rw [← hcapw_eq]; exact hcap_le1024)
          (by change memW s (globN s "ev" + 16) = spw.toNat; exact hspw_eq.symm)
          hs2_sp hs2_v

/-! ## 3. Wrapper specs: `eps_stack_push_word` and `eps_stack_push_bool` -/

theorem eps_seq_call_ret0 {fname : MlS}
    (hf : EvmPreservingSpec (fun _ => True)
      (fun s _ post => ∀ g : String, ofString g ≠ ofString "scratch_ptr" → globN post g = globN s g) fname)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (args : List (ExpHOL 64))
    (hcode : s.code = originalRuntimeCode) (hInv : EvmInv s)
    (hnt : (evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname args) (.return (.const 0#64)))).1 ≠ some .timeOut) :
    let r := (evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname args) (.return (.const 0#64)))).1
    let post := (evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname args) (.return (.const 0#64)))).2
    (∀ v, r = some (.returned v) →
      EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s ∧
      (∀ g : String, ofString g ≠ ofString "scratch_ptr" → globN post g = globN s g)) ∧
    (IsEvmErr r →
      EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s) := by
  dsimp only
  have herr_triv : ∀ {P1 P2 : Prop},
      (∀ v, (some PanSemResultExact.error : Option (PanSemResultExact 64)) = some (.returned v) → P1) ∧
      (IsEvmErr (some PanSemResultExact.error) → P2) := by
    intro _ _; constructor
    · intro _ h; cases h
    · rintro ⟨_, h⟩; cases h
  obtain ⟨params, body, retShape, hlk, hspec⟩ := hf
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · exact herr_triv
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · exact herr_triv
    · simp only [hl] at hnt ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hbody_eq : body' = body :=
          lookupCodeHOLFinite_installed_body s.code.lookup fname params body body' retShape ret' vals callee
            (by rw [hcode]; exact hlk) hl
        subst body'
        have hret_eq : ret' = retShape := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some s.code.lookup fname vals body callee ret' hl
          rw [hcode] at hx; simp only [Flapjack.lookupCodeHOLExact, hlk] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst ret'
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, retShape) := by
          rwa [← hcode]
        have hInv_ce : EvmInv (callEntryStateHOLFinite s callee) := localsFree_evmInv s callee (s.clock - 1) hInv
        have hc_ce := evm_congr (s := s) (t := callEntryStateHOLFinite s callee) rfl rfl
        have hs_spec := hspec (callEntryStateHOLFinite s callee) hcode hInv_ce trivial ⟨vals, hl_orig⟩
        dsimp only at hs_spec
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, cpost⟩
        simp only [hrun] at hnt hs_spec ⊢
        cases res with
        | none => exact herr_triv
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned vr =>
            by_cases hsh : shapeEqHOL (shapeOfHOLExact vr) retShape = true
            · simp only [hsh, ↓reduceIte]
              obtain ⟨hInv_cp, hch_cp, hR_cp, hg_cp⟩ := (hs_spec (by simp)).1 vr rfl
              rw [evaluateHOLFiniteState_return]; dsimp only [evalHOLExact]
              have hsz0 : sizeOfShapeWithContextHOL cpost.structs
                  (shapeOfHOLExact (.val (.word 0#64))) ≤ 32 := by
                simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
              rw [if_pos hsz0]; dsimp only
              let post := ({ cpost with locals := s.locals } : PanSemStateFiniteExact 64 F).emptyLocalsHOLFinite
              have hInv_p : EvmInv post := localsFree_evmInv cpost post.locals cpost.clock hInv_cp
              have hc_p := evm_congr (s := cpost) (t := post) rfl rfl
              have hch_final : evmChain post = evmChain s := by
                have h1 : evmChain post = evmChain cpost := evmChain_congr rfl rfl
                have h2 : evmChain (callEntryStateHOLFinite s callee) = evmChain s := evmChain_congr rfl rfl
                exact h1.trans (hch_cp.trans h2)
              have hR_final : evmR post ≤ evmR s := by
                rw [hc_p.2.1]; rw [hc_ce.2.1] at hR_cp; exact hR_cp
              have hg_final : ∀ g : String, ofString g ≠ ofString "scratch_ptr" → globN post g = globN s g :=
                fun g hg => hg_cp g hg
              constructor
              · intro _ _; exact ⟨hInv_p, hch_final, hR_final, hg_final⟩
              · rintro ⟨_, h⟩; cases h
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte]
              exact herr_triv
          | exception eid ev =>
            dsimp only
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨hInv_cp, hch_cp, hR_cp⟩ := (hs_spec (by simp)).2 ⟨ev, rfl⟩
              have hInv_el : EvmInv cpost.emptyLocalsHOLFinite := localsFree_evmInv cpost _ cpost.clock hInv_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              have hch_final : evmChain cpost.emptyLocalsHOLFinite = evmChain s := by
                have h1 : evmChain cpost.emptyLocalsHOLFinite = evmChain cpost := evmChain_congr rfl rfl
                have h2 : evmChain (callEntryStateHOLFinite s callee) = evmChain s := evmChain_congr rfl rfl
                exact h1.trans (hch_cp.trans h2)
              have hR_final : evmR cpost.emptyLocalsHOLFinite ≤ evmR s := by
                rw [hc_el.2.1]; rw [hc_ce.2.1] at hR_cp; exact hR_cp
              constructor
              · intro _ h; cases h
              · intro _; exact ⟨hInv_el, hch_final, hR_final⟩
            · constructor
              · intro _ h; cases h
              · rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact (heid h1).elim
          | «break» => exact herr_triv
          | «continue» => exact herr_triv
          | finalFfi _ =>
            constructor
            · intro _ h; cases h
            · rintro ⟨_, h⟩; cases h
          | error => exact herr_triv

theorem lookup_stack_push_word :
    originalRuntimeCode.lookup (ofString "stack_push_word") =
      some ([(ofString "w", .one)], sourceFnBody Guest.Software.guestFn_stack_push_word, .one) :=
  lookup_of_guestAst_getElem 455 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_stack_push_word) rfl

theorem eps_stack_push_word :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => ∀ g : String, ofString g ≠ ofString "scratch_ptr" → globN post g = globN s g)
      (ofString "stack_push_word") := by
  refine ⟨_, _, _, lookup_stack_push_word, ?_⟩
  intro F s hcode hInv _ _ hnt
  have hb : sourceFnBody Guest.Software.guestFn_stack_push_word =
      .seq
        (.call (some (none, none)) (ofString "stack_push")
          [.rstruct [.var .local (ofString "w"), .const 0#64, .const 0#64, .const 0#64]])
        (.return (.const 0#64)) := rfl
  dsimp only; rw [hb] at hnt ⊢
  exact eps_seq_call_ret0 eps_stack_push s _ hcode hInv hnt

theorem lookup_stack_push_bool :
    originalRuntimeCode.lookup (ofString "stack_push_bool") =
      some ([(ofString "b", .one)], sourceFnBody Guest.Software.guestFn_stack_push_bool, .one) :=
  lookup_of_guestAst_getElem 456 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_stack_push_bool) rfl

theorem eps_stack_push_bool :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => ∀ g : String, ofString g ≠ ofString "scratch_ptr" → globN post g = globN s g)
      (ofString "stack_push_bool") := by
  refine ⟨_, _, _, lookup_stack_push_bool, ?_⟩
  intro F s hcode hInv _ _ hnt
  have hb : sourceFnBody Guest.Software.guestFn_stack_push_bool =
      .seq
        (.ite (.cmp .notEqual (.var .local (ofString "b")) (.const 0#64))
          (.call (some (none, none)) (ofString "stack_push")
            [.rstruct [.const 1#64, .const 0#64, .const 0#64, .const 0#64]])
          (.call (some (none, none)) (ofString "stack_push")
            [.rstruct [.const 0#64, .const 0#64, .const 0#64, .const 0#64]]))
        (.return (.const 0#64)) := rfl
  dsimp only; rw [hb] at hnt ⊢
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split
  · rename_i cw _
    by_cases hcw0 : cw = 0
    · subst hcw0; simp only [↓reduceIte]
      rw [← evaluateHOLFiniteState_seq_line780]
      intro hnt; exact eps_seq_call_ret0 eps_stack_push s _ hcode hInv hnt
    · simp only [hcw0, ↓reduceIte]
      rw [← evaluateHOLFiniteState_seq_line780]
      intro hnt; exact eps_seq_call_ret0 eps_stack_push s _ hcode hInv hnt
  · intro _
    constructor
    · intro _ h; cases h
    · rintro ⟨_, h⟩; cases h

end InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
