import InitECandidate.Solver.Wave8GuestInv.R10Shards.EvmStepLemmas

/-! R11 proofs for EVM frame contracts in `ContractParts/C08.lean` and `ContractParts/C00.lean`:
- `ek_charge_gas`
- `ek_frame_halt`
- `ek_refill_frame_state_gas`
- `ek_stack_pop`
- `ek_u256_to_be32`
- `frame_exception_spec` (and `fb_frame_exception`, `fb_frame_halt`, `fb_refill_frame_state_gas`)
-/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.EvmFrameSpecs

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.EvmBase
open InitECandidate.Solver.Wave8GuestInv.EvmStepLemmas

/-! ## 1. Lookup lemmas -/

theorem lookup_charge_gas :
    originalRuntimeCode.lookup (ofString "charge_gas") =
      some ([(ofString "amount", .one)], sourceFnBody Guest.Software.guestFn_charge_gas, .one) :=
  lookup_of_guestAst_getElem 448 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_charge_gas) rfl

theorem lookup_refill_frame_state_gas :
    originalRuntimeCode.lookup (ofString "refill_frame_state_gas") =
      some ([], sourceFnBody Guest.Software.guestFn_refill_frame_state_gas, .one) :=
  lookup_of_guestAst_getElem 452 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_refill_frame_state_gas) rfl

theorem lookup_stack_pop :
    originalRuntimeCode.lookup (ofString "stack_pop") =
      some ([], sourceFnBody Guest.Software.guestFn_stack_pop, .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 453 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_stack_pop) rfl

theorem lookup_frame_exception :
    originalRuntimeCode.lookup (ofString "frame_exception") =
      some ([(ofString "err", .one)], sourceFnBody Guest.Software.guestFn_frame_exception, .one) :=
  lookup_of_guestAst_getElem 579 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_frame_exception) rfl

theorem lookup_frame_halt :
    originalRuntimeCode.lookup (ofString "frame_halt") =
      some ([(ofString "err", .one)], sourceFnBody Guest.Software.guestFn_frame_halt, .one) :=
  lookup_of_guestAst_getElem 586 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_frame_halt) rfl

theorem lookup_bswap64 :
    originalRuntimeCode.lookup (ofString "bswap64") =
      some ([(ofString "x", .one)], sourceFnBody Guest.Software.guestFn_bswap64, .one) :=
  lookup_of_guestAst_getElem 23 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bswap64) rfl

theorem lookup_st_be32 :
    originalRuntimeCode.lookup (ofString "st_be32") =
      some ([(ofString "p", .one), (ofString "v", .one)], sourceFnBody Guest.Software.guestFn_st_be32, .one) :=
  lookup_of_guestAst_getElem 27 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_st_be32) rfl

theorem lookup_st_be64 :
    originalRuntimeCode.lookup (ofString "st_be64") =
      some ([(ofString "p", .one), (ofString "v", .one)], sourceFnBody Guest.Software.guestFn_st_be64, .one) :=
  lookup_of_guestAst_getElem 28 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_st_be64) rfl

theorem lookup_u256_to_be32 :
    originalRuntimeCode.lookup (ofString "u256_to_be32") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_u256_to_be32, .one) :=
  lookup_of_guestAst_getElem 87 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_to_be32) rfl

/-! ## 2. Shared helpers on `EvmInv` head frame / continuation -/

theorem not_resumes_error : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

theorem not_resumes_timeOut : ¬ Resumes (some (.timeOut : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

theorem store_res_not_resumes {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {res : PanSemResultExact 64}
    (h : evaluateHOLFiniteState s (.store dst val) = (some res, post)) :
    ¬ Resumes (some res) := by
  have herr : res = .error := by
    rw [evaluateHOLFiniteState_store] at h
    revert h
    rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst with _ | dv
    · intro h; injection h with h1; injection h1 with h2; exact h2.symm
    · rcases dv with ⟨⟨addr⟩⟩ | _ | _
      · rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val with _ | v
        · intro h; injection h with h1; injection h1 with h2; exact h2.symm
        · dsimp only
          split
          · intro h; injection h with h1; cases h1
          · intro h; injection h with h1; injection h1 with h2; exact h2.symm
      · intro h; injection h with h1; injection h1 with h2; exact h2.symm
      · intro h; injection h with h1; injection h1 with h2; exact h2.symm
  subst herr
  exact not_resumes_error

theorem evmStep_refl_locals_clock {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s)
    (hpost : post = { s with locals := post.locals, clock := post.clock }) :
    EvmStep [] s post ∧ evmR post ≤ evmR s := by
  rw [hpost]
  have h1 := localsFree_evmInv s post.locals post.clock hInv
  have h2 := evmChain_with_locals s post.locals post.clock
  refine ⟨⟨h1, le_refl _, fun _ _ => rfl, h2⟩, ?_⟩
  unfold evmR; rw [h2]; rfl

theorem evmInv_head_info {F : Type} {s : PanSemStateFiniteExact 64 F} (hInv : EvmInv s) :
    (globN s "ev", globN s "cur_cont") ∈ evmChain s ∧
    0 < globN s "ev" ∧ globN s "ev" + 280 ≤ 2 ^ 64 ∧
    0 < globN s "cur_cont" ∧ globN s "cur_cont" + 104 ≤ 2 ^ 64 ∧
    memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) + 1 < 2 ^ 64 := by
  obtain ⟨hAs, S, hW, hch_ne, hch_len, hch_last, hFW_all, _, _, _, _, _, _, _, hGas⟩ := hInv
  have hch_cons : ∃ tail, evmChain s = (globN s "ev", globN s "cur_cont") :: tail := by
    unfold evmChain
    have hpos : ∃ m, Wave8GuestInv.maxChain + 1 = m + 1 := ⟨Wave8GuestInv.maxChain, rfl⟩
    obtain ⟨m, hm⟩ := hpos; rw [hm, evmChainFrom]; exact ⟨_, rfl⟩
  obtain ⟨chTail, hch⟩ := hch_cons
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by rw [hch]; exact List.mem_cons_self
  have hFW0 := hFW_all _ hhead
  obtain ⟨hb_ev, hb_cc, _, _⟩ := frameWF_bounds hAs.2 hFW0
  dsimp only at hb_ev hb_cc
  have hin_ev := (hFW0.1 (globN s "ev", 280) (by simp)).1.1
  have hin_cc := (hFW0.1 (globN s "cur_cont", 104) (by simp)).1.1
  dsimp only at hin_ev hin_cc
  have hfm1 := hAs.2.2.2.1; have hfm2 := hAs.2.2.2.2.1
  rw [scratchStart_val] at hfm1
  rw [hch, List.map_cons, List.sum_cons] at hGas
  dsimp only at hGas
  exact ⟨hhead, by omega, hb_ev, by omega, hb_cc, by omega⟩

/-- One-word store at `ev + off` inside `[(evBase, 280), (ccBase, 104)]`. -/
theorem store_ev_off_step {F : Type} {t post : PanSemStateFiniteExact 64 F}
    {evBase ccBase off : Nat} {valExp : ExpHOL 64}
    (hma : t.memaddrs = ordinaryDomain)
    (hb_ev : evBase + 280 ≤ 2 ^ 64)
    (hoff : off + 8 ≤ 280 ∧ off % 8 = 0)
    (hevw : ∃ evw : BitVec 64,
      t.globals.lookup (ofString "ev") = some (.val (.word evw)) ∧ evw.toNat = evBase)
    (hval : ∀ v : ValueHOL 64,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) valExp = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (hrun : evaluateHOLFiniteState t
      (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) valExp) =
      (none, post)) :
    ByteRegionEffect t post [(evBase, 280), (ccBase, 104)] ∧
    post.locals = t.locals ∧
    (∀ a : Nat, a < 2 ^ 64 → a ≠ evBase + off → memW post a = memW t a) ∧
    (∃ w : BitVec 64,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) valExp =
        some (.val (.word w)) ∧ memW post (evBase + off) = w.toNat) := by
  obtain ⟨evw, hevw_lk, hevw_nat⟩ := hevw
  have hdst_eval : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) =
      some (.val (.word (BitVec.ofNat 64 (evBase + off)))) := by
    simp only [evalHOLExact, evalListHOLExact, hevw_lk, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, BitVec.add_zero]
    congr 3
    apply BitVec.eq_of_toNat_eq
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat, hz0, Nat.add_zero,
      Nat.mod_eq_of_lt (show off < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show evBase + off < 2 ^ 64 by omega)]
  obtain ⟨heff, hloc⟩ := ByteRegionEffect.of_store_word (Rl := [(evBase, 280), (ccBase, 104)]) hma hrun hval
    (fun addr hdst _ => by
      rw [hdst_eval] at hdst
      injection hdst with h1; injection h1 with h2; injection h2 with h3; subst h3
      have htn : (BitVec.ofNat 64 (evBase + off)).toNat = evBase + off := Nat.mod_eq_of_lt (by omega)
      exact ⟨(evBase, 280), by simp, by rw [htn]; omega, by rw [htn]; omega⟩)
  have hval_eval := hrun
  rw [evaluateHOLFiniteState_store, hdst_eval] at hval_eval
  revert hval_eval
  cases hv : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) valExp with
  | none => simp
  | some v =>
    obtain ⟨w, rfl⟩ := hval v hv
    dsimp only
    split
    · rename_i m' hst
      unfold flattenHOL panMemStoresHOL panMemStoreHOL at hst
      by_cases hdom : t.memaddrs (BitVec.ofNat 64 (evBase + off))
      · simp only [hdom, ↓reduceIte, panMemStoresHOL, Option.some.injEq] at hst
        subst hst
        intro hval_eval; injection hval_eval with _ hpost; subst hpost
        refine ⟨heff, rfl, ?_, w, rfl, ?_⟩
        · intro a ha hne
          unfold memW; dsimp only
          have hne_bv : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 (evBase + off) := by
            intro heq
            have hn := congrArg BitVec.toNat heq
            rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
                Nat.mod_eq_of_lt (by omega)] at hn
            exact hne hn
          rw [if_neg hne_bv]
        · unfold memW; simp
      · simp [hdom] at hst
    · simp

theorem word_of_wordOp_add {F : Type} (s : PanSemStateFiniteExact 64 F) (args : List (ExpHOL 64))
    (v : ValueHOL 64)
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add args) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  simp only [evalHOLExact, wordOpHOL] at hv
  revert hv
  rcases @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp
  · dsimp only
    split
    · simp only [Option.map]
      rcases wordOp .add (vs.map valueWord) with _ | w
      · simp
      · intro hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
    · simp

theorem word_of_wordOp_sub {F : Type} (s : PanSemStateFiniteExact 64 F) (args : List (ExpHOL 64))
    (v : ValueHOL 64)
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .sub args) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  simp only [evalHOLExact, wordOpHOL] at hv
  revert hv
  rcases @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp
  · dsimp only
    split
    · simp only [Option.map]
      rcases wordOp .sub (vs.map valueWord) with _ | w
      · simp
      · intro hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
    · simp

theorem word_of_load_one {F : Type} (s : PanSemStateFiniteExact 64 F) (addrExp : ExpHOL 64)
    (v : ValueHOL 64)
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one addrExp) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  unfold evalHOLExact at hv
  revert hv
  split
  · split
    · rename_i addr _
      intro hml
      unfold memLoadHOLExact at hml
      by_cases hd : s.memaddrs addr
      · rw [if_pos hd] at hml
        injection hml with hv'
        change ValueHOL.val (s.memory addr) = v at hv'
        cases hm : s.memory addr with
        | word w => rw [hm] at hv'; exact ⟨w, hv'.symm⟩
      · rw [if_neg hd] at hml; cases hml
    · simp
  · simp

/-! ## 3. `ek_charge_gas` -/

theorem «ek_charge_gas» : EvmKeeps EvmInv [] (ofString "charge_gas") := by
  refine ⟨_, _, _, lookup_charge_gas, ?_⟩
  intro F s hcode hInv hlookup _hnt hres
  obtain ⟨amtw_in, hamt_in⟩ := lookup_param_word_one s lookup_charge_gas hlookup
  obtain ⟨hhead, hev_pos, hb_ev, _, hb_cc, _⟩ := evmInv_head_info hInv
  obtain ⟨evw, hevw_lk, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
  have hbody : sourceFnBody Guest.Software.guestFn_charge_gas =
      .dec (ofString "gl") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 64]))
        (.seq
          (.ite (.cmp .lower (.var .local (ofString "gl")) (.var .local (ofString "amount")))
            (.raise (ofString "EvmErr") (.const 4))
            .skip)
          (.seq
            (.store (.op .add [.var .global (ofString "ev"), .const 64])
              (.op .sub [.var .local (ofString "gl"), .var .local (ofString "amount")]))
            (.seq
              (.store (.op .add [.var .global (ofString "ev"), .const 184])
                (.op .add
                  [.load .one (.op .add [.var .global (ofString "ev"), .const 184]),
                   .var .local (ofString "amount")]))
              (.return (.const 0))))) := rfl
  rw [hbody, evaluateHOLFiniteState_dec_total] at hres ⊢
  dsimp only at hres ⊢
  revert hres
  split
  · intro h; exact absurd h not_resumes_error
  · rename_i glv hgl
    obtain ⟨glw, rfl, hgl_memW⟩ := evalAt_loadG s "ev" 64 glv hgl
    have h64_nat : (64 : BitVec 64).toNat = 64 := rfl
    rw [h64_nat] at hgl_memW
    have hsh_gl : shapeEqHOL .one (shapeOfHOLExact (.val (.word glw) : ValueHOL 64)) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hsh_gl]; dsimp only; intro hres
    set s1 := setVarHOLFinite (ofString "gl") (.val (.word glw)) s with hs1
    have hs1_gl : s1.locals.lookup (ofString "gl") = some (.val (.word glw)) := by
      simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs1_amt : s1.locals.lookup (ofString "amount") = some (.val (.word amtw_in)) := by
      simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hamt_in,
        show ofString "gl" ≠ ofString "amount" by decide]
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres ⊢
    have hcmp : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.cmp .lower (.var .local (ofString "gl")) (.var .local (ofString "amount"))) =
        some (.val (.word (if glw < amtw_in then 1 else 0))) := by
      simp [evalHOLExact, hs1_gl, hs1_amt, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcmp] at hres ⊢; dsimp only at hres ⊢
    by_cases hlt : glw < amtw_in
    · -- Raise `EvmErr`: memory and globals unchanged!
      have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
      simp only [hlt, ↓reduceIte, h10] at hres ⊢
      rcases hraise : evaluateHOLFiniteState s1 (.raise (ofString "EvmErr") (.const 4)) with ⟨rr, sr⟩
      have hraise_info : rr ≠ none ∧ sr = { s with locals := sr.locals, clock := sr.clock } := by
        rw [evaluateHOLFiniteState_raise] at hraise
        dsimp only [evalHOLExact] at hraise
        split at hraise
        · split at hraise <;> (injection hraise with hrr hsr; subst hrr hsr; exact ⟨by simp, rfl⟩)
        · injection hraise with hrr hsr; subst hrr hsr; exact ⟨by simp, rfl⟩
      cases rr with
      | none => exact absurd rfl hraise_info.1
      | some _ =>
        dsimp only
        refine (evmStep_refl_locals_clock hInv ?_).1
        conv_lhs => rw [hraise_info.2]
    · -- `amtw_in ≤ glw`: stores `glw - amtw_in` at `ev + 64` and `load(ev+184) + amtw_in` at `ev + 184`!
      have hamt_le : amtw_in.toNat ≤ glw.toNat := by rw [BitVec.lt_def] at hlt; omega
      simp only [hlt, ↓reduceIte, evaluateHOLFiniteState_skip] at hres ⊢
      rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
      cases h1 : evaluateHOLFiniteState s1
          (.store (.op .add [.var .global (ofString "ev"), .const 64])
            (.op .sub [.var .local (ofString "gl"), .var .local (ofString "amount")])) with
      | mk r1 s2 =>
        rw [h1] at hres; dsimp only at hres ⊢
        rcases r1 with _ | res1
        · obtain ⟨heff1, hloc1, hkeep1, w1, hw1_ev, hw1_mem⟩ :=
            store_ev_off_step (t := s1) (post := s2)
              (evBase := globN s "ev") (ccBase := globN s "cur_cont") (off := 64)
              hInv.1.1.memaddrs hb_ev ⟨by omega, by omega⟩
              ⟨evw, hevw_lk, hevw_nat⟩
              (word_of_wordOp_sub s1 _) h1
          have hw1_le : w1.toNat ≤ memW s (globN s "ev" + 64) := by
            have hsub_ev : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
                (.op .sub [.var .local (ofString "gl"), .var .local (ofString "amount")]) =
                some (.val (.word (glw - amtw_in))) := by
              simp [evalHOLExact, evalListHOLExact, hs1_gl, hs1_amt, valueIsWord, valueWord, wordOpHOL, wordOp]
            rw [hsub_ev] at hw1_ev
            injection hw1_ev with ha; injection ha with hb; injection hb with hc
            rw [← hc, BitVec.toNat_sub_of_le (BitVec.le_def.2 hamt_le), hgl_memW]
            omega
          rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
          cases h2 : evaluateHOLFiniteState s2
              (.store (.op .add [.var .global (ofString "ev"), .const 184])
                (.op .add
                  [.load .one (.op .add [.var .global (ofString "ev"), .const 184]),
                   .var .local (ofString "amount")])) with
          | mk r2 s3 =>
            rw [h2] at hres; dsimp only at hres ⊢
            rcases r2 with _ | res2
            · obtain ⟨heff2, _, hkeep2, _⟩ :=
                store_ev_off_step (t := s2) (post := s3)
                  (evBase := globN s "ev") (ccBase := globN s "cur_cont") (off := 184)
                  (heff1.memaddrs.trans hInv.1.1.memaddrs) hb_ev ⟨by omega, by omega⟩
                  ⟨evw, by rw [heff1.globals]; exact hevw_lk, hevw_nat⟩
                  (word_of_wordOp_add s2 _) h2
              rw [evaluateHOLFiniteState_return] at hres ⊢
              dsimp only [evalHOLExact] at hres ⊢
              have hle32 : sizeOfShapeWithContextHOL s3.structs
                  (shapeOfHOLExact (ValueHOL.val (HolWordLab.word (0 : BitVec 64)))) ≤ 32 := by
                simp [shapeOfHOLExact]
              rw [if_pos hle32]; dsimp only
              have heff_all : ByteRegionEffect s
                  { (emptyLocalsHOLFinite s3) with
                    locals := (emptyLocalsHOLFinite s3).locals.resVarEq
                      (ofString "gl", s.locals.lookup (ofString "gl")) }
                  [(globN s "ev", 280), (globN s "cur_cont", 104)] :=
                (((ByteRegionEffect.refl s _).with_locals_clock _ _).trans
                  (heff1.trans heff2)).with_locals_clock _ _
              refine (evmStep_of_head_frame_cont_update hInv heff_all ?_ ?_ ?_ ?_).1
              · intro k hk hk8 hknot
                change memW s3 (globN s "ev" + k) = memW s (globN s "ev" + k)
                have hk2 := hkeep2 (globN s "ev" + k) (by omega) (by intro h; apply hknot; simp; omega)
                have hk1 := hkeep1 (globN s "ev" + k) (by omega) (by intro h; apply hknot; simp; omega)
                exact hk2.trans hk1
              · change memW s3 (globN s "ev" + 16) ≤ memW s (globN s "ev" + 16)
                rw [hkeep2 (globN s "ev" + 16) (by omega) (by omega),
                    hkeep1 (globN s "ev" + 16) (by omega) (by omega)]
                exact le_refl _
              · intro k hk _ _
                change memW s3 (globN s "cur_cont" + k) = memW s (globN s "cur_cont" + k)
                have hdj_ec : Disj (globN s "ev", 280) (globN s "cur_cont", 104) := by
                  obtain ⟨_, _, _, _, _, _, _, _, _, hFO_pw, _⟩ := hInv
                  have hch_cons : ∃ tail, evmChain s = (globN s "ev", globN s "cur_cont") :: tail := by
                    unfold evmChain
                    have hpos : ∃ m, Wave8GuestInv.maxChain + 1 = m + 1 := ⟨Wave8GuestInv.maxChain, rfl⟩
                    obtain ⟨m, hm⟩ := hpos; rw [hm, evmChainFrom]; exact ⟨_, rfl⟩
                  obtain ⟨_, hch⟩ := hch_cons
                  rw [hch, List.map_cons, List.flatten_cons, List.pairwise_append] at hFO_pw
                  have hpw0 := hFO_pw.1
                  unfold frameObjects at hpw0
                  rw [List.cons_append, List.pairwise_cons] at hpw0
                  exact hpw0.1 _ (by simp)
                have hne_ev : ∀ off_ev, off_ev + 8 ≤ 280 → globN s "cur_cont" + k ≠ globN s "ev" + off_ev := by
                  intro off_ev hoff heq
                  rcases hdj_ec with h0 | h0 | h1 | h2 <;> dsimp only at * <;> omega
                rw [hkeep2 (globN s "cur_cont" + k) (by omega) (hne_ev 184 (by omega)),
                    hkeep1 (globN s "cur_cont" + k) (by omega) (hne_ev 64 (by omega))]
                rfl
              · change memW s3 (globN s "ev" + 64) + memW s3 (globN s "ev" + 192) ≤ _
                rw [hkeep2 (globN s "ev" + 64) (by omega) (by omega),
                    hw1_mem,
                    hkeep2 (globN s "ev" + 192) (by omega) (by omega),
                    hkeep1 (globN s "ev" + 192) (by omega) (by omega)]
                exact Nat.add_le_add_right hw1_le _
            · exact absurd hres (store_res_not_resumes h2)
        · exact absurd hres (store_res_not_resumes h1)

/-! ## 4. `refill_frame_state_gas_exec` and `ek_refill_frame_state_gas` -/

/-- Exact execution of `refill_frame_state_gas` body on any `EvmInv` state: on every resuming outcome
it returns `0` (`some (.returned (.val (.word 0)))`), writes inside `[(globN s "ev", 280), (globN s "cur_cont", 104)]`,
keeps all `ev` offsets outside `{64, 72, 192}` and all `cur_cont` offsets, and keeps
`memW post (ev + 64) + memW post (ev + 192) = memW s (ev + 64) + memW s (ev + 192)`! -/
theorem refill_frame_state_gas_body_exec {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hInv : EvmInv s)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_refill_frame_state_gas)).1) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_refill_frame_state_gas)
    out.1 = some (.returned (.val (.word 0))) ∧
    ByteRegionEffect s out.2 [(globN s "ev", 280), (globN s "cur_cont", 104)] ∧
    (∀ k, k + 8 ≤ 280 → k % 8 = 0 → k ∉ ([64, 72, 192] : List Nat) →
      memW out.2 (globN s "ev" + k) = memW s (globN s "ev" + k)) ∧
    (∀ k, k + 8 ≤ 104 → memW out.2 (globN s "cur_cont" + k) = memW s (globN s "cur_cont" + k)) ∧
    memW out.2 (globN s "ev" + 64) + memW out.2 (globN s "ev" + 192) ≤
      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) ∧
    EvmStep [] s out.2 ∧ evmR out.2 ≤ evmR s := by
  dsimp only
  obtain ⟨hhead, hev_pos, hb_ev, _, hb_cc, hgas_sum⟩ := evmInv_head_info hInv
  obtain ⟨evw, hevw_lk, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
  have hdj_ec : Disj (globN s "ev", 280) (globN s "cur_cont", 104) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hFO_pw, _⟩ := hInv
    have hch_cons : ∃ tail, evmChain s = (globN s "ev", globN s "cur_cont") :: tail := by
      unfold evmChain
      have hpos : ∃ m, Wave8GuestInv.maxChain + 1 = m + 1 := ⟨Wave8GuestInv.maxChain, rfl⟩
      obtain ⟨m, hm⟩ := hpos; rw [hm, evmChainFrom]; exact ⟨_, rfl⟩
    obtain ⟨_, hch⟩ := hch_cons
    rw [hch, List.map_cons, List.flatten_cons, List.pairwise_append] at hFO_pw
    have hpw0 := hFO_pw.1
    unfold frameObjects at hpw0
    rw [List.cons_append, List.pairwise_cons] at hpw0
    exact hpw0.1 _ (by simp)
  have hne_cc_ev : ∀ k off_ev, k + 8 ≤ 104 → off_ev + 8 ≤ 280 →
      globN s "cur_cont" + k ≠ globN s "ev" + off_ev := by
    intro k off_ev hk hoff heq
    rcases hdj_ec with h0 | h0 | h1 | h2 <;> dsimp only at * <;> omega
  have hbody : sourceFnBody Guest.Software.guestFn_refill_frame_state_gas =
      .dec (ofString "msg") .one
        (.load .one (.op .add [.var .global (ofString "ev"), .const 112]))
        (.seq
          (.store (.op .add [.var .global (ofString "ev"), .const 64])
            (.op .add
              [.load .one (.op .add [.var .global (ofString "ev"), .const 64]),
               .load .one (.op .add [.var .global (ofString "ev"), .const 192])]))
          (.seq
            (.store (.op .add [.var .global (ofString "ev"), .const 72])
              (.load .one (.op .add [.var .local (ofString "msg"), .const 48])))
            (.seq
              (.store (.op .add [.var .global (ofString "ev"), .const 192]) (.const 0))
              (.return (.const 0))))) := rfl
  rw [hbody, evaluateHOLFiniteState_dec_total] at hres ⊢
  dsimp only at hres ⊢
  revert hres
  rcases hmsg_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ev"), .const 112])) with _ | msgVal
  · dsimp only; intro hres; exact absurd hres not_resumes_error
  · dsimp only
    by_cases hsh_msg : shapeEqHOL .one (shapeOfHOLExact msgVal) = true
    · rw [if_pos hsh_msg]; dsimp only; intro hres
      let s0 := setVarHOLFinite (ofString "msg") msgVal s
      have heff0 : ByteRegionEffect s s0 [(globN s "ev", 280), (globN s "cur_cont", 104)] :=
        (ByteRegionEffect.refl s _).with_locals_clock _ _
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
      change Resumes (evaluateHOLFiniteState s0 body0).1 at hres
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
        · obtain ⟨heff1, _, hkeep1, w1, hw1_ev, hw1_mem⟩ :=
            store_ev_off_step (t := s0) (post := s1)
              (evBase := globN s "ev") (ccBase := globN s "cur_cont") (off := 64)
              hInv.1.1.memaddrs hb_ev ⟨by omega, by omega⟩
              ⟨evw, hevw_lk, hevw_nat⟩
              (word_of_wordOp_add s0 _) h1
          have hw1_sum : w1.toNat = memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) := by
            obtain ⟨_, S, hAt⟩ := hInv
            have hrec_w := ((hAt.2.2.2.2.1 _ hhead).1 (globN s "ev", 280) (by simp)).2
            obtain ⟨wg, hdom64, hmem64⟩ := hrec_w.2.2 8 (by omega)
            obtain ⟨wsp, hdom192, hmem192⟩ := hrec_w.2.2 24 (by omega)
            have h64_eq : globN s "ev" + 8 * 8 = globN s "ev" + 64 := by omega
            have h192_eq : globN s "ev" + 8 * 24 = globN s "ev" + 192 := by omega
            rw [h64_eq] at hdom64 hmem64
            rw [h192_eq] at hdom192 hmem192
            have had64 : evw + (64 + 0) = BitVec.ofNat 64 (globN s "ev" + 64) := by
              apply BitVec.eq_of_toNat_eq
              have hz0 : (0 : BitVec 64).toNat = 0 := rfl
              have h64n : (64 : BitVec 64).toNat = 64 := rfl
              simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat, hz0, h64n, Nat.add_zero,
                Nat.mod_eq_of_lt (show 64 < 2 ^ 64 by omega),
                Nat.mod_eq_of_lt (show globN s "ev" + 64 < 2 ^ 64 by omega)]
            have had192 : evw + (192 + 0) = BitVec.ofNat 64 (globN s "ev" + 192) := by
              apply BitVec.eq_of_toNat_eq
              have hz0 : (0 : BitVec 64).toNat = 0 := rfl
              have h192n : (192 : BitVec 64).toNat = 192 := rfl
              simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat, hz0, h192n, Nat.add_zero,
                Nat.mod_eq_of_lt (show 192 < 2 ^ 64 by omega),
                Nat.mod_eq_of_lt (show globN s "ev" + 192 < 2 ^ 64 by omega)]
            have hsum_ev : @evalHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
                (.op .add
                  [.load .one (.op .add [.var .global (ofString "ev"), .const 64]),
                   .load .one (.op .add [.var .global (ofString "ev"), .const 192])]) =
                some (.val (.word (wg + (wsp + 0)))) := by
              have hdom64_0 : s0.memaddrs (BitVec.ofNat 64 (globN s "ev" + 64)) := hdom64
              have hmem64_0 : s0.memory (BitVec.ofNat 64 (globN s "ev" + 64)) = .word wg := hmem64
              have hdom192_0 : s0.memaddrs (BitVec.ofNat 64 (globN s "ev" + 192)) := hdom192
              have hmem192_0 : s0.memory (BitVec.ofNat 64 (globN s "ev" + 192)) = .word wsp := hmem192
              have hev_s0 : s0.globals.lookup (ofString "ev") = some (.val (.word evw)) := hevw_lk
              have hml64 : @memLoadHOLExact 64 _ .one (BitVec.ofNat 64 (globN s "ev" + 64))
                  s0.memaddrs (fun a => Classical.propDecidable (s0.memaddrs a))
                  s0.memory s0.structs = some (.val (.word wg)) := by
                unfold memLoadHOLExact; rw [if_pos hdom64_0, hmem64_0]
              have hml192 : @memLoadHOLExact 64 _ .one (BitVec.ofNat 64 (globN s "ev" + 192))
                  s0.memaddrs (fun a => Classical.propDecidable (s0.memaddrs a))
                  s0.memory s0.structs = some (.val (.word wsp)) := by
                unfold memLoadHOLExact; rw [if_pos hdom192_0, hmem192_0]
              have hwf0 : isWfShapeExactHOL s0.structs .one = true := rfl
              simp only [evalHOLExact, evalListHOLExact, PanSemStateFiniteExact.toExact,
                hev_s0, hwf0, wordOpHOL, wordOp, valueIsWord, valueWord,
                List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
                had64, had192, hml64, hml192]
            rw [hsum_ev] at hw1_ev
            injection hw1_ev with h_a; injection h_a with h_b; injection h_b with h_c
            have hmw64 : memW s (globN s "ev" + 64) = wg.toNat := by unfold memW; rw [hmem64]
            have hmw192 : memW s (globN s "ev" + 192) = wsp.toNat := by unfold memW; rw [hmem192]
            rw [← h_c, hmw64, hmw192]
            have hz0 : (0 : BitVec 64).toNat = 0 := rfl
            simp only [BitVec.toNat_add, hz0, Nat.add_zero]
            rw [Nat.mod_eq_of_lt (show wsp.toNat < 2 ^ 64 from wsp.isLt),
                Nat.mod_eq_of_lt (by rw [← hmw64, ← hmw192]; omega)]
          rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
          cases h2 : evaluateHOLFiniteState s1
              (.store (.op .add [.var .global (ofString "ev"), .const 72])
                (.load .one (.op .add [.var .local (ofString "msg"), .const 48]))) with
          | mk r2 s2 =>
            rw [h2] at hres; dsimp only at hres ⊢
            rcases r2 with _ | res2
            · obtain ⟨heff2, _, hkeep2, _⟩ :=
                store_ev_off_step (t := s1) (post := s2)
                  (evBase := globN s "ev") (ccBase := globN s "cur_cont") (off := 72)
                  (heff1.memaddrs.trans hInv.1.1.memaddrs) hb_ev ⟨by omega, by omega⟩
                  ⟨evw, by rw [heff1.globals]; exact hevw_lk, hevw_nat⟩
                  (word_of_load_one s1 _) h2
              rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
              cases h3 : evaluateHOLFiniteState s2
                  (.store (.op .add [.var .global (ofString "ev"), .const 192]) (.const 0)) with
              | mk r3 s3 =>
                rw [h3] at hres; dsimp only at hres ⊢
                rcases r3 with _ | res3
                · obtain ⟨heff3, _, hkeep3, w3, hw3_ev, hw3_mem⟩ :=
                    store_ev_off_step (t := s2) (post := s3)
                      (evBase := globN s "ev") (ccBase := globN s "cur_cont") (off := 192)
                      (heff2.memaddrs.trans (heff1.memaddrs.trans hInv.1.1.memaddrs))
                      hb_ev ⟨by omega, by omega⟩
                      ⟨evw, by rw [heff2.globals, heff1.globals]; exact hevw_lk, hevw_nat⟩
                      (fun v hv => by injection hv with hv'; exact ⟨0, hv'.symm⟩) h3
                  have hw3_zero : w3.toNat = 0 := by
                    change some (ValueHOL.val (.word 0)) = some (.val (.word w3)) at hw3_ev
                    injection hw3_ev with ha; injection ha with hb; injection hb with hc
                    rw [← hc]; rfl
                  rw [evaluateHOLFiniteState_return] at hres ⊢
                  dsimp only [evalHOLExact] at hres ⊢
                  have hle32 : sizeOfShapeWithContextHOL s3.structs
                      (shapeOfHOLExact (ValueHOL.val (HolWordLab.word (0 : BitVec 64)))) ≤ 32 := by
                    simp [shapeOfHOLExact]
                  rw [if_pos hle32]; dsimp only
                  have heff_all : ByteRegionEffect s
                      { (emptyLocalsHOLFinite s3) with
                        locals := (emptyLocalsHOLFinite s3).locals.resVarEq
                          (ofString "msg", s.locals.lookup (ofString "msg")) }
                      [(globN s "ev", 280), (globN s "cur_cont", 104)] :=
                    (heff0.trans (heff1.trans (heff2.trans heff3))).with_locals_clock _ _
                  have hkeep_ev_fn : ∀ k, k + 8 ≤ 280 → k % 8 = 0 → k ∉ ([64, 72, 192] : List Nat) →
                      memW s3 (globN s "ev" + k) = memW s (globN s "ev" + k) := by
                    intro k hk hk8 hkn
                    have hk3 := hkeep3 (globN s "ev" + k) (by omega) (by intro h; apply hkn; simp; omega)
                    have hk2 := hkeep2 (globN s "ev" + k) (by omega) (by intro h; apply hkn; simp; omega)
                    have hk1 := hkeep1 (globN s "ev" + k) (by omega) (by intro h; apply hkn; simp; omega)
                    exact hk3.trans (hk2.trans hk1)
                  have hkeep_cc_fn : ∀ k, k + 8 ≤ 104 → memW s3 (globN s "cur_cont" + k) = memW s (globN s "cur_cont" + k) := by
                    intro k hk
                    rw [hkeep3 (globN s "cur_cont" + k) (by omega) (hne_cc_ev k 192 hk (by omega)),
                        hkeep2 (globN s "cur_cont" + k) (by omega) (hne_cc_ev k 72 hk (by omega)),
                        hkeep1 (globN s "cur_cont" + k) (by omega) (hne_cc_ev k 64 hk (by omega))]
                    rfl
                  have hgas_fn : memW s3 (globN s "ev" + 64) + memW s3 (globN s "ev" + 192) ≤
                      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) := by
                    rw [hkeep3 (globN s "ev" + 64) (by omega) (by omega),
                        hkeep2 (globN s "ev" + 64) (by omega) (by omega),
                        hw1_mem, hw1_sum, hw3_mem, hw3_zero]
                    omega
                  have hstep := evmStep_of_head_frame_cont_update hInv heff_all
                    (fun k hk hk8 hkn => hkeep_ev_fn k hk hk8 (by intro h; apply hkn; simp at h; rcases h with rfl | rfl | rfl <;> decide))
                    (by
                      change memW s3 (globN s "ev" + 16) ≤ memW s (globN s "ev" + 16)
                      rw [hkeep_ev_fn 16 (by omega) (by omega) (by decide)])
                    (fun k hk _ _ => hkeep_cc_fn k hk)
                    hgas_fn
                  exact ⟨rfl, heff_all, hkeep_ev_fn, hkeep_cc_fn, hgas_fn, hstep.1, hstep.2⟩
                · exact absurd hres (store_res_not_resumes h3)
            · exact absurd hres (store_res_not_resumes h2)
        · exact absurd hres (store_res_not_resumes h1)
    · rw [if_neg hsh_msg]; dsimp only; intro hres; exact absurd hres not_resumes_error

theorem «ek_refill_frame_state_gas» : EvmKeeps EvmInv [] (ofString "refill_frame_state_gas") :=
  ⟨_, _, _, lookup_refill_frame_state_gas,
    fun s _ hInv _ _ hres => (refill_frame_state_gas_body_exec s hInv hres).2.2.2.2.2.1⟩

/-! ## 5. `frame_halt_body_exec` and `ek_frame_halt` (R11: `hlookup` enforces 1-word `err`!) -/

theorem frame_halt_body_exec {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hInv : EvmInv s) {w_err : BitVec 64}
    (hw_err : s.locals.lookup (ofString "err") = some (.val (.word w_err)))
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_halt)).1) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_halt)
    out.1 = some (.returned (.val (.word 0))) ∧
    ByteRegionEffect s out.2 [(globN s "ev", 280), (globN s "cur_cont", 104)] ∧
    (∀ k, k + 8 ≤ 280 → k % 8 = 0 → k ∉ ([64, 160, 184] : List Nat) →
      memW out.2 (globN s "ev" + k) = memW s (globN s "ev" + k)) ∧
    (∀ k, k + 8 ≤ 104 → memW out.2 (globN s "cur_cont" + k) = memW s (globN s "cur_cont" + k)) ∧
    memW out.2 (globN s "ev" + 64) + memW out.2 (globN s "ev" + 192) ≤
      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) ∧
    EvmStep [] s out.2 ∧ evmR out.2 ≤ evmR s := by
  dsimp only
  obtain ⟨_, hev_pos, hb_ev, _, hb_cc, _⟩ := evmInv_head_info hInv
  obtain ⟨evw, hevw_lk, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
  have hdj_ec : Disj (globN s "ev", 280) (globN s "cur_cont", 104) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hFO_pw, _⟩ := hInv
    have hch_cons : ∃ tail, evmChain s = (globN s "ev", globN s "cur_cont") :: tail := by
      unfold evmChain
      have hpos : ∃ m, Wave8GuestInv.maxChain + 1 = m + 1 := ⟨Wave8GuestInv.maxChain, rfl⟩
      obtain ⟨m, hm⟩ := hpos; rw [hm, evmChainFrom]; exact ⟨_, rfl⟩
    obtain ⟨_, hch⟩ := hch_cons
    rw [hch, List.map_cons, List.flatten_cons, List.pairwise_append] at hFO_pw
    have hpw0 := hFO_pw.1
    unfold frameObjects at hpw0
    rw [List.cons_append, List.pairwise_cons] at hpw0
    exact hpw0.1 _ (by simp)
  have hne_cc_ev : ∀ k off_ev, k + 8 ≤ 104 → off_ev + 8 ≤ 280 →
      globN s "cur_cont" + k ≠ globN s "ev" + off_ev := by
    intro k off_ev hk hoff heq
    rcases hdj_ec with h0 | h0 | h1 | h2 <;> dsimp only at * <;> omega
  have hbody : sourceFnBody Guest.Software.guestFn_frame_halt =
      .seq
        (.store (.op .add [.var .global (ofString "ev"), .const 184])
          (.op .add
            [.load .one (.op .add [.var .global (ofString "ev"), .const 184]),
             .load .one (.op .add [.var .global (ofString "ev"), .const 64])]))
        (.seq
          (.store (.op .add [.var .global (ofString "ev"), .const 64]) (.const 0))
          (.seq
            (.store (.op .add [.var .global (ofString "ev"), .const 160])
              (.var .local (ofString "err")))
            (.return (.const 0)))) := rfl
  rw [hbody, evaluateHOLFiniteState_seq_line780] at hres ⊢
  cases h1 : evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "ev"), .const 184])
        (.op .add
          [.load .one (.op .add [.var .global (ofString "ev"), .const 184]),
           .load .one (.op .add [.var .global (ofString "ev"), .const 64])])) with
  | mk r1 s1 =>
    rw [h1] at hres; dsimp only at hres ⊢
    rcases r1 with _ | res1
    · obtain ⟨heff1, hloc1, hkeep1, _⟩ :=
        store_ev_off_step (t := s) (post := s1)
          (evBase := globN s "ev") (ccBase := globN s "cur_cont") (off := 184)
          hInv.1.1.memaddrs hb_ev ⟨by omega, by omega⟩
          ⟨evw, hevw_lk, hevw_nat⟩
          (word_of_wordOp_add s _) h1
      rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
      cases h2 : evaluateHOLFiniteState s1
          (.store (.op .add [.var .global (ofString "ev"), .const 64]) (.const 0)) with
      | mk r2 s2 =>
        rw [h2] at hres; dsimp only at hres ⊢
        rcases r2 with _ | res2
        · obtain ⟨heff2, hloc2, hkeep2, w2, hw2_ev, hw2_mem⟩ :=
            store_ev_off_step (t := s1) (post := s2)
              (evBase := globN s "ev") (ccBase := globN s "cur_cont") (off := 64)
              (heff1.memaddrs.trans hInv.1.1.memaddrs) hb_ev ⟨by omega, by omega⟩
              ⟨evw, by rw [heff1.globals]; exact hevw_lk, hevw_nat⟩
              (fun v hv => by injection hv with hv'; exact ⟨0, hv'.symm⟩) h2
          have hw2_zero : w2.toNat = 0 := by
            change some (ValueHOL.val (.word 0)) = some (.val (.word w2)) at hw2_ev
            injection hw2_ev with ha; injection ha with hb; injection hb with hc
            rw [← hc]; rfl
          rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
          cases h3 : evaluateHOLFiniteState s2
              (.store (.op .add [.var .global (ofString "ev"), .const 160])
                (.var .local (ofString "err"))) with
          | mk r3 s3 =>
            rw [h3] at hres; dsimp only at hres ⊢
            rcases r3 with _ | res3
            · obtain ⟨heff3, _, hkeep3, _⟩ :=
                store_ev_off_step (t := s2) (post := s3)
                  (evBase := globN s "ev") (ccBase := globN s "cur_cont") (off := 160)
                  (heff2.memaddrs.trans (heff1.memaddrs.trans hInv.1.1.memaddrs))
                  hb_ev ⟨by omega, by omega⟩
                  ⟨evw, by rw [heff2.globals, heff1.globals]; exact hevw_lk, hevw_nat⟩
                  (fun v hv => by
                    change s2.locals.lookup (ofString "err") = some v at hv
                    rw [hloc2, hloc1, hw_err] at hv
                    injection hv with hv'; exact ⟨w_err, hv'.symm⟩) h3
              rw [evaluateHOLFiniteState_return] at hres ⊢
              dsimp only [evalHOLExact] at hres ⊢
              have hle32 : sizeOfShapeWithContextHOL s3.structs
                  (shapeOfHOLExact (ValueHOL.val (HolWordLab.word (0 : BitVec 64)))) ≤ 32 := by
                simp [shapeOfHOLExact]
              rw [if_pos hle32]; dsimp only
              have heff_all : ByteRegionEffect s (emptyLocalsHOLFinite s3)
                  [(globN s "ev", 280), (globN s "cur_cont", 104)] :=
                (heff1.trans (heff2.trans heff3)).with_locals_clock _ _
              have hkeep_ev_fn : ∀ k, k + 8 ≤ 280 → k % 8 = 0 → k ∉ ([64, 160, 184] : List Nat) →
                  memW s3 (globN s "ev" + k) = memW s (globN s "ev" + k) := by
                intro k hk hk8 hkn
                have hk3 := hkeep3 (globN s "ev" + k) (by omega) (by intro h; apply hkn; simp; omega)
                have hk2 := hkeep2 (globN s "ev" + k) (by omega) (by intro h; apply hkn; simp; omega)
                have hk1 := hkeep1 (globN s "ev" + k) (by omega) (by intro h; apply hkn; simp; omega)
                exact hk3.trans (hk2.trans hk1)
              have hkeep_cc_fn : ∀ k, k + 8 ≤ 104 → memW s3 (globN s "cur_cont" + k) = memW s (globN s "cur_cont" + k) := by
                intro k hk
                rw [hkeep3 (globN s "cur_cont" + k) (by omega) (hne_cc_ev k 160 hk (by omega)),
                    hkeep2 (globN s "cur_cont" + k) (by omega) (hne_cc_ev k 64 hk (by omega)),
                    hkeep1 (globN s "cur_cont" + k) (by omega) (hne_cc_ev k 184 hk (by omega))]
              have hgas_fn : memW s3 (globN s "ev" + 64) + memW s3 (globN s "ev" + 192) ≤
                  memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) := by
                rw [hkeep3 (globN s "ev" + 64) (by omega) (by omega),
                    hw2_mem, hw2_zero,
                    hkeep3 (globN s "ev" + 192) (by omega) (by omega),
                    hkeep2 (globN s "ev" + 192) (by omega) (by omega),
                    hkeep1 (globN s "ev" + 192) (by omega) (by omega)]
                omega
              have hstep := evmStep_of_head_frame_cont_update hInv heff_all
                (fun k hk hk8 hkn => hkeep_ev_fn k hk hk8 (by intro h; apply hkn; simp at h; rcases h with rfl | rfl | rfl <;> decide))
                (by
                  change memW s3 (globN s "ev" + 16) ≤ memW s (globN s "ev" + 16)
                  rw [hkeep_ev_fn 16 (by omega) (by omega) (by decide)])
                (fun k hk _ _ => hkeep_cc_fn k hk)
                hgas_fn
              exact ⟨rfl, heff_all, hkeep_ev_fn, hkeep_cc_fn, hgas_fn, hstep.1, hstep.2⟩
            · exact absurd hres (store_res_not_resumes h3)
        · exact absurd hres (store_res_not_resumes h2)
    · exact absurd hres (store_res_not_resumes h1)

theorem «ek_frame_halt» : EvmKeeps EvmInv [] (ofString "frame_halt") := by
  refine ⟨_, _, _, lookup_frame_halt, ?_⟩
  intro F s _hcode hInv hlookup _hnt hres
  obtain ⟨w_err, hw_err⟩ := lookup_param_word_one s lookup_frame_halt hlookup
  exact (frame_halt_body_exec s hInv hw_err hres).2.2.2.2.2.1

/-! ## 6. `ek_stack_pop` -/

theorem «ek_stack_pop» : EvmKeeps EvmInv [] (ofString "stack_pop") := by
  refine ⟨_, _, _, lookup_stack_pop, ?_⟩
  intro F s _hcode hInv _hlookup _hnt hres
  obtain ⟨_, hev_pos, hb_ev, _, hb_cc, _⟩ := evmInv_head_info hInv
  obtain ⟨evw, hevw_lk, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
  have hdj_ec : Disj (globN s "ev", 280) (globN s "cur_cont", 104) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hFO_pw, _⟩ := hInv
    have hch_cons : ∃ tail, evmChain s = (globN s "ev", globN s "cur_cont") :: tail := by
      unfold evmChain
      have hpos : ∃ m, Wave8GuestInv.maxChain + 1 = m + 1 := ⟨Wave8GuestInv.maxChain, rfl⟩
      obtain ⟨m, hm⟩ := hpos; rw [hm, evmChainFrom]; exact ⟨_, rfl⟩
    obtain ⟨_, hch⟩ := hch_cons
    rw [hch, List.map_cons, List.flatten_cons, List.pairwise_append] at hFO_pw
    have hpw0 := hFO_pw.1
    unfold frameObjects at hpw0
    rw [List.cons_append, List.pairwise_cons] at hpw0
    exact hpw0.1 _ (by simp)
  have hne_cc_ev : ∀ k off_ev, k + 8 ≤ 104 → off_ev + 8 ≤ 280 →
      globN s "cur_cont" + k ≠ globN s "ev" + off_ev := by
    intro k off_ev hk hoff heq
    rcases hdj_ec with h0 | h0 | h1 | h2 <;> dsimp only at * <;> omega
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
  rw [hb, evaluateHOLFiniteState_dec_total] at hres ⊢
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
    rw [if_pos hsh_sp] at hres ⊢; dsimp only at hres ⊢
    set s1 := setVarHOLFinite (ofString "sp") (.val (.word sp)) s with hs1
    have hs1_sp : s1.locals.lookup (ofString "sp") = some (.val (.word sp)) := by
      simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres ⊢
    have hcmp_eval : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.cmp .equal (.var .local (ofString "sp")) (.const 0)) =
        some (.val (.word (if sp = 0 then 1 else 0))) := by
      simp [evalHOLExact, hs1_sp, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcmp_eval] at hres ⊢; dsimp only at hres ⊢
    by_cases hsp0 : sp = 0
    · subst hsp0
      have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
      simp only [↓reduceIte, h10] at hres ⊢
      rcases hraise : evaluateHOLFiniteState s1 (.raise (ofString "EvmErr") (.const 2)) with ⟨rr, sr⟩
      have hraise_info : rr ≠ none ∧ sr = { s with locals := sr.locals, clock := sr.clock } := by
        rw [evaluateHOLFiniteState_raise] at hraise
        dsimp only [evalHOLExact] at hraise
        split at hraise
        · split at hraise <;> (injection hraise with hrr hsr; subst hrr hsr; exact ⟨by simp, rfl⟩)
        · injection hraise with hrr hsr; subst hrr hsr; exact ⟨by simp, rfl⟩
      cases rr with
      | none => exact absurd rfl hraise_info.1
      | some _ =>
        dsimp only
        refine (evmStep_refl_locals_clock hInv ?_).1
        conv_lhs => rw [hraise_info.2]
    · have hsp_pos : 0 < memW s (globN s "ev" + 16) := by
        rw [← hsp_memW]
        exact Nat.pos_of_ne_zero (fun hz => hsp0 (BitVec.eq_of_toNat_eq hz))
      simp only [hsp0, ↓reduceIte, evaluateHOLFiniteState_skip] at hres ⊢
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hres ⊢
      have hsub_eval : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
          (.op .sub [.var .local (ofString "sp"), .const 1]) = some (.val (.word (sp - 1))) := by
        simp [evalHOLExact, evalListHOLExact, hs1_sp, valueIsWord, valueWord, wordOpHOL, wordOp]
      have hvalid_sp : s1.isValidValueHOLFinite .local (ofString "sp") (.val (.word (sp - 1))) = true := by
        simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hs1_sp, shapeOfHOLExact, shapeEqHOL]
      rw [hsub_eval] at hres ⊢; dsimp only at hres ⊢
      rw [if_pos hvalid_sp] at hres ⊢; dsimp only at hres ⊢
      set s2 := setKvarHOLFinite .local (ofString "sp") (.val (.word (sp - 1))) s1 with hs2
      have hs2_sp : s2.locals.lookup (ofString "sp") = some (.val (.word (sp - 1))) := by
        simp [hs2, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
      cases hst : evaluateHOLFiniteState s2
          (.store (.op .add [.var .global (ofString "ev"), .const 16]) (.var .local (ofString "sp"))) with
      | mk rst s3 =>
        rw [hst] at hres; dsimp only at hres ⊢
        rcases rst with _ | res_st
        · obtain ⟨heff_st, _, hkeep_st, wsp, hwsp_ev, hwsp_mem⟩ :=
            store_ev_off_step (t := s2) (post := s3)
              (evBase := globN s "ev") (ccBase := globN s "cur_cont") (off := 16)
              hInv.1.1.memaddrs hb_ev ⟨by omega, by omega⟩
              ⟨evw, hevw_lk, hevw_nat⟩
              (fun v hv => by
                change s2.locals.lookup (ofString "sp") = some v at hv
                rw [hs2_sp] at hv; injection hv with hv'; exact ⟨sp - 1, hv'.symm⟩) hst
          have hwsp_eq : wsp = sp - 1 := by
            change s2.locals.lookup (ofString "sp") = some (.val (.word wsp)) at hwsp_ev
            rw [hs2_sp] at hwsp_ev
            injection hwsp_ev with ha; injection ha with hb; injection hb with hc; exact hc.symm
          have hwsp_le : wsp.toNat ≤ memW s (globN s "ev" + 16) := by
            rw [hwsp_eq, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 1 ≤ sp.toNat; omega), hsp_memW]
            have : (1 : BitVec 64).toNat = 1 := rfl
            rw [this]; omega
          rcases hret_pair : evaluateHOLFiniteState s3 (.return retExp) with ⟨rr, sr⟩
          have hsr_eq : sr = { s3 with locals := sr.locals } := by
            rw [evaluateHOLFiniteState_return] at hret_pair
            revert hret_pair
            split
            · intro h; injection h with _ hs; rw [← hs]
            · split
              · intro h; injection h with _ hs; rw [← hs]; rfl
              · intro h; injection h with _ hs; rw [← hs]
          dsimp only
          have heff_all : ByteRegionEffect s
              { sr with locals := sr.locals.resVarEq (ofString "sp", s.locals.lookup (ofString "sp")) }
              [(globN s "ev", 280), (globN s "cur_cont", 104)] := by
            have heff_sr : ByteRegionEffect s2 sr [(globN s "ev", 280), (globN s "cur_cont", 104)] := by
              rw [hsr_eq]; exact heff_st.with_locals_clock _ _
            exact (((ByteRegionEffect.refl s _).with_locals_clock _ _).trans heff_sr).with_locals_clock _ _
          have hmemW_sr : ∀ a, memW sr a = memW s3 a := fun a => by rw [hsr_eq]; rfl
          refine (evmStep_of_head_frame_cont_update hInv heff_all ?_ ?_ ?_ ?_).1
          · intro k hk _ hkn
            change memW sr (globN s "ev" + k) = memW s (globN s "ev" + k)
            rw [hmemW_sr]
            exact hkeep_st (globN s "ev" + k) (by omega) (by intro h; apply hkn; simp; omega)
          · change memW sr (globN s "ev" + 16) ≤ memW s (globN s "ev" + 16)
            rw [hmemW_sr, hwsp_mem]; exact hwsp_le
          · intro k hk _ _
            change memW sr (globN s "cur_cont" + k) = memW s (globN s "cur_cont" + k)
            rw [hmemW_sr]
            exact hkeep_st (globN s "cur_cont" + k) (by omega) (hne_cc_ev k 16 hk (by omega))
          · change memW sr (globN s "ev" + 64) + memW sr (globN s "ev" + 192) ≤ _
            rw [hmemW_sr, hmemW_sr,
                hkeep_st (globN s "ev" + 64) (by omega) (by omega),
                hkeep_st (globN s "ev" + 192) (by omega) (by omega)]
            exact le_refl _
        · exact absurd hres (store_res_not_resumes hst)

/-! ## 7. `ek_u256_to_be32` (`u256_to_be32(a, out)`) -/

private theorem byteAlign_lt_heapEnd {s_ma : BitVec 64 → Prop} (hma : s_ma = ordinaryDomain)
    (addr : BitVec 64) (hdom : s_ma (panByteAlignHOL addr)) :
    addr.toNat < heapEnd := by
  rw [hma, ordinaryDomain_iff] at hdom
  have hal := panByteAlign_toNat64 addr
  rw [heapEnd_val]
  omega

private theorem word_dom_lt_heapEnd {s_ma : BitVec 64 → Prop} (hma : s_ma = ordinaryDomain)
    (addr : BitVec 64) (hdom : s_ma addr) :
    addr.toNat + 8 ≤ heapEnd := by
  rw [hma, ordinaryDomain_iff] at hdom
  rw [heapEnd_val]
  omega

private theorem bv_add_off_nat (base : BitVec 64) (off : Nat)
    (hbase : base.toNat < heapEnd) (hoff : off ≤ 32) :
    (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
  rw [heapEnd_val] at hbase
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
  have ho_lt : off < 18446744073709551616 := by omega
  have hsum_lt : base.toNat + off < 18446744073709551616 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, h264, Nat.mod_eq_of_lt ho_lt, Nat.mod_eq_of_lt hsum_lt]

private theorem eval_var_local {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : String) (w : BitVec 64)
    (hloc : s.locals.lookup (ofString nm) = some (.val (.word w))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString nm)) =
      some (.val (.word w)) := hloc

private theorem eval_var_local_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : String) (base : BitVec 64)
    (hloc : s.locals.lookup (ofString nm) = some (.val (.word base))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString nm)) =
      some (.val (.word (base + BitVec.ofNat 64 0))) := by
  have hz : base + BitVec.ofNat 64 0 = base := BitVec.add_zero base
  rw [hz]; exact hloc

private theorem eval_add_local_const {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : String) (base : BitVec 64) (off : Nat)
    (hloc : s.locals.lookup (ofString nm) = some (.val (.word base))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString nm), .const (BitVec.ofNat 64 off)]) =
      some (.val (.word (base + BitVec.ofNat 64 off))) := by
  simp only [evalHOLExact, evalListHOLExact, hloc, wordOpHOL, wordOp, valueIsWord, valueWord,
    List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
  have hz : BitVec.ofNat 64 off + (0 : BitVec 64) = BitVec.ofNat 64 off := BitVec.add_zero _
  exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word (base + w)))) hz

private theorem eval_align8_eq0 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : String) (base : BitVec 64)
    (hloc : s.locals.lookup (ofString nm) = some (.val (.word base))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.op .and [.var .local (ofString nm), .const 7#64]) (.const 0#64)) =
      some (.val (.word (if (base &&& 7#64) = 0#64 then 1 else 0))) := by
  simp only [evalHOLExact, evalListHOLExact, hloc, wordOpHOL, wordOp, valueIsWord, valueWord,
    List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
    Compiler.Encoders.Asm.wordCmpHOL]
  have h7 : (7#64 : BitVec 64) &&& 18446744073709551615#64 = 7#64 := by decide
  change some (ValueHOL.val (HolWordLab.word (if decide ((base &&& (7#64 &&& 18446744073709551615#64)) = 0#64) = true then 1 else 0))) = _
  rw [h7]
  by_cases hc : (base &&& 7#64) = 0#64 <;> simp [hc]

private theorem return_const0_step {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s (.return (.const 0#64))).1 = some (.returned (.val (.word 0))) ∧
    (evaluateHOLFiniteState s (.return (.const 0#64))).2 = emptyLocalsHOLFinite s := by
  rw [evaluateHOLFiniteState_return]
  have he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.const 0#64) = some (.val (.word 0)) := rfl
  rw [he]
  have hsz : sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
  dsimp only
  rw [if_pos hsz]
  exact ⟨rfl, rfl⟩

private theorem return_eff {F : Type} (s : PanSemStateFiniteExact 64 F) (ex : ExpHOL 64) (Rl : List Ivl) :
    ByteRegionEffect s (evaluateHOLFiniteState s (.return ex)).2 Rl := by
  have hret : (evaluateHOLFiniteState s (.return ex)).2 =
      { s with locals := (evaluateHOLFiniteState s (.return ex)).2.locals } := by
    rw [evaluateHOLFiniteState_return]
    split
    · rfl
    · split <;> rfl
  conv => arg 2; rw [hret]
  exact (ByteRegionEffect.refl s Rl).with_locals_clock _ s.clock

private theorem ByteRegionEffect.of_mem_globals_eq {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (Rl : List Ivl)
    (hg : post.globals = s.globals)
    (hm : post.memory = s.memory)
    (hc : post.code = s.code)
    (hma : post.memaddrs = s.memaddrs)
    (hsh : post.shMemaddrs = s.shMemaddrs)
    (hba : post.baseAddr = s.baseAddr)
    (hbe : post.be = s.be) :
    ByteRegionEffect s post Rl :=
  ⟨hc, hma, hsh, hba, hbe, hg, fun _ _ => by rw [hm], fun _ _ => by rw [hm],
   fun _ _ _ => by simp [memB, hm, hbe]⟩

private theorem bswap64_body_ro {F : Type} (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl) :
    ByteRegionEffect s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_bswap64)).2 Rl := by
  have hb : sourceFnBody Guest.Software.guestFn_bswap64 =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_bswap64).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_bswap64,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  have hasgn : ∀ (st : PanSemStateFiniteExact 64 F) (nm : MlS) (ex : ExpHOL 64),
      (evaluateHOLFiniteState st (.assign .local nm ex)).2 =
        { st with locals := (evaluateHOLFiniteState st (.assign .local nm ex)).2.locals } := by
    intro st nm ex
    rw [evaluateHOLFiniteState_assign]
    split
    · rfl
    · split <;> rfl
  have hseq_ro : ∀ (st : PanSemStateFiniteExact 64 F) (a b : ProgHOL 64),
      ByteRegionEffect st (evaluateHOLFiniteState st a).2 Rl →
      (∀ m, ByteRegionEffect st m Rl → ByteRegionEffect st (evaluateHOLFiniteState m b).2 Rl) →
      ByteRegionEffect st (evaluateHOLFiniteState st (.seq a b)).2 Rl := by
    intro st a b ha hb'
    rw [evaluateHOLFiniteState_seq_line780]
    rcases h1 : evaluateHOLFiniteState st a with ⟨r1, s1⟩
    rw [h1] at ha
    cases r1 with
    | none => exact hb' s1 ha
    | some _ => exact ha
  have hasgn_eff : ∀ (st : PanSemStateFiniteExact 64 F) (nm : MlS) (ex : ExpHOL 64),
      ByteRegionEffect st (evaluateHOLFiniteState st (.assign .local nm ex)).2 Rl := by
    intro st nm ex
    conv => arg 2; rw [hasgn st nm ex]
    exact (ByteRegionEffect.refl st Rl).with_locals_clock _ st.clock
  refine hseq_ro s _ _ (hasgn_eff s _ _) fun s1 hs1 => ?_
  exact hs1.trans (hseq_ro s1 _ _ (hasgn_eff s1 _ _) (fun s2 hs2 => hs2.trans (return_eff s2 _ Rl)))

private theorem bswap64_body_mem_eq {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_bswap64)).2.memory = s.memory := by
  have h := bswap64_body_ro s []
  funext a
  exact h.cell_frame a (fun _ hi _ => by simp at hi)

private theorem decCall_bswap64_eff {F : Type} {s : PanSemStateFiniteExact 64 F}
    {argExp : ExpHOL 64} {cont : ProgHOL 64} {Rl : List Ivl}
    (hcode : s.code = originalRuntimeCode)
    (hcont : ∀ mid : PanSemStateFiniteExact 64 F,
      mid.code = originalRuntimeCode →
      mid.memaddrs = s.memaddrs →
      mid.locals.lookup (ofString "out") = s.locals.lookup (ofString "out") →
      mid.locals.lookup (ofString "p") = s.locals.lookup (ofString "p") →
      mid.locals.lookup (ofString "a") = s.locals.lookup (ofString "a") →
      (∃ wv : BitVec 64, mid.locals.lookup (ofString "w") = some (.val (.word wv))) →
      ByteRegionEffect mid (evaluateHOLFiniteState mid cont).2 Rl) :
    ByteRegionEffect s
      (evaluateHOLFiniteState s (.decCall (ofString "w") .one (ofString "bswap64") [argExp] cont)).2
      Rl := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [argExp] with _ | vals
  · exact ByteRegionEffect.refl s Rl
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "bswap64") vals with _ | ⟨body', callee, ret'⟩
    · exact ByteRegionEffect.refl s Rl
    · dsimp only
      have hinst := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "bswap64")
        _ _ body' _ ret' vals callee (by rw [hcode]; exact lookup_bswap64) hl
      subst hinst
      have hret_eq : ret' = .one :=
        lookupCodeHOLFinite_installed_return s (ofString "bswap64") _ _ _ .one ret' vals callee
          (by rw [hcode]; exact lookup_bswap64) hl
      subst hret_eq
      split
      · exact (ByteRegionEffect.refl s Rl).with_locals_clock _ _
      · have heff_entry : ByteRegionEffect s (callEntryStateHOLFinite s callee) Rl :=
          (ByteRegionEffect.refl s Rl).with_locals_clock _ _
        have heff_b := bswap64_body_ro (callEntryStateHOLFinite s callee) Rl
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_bswap64) with ⟨rb, sb⟩
        rw [hb] at heff_b
        dsimp only at heff_b ⊢
        have heff_sb : ByteRegionEffect s sb Rl := heff_entry.trans heff_b
        cases rb with
        | none => exact heff_sb
        | some r =>
          cases r with
          | returned v =>
            dsimp only
            split
            · rename_i hsh
              have hvw : ∃ wv : BitVec 64, v = .val (.word wv) := by
                rcases v with ⟨⟨wv⟩⟩ | _ | _
                · exact ⟨wv, rfl⟩
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh
              obtain ⟨wv, rfl⟩ := hvw
              let mid := setVarHOLFinite (ofString "w") (.val (.word wv)) { sb with locals := s.locals }
              have heff_mid : ByteRegionEffect s mid Rl := heff_sb.with_locals_clock _ _
              have hc_mid : mid.code = originalRuntimeCode := heff_mid.code.trans hcode
              have hm_mid : mid.memaddrs = s.memaddrs := heff_mid.memaddrs
              have hout_mid : mid.locals.lookup (ofString "out") = s.locals.lookup (ofString "out") := by
                simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "w" ≠ ofString "out" by decide]
              have hp_mid : mid.locals.lookup (ofString "p") = s.locals.lookup (ofString "p") := by
                simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "w" ≠ ofString "p" by decide]
              have ha_mid : mid.locals.lookup (ofString "a") = s.locals.lookup (ofString "a") := by
                simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "w" ≠ ofString "a" by decide]
              have hw_mid : ∃ wv : BitVec 64, mid.locals.lookup (ofString "w") = some (.val (.word wv)) :=
                ⟨wv, by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
              have heff_c := hcont mid hc_mid hm_mid hout_mid hp_mid ha_mid hw_mid
              exact (heff_mid.trans heff_c).with_locals_clock _ _
            · exact heff_sb
          | timeOut | error | exception _ _ | finalFfi _ => exact heff_sb.with_locals_clock _ _
          | «break» | «continue» => exact heff_sb

private theorem seq_call_bswap64_eff {F : Type} {s : PanSemStateFiniteExact 64 F}
    {argExp : ExpHOL 64} {cont : ProgHOL 64} {Rl : List Ivl}
    (hcode : s.code = originalRuntimeCode)
    (hcont : ∀ mid : PanSemStateFiniteExact 64 F,
      mid.code = originalRuntimeCode →
      mid.memaddrs = s.memaddrs →
      mid.locals.lookup (ofString "out") = s.locals.lookup (ofString "out") →
      mid.locals.lookup (ofString "a") = s.locals.lookup (ofString "a") →
      (∃ wv : BitVec 64, mid.locals.lookup (ofString "w") = some (.val (.word wv))) →
      ByteRegionEffect mid (evaluateHOLFiniteState mid cont).2 Rl) :
    ByteRegionEffect s
      (evaluateHOLFiniteState s
        (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [argExp]) cont)).2
      Rl := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hc : evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [argExp]) with ⟨rc, sc⟩
  rw [evaluateHOLFiniteState_call] at hc
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [argExp] with _ | vals
  · rw [hargs] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s Rl
  · rw [hargs] at hc; dsimp only at hc
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "bswap64") vals with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s Rl
    · rw [hl] at hc; dsimp only at hc
      have hinst := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "bswap64")
        _ _ body' _ ret' vals callee (by rw [hcode]; exact lookup_bswap64) hl
      subst hinst
      have hret_eq : ret' = .one :=
        lookupCodeHOLFinite_installed_return s (ofString "bswap64") _ _ _ .one ret' vals callee
          (by rw [hcode]; exact lookup_bswap64) hl
      subst hret_eq
      split at hc
      · injection hc with hr hsc; subst hr hsc; exact (ByteRegionEffect.refl s Rl).with_locals_clock _ _
      · have heff_entry : ByteRegionEffect s (callEntryStateHOLFinite s callee) Rl :=
          (ByteRegionEffect.refl s Rl).with_locals_clock _ _
        have heff_b := bswap64_body_ro (callEntryStateHOLFinite s callee) Rl
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_bswap64) with ⟨rb, sb⟩
        rw [hb] at hc heff_b
        dsimp only at heff_b
        have heff_sb : ByteRegionEffect s sb Rl := heff_entry.trans heff_b
        cases rb with
        | none => injection hc with hr hsc; subst hr hsc; exact heff_sb
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hc
            split at hc
            · rename_i hsh
              have hvw : ∃ wv : BitVec 64, v = .val (.word wv) := by
                rcases v with ⟨⟨wv⟩⟩ | _ | _
                · exact ⟨wv, rfl⟩
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh
              obtain ⟨wv, rfl⟩ := hvw
              split at hc
              · injection hc with hr hsc; subst hr hsc
                dsimp only
                let mid := setKvarHOLFinite .local (ofString "w") (.val (.word wv)) { sb with locals := s.locals }
                have heff_mid : ByteRegionEffect s mid Rl := heff_sb.with_locals_clock _ _
                have hc_mid : mid.code = originalRuntimeCode := heff_mid.code.trans hcode
                have hm_mid : mid.memaddrs = s.memaddrs := heff_mid.memaddrs
                have hout_mid : mid.locals.lookup (ofString "out") = s.locals.lookup (ofString "out") := by
                  simp [mid, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "w" ≠ ofString "out" by decide]
                have ha_mid : mid.locals.lookup (ofString "a") = s.locals.lookup (ofString "a") := by
                  simp [mid, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "w" ≠ ofString "a" by decide]
                have hw_mid : ∃ wv : BitVec 64, mid.locals.lookup (ofString "w") = some (.val (.word wv)) :=
                  ⟨wv, by simp [mid, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
                exact heff_mid.trans (hcont mid hc_mid hm_mid hout_mid ha_mid hw_mid)
              · injection hc with hr hsc; subst hr hsc; exact heff_sb
            · injection hc with hr hsc; subst hr hsc; exact heff_sb
          | timeOut | error | exception _ _ | finalFfi _ =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb.with_locals_clock _ _
          | «break» | «continue» =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb

private theorem seq_store_word_eff {F : Type} {s : PanSemStateFiniteExact 64 F}
    {dstExp valExp : ExpHOL 64} {base w : BitVec 64} {off len : Nat} {cont : ProgHOL 64}
    (hma : s.memaddrs = ordinaryDomain)
    (hlen : len ≤ 32)
    (hoff : off + 8 ≤ len)
    (hprev : off > 0 → base.toNat < heapEnd)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word (base + BitVec.ofNat 64 off))))
    (hval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some (.val (.word w)))
    (hcont : ∀ s1 : PanSemStateFiniteExact 64 F,
      base.toNat < heapEnd →
      s1.code = s.code →
      s1.memaddrs = s.memaddrs →
      s1.locals = s.locals →
      ByteRegionEffect s1 (evaluateHOLFiniteState s1 cont).2 [(base.toNat, len)]) :
    ByteRegionEffect s (evaluateHOLFiniteState s (.seq (.store dstExp valExp) cont)).2 [(base.toNat, len)] := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases h1 : evaluateHOLFiniteState s (.store dstExp valExp) with ⟨r1, s1⟩
  cases r1 with
  | some _ =>
    have h1' := h1
    rw [evaluateHOLFiniteState_store, hdst, hval] at h1'
    dsimp only at h1'
    split at h1'
    · cases h1'
    · injection h1' with _ hs1; subst hs1; exact ByteRegionEffect.refl s _
  | none =>
    have hbase_lt : base.toNat < heapEnd := by
      have hrun' := h1
      rw [evaluateHOLFiniteState_store, hdst, hval] at hrun'
      dsimp only at hrun'
      split at hrun'
      · rename_i m' hst
        unfold flattenHOL panMemStoresHOL panMemStoreHOL at hst
        by_cases hd : s.memaddrs (base + BitVec.ofNat 64 off)
        · by_cases hz : off = 0
          · subst hz; have h0 : base + BitVec.ofNat 64 0 = base := by simp
            rw [h0] at hd; have := word_dom_lt_heapEnd hma base hd; omega
          · exact hprev (by omega)
        · simp [hd] at hst
      · cases hrun'
    have heff1 := ByteRegionEffect.of_store_word (Rl := [(base.toNat, len)]) hma h1
      (fun v hv => by rw [hval] at hv; injection hv with h; exact ⟨w, h.symm⟩)
      (fun addr ha _ => by
        rw [hdst] at ha
        injection ha with e1; injection e1 with e2; injection e2 with e3; subst e3
        have hnat := bv_add_off_nat base off hbase_lt (by omega)
        exact ⟨(base.toNat, len), List.mem_singleton.2 rfl, by rw [hnat]; omega, by rw [hnat]; omega⟩)
    exact heff1.1.trans (hcont s1 hbase_lt heff1.1.code heff1.1.memaddrs heff1.2)

private theorem seq_storeByte_eff {F : Type} {s : PanSemStateFiniteExact 64 F}
    {dstExp valExp : ExpHOL 64} {base : BitVec 64} {off len : Nat} {cont : ProgHOL 64}
    (hma : s.memaddrs = ordinaryDomain)
    (hlen : len ≤ 32)
    (hoff : off < len)
    (hprev : off > 0 → base.toNat < heapEnd)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word (base + BitVec.ofNat 64 off))))
    (hcont : ∀ s1 : PanSemStateFiniteExact 64 F,
      base.toNat < heapEnd →
      s1.code = s.code →
      s1.memaddrs = s.memaddrs →
      s1.locals = s.locals →
      ByteRegionEffect s1 (evaluateHOLFiniteState s1 cont).2 [(base.toNat, len)]) :
    ByteRegionEffect s (evaluateHOLFiniteState s (.seq (.storeByte dstExp valExp) cont)).2 [(base.toNat, len)] := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases h1 : evaluateHOLFiniteState s (.storeByte dstExp valExp) with ⟨r1, s1⟩
  cases r1 with
  | some _ =>
    have h1' := h1
    rw [evaluateHOLFiniteState_storeByte, hdst] at h1'
    rcases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp with _ | vv
    · rw [hv] at h1'; dsimp only at h1'; injection h1' with _ hs1; subst hs1; exact ByteRegionEffect.refl s _
    · rw [hv] at h1'
      rcases vv with ⟨⟨v⟩⟩ | _ | _
      · dsimp only at h1'
        split at h1'
        · cases h1'
        · injection h1' with _ hs1; subst hs1; exact ByteRegionEffect.refl s _
      · dsimp only at h1'; injection h1' with _ hs1; subst hs1; exact ByteRegionEffect.refl s _
      · dsimp only at h1'; injection h1' with _ hs1; subst hs1; exact ByteRegionEffect.refl s _
  | none =>
    have hbase_lt_of_dom : s.memaddrs (panByteAlignHOL (base + BitVec.ofNat 64 off)) → base.toNat < heapEnd := by
      intro hd
      by_cases hz : off = 0
      · subst hz; have h0 : base + BitVec.ofNat 64 0 = base := by simp
        rw [h0] at hd; exact byteAlign_lt_heapEnd hma base hd
      · exact hprev (by omega)
    have hbase_lt : base.toNat < heapEnd := by
      have hrun' := h1
      rw [evaluateHOLFiniteState_storeByte, hdst] at hrun'
      rcases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp with _ | vv
      · rw [hv] at hrun'; simp at hrun'
      · rw [hv] at hrun'
        rcases vv with ⟨⟨v⟩⟩ | _ | _
        · dsimp only at hrun'
          split at hrun'
          · rename_i m' hst
            unfold panMemStoreByteWord8HOL at hst
            rcases hm : s.memory (panByteAlignHOL (base + BitVec.ofNat 64 off)) with ⟨cell⟩
            have hm' : (s.6 (panByteAlignHOL (base + BitVec.ofNat 64 off))).1 = cell := by
              change (s.memory (panByteAlignHOL (base + BitVec.ofNat 64 off))).1 = cell; rw [hm]
            dsimp only at hst; rw [hm'] at hst
            by_cases hd : s.memaddrs (panByteAlignHOL (base + BitVec.ofNat 64 off))
            · exact hbase_lt_of_dom hd
            · simp [hd] at hst
          · simp at hrun'
        · simp at hrun'
        · simp at hrun'
    have heff1 := ByteRegionEffect.of_storeByte (Rl := [(base.toNat, len)]) h1
      (fun addr ha _ => by
        rw [hdst] at ha
        injection ha with e1; injection e1 with e2; injection e2 with e3; subst e3
        have hnat := bv_add_off_nat base off hbase_lt (by omega)
        exact ⟨(base.toNat, len), List.mem_singleton.2 rfl, by rw [hnat]; omega, by rw [hnat]; omega⟩)
    exact heff1.1.trans (hcont s1 hbase_lt heff1.1.code heff1.1.memaddrs heff1.2)

private theorem st_be32_body_eff {F : Type} (s : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (hma : s.memaddrs = ordinaryDomain)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p))) :
    ByteRegionEffect s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_be32)).2 [(p.toNat, 4)] ∧
    ((evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_be32)).2.memory = s.memory ∨ p.toNat < heapEnd) ∧
    (∀ rv, (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_be32)).1 = some (.returned rv) →
      p.toNat < heapEnd) := by
  have hb : sourceFnBody Guest.Software.guestFn_st_be32 =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_st_be32).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_st_be32,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural]
  have hp_ev0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString "p")) = some (.val (.word p)) := hp
  have hmem_or_lt :
      ((evaluateHOLFiniteState s
        (.seq (.storeByte (.var .local (ofString "p")) (.shift .lsr (.var .local (ofString "v")) (.const 24#64)))
          (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 1#64]) (.shift .lsr (.var .local (ofString "v")) (.const 16#64)))
            (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 2#64]) (.shift .lsr (.var .local (ofString "v")) (.const 8#64)))
              (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 3#64]) (.var .local (ofString "v")))
                (.return (.const 0#64))))))).2.memory = s.memory ∧
       ∀ rv, (evaluateHOLFiniteState s
        (.seq (.storeByte (.var .local (ofString "p")) (.shift .lsr (.var .local (ofString "v")) (.const 24#64)))
          (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 1#64]) (.shift .lsr (.var .local (ofString "v")) (.const 16#64)))
            (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 2#64]) (.shift .lsr (.var .local (ofString "v")) (.const 8#64)))
              (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 3#64]) (.var .local (ofString "v")))
                (.return (.const 0#64))))))).1 ≠ some (.returned rv)) ∨ p.toNat < heapEnd := by
    rw [evaluateHOLFiniteState_seq_line780]
    rcases h1 : evaluateHOLFiniteState s
        (.storeByte (.var .local (ofString "p")) (.shift .lsr (.var .local (ofString "v")) (.const 24#64))) with ⟨r1, s1⟩
    rw [evaluateHOLFiniteState_storeByte, hp_ev0] at h1
    rcases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.shift .lsr (.var .local (ofString "v")) (.const 24#64)) with _ | vv
    · rw [hv] at h1; dsimp only at h1; injection h1 with hr1 hs1; subst hr1 hs1
      exact Or.inl ⟨rfl, by simp⟩
    · rw [hv] at h1
      rcases vv with ⟨⟨vw⟩⟩ | _ | _
      · dsimp only at h1
        split at h1
        · rename_i m' hst
          unfold panMemStoreByteWord8HOL at hst
          rcases hm : s.memory (panByteAlignHOL p) with ⟨cell⟩
          have hm' : (s.6 (panByteAlignHOL p)).1 = cell := by
            change (s.memory (panByteAlignHOL p)).1 = cell; rw [hm]
          dsimp only at hst; rw [hm'] at hst
          by_cases hd : s.memaddrs (panByteAlignHOL p)
          · exact Or.inr (byteAlign_lt_heapEnd hma p hd)
          · simp [hd] at hst
        · injection h1 with hr1 hs1; subst hr1 hs1; exact Or.inl ⟨rfl, by simp⟩
      · dsimp only at h1; injection h1 with hr1 hs1; subst hr1 hs1; exact Or.inl ⟨rfl, by simp⟩
      · dsimp only at h1; injection h1 with hr1 hs1; subst hr1 hs1; exact Or.inl ⟨rfl, by simp⟩
  refine ⟨?_, ?_, ?_⟩
  · refine seq_storeByte_eff (base := p) (off := 0) (len := 4) hma (by omega) (by omega) (fun h => by omega)
      (eval_var_local_zero s "p" p hp) fun s1 hp_lt _ hm1 hl1 => ?_
    have hp1 : s1.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hl1]; exact hp
    refine seq_storeByte_eff (s := s1) (base := p) (off := 1) (len := 4) (hm1.trans hma) (by omega) (by omega)
      (fun _ => hp_lt) (eval_add_local_const s1 "p" p 1 hp1) fun s2 _ _ hm2 hl2 => ?_
    have hp2 : s2.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hl2]; exact hp1
    refine seq_storeByte_eff (s := s2) (base := p) (off := 2) (len := 4) (hm2.trans (hm1.trans hma)) (by omega) (by omega)
      (fun _ => hp_lt) (eval_add_local_const s2 "p" p 2 hp2) fun s3 _ _ hm3 hl3 => ?_
    have hp3 : s3.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hl3]; exact hp2
    refine seq_storeByte_eff (s := s3) (base := p) (off := 3) (len := 4) (hm3.trans (hm2.trans (hm1.trans hma))) (by omega) (by omega)
      (fun _ => hp_lt) (eval_add_local_const s3 "p" p 3 hp3) fun s4 _ _ _ _ => return_eff s4 _ _
  · rcases hmem_or_lt with ⟨hm_eq, _⟩ | hp_lt
    · exact Or.inl hm_eq
    · exact Or.inr hp_lt
  · intro rv hret
    rcases hmem_or_lt with ⟨_, hne⟩ | hp_lt
    · exact absurd hret (hne rv)
    · exact hp_lt

private theorem lookup_two_words_reject_nonword {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (fname p1 p2 : MlS) (body : ProgHOL width) (w1 : BitVec width) (v2 : ValueHOL width)
    (hlook : code fname = some ([(p1, .one), (p2, .one)], body, .one))
    (hnot : ∀ w2 : BitVec width, v2 ≠ .val (.word w2)) :
    lookupCodeHOLFinite code fname [.val (.word w1), v2] = none := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rfl
  · rename_i eb el es hraw
    unfold lookupCodeHOLExact at hraw
    rw [hlook] at hraw
    rcases v2 with ⟨⟨w2⟩⟩ | _ | _
    · exact absurd rfl (hnot w2)
    · simp [shapeOfHOLExact, shapeEqHOL] at hraw
    · simp [shapeOfHOLExact, shapeEqHOL] at hraw

private theorem seq_call_st_be32_eff {F : Type} {s : PanSemStateFiniteExact 64 F}
    {pExp vExp : ExpHOL 64} {base : BitVec 64} {off len : Nat} {cont : ProgHOL 64}
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hlen : len ≤ 32)
    (hoff : off + 4 ≤ len)
    (hprev : off > 0 → base.toNat < heapEnd)
    (hp_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pExp =
      some (.val (.word (base + BitVec.ofNat 64 off))))
    (hcont : ∀ s1 : PanSemStateFiniteExact 64 F,
      base.toNat < heapEnd →
      s1.code = originalRuntimeCode →
      s1.memaddrs = ordinaryDomain →
      s1.locals = s.locals →
      ByteRegionEffect s1 (evaluateHOLFiniteState s1 cont).2 [(base.toNat, len)]) :
    ByteRegionEffect s
      (evaluateHOLFiniteState s (.seq (.call (some (none, none)) (ofString "st_be32") [pExp, vExp]) cont)).2
      [(base.toNat, len)] := by
  let pArg := base + BitVec.ofNat 64 off
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hc : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "st_be32") [pExp, vExp]) with ⟨rc, sc⟩
  rw [evaluateHOLFiniteState_call] at hc
  rcases hv_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) vExp with _ | vv
  · have hnone : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [pExp, vExp] = none := by
      simp [evalListHOLFinite, evalListHOLExact, hp_ev, hv_ev]
    rw [hnone] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s _
  · have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [pExp, vExp] =
        some [.val (.word pArg), vv] := by
      simp [evalListHOLFinite, evalListHOLExact, hp_ev, hv_ev, pArg]
    rw [hargs] at hc; dsimp only at hc
    by_cases hvw : ∃ vW : BitVec 64, vv = .val (.word vW)
    · obtain ⟨vW, rfl⟩ := hvw
      have hl := pan_two_word_lookup s.code.lookup (ofString "st_be32") (ofString "p") (ofString "v")
        (sourceFnBody Guest.Software.guestFn_st_be32) pArg vW (by decide) (by rw [hcode]; exact lookup_st_be32)
      rw [hl] at hc; dsimp only at hc
      split at hc
      · injection hc with hr hsc; subst hr hsc; exact (ByteRegionEffect.refl s _).with_locals_clock _ _
      · let entry := callEntryStateHOLFinite s
          ((HolFiniteMapExact.empty.update (ofString "p", .val (.word pArg))).update (ofString "v", .val (.word vW)))
        have hp_in : entry.locals.lookup (ofString "p") = some (.val (.word pArg)) := by
          simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "v" ≠ ofString "p" by decide]
        obtain ⟨heff_b, hlt_or_eq, hlt_b⟩ := st_be32_body_eff entry pArg hma hp_in
        rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_st_be32) with ⟨rb, sb⟩
        have hb_entry : evaluateHOLFiniteState
            (callEntryStateHOLFinite s
              ((HolFiniteMapExact.empty.update (ofString "p", .val (.word pArg))).update (ofString "v", .val (.word vW))))
            (sourceFnBody Guest.Software.guestFn_st_be32) = (rb, sb) := hb
        rw [hb_entry] at hc
        rw [hb] at heff_b hlt_or_eq
        dsimp only at heff_b hlt_or_eq
        have heff_entry : ByteRegionEffect s entry [(base.toNat, len)] :=
          (ByteRegionEffect.refl s _).with_locals_clock _ _
        have heff_sb : ByteRegionEffect s sb [(base.toNat, len)] := by
          rcases hlt_or_eq with hmem_eq | hpArg_lt
          · exact ByteRegionEffect.of_mem_globals_eq [(base.toNat, len)]
              heff_b.globals hmem_eq heff_b.code heff_b.memaddrs heff_b.shMemaddrs heff_b.baseAddr heff_b.be
          · have hbase_lt : base.toNat < heapEnd := by
              by_cases hz_off : off = 0
              · subst hz_off; have h0 : pArg = base := by simp [pArg]
                rwa [h0] at hpArg_lt
              · exact hprev (by omega)
            have hpArg_nat : pArg.toNat = base.toNat + off := bv_add_off_nat base off hbase_lt (by omega)
            exact heff_entry.trans (heff_b.mono fun i hi => by
              simp only [List.mem_singleton] at hi; subst hi
              exact Or.inr ⟨(base.toNat, len), List.mem_singleton.2 rfl, by rw [hpArg_nat]; omega, by rw [hpArg_nat]; omega⟩)
        cases rb with
        | none => injection hc with hr hsc; subst hr hsc; exact heff_sb
        | some r =>
          cases r with
          | returned rv =>
            dsimp only at hc
            split at hc
            · injection hc with hr hsc; subst hr hsc
              dsimp only
              have hpArg_lt := hlt_b rv (by rw [hb])
              have hbase_lt : base.toNat < heapEnd := by
                by_cases hz_off : off = 0
                · subst hz_off; have h0 : pArg = base := by simp [pArg]
                  rwa [h0] at hpArg_lt
                · exact hprev (by omega)
              let s1 : PanSemStateFiniteExact 64 F := { sb with locals := s.locals }
              have heff_s1 : ByteRegionEffect s s1 [(base.toNat, len)] := heff_sb.with_locals_clock _ _
              exact heff_s1.trans (hcont s1 hbase_lt (heff_s1.code.trans hcode) (heff_s1.memaddrs.trans hma) rfl)
            · injection hc with hr hsc; subst hr hsc; exact heff_sb
          | timeOut | error | exception _ _ | finalFfi _ =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb.with_locals_clock _ _
          | «break» | «continue» =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb
    · have hln := lookup_two_words_reject_nonword s.code.lookup (ofString "st_be32") (ofString "p") (ofString "v")
        _ pArg vv (by rw [hcode]; exact lookup_st_be32) (fun w hw => hvw ⟨w, hw⟩)
      rw [hln] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s _

private theorem st_be64_body_eff {F : Type} (s : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p))) :
    ByteRegionEffect s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_be64)).2 [(p.toNat, 8)] ∧
    ((evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_be64)).2.memory = s.memory ∨ p.toNat < heapEnd) ∧
    (∀ rv, (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_be64)).1 = some (.returned rv) →
      p.toNat < heapEnd) := by
  have hb : sourceFnBody Guest.Software.guestFn_st_be64 =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_st_be64).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_st_be64,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    List.map, Option.map]
  have hcond := eval_align8_eq0 s "p" p hp
  by_cases hal : (p &&& 7#64) = 0#64
  · let yesProg : ProgHOL 64 :=
      .decCall (ofString "w") .one (ofString "bswap64") [.var .local (ofString "v")]
        (.seq (.store (.var .local (ofString "p")) (.var .local (ofString "w")))
          (.return (.const 0#64)))
    have hyes_info :
        (evaluateHOLFiniteState s yesProg).1 ≠ none ∧
        (((evaluateHOLFiniteState s yesProg).2.memory = s.memory ∧
          ∀ rv, (evaluateHOLFiniteState s yesProg).1 ≠ some (.returned rv)) ∨ p.toNat < heapEnd) := by
      dsimp only [yesProg]
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
      rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.var .local (ofString "v")] with _ | vals
      · exact ⟨by simp, Or.inl ⟨rfl, by simp⟩⟩
      · dsimp only
        rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "bswap64") vals with _ | ⟨b', cal', rs'⟩
        · exact ⟨by simp, Or.inl ⟨rfl, by simp⟩⟩
        · dsimp only
          have hinst := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "bswap64")
            _ _ b' _ rs' vals cal' (by rw [hcode]; exact lookup_bswap64) hl
          subst hinst
          have hrs_eq : rs' = .one :=
            lookupCodeHOLFinite_installed_return s (ofString "bswap64") _ _ _ .one rs' vals cal'
              (by rw [hcode]; exact lookup_bswap64) hl
          subst hrs_eq
          split
          · exact ⟨by simp, Or.inl ⟨rfl, by simp⟩⟩
          · have hro0 := bswap64_body_ro (callEntryStateHOLFinite s cal') []
            have hmem0 := bswap64_body_mem_eq (callEntryStateHOLFinite s cal')
            rcases hb_run : evaluateHOLFiniteState (callEntryStateHOLFinite s cal')
                (sourceFnBody Guest.Software.guestFn_bswap64) with ⟨rb, sb⟩
            rw [hb_run] at hro0 hmem0
            dsimp only at hro0 hmem0 ⊢
            have hsb_ma : sb.memaddrs = ordinaryDomain := hro0.memaddrs.trans hma
            cases rb with
            | none => exact ⟨by simp, Or.inl ⟨hmem0, by simp⟩⟩
            | some r =>
              cases r with
              | returned v =>
                dsimp only
                split
                · rename_i hsh_v
                  have hvw : ∃ wv : BitVec 64, v = .val (.word wv) := by
                    rcases v with ⟨⟨wv⟩⟩ | _ | _
                    · exact ⟨wv, rfl⟩
                    · simp [shapeOfHOLExact, shapeEqHOL] at hsh_v
                    · simp [shapeOfHOLExact, shapeEqHOL] at hsh_v
                  obtain ⟨wv, rfl⟩ := hvw
                  let mid := setVarHOLFinite (ofString "w") (.val (.word wv)) { sb with locals := s.locals }
                  have hp_mid : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
                      (.var .local (ofString "p")) = some (.val (.word p)) := by
                    simp [evalHOLExact, mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp,
                      show ofString "w" ≠ ofString "p" by decide]
                  have hw_mid : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
                      (.var .local (ofString "w")) = some (.val (.word wv)) := by
                    simp [evalHOLExact, mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  rw [evaluateHOLFiniteState_seq_line780]
                  rcases hst_pair : evaluateHOLFiniteState mid
                      (.store (.var .local (ofString "p")) (.var .local (ofString "w"))) with ⟨rst, sst⟩
                  rw [evaluateHOLFiniteState_store, hp_mid, hw_mid] at hst_pair
                  dsimp only at hst_pair
                  split at hst_pair
                  · rename_i m' hst_p
                    injection hst_pair with hrst hsst; subst hrst hsst
                    unfold flattenHOL panMemStoresHOL panMemStoreHOL at hst_p
                    by_cases hd : sb.memaddrs p
                    · dsimp only
                      rw [(return_const0_step _).1]
                      exact ⟨by simp, Or.inr (by have := word_dom_lt_heapEnd hsb_ma p hd; omega)⟩
                    · have hdm : ¬ mid.memaddrs p := hd
                      simp [hdm] at hst_p
                  · injection hst_pair with hrst hsst; subst hrst hsst
                    exact ⟨by simp, Or.inl ⟨hmem0, by simp⟩⟩
                · exact ⟨by simp, Or.inl ⟨hmem0, by simp⟩⟩
              | timeOut | error | exception _ _ | finalFfi _ | «break» | «continue» =>
                exact ⟨by simp, Or.inl ⟨hmem0, by simp⟩⟩
    have hnn := hyes_info.1
    have hml := hyes_info.2
    have hgoal_ite : evaluateHOLFiniteState s
        (.seq (.ite (.cmp .equal (.op .and [.var .local (ofString "p"), .const 7#64]) (.const 0#64)) yesProg .skip)
          (.seq (.call (some (none, none)) (ofString "st_be32")
              [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32#64)])
            (.seq (.call (some (none, none)) (ofString "st_be32")
                [.op .add [.var .local (ofString "p"), .const 4#64], .var .local (ofString "v")])
              (.return (.const 0#64))))) = evaluateHOLFiniteState s yesProg := by
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcond]
      simp only [hal, ↓reduceIte]
      have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
      rw [if_neg h10]
      rcases hy : evaluateHOLFiniteState s yesProg with ⟨ry, sy⟩
      rw [hy] at hnn
      cases ry with
      | none => exact absurd rfl hnn
      | some _ => rfl
    rw [hgoal_ite]
    have heff_yes : ByteRegionEffect s (evaluateHOLFiniteState s yesProg).2 [(p.toNat, 8)] :=
      decCall_bswap64_eff (s := s) (argExp := .var .local (ofString "v"))
        (Rl := [(p.toNat, 8)]) hcode fun mid _ hm_mid _ hp_mid _ ⟨wv, hw_mid⟩ => by
          have hp_m : mid.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hp_mid]; exact hp
          exact seq_store_word_eff (s := mid) (base := p) (w := wv) (off := 0) (len := 8)
            (hm_mid.trans hma) (by omega) (by omega) (fun h => by omega)
            (eval_var_local_zero mid "p" p hp_m)
            (eval_var_local mid "w" wv hw_mid) fun s1 _ _ _ _ => return_eff s1 _ _
    refine ⟨heff_yes, ?_, ?_⟩
    · rcases hml with ⟨hm_eq, _⟩ | hp_lt
      · exact Or.inl hm_eq
      · exact Or.inr hp_lt
    · intro rv hret
      rcases hml with ⟨_, hne⟩ | hp_lt
      · exact absurd hret (hne rv)
      · exact hp_lt
  · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcond]
    simp only [hal, ↓reduceIte, evaluateHOLFiniteState_skip]
    have hp_ev0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.var .local (ofString "p")) = some (.val (.word p)) := hp
    have hfirst_call :
        ((evaluateHOLFiniteState s
          (.seq (.call (some (none, none)) (ofString "st_be32")
              [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32#64)])
            (.seq (.call (some (none, none)) (ofString "st_be32")
                [.op .add [.var .local (ofString "p"), .const 4#64], .var .local (ofString "v")])
              (.return (.const 0#64))))).2.memory = s.memory ∧
         ∀ rv, (evaluateHOLFiniteState s
          (.seq (.call (some (none, none)) (ofString "st_be32")
              [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32#64)])
            (.seq (.call (some (none, none)) (ofString "st_be32")
                [.op .add [.var .local (ofString "p"), .const 4#64], .var .local (ofString "v")])
              (.return (.const 0#64))))).1 ≠ some (.returned rv)) ∨ p.toNat < heapEnd := by
      rw [evaluateHOLFiniteState_seq_line780]
      rcases hc1 : evaluateHOLFiniteState s
          (.call (some (none, none)) (ofString "st_be32")
            [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32#64)]) with ⟨rc1, sc1⟩
      rw [evaluateHOLFiniteState_call] at hc1
      rcases hv_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.shift .lsr (.var .local (ofString "v")) (.const 32#64)) with _ | vv
      · have hnone : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
            [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32#64)] = none := by
          simp [evalListHOLFinite, evalListHOLExact, hp_ev0, hv_ev]
        rw [hnone] at hc1; injection hc1 with hr hsc1; subst hr hsc1; exact Or.inl ⟨rfl, by simp⟩
      · have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
            [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32#64)] =
            some [.val (.word p), vv] := by
          simp [evalListHOLFinite, evalListHOLExact, hp_ev0, hv_ev]
        rw [hargs] at hc1; dsimp only at hc1
        by_cases hvw : ∃ vW : BitVec 64, vv = .val (.word vW)
        · obtain ⟨vW, rfl⟩ := hvw
          have hl := pan_two_word_lookup s.code.lookup (ofString "st_be32") (ofString "p") (ofString "v")
            (sourceFnBody Guest.Software.guestFn_st_be32) p vW (by decide) (by rw [hcode]; exact lookup_st_be32)
          rw [hl] at hc1; dsimp only at hc1
          split at hc1
          · injection hc1 with hr hsc1; subst hr hsc1; exact Or.inl ⟨rfl, by simp⟩
          · let entry := callEntryStateHOLFinite s
              ((HolFiniteMapExact.empty.update (ofString "p", .val (.word p))).update (ofString "v", .val (.word vW)))
            have hp_in : entry.locals.lookup (ofString "p") = some (.val (.word p)) := by
              simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "v" ≠ ofString "p" by decide]
            obtain ⟨_, hlt_or_eq, hlt_b⟩ := st_be32_body_eff entry p hma hp_in
            rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_st_be32) with ⟨rb, sb⟩
            have hb_entry : evaluateHOLFiniteState
                (callEntryStateHOLFinite s
                  ((HolFiniteMapExact.empty.update (ofString "p", .val (.word p))).update (ofString "v", .val (.word vW))))
                (sourceFnBody Guest.Software.guestFn_st_be32) = (rb, sb) := hb
            rw [hb_entry] at hc1
            rw [hb] at hlt_or_eq
            dsimp only at hlt_or_eq
            rcases hlt_or_eq with hmem_eq | hp_lt
            · cases rb with
              | none => injection hc1 with hr hsc1; subst hr hsc1; exact Or.inl ⟨hmem_eq, by simp⟩
              | some r =>
                cases r with
                | returned rv' => exact Or.inr (hlt_b rv' (by rw [hb]))
                | timeOut | error | exception _ _ | finalFfi _ | «break» | «continue» =>
                  injection hc1 with hr hsc1; subst hr hsc1; exact Or.inl ⟨hmem_eq, by simp⟩
            · exact Or.inr hp_lt
        · have hln := lookup_two_words_reject_nonword s.code.lookup (ofString "st_be32") (ofString "p") (ofString "v")
            _ p vv (by rw [hcode]; exact lookup_st_be32) (fun w hw => hvw ⟨w, hw⟩)
          rw [hln] at hc1; injection hc1 with hr hsc1; subst hr hsc1; exact Or.inl ⟨rfl, by simp⟩
    refine ⟨?_, ?_, ?_⟩
    · refine seq_call_st_be32_eff (base := p) (off := 0) (len := 8) hcode hma (by omega) (by omega)
        (fun h => by omega)
        (eval_var_local_zero s "p" p hp)
        fun s1 hp_lt hc1 hm1 hl1 => ?_
      have hp1 : s1.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hl1]; exact hp
      refine seq_call_st_be32_eff (s := s1) (base := p) (off := 4) (len := 8) hc1 hm1 (by omega) (by omega)
        (fun _ => hp_lt) (eval_add_local_const s1 "p" p 4 hp1)
        fun s2 _ _ _ _ => return_eff s2 _ _
    · rcases hfirst_call with ⟨hm_eq, _⟩ | hp_lt
      · exact Or.inl hm_eq
      · exact Or.inr hp_lt
    · intro rv hret
      rcases hfirst_call with ⟨_, hne⟩ | hp_lt
      · exact absurd hret (hne rv)
      · exact hp_lt

private theorem seq_call_st_be64_eff {F : Type} {s : PanSemStateFiniteExact 64 F}
    {pExp vExp : ExpHOL 64} {base : BitVec 64} {off : Nat} {cont : ProgHOL 64}
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hoff : off + 8 ≤ 32)
    (hprev : off > 0 → base.toNat < heapEnd)
    (hp_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pExp =
      some (.val (.word (base + BitVec.ofNat 64 off))))
    (hcont : ∀ s1 : PanSemStateFiniteExact 64 F,
      base.toNat < heapEnd →
      s1.code = originalRuntimeCode →
      s1.memaddrs = ordinaryDomain →
      s1.locals = s.locals →
      ByteRegionEffect s1 (evaluateHOLFiniteState s1 cont).2 [(base.toNat, 32)]) :
    ByteRegionEffect s
      (evaluateHOLFiniteState s (.seq (.call (some (none, none)) (ofString "st_be64") [pExp, vExp]) cont)).2
      [(base.toNat, 32)] := by
  let pArg := base + BitVec.ofNat 64 off
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hc : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "st_be64") [pExp, vExp]) with ⟨rc, sc⟩
  rw [evaluateHOLFiniteState_call] at hc
  rcases hv_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) vExp with _ | vv
  · have hnone : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [pExp, vExp] = none := by
      simp [evalListHOLFinite, evalListHOLExact, hp_ev, hv_ev]
    rw [hnone] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s _
  · have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [pExp, vExp] =
        some [.val (.word pArg), vv] := by
      simp [evalListHOLFinite, evalListHOLExact, hp_ev, hv_ev, pArg]
    rw [hargs] at hc; dsimp only at hc
    by_cases hvw : ∃ vW : BitVec 64, vv = .val (.word vW)
    · obtain ⟨vW, rfl⟩ := hvw
      have hl := pan_two_word_lookup s.code.lookup (ofString "st_be64") (ofString "p") (ofString "v")
        (sourceFnBody Guest.Software.guestFn_st_be64) pArg vW (by decide) (by rw [hcode]; exact lookup_st_be64)
      rw [hl] at hc; dsimp only at hc
      split at hc
      · injection hc with hr hsc; subst hr hsc; exact (ByteRegionEffect.refl s _).with_locals_clock _ _
      · let entry := callEntryStateHOLFinite s
          ((HolFiniteMapExact.empty.update (ofString "p", .val (.word pArg))).update (ofString "v", .val (.word vW)))
        have hp_in : entry.locals.lookup (ofString "p") = some (.val (.word pArg)) := by
          simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "v" ≠ ofString "p" by decide]
        obtain ⟨heff_b, hlt_or_eq, hlt_b⟩ := st_be64_body_eff entry pArg hcode hma hp_in
        rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_st_be64) with ⟨rb, sb⟩
        have hb_entry : evaluateHOLFiniteState
            (callEntryStateHOLFinite s
              ((HolFiniteMapExact.empty.update (ofString "p", .val (.word pArg))).update (ofString "v", .val (.word vW))))
            (sourceFnBody Guest.Software.guestFn_st_be64) = (rb, sb) := hb
        rw [hb_entry] at hc
        rw [hb] at heff_b hlt_or_eq
        dsimp only at heff_b hlt_or_eq
        have heff_entry : ByteRegionEffect s entry [(base.toNat, 32)] :=
          (ByteRegionEffect.refl s _).with_locals_clock _ _
        have heff_sb : ByteRegionEffect s sb [(base.toNat, 32)] := by
          rcases hlt_or_eq with hmem_eq | hpArg_lt
          · exact ByteRegionEffect.of_mem_globals_eq [(base.toNat, 32)]
              heff_b.globals hmem_eq heff_b.code heff_b.memaddrs heff_b.shMemaddrs heff_b.baseAddr heff_b.be
          · have hbase_lt : base.toNat < heapEnd := by
              by_cases hz_off : off = 0
              · subst hz_off; have h0 : pArg = base := by simp [pArg]
                rwa [h0] at hpArg_lt
              · exact hprev (by omega)
            have hpArg_nat : pArg.toNat = base.toNat + off := bv_add_off_nat base off hbase_lt (by omega)
            exact heff_entry.trans (heff_b.mono fun i hi => by
              simp only [List.mem_singleton] at hi; subst hi
              exact Or.inr ⟨(base.toNat, 32), List.mem_singleton.2 rfl, by rw [hpArg_nat]; omega, by rw [hpArg_nat]; omega⟩)
        cases rb with
        | none => injection hc with hr hsc; subst hr hsc; exact heff_sb
        | some r =>
          cases r with
          | returned rv =>
            dsimp only at hc
            split at hc
            · injection hc with hr hsc; subst hr hsc
              dsimp only
              have hpArg_lt := hlt_b rv (by rw [hb])
              have hbase_lt : base.toNat < heapEnd := by
                by_cases hz_off : off = 0
                · subst hz_off; have h0 : pArg = base := by simp [pArg]
                  rwa [h0] at hpArg_lt
                · exact hprev (by omega)
              let s1 : PanSemStateFiniteExact 64 F := { sb with locals := s.locals }
              have heff_s1 : ByteRegionEffect s s1 [(base.toNat, 32)] := heff_sb.with_locals_clock _ _
              exact heff_s1.trans (hcont s1 hbase_lt (heff_s1.code.trans hcode) (heff_s1.memaddrs.trans hma) rfl)
            · injection hc with hr hsc; subst hr hsc; exact heff_sb
          | timeOut | error | exception _ _ | finalFfi _ =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb.with_locals_clock _ _
          | «break» | «continue» =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb
    · have hln := lookup_two_words_reject_nonword s.code.lookup (ofString "st_be64") (ofString "p") (ofString "v")
        _ pArg vv (by rw [hcode]; exact lookup_st_be64) (fun w hw => hvw ⟨w, hw⟩)
      rw [hln] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s _

/-- `u256_to_be32` (AST line 2265): EVM step: `EvmInv`, `ev`/`cur_cont` and the frame chain kept. -/
theorem «ek_u256_to_be32» :
    EvmKeeps (EvmAvoids (fun s => [(locN s "out", 32)]))
    [] (ofString "u256_to_be32") := by
  refine ⟨_, _, _, lookup_u256_to_be32, ?_⟩
  intro F s hcode hAv _hlookup _hnt hres
  have hma : s.memaddrs = ordinaryDomain := hAv.1.1.memaddrs
  suffices heff : ByteRegionEffect s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_to_be32)).2
      [(locN s "out", 32)] by
    exact ByteRegionEffect.to_evmStep_avoids hAv heff
  have hb : sourceFnBody Guest.Software.guestFn_u256_to_be32 =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_u256_to_be32).body := rfl
  rw [hb] at hres ⊢
  dsimp only [extractFn, Guest.Software.guestFn_u256_to_be32,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    List.map, Option.map] at hres ⊢
  rcases hout_lu : s.locals.lookup (ofString "out") with _ | vout
  · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres
    simp [evalHOLExact, evalListHOLExact, hout_lu] at hres
    exact absurd hres not_resumes_error
  · rcases vout with ⟨⟨out⟩⟩ | _ | _
    · have hloc_out : locN s "out" = out.toNat := by simp [locN, hout_lu]
      rw [hloc_out]
      have hcond := eval_align8_eq0 s "out" out hout_lu
      by_cases hal : (out &&& 7#64) = 0#64
      · have hdc_ne_none : ∀ (st : PanSemStateFiniteExact 64 F) (nm : MlS) (sh : ShapeHOL)
            (fn : MlS) (args : List (ExpHOL 64)) (c : ProgHOL 64),
            (∀ (m : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState m c).1 ≠ none) →
            (evaluateHOLFiniteState st (.decCall nm sh fn args c)).1 ≠ none := by
          intro st nm sh fn args c hc_nn
          rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
          rcases evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a)) args with _ | _
          · simp
          · dsimp only
            rcases lookupCodeHOLFinite st.code.lookup fn _ with _ | ⟨b', cal', rs'⟩
            · simp
            · dsimp only; split
              · simp
              · rcases evaluateHOLFiniteState (callEntryStateHOLFinite st cal') b' with ⟨rb, sb⟩
                cases rb with
                | none => simp
                | some r =>
                  cases r with
                  | returned _ => dsimp only; split <;> [ exact hc_nn _; simp ]
                  | _ => simp
        have hseq_ne_none : ∀ {p1 p2 : ProgHOL 64},
            (∀ (m : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState m p2).1 ≠ none) →
            ∀ (m : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState m (.seq p1 p2)).1 ≠ none := by
          intro p1 p2 hp2 m
          rw [evaluateHOLFiniteState_seq_line780]
          rcases evaluateHOLFiniteState m p1 with ⟨r1, m1⟩
          cases r1 with
          | none => exact hp2 m1
          | some _ => simp
        have hret_ne_none : ∀ (m : PanSemStateFiniteExact 64 F),
            (evaluateHOLFiniteState m (.return (.const 0#64))).1 ≠ none := by
          intro m; rw [(return_const0_step m).1]; simp
        let yesProg256 : ProgHOL 64 :=
          .decCall (ofString "w") .one (ofString "bswap64") [.rfield 3 (.var .local (ofString "a"))]
            (.seq (.store (.var .local (ofString "out")) (.var .local (ofString "w")))
              (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [.rfield 2 (.var .local (ofString "a"))])
                (.seq (.store (.op .add [.var .local (ofString "out"), .const 8#64]) (.var .local (ofString "w")))
                  (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [.rfield 1 (.var .local (ofString "a"))])
                    (.seq (.store (.op .add [.var .local (ofString "out"), .const 16#64]) (.var .local (ofString "w")))
                      (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [.rfield 0 (.var .local (ofString "a"))])
                        (.seq (.store (.op .add [.var .local (ofString "out"), .const 24#64]) (.var .local (ofString "w")))
                          (.return (.const 0#64)))))))))
        have hyes256_nn : (evaluateHOLFiniteState s yesProg256).1 ≠ none :=
          hdc_ne_none s _ _ _ _ _
            (hseq_ne_none (hseq_ne_none (hseq_ne_none (hseq_ne_none
              (hseq_ne_none (hseq_ne_none (hseq_ne_none hret_ne_none)))))))
        have hgoal_yes256 : evaluateHOLFiniteState s
            (.seq (.ite (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7#64]) (.const 0#64)) yesProg256 .skip)
              (.seq (.call (some (none, none)) (ofString "st_be64") [.var .local (ofString "out"), .rfield 3 (.var .local (ofString "a"))])
                (.seq (.call (some (none, none)) (ofString "st_be64") [.op .add [.var .local (ofString "out"), .const 8#64], .rfield 2 (.var .local (ofString "a"))])
                  (.seq (.call (some (none, none)) (ofString "st_be64") [.op .add [.var .local (ofString "out"), .const 16#64], .rfield 1 (.var .local (ofString "a"))])
                    (.seq (.call (some (none, none)) (ofString "st_be64") [.op .add [.var .local (ofString "out"), .const 24#64], .rfield 0 (.var .local (ofString "a"))])
                      (.return (.const 0#64))))))) = evaluateHOLFiniteState s yesProg256 := by
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcond]
          simp only [hal, ↓reduceIte]
          have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
          rw [if_neg h10]
          rcases hy : evaluateHOLFiniteState s yesProg256 with ⟨ry, sy⟩
          rw [hy] at hyes256_nn
          cases ry with
          | none => exact absurd rfl hyes256_nn
          | some _ => rfl
        rw [hgoal_yes256]
        exact decCall_bswap64_eff (s := s) (Rl := [(out.toNat, 32)]) hcode
          fun mid0 hc_m0 hm_m0 hout_m0 _ _ ⟨wv0, hw_m0⟩ => by
            have ho0 : mid0.locals.lookup (ofString "out") = some (.val (.word out)) := by
              rw [hout_m0]; exact hout_lu
            refine seq_store_word_eff (s := mid0) (base := out) (w := wv0) (off := 0) (len := 32)
              (hm_m0.trans hma) (by omega) (by omega) (fun h => by omega)
              (eval_var_local_zero mid0 "out" out ho0)
              (eval_var_local mid0 "w" wv0 hw_m0) fun s1 hout_lt hc_s1 hm_s1 hl_s1 => ?_
            refine seq_call_bswap64_eff (s := s1) (Rl := [(out.toNat, 32)])
              (hc_s1.trans hc_m0) fun mid1 hc_m1 hm_m1 hout_m1 _ ⟨wv1, hw_m1⟩ => ?_
            have ho1 : mid1.locals.lookup (ofString "out") = some (.val (.word out)) := by
              rw [hout_m1, hl_s1]; exact ho0
            refine seq_store_word_eff (s := mid1) (base := out) (w := wv1) (off := 8) (len := 32)
              (hm_m1.trans (hm_s1.trans (hm_m0.trans hma))) (by omega) (by omega) (fun _ => hout_lt)
              (eval_add_local_const mid1 "out" out 8 ho1)
              (eval_var_local mid1 "w" wv1 hw_m1) fun s2 _ hc_s2 hm_s2 hl_s2 => ?_
            refine seq_call_bswap64_eff (s := s2) (Rl := [(out.toNat, 32)])
              (hc_s2.trans hc_m1) fun mid2 hc_m2 hm_m2 hout_m2 _ ⟨wv2, hw_m2⟩ => ?_
            have ho2 : mid2.locals.lookup (ofString "out") = some (.val (.word out)) := by
              rw [hout_m2, hl_s2]; exact ho1
            refine seq_store_word_eff (s := mid2) (base := out) (w := wv2) (off := 16) (len := 32)
              (hm_m2.trans (hm_s2.trans (hm_m1.trans (hm_s1.trans (hm_m0.trans hma))))) (by omega) (by omega)
              (fun _ => hout_lt)
              (eval_add_local_const mid2 "out" out 16 ho2)
              (eval_var_local mid2 "w" wv2 hw_m2) fun s3 _ hc_s3 hm_s3 hl_s3 => ?_
            refine seq_call_bswap64_eff (s := s3) (Rl := [(out.toNat, 32)])
              (hc_s3.trans hc_m2) fun mid3 _ hm_m3 hout_m3 _ ⟨wv3, hw_m3⟩ => ?_
            have ho3 : mid3.locals.lookup (ofString "out") = some (.val (.word out)) := by
              rw [hout_m3, hl_s3]; exact ho2
            refine seq_store_word_eff (s := mid3) (base := out) (w := wv3) (off := 24) (len := 32)
              (hm_m3.trans (hm_s3.trans (hm_m2.trans (hm_s2.trans (hm_m1.trans (hm_s1.trans (hm_m0.trans hma)))))))
              (by omega) (by omega) (fun _ => hout_lt)
              (eval_add_local_const mid3 "out" out 24 ho3)
              (eval_var_local mid3 "w" wv3 hw_m3) fun s4 _ _ _ _ => return_eff s4 _ _
      · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcond]
        simp only [hal, ↓reduceIte, evaluateHOLFiniteState_skip]
        refine seq_call_st_be64_eff (base := out) (off := 0) hcode hma (by omega) (fun h => by omega)
          (eval_var_local_zero s "out" out hout_lu)
          fun s1 hout_lt hc1 hm1 hl1 => ?_
        have hout1 : s1.locals.lookup (ofString "out") = some (.val (.word out)) := by rw [hl1]; exact hout_lu
        refine seq_call_st_be64_eff (s := s1) (base := out) (off := 8) hc1 hm1 (by omega) (fun _ => hout_lt)
          (eval_add_local_const s1 "out" out 8 hout1)
          fun s2 _ hc2 hm2 hl2 => ?_
        have hout2 : s2.locals.lookup (ofString "out") = some (.val (.word out)) := by rw [hl2]; exact hout1
        refine seq_call_st_be64_eff (s := s2) (base := out) (off := 16) hc2 hm2 (by omega) (fun _ => hout_lt)
          (eval_add_local_const s2 "out" out 16 hout2)
          fun s3 _ hc3 hm3 hl3 => ?_
        have hout3 : s3.locals.lookup (ofString "out") = some (.val (.word out)) := by rw [hl3]; exact hout2
        refine seq_call_st_be64_eff (s := s3) (base := out) (off := 24) hc3 hm3 (by omega) (fun _ => hout_lt)
          (eval_add_local_const s3 "out" out 24 hout3)
          fun s4 _ _ _ _ => return_eff s4 _ _
    · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres
      simp [evalHOLExact, evalListHOLExact, hout_lu, valueIsWord] at hres
      exact absurd hres not_resumes_error
    · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres
      simp [evalHOLExact, evalListHOLExact, hout_lu, valueIsWord] at hres
      exact absurd hres not_resumes_error

/-! ## 8. `ek_is_warm_storage_key` (`is_warm_storage_key(addr, key)`) -/

theorem lookup_memcpy :
    originalRuntimeCode.lookup (ofString "memcpy") =
      some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memcpy, .one) :=
  lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memcpy) rfl

theorem lookup_memeq :
    originalRuntimeCode.lookup (ofString "memeq") =
      some ([(ofString "a", .one), (ofString "b", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memeq, .one) :=
  lookup_of_guestAst_getElem 18 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memeq) rfl

theorem lookup_htab_find_leaf :
    originalRuntimeCode.lookup (ofString "htab_find_leaf") =
      some ([(ofString "t", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_htab_find_leaf, .one) :=
  lookup_of_guestAst_getElem 131 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_find_leaf) rfl

theorem lookup_htab_has :
    originalRuntimeCode.lookup (ofString "htab_has") =
      some ([(ofString "t", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_htab_has, .one) :=
  lookup_of_guestAst_getElem 133 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_has) rfl

theorem lookup_sk_make :
    originalRuntimeCode.lookup (ofString "sk_make") =
      some ([(ofString "addr", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_sk_make, .one) :=
  lookup_of_guestAst_getElem 360 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_sk_make) rfl

theorem lookup_is_warm_storage_key :
    originalRuntimeCode.lookup (ofString "is_warm_storage_key") =
      some ([(ofString "addr", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_is_warm_storage_key, .one) :=
  lookup_of_guestAst_getElem 525 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_is_warm_storage_key) rfl

private def LocFrame {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  t = { s with locals := t.locals, clock := t.clock }

private theorem LocFrame.refl {F : Type} (s : PanSemStateFiniteExact 64 F) : LocFrame s s := by
  cases s; rfl

private theorem LocFrame.trans {F : Type} {s t u : PanSemStateFiniteExact 64 F}
    (h1 : LocFrame s t) (h2 : LocFrame t u) : LocFrame s u := by
  unfold LocFrame at *; rw [h2, h1]

private theorem LocFrame.with_locals_clock {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : LocFrame s t) (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    LocFrame s { t with locals := locals, clock := k } := by
  unfold LocFrame at h ⊢; rw [h]

private def readOnlyProg (good : MlS → Bool) : ProgHOL 64 → Bool
  | .dec _ _ _ body => readOnlyProg good body
  | .seq first second => readOnlyProg good first && readOnlyProg good second
  | .ite _ yes no => readOnlyProg good yes && readOnlyProg good no
  | .while _ body => readOnlyProg good body
  | .decCall _ _ fname _ cont => good fname && readOnlyProg good cont
  | .assign .local _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | _ => false

private theorem lex_of {a1 a2 b1 b2 : Nat} (h : a1 < a2 ∨ a1 = a2 ∧ b1 < b2) :
    Prod.Lex (· < ·) (· < ·) (a1, b1) (a2, b2) := by
  rcases h with h | ⟨rfl, h⟩
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ h

private theorem evaluate_readOnlyProg {F : Type} (good : MlS → Bool)
    (hgood : ∀ function, good function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      readOnlyProg good body = true)
    (program : ProgHOL 64) (supported : readOnlyProg good program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode) :
    LocFrame state (evaluateHOLFiniteState state program).2 := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]; exact LocFrame.refl state
  | «break» => rw [evaluateHOLFiniteState_break]; exact LocFrame.refl state
  | «continue» => rw [evaluateHOLFiniteState_continue]; exact LocFrame.refl state
  | annot _ _ => rw [evaluateHOLFiniteState_annot]; exact LocFrame.refl state
  | raise _ _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only
      split
      · rfl
      · exact LocFrame.refl state
    · exact LocFrame.refl state
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · exact LocFrame.refl state
    · split
      · rfl
      · exact LocFrame.refl state
  | assign kind name value =>
    cases kind with
    | global => simp [shape, readOnlyProg] at supported
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact LocFrame.refl state
      · split
        · rfl
        · exact LocFrame.refl state
  | dec name kind initializer body =>
    have child : readOnlyProg good body = true := by simpa only [shape, readOnlyProg] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact LocFrame.refl state
    · rename_i val _
      split
      · have ih := evaluate_readOnlyProg good hgood body child (setVarHOLFinite name val state) code
        unfold LocFrame at ih ⊢; dsimp only; rw [ih]; rfl
      · exact LocFrame.refl state
  | seq first second =>
    have children : readOnlyProg good first = true ∧ readOnlyProg good second = true := by
      simpa only [shape, readOnlyProg, Bool.and_eq_true] using supported
    have ih1 := evaluate_readOnlyProg good hgood first children.1 state code
    have remaining := evaluateHOLFiniteState_clock_le state first
    have meta' := PanRunBounded.evaluateHOLFiniteState_metadata state first
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at ih1 remaining meta'
      dsimp only at ih1 remaining meta' ⊢
      cases result with
      | none =>
        have mclock : middle.clock ≤ state.clock := remaining
        exact ih1.trans (evaluate_readOnlyProg good hgood second children.2 middle (meta'.1.trans code))
      | some _ => exact ih1
  | ite condition yes no =>
    have children : readOnlyProg good yes = true ∧ readOnlyProg good no = true := by
      simpa only [shape, readOnlyProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_readOnlyProg good hgood no children.2 state code
      · exact evaluate_readOnlyProg good hgood yes children.1 state code
    · exact LocFrame.refl state
  | «while» condition body =>
    have child : readOnlyProg good body = true := by simpa only [shape, readOnlyProg] using supported
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rfl
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_readOnlyProg good hgood body child (decClockHOLFinite state) code
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          have meta' := PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at ih1 remaining meta'
            dsimp only at ih1 remaining meta' ⊢
            have smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining; omega
            have mCode : middle.code = originalRuntimeCode := meta'.1.trans code
            have ih1' : LocFrame state middle := by unfold LocFrame at ih1 ⊢; rw [ih1]; rfl
            cases result with
            | none =>
              exact ih1'.trans (evaluate_readOnlyProg good hgood (.while condition body)
                (by simpa [readOnlyProg] using child) middle mCode)
            | some result =>
              cases result with
              | «continue» =>
                exact ih1'.trans (evaluate_readOnlyProg good hgood (.while condition body)
                  (by simpa [readOnlyProg] using child) middle mCode)
              | «break» | returned _ | exception _ _ | finalFfi _ | error | timeOut => exact ih1'
      · exact LocFrame.refl state
    · exact LocFrame.refl state
  | decCall name kind function arguments continuation =>
    have children : good function = true ∧ readOnlyProg good continuation = true := by
      simpa only [shape, readOnlyProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    rcases hargs : evalListHOLFinite state
        (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with _ | values
    · exact LocFrame.refl state
    · dsimp only
      rcases found : lookupCodeHOLFinite state.code.lookup function values with _ | ⟨body, callee, rs⟩
      · exact LocFrame.refl state
      · dsimp only
        have found' : lookupCodeHOLFinite originalRuntimeCode.lookup function values =
            some (body, callee, rs) := by rwa [← code]
        have bodyOk := hgood function children.1 values body callee rs found'
        split
        · rfl
        · rename_i nonzero
          have ih := evaluate_readOnlyProg good hgood body bodyOk
            (callEntryStateHOLFinite state callee) code
          have meta' := PanRunBounded.evaluateHOLFiniteState_metadata
            (callEntryStateHOLFinite state callee) body
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
          | mk res st =>
            rw [hrun] at ih meta' cl
            dsimp only at ih meta' cl ⊢
            change st.clock ≤ state.clock - 1 at cl
            have small : st.clock < state.clock := by omega
            have stCode : st.code = originalRuntimeCode := meta'.1.trans code
            have ih' : LocFrame state st := by unfold LocFrame at ih ⊢; rw [ih]; rfl
            cases res with
            | none => exact ih'
            | some r =>
              cases r with
              | returned v =>
                dsimp only
                split
                · set resumed := setVarHOLFinite name v { st with locals := state.locals }
                  have smallR : resumed.clock < state.clock := small
                  have rCode : resumed.code = originalRuntimeCode := stCode
                  have ihR : LocFrame state resumed := ih'.with_locals_clock _ _
                  have ih2 := evaluate_readOnlyProg good hgood continuation children.2 resumed rCode
                  exact (ihR.trans ih2).with_locals_clock _ _
                · exact ih'
              | timeOut | error | exception _ _ | finalFfi _ => exact ih'.with_locals_clock _ _
              | «break» | «continue» => exact ih'
  | _ => simp [shape, readOnlyProg] at supported
termination_by (state.clock, sizeOf program)
decreasing_by
  all_goals
    simp_wf
    apply lex_of
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite,
      ProgHOL.seq.sizeOf_spec, ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec,
      ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec, true_and]
    first
      | exact Or.inl smallR
      | exact Or.inl smaller
      | omega
      | (rcases Nat.lt_or_eq_of_le mclock with h | h
         · exact Or.inl h
         · exact Or.inr ⟨h, by simp +arith⟩)
      | exact Or.inr ⟨rfl, by simp +arith⟩

private def htabHasCallees (f : MlS) : Bool :=
  f == ofString "htab_has" || f == ofString "htab_find_leaf" || f == ofString "memeq"

private theorem htabHasCallees_good :
    ∀ function, htabHasCallees function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      readOnlyProg htabHasCallees body = true := by
  intro function hfn values body callee rs hfound
  simp only [htabHasCallees, Bool.or_eq_true, beq_iff_eq] at hfn
  rcases hfn with (rfl | rfl) | rfl
  · have hsame := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
      (ofString "htab_has") _ _ body _ rs values callee lookup_htab_has hfound
    subst hsame; rfl
  · have hsame := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
      (ofString "htab_find_leaf") _ _ body _ rs values callee lookup_htab_find_leaf hfound
    subst hsame; rfl
  · have hsame := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
      (ofString "memeq") _ _ body _ rs values callee lookup_memeq hfound
    subst hsame; rfl

private def noReturnOrRaise : ProgHOL 64 → Bool
  | .seq a b => noReturnOrRaise a && noReturnOrRaise b
  | .ite _ a b => noReturnOrRaise a && noReturnOrRaise b
  | .while _ a => noReturnOrRaise a
  | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

private theorem evaluate_noReturnOrRaise {F : Type} (p : ProgHOL 64) (hp : noReturnOrRaise p = true)
    (s : PanSemStateFiniteExact 64 F) :
    ¬ Resumes (evaluateHOLFiniteState s p).1 := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
  | assign k _ _ =>
    cases k with
    | global => simp [shape, noReturnOrRaise] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact not_resumes_error
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · exact not_resumes_error
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · exact not_resumes_error
      · exact not_resumes_error
    · exact not_resumes_error
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · exact not_resumes_error
      · exact not_resumes_error
    · exact not_resumes_error
  | seq a b =>
    have hab : noReturnOrRaise a = true ∧ noReturnOrRaise b = true := by
      simpa [shape, noReturnOrRaise, Bool.and_eq_true] using hp
    have rem := evaluateHOLFiniteState_clock_le s a
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noReturnOrRaise a hab.1 s
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha rem
    cases r with
    | none =>
      have mclk : m.clock ≤ s.clock := rem
      exact evaluate_noReturnOrRaise b hab.2 m
    | some _ => exact ha
  | ite _ a b =>
    have hab : noReturnOrRaise a = true ∧ noReturnOrRaise b = true := by
      simpa [shape, noReturnOrRaise, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noReturnOrRaise b hab.2 s
      · exact evaluate_noReturnOrRaise a hab.1 s
    · exact not_resumes_error
  | «while» cond body =>
    have hb : noReturnOrRaise body = true := by simpa [shape, noReturnOrRaise] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · rename_i nonzero
          have dec_lt : (decClockHOLFinite s).clock < s.clock := by
            simp only [decClockHOLFinite]; omega
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_noReturnOrRaise body hb (decClockHOLFinite s)
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem
          have smaller : mid.clock < s.clock := by
            change mid.clock ≤ s.clock - 1 at rem; omega
          cases r1 with
          | none =>
            exact evaluate_noReturnOrRaise (.while cond body) (by simpa [noReturnOrRaise] using hb) mid
          | some r1 =>
            cases r1 with
            | «continue» =>
              exact evaluate_noReturnOrRaise (.while cond body) (by simpa [noReturnOrRaise] using hb) mid
            | «break» | timeOut | finalFfi _ => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
            | returned _ | exception _ _ => exact ih1
            | error => exact not_resumes_error
      · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
    · exact not_resumes_error
  | _ => simp [shape, noReturnOrRaise] at hp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    subst shape
    simp_wf
    first
      | exact Prod.Lex.left _ _ dec_lt
      | exact Prod.Lex.left _ _ smaller
      | exact Prod.Lex.right _ (by omega)
      | (rcases Nat.lt_or_eq_of_le mclk with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (by omega))

private def noBreak : ProgHOL 64 → Bool
  | .break => false
  | .seq a b => noBreak a && noBreak b
  | .ite _ a b => noBreak a && noBreak b
  | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

private theorem evaluate_noBreak {F : Type} (p : ProgHOL 64) (hp : noBreak p = true)
    (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s p).1 ≠ some .break := by
  cases shape : p with
  | «break» => simp [shape, noBreak] at hp
  | skip => simp [evaluateHOLFiniteState_skip]
  | assign k _ _ =>
    cases k with
    | global => simp [shape, noBreak] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · simp
      · split <;> simp
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | seq a b =>
    have hab : noBreak a = true ∧ noBreak b = true := by
      simpa [shape, noBreak, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noBreak a hab.1 s
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha
    cases r with
    | none => exact evaluate_noBreak b hab.2 m
    | some _ => exact ha
  | ite _ a b =>
    have hab : noBreak a = true ∧ noBreak b = true := by
      simpa [shape, noBreak, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noBreak b hab.2 s
      · exact evaluate_noBreak a hab.1 s
    · simp
  | _ => simp [shape, noBreak] at hp

private def MemcpyEffInv {F : Type} (dst0 n0 : BitVec 64) (Rl : List Ivl)
    (s0 s : PanSemStateFiniteExact 64 F) : Prop :=
  s.code = originalRuntimeCode ∧
  s.memaddrs = ordinaryDomain ∧
  ByteRegionEffect s0 s Rl ∧
  s.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
  s.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
  ∃ iw : BitVec 64,
    s.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
    iw.toNat ≤ n0.toNat ∧
    (0 < iw.toNat → sourceBase ≤ dst0.toNat)

private theorem eval_load_one_isWord {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (val : ValueHOL 64)
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one e) = some val) :
    ∃ w : BitVec 64, val = .val (.word w) :=
  word_of_load_one s e val he

private theorem eval_add2_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (d i : MlS) (x y a : BitVec 64)
    (hx : s.locals.lookup d = some (.val (.word x)))
    (hy : s.locals.lookup i = some (.val (.word y)))
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local d, .var .local i]) = some (.val (.word a))) :
    a = x + y := by
  simp [evalHOLExact, evalListHOLExact, hx, hy, valueIsWord, valueWord, wordOpHOL, wordOp] at he
  exact he.symm

private theorem eval_add3_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (d i : MlS) (x y c a : BitVec 64)
    (hx : s.locals.lookup d = some (.val (.word x)))
    (hy : s.locals.lookup i = some (.val (.word y)))
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local d, .var .local i, .const c]) = some (.val (.word a))) :
    a = x + y + c := by
  simp [evalHOLExact, evalListHOLExact, hx, hy, valueIsWord, valueWord, wordOpHOL, wordOp] at he
  rw [← he, BitVec.add_assoc]

private theorem eval_notLower_true {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n0 iw k w : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const k])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    ¬ (n0 < iw + k) := by
  simp [evalHOLExact, evalListHOLExact, hn, hi, valueIsWord, valueWord, wordOpHOL, wordOp,
    Compiler.Encoders.Asm.wordCmpHOL] at he
  intro hlt
  have hnotle : ¬ (iw + k ≤ n0) := by
    rw [BitVec.lt_def] at hlt; rw [BitVec.le_def]; omega
  simp [hnotle] at he
  exact hw he.symm

private theorem eval_lower_true {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n0 iw w : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word w)))
    (hw : w ≠ 0) :
    iw < n0 := by
  simp [evalHOLExact, hn, hi, Compiler.Encoders.Asm.wordCmpHOL] at he
  by_contra hge
  simp [hge] at he
  exact hw he.symm

private theorem eval_lower_false {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n0 iw : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word 0))) :
    n0.toNat ≤ iw.toNat := by
  simp only [evalHOLExact, hn, hi, Compiler.Encoders.Asm.wordCmpHOL] at he
  by_cases hlt : iw < n0
  · simp [hlt] at he
  · rw [BitVec.lt_def] at hlt; omega

private theorem while_preserve_eff {F : Type} {dst0 n0 : BitVec 64} {Rl : List Ivl}
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (hnb : noBreak body = true) (hnc : noTopContinue body = true)
    (hbody : ∀ (s0 s : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      MemcpyEffInv dst0 n0 Rl s0 s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word w)) → w ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      MemcpyEffInv dst0 n0 Rl s0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2)
    (k : Nat) (s0 s post : PanSemStateFiniteExact 64 F) (hk : s.clock ≤ k)
    (hinv : MemcpyEffInv dst0 n0 Rl s0 s)
    (hrun : evaluateHOLFiniteState s (.while cond body) = (none, post)) :
    MemcpyEffInv dst0 n0 Rl s0 post ∧
      @evalHOLExact 64 F _ post.toExact (fun a => Classical.propDecidable (post.memaddrs a)) cond =
        some (.val (.word 0)) := by
  induction k generalizing s with
  | zero =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · split at hrun
        · simp at hrun
        · omega
      · rename_i hz
        have hcw0 : cw = 0 := Classical.not_not.mp hz
        subst hcw0; simp at hrun; subst hrun; exact ⟨hinv, hcond⟩
    · simp at hrun
  | succ k ih =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · rename_i hnz
        split at hrun
        · simp at hrun
        · dsimp only at hrun
          rw [fixClockHOLFinite_evaluateState] at hrun
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have nb := evaluate_noBreak body hnb (decClockHOLFinite s)
          have nc := evaluate_noTopContinue body hnc (decClockHOLFinite s)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at hrun rem nb nc
          cases r1 with
          | none =>
            have hmid : MemcpyEffInv dst0 n0 Rl s0 mid := by
              have hb := hbody s0 s cw hinv hcond hnz (by rw [hbr])
              rw [hbr] at hb; exact hb
            have hmk : mid.clock ≤ k := by change mid.clock ≤ s.clock - 1 at rem; omega
            exact ih mid hmk hmid hrun
          | some r1 =>
            cases r1 with
            | «continue» => exact absurd rfl nc
            | «break» => exact absurd rfl nb
            | _ => simp at hrun
      · rename_i hz
        have hcw0 : cw = 0 := Classical.not_not.mp hz
        subst hcw0; simp at hrun; subst hrun; exact ⟨hinv, hcond⟩
    · simp at hrun

private theorem memcpy_store_word_step {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {dst0 iw n0 : BitVec 64} {Rl : List Ivl}
    {dstExp srcExp : ExpHOL 64} {off : Nat}
    (hma : s.memaddrs = ordinaryDomain)
    (_hfit : dst0.toNat + n0.toNat ≤ 2 ^ 64)
    (hin_rl : (dst0.toNat, n0.toNat) ∈ Rl)
    (hiw_end : iw.toNat + off + 8 ≤ n0.toNat)
    (hrun : evaluateHOLFiniteState s (.store dstExp (.load .one srcExp)) = (none, post))
    (hdst_ev : ∀ a : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) dstExp =
        some (.val (.word a)) → a.toNat = dst0.toNat + iw.toNat + off) :
    ByteRegionEffect s post Rl ∧ post.locals = s.locals ∧
      sourceBase ≤ dst0.toNat + iw.toNat + off := by
  have hd : sourceBase ≤ dst0.toNat + iw.toNat + off := by
    rw [evaluateHOLFiniteState_store] at hrun
    split at hrun
    · rename_i addr had
      split at hrun
      · rename_i val hv
        obtain ⟨w, rfl⟩ := eval_load_one_isWord s srcExp val hv
        split at hrun
        · rename_i mem hmem
          have hdom : s.memaddrs addr := by
            simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hmem
            by_contra hc; simp [hc] at hmem
          rw [hma, ordinaryDomain_iff] at hdom
          have ha_eq := hdst_ev addr had
          rw [sourceBase_val]; omega
        · simp at hrun
      · simp at hrun
    · simp at hrun
  have he := ByteRegionEffect.of_store_word hma hrun (eval_load_one_isWord s srcExp)
    (fun addr had _ => ⟨(dst0.toNat, n0.toNat), hin_rl, by have := hdst_ev addr had; omega,
      by have := hdst_ev addr had; omega⟩)
  exact ⟨he.1, he.2, hd⟩

private theorem memcpy_storeByte_step {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {dst0 iw n0 : BitVec 64} {Rl : List Ivl}
    {dstExp valExp : ExpHOL 64} {off : Nat}
    (hma : s.memaddrs = ordinaryDomain)
    (_hfit : dst0.toNat + n0.toNat ≤ 2 ^ 64)
    (hin_rl : (dst0.toNat, n0.toNat) ∈ Rl)
    (hiw_end : iw.toNat + off < n0.toNat)
    (hrun : evaluateHOLFiniteState s (.storeByte dstExp valExp) = (none, post))
    (hdst_ev : ∀ a : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) dstExp =
        some (.val (.word a)) → a.toNat = dst0.toNat + iw.toNat + off) :
    ByteRegionEffect s post Rl ∧ post.locals = s.locals ∧
      sourceBase ≤ dst0.toNat + iw.toNat + off := by
  have hd : sourceBase ≤ dst0.toNat + iw.toNat + off := by
    rw [evaluateHOLFiniteState_storeByte] at hrun
    split at hrun
    · rename_i addr had
      split at hrun
      · split at hrun
        · rename_i mem hmem
          have hdom : s.memaddrs (panByteAlignHOL addr) := by
            by_contra hc
            revert hmem
            simp only [panMemStoreByteWord8HOL]
            split <;> first | contradiction | simp [hc] | (split <;> first | contradiction | simp [hc])
          rw [hma, ordinaryDomain_iff] at hdom
          have hal : (panByteAlignHOL addr).toNat = addr.toNat / 8 * 8 := panByteAlign_toNat64 addr
          have ha_eq := hdst_ev addr had
          rw [sourceBase_val]; omega
        · simp at hrun
      · simp at hrun
    · simp at hrun
  have he := ByteRegionEffect.of_storeByte hrun
    (fun addr had _ => ⟨(dst0.toNat, n0.toNat), hin_rl, by have := hdst_ev addr had; omega,
      by have := hdst_ev addr had; omega⟩)
  exact ⟨he.1, he.2, hd⟩

private theorem assign_i_add_step {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {iw k : BitVec 64} {Rl : List Ivl}
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hrun : evaluateHOLFiniteState s
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const k])) = (none, post)) :
    ByteRegionEffect s post Rl ∧
      post.locals.lookup (ofString "i") = some (.val (.word (iw + k))) ∧
      (∀ m, m ≠ ofString "i" → post.locals.lookup m = s.locals.lookup m) := by
  rw [evaluateHOLFiniteState_assign] at hrun
  have hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "i"), .const k]) = some (.val (.word (iw + k))) := by
    simp [evalHOLExact, evalListHOLExact, hi, valueIsWord, valueWord, wordOpHOL, wordOp]
  have hval : s.isValidValueHOLFinite .local (ofString "i") (.val (.word (iw + k))) = true := by
    simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hi, shapeOfHOLExact, shapeEqHOL]
  rw [hev] at hrun; dsimp only at hrun; rw [if_pos hval] at hrun
  injection hrun with _ hpost
  subst hpost
  refine ⟨(ByteRegionEffect.refl s Rl).with_locals_clock _ _, ?_, ?_⟩
  · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · intro m hm
    simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hm]

private theorem eval_memcpy_bounded {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dst0 src0 n0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (_hsrc : s.locals.lookup (ofString "src") = some (.val (.word src0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hn_pos : 0 < n0.toNat)
    (hn_small : n0.toNat ≤ 64)
    (hfit : dst0.toNat + n0.toNat ≤ 2 ^ 64)
    (hin_rl : (dst0.toNat, n0.toNat) ∈ Rl)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memcpy)).1) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memcpy)).1 =
      some (.returned (.val (.word 0))) ∧
    sourceBase ≤ dst0.toNat ∧
    ByteRegionEffect s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memcpy)).2 Rl := by
  revert hres
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memcpy,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  have hiv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.const (BitVec.ofNat 64 0)) = some (.val (.word 0)) := rfl
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [hiv]; dsimp only; rw [if_pos hsh0]
  set s1 := setVarHOLFinite (ofString "i") (.val (.word 0)) s with hs1
  have hinv1 : MemcpyEffInv dst0 n0 Rl s s1 := by
    refine ⟨hcode, hma, (ByteRegionEffect.refl s Rl).with_locals_clock _ _, ?_, ?_, 0, ?_, Nat.zero_le _,
      fun h => by simp at h⟩
    · have hne : ofString "dst" ≠ ofString "i" := by decide
      simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne, hdst]
    · have hne : ofString "n" ≠ ofString "i" := by decide
      simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne, hn]
    · simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hnw_step : ∀ (iw k : BitVec 64), iw.toNat ≤ n0.toNat → k.toNat ≤ 32 → ¬ (n0 < iw + k) →
      (iw + k).toNat = iw.toNat + k.toNat ∧ iw.toNat + k.toNat ≤ n0.toNat := by
    intro iw k hiw hk hnl
    have hsum_lt : iw.toNat + k.toNat < 2 ^ 64 := by omega
    have hadd : (iw + k).toNat = iw.toNat + k.toNat := BitVec.toNat_add_of_lt hsum_lt
    rw [BitVec.lt_def, hadd] at hnl
    exact ⟨hadd, by omega⟩
  have hdom_first : ∀ (iw : BitVec 64), (0 < iw.toNat → sourceBase ≤ dst0.toNat) →
      sourceBase ≤ dst0.toNat + iw.toNat + 0 → sourceBase ≤ dst0.toNat := by
    intro iw hprev h0
    by_cases hiz : iw.toNat = 0
    · omega
    · exact hprev (by omega)
  have hstep1 : ∀ (s0 t : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      MemcpyEffInv dst0 n0 Rl s0 t →
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .notLower (.var .local (ofString "n"))
          (.op .add [.var .local (ofString "i"), .const 32])) = some (.val (.word w)) →
      w ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite t)
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
            (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
          (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8])
              (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 8])))
            (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16])
                (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 16])))
              (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24])
                  (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 24])))
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32]))))))).1 = none →
      MemcpyEffInv dst0 n0 Rl s0 (evaluateHOLFiniteState (decClockHOLFinite t)
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
            (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
          (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8])
              (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 8])))
            (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16])
                (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 16])))
              (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24])
                  (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 24])))
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32]))))))).2 := by
    intro s0 t w ⟨hc, hm, heff0, ht_d, ht_n, iw, ht_i, hiw_le, hdprev⟩ hcond hw hnone
    have hnl := eval_notLower_true t n0 iw 32 w ht_n ht_i hcond hw
    obtain ⟨hik_eq, hik_le⟩ := hnw_step iw 32 hiw_le (by decide) hnl
    have h32_nat : (32 : BitVec 64).toNat = 32 := rfl
    rw [h32_nat] at hik_eq hik_le
    let t0 := decClockHOLFinite t
    have hm0 : t0.memaddrs = ordinaryDomain := hm
    rcases hr : evaluateHOLFiniteState t0 _ with ⟨r_all, post_b⟩
    rw [hr] at hnone; dsimp only at hnone; subst hnone
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs0 : evaluateHOLFiniteState t0 _ with ⟨r0, m1⟩
    rw [hs0] at hr; cases r0 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he0, hl0, hsb0⟩ := memcpy_store_word_step (s := t0) (iw := iw) (off := 0) hm0 hfit hin_rl (by omega) hs0
      (fun a ha => by
        rw [eval_add2_locals t0 _ _ dst0 iw a ht_d ht_i ha, BitVec.toNat_add_of_lt (by omega)]; omega)
    have hdst_sb := hdom_first iw hdprev hsb0
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs8 : evaluateHOLFiniteState m1 _ with ⟨r8, m2⟩
    rw [hs8] at hr; cases r8 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he8, hl8, _⟩ := memcpy_store_word_step (s := m1) (iw := iw) (off := 8) (he0.memaddrs.trans hm0) hfit hin_rl (by omega) hs8
      (fun a ha => by
        rw [eval_add3_locals m1 _ _ dst0 iw 8 a (hl0 ▸ ht_d) (hl0 ▸ ht_i) ha]
        rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_add_of_lt (by omega)]; change _ + 8 < _; omega),
            BitVec.toNat_add_of_lt (by omega)]; rfl)
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs16 : evaluateHOLFiniteState m2 _ with ⟨r16, m3⟩
    rw [hs16] at hr; cases r16 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he16, hl16, _⟩ := memcpy_store_word_step (s := m2) (iw := iw) (off := 16) (he8.memaddrs.trans (he0.memaddrs.trans hm0)) hfit hin_rl (by omega) hs16
      (fun a ha => by
        rw [eval_add3_locals m2 _ _ dst0 iw 16 a (hl8 ▸ hl0 ▸ ht_d) (hl8 ▸ hl0 ▸ ht_i) ha]
        rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_add_of_lt (by omega)]; change _ + 16 < _; omega),
            BitVec.toNat_add_of_lt (by omega)]; rfl)
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs24 : evaluateHOLFiniteState m3 _ with ⟨r24, m4⟩
    rw [hs24] at hr; cases r24 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he24, hl24, _⟩ := memcpy_store_word_step (s := m3) (iw := iw) (off := 24) (he16.memaddrs.trans (he8.memaddrs.trans (he0.memaddrs.trans hm0))) hfit hin_rl (by omega) hs24
      (fun a ha => by
        rw [eval_add3_locals m3 _ _ dst0 iw 24 a (hl16 ▸ hl8 ▸ hl0 ▸ ht_d) (hl16 ▸ hl8 ▸ hl0 ▸ ht_i) ha]
        rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_add_of_lt (by omega)]; change _ + 24 < _; omega),
            BitVec.toNat_add_of_lt (by omega)]; rfl)
    obtain ⟨he_asg, hi_post, hother_post⟩ := assign_i_add_step (Rl := Rl) (hl24 ▸ hl16 ▸ hl8 ▸ hl0 ▸ ht_i) hr
    have heff_all : ByteRegionEffect s0 post_b Rl :=
      ((((heff0.with_locals_clock t.locals (t.clock - 1)).trans he0).trans he8).trans he16).trans (he24.trans he_asg)
    refine ⟨heff_all.code.trans (heff0.code.symm.trans hc),
      heff_all.memaddrs.trans (heff0.memaddrs.symm.trans hm),
      heff_all, ?_, ?_, iw + 32, hi_post, by rw [hik_eq]; omega, fun _ => hdst_sb⟩
    · rw [hother_post _ (by decide), hl24, hl16, hl8, hl0]; exact ht_d
    · rw [hother_post _ (by decide), hl24, hl16, hl8, hl0]; exact ht_n
  have hstep2 : ∀ (s0 t : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      MemcpyEffInv dst0 n0 Rl s0 t →
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .notLower (.var .local (ofString "n"))
          (.op .add [.var .local (ofString "i"), .const 8])) = some (.val (.word w)) →
      w ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite t)
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
            (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))).1 = none →
      MemcpyEffInv dst0 n0 Rl s0 (evaluateHOLFiniteState (decClockHOLFinite t)
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
            (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))).2 := by
    intro s0 t w ⟨hc, hm, heff0, ht_d, ht_n, iw, ht_i, hiw_le, hdprev⟩ hcond hw hnone
    have hnl := eval_notLower_true t n0 iw 8 w ht_n ht_i hcond hw
    obtain ⟨hik_eq, hik_le⟩ := hnw_step iw 8 hiw_le (by decide) hnl
    have h8_nat : (8 : BitVec 64).toNat = 8 := rfl
    rw [h8_nat] at hik_eq hik_le
    let t0 := decClockHOLFinite t
    have hm0 : t0.memaddrs = ordinaryDomain := hm
    rcases hr : evaluateHOLFiniteState t0 _ with ⟨r_all, post_b⟩
    rw [hr] at hnone; dsimp only at hnone; subst hnone
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs0 : evaluateHOLFiniteState t0 _ with ⟨r0, m1⟩
    rw [hs0] at hr; cases r0 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he0, hl0, hsb0⟩ := memcpy_store_word_step (s := t0) (iw := iw) (off := 0) hm0 hfit hin_rl (by omega) hs0
      (fun a ha => by
        rw [eval_add2_locals t0 _ _ dst0 iw a ht_d ht_i ha, BitVec.toNat_add_of_lt (by omega)]; omega)
    have hdst_sb := hdom_first iw hdprev hsb0
    obtain ⟨he_asg, hi_post, hother_post⟩ := assign_i_add_step (Rl := Rl) (hl0 ▸ ht_i) hr
    have heff_all : ByteRegionEffect s0 post_b Rl :=
      ((heff0.with_locals_clock t.locals (t.clock - 1)).trans he0).trans he_asg
    refine ⟨heff_all.code.trans (heff0.code.symm.trans hc),
      heff_all.memaddrs.trans (heff0.memaddrs.symm.trans hm),
      heff_all, ?_, ?_, iw + 8, hi_post, by rw [hik_eq]; omega, fun _ => hdst_sb⟩
    · rw [hother_post _ (by decide), hl0]; exact ht_d
    · rw [hother_post _ (by decide), hl0]; exact ht_n
  have hstep3 : ∀ (s0 t : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      MemcpyEffInv dst0 n0 Rl s0 t →
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .notLower (.var .local (ofString "n"))
          (.op .add [.var .local (ofString "i"), .const 8])) = some (.val (.word w)) →
      w ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite t)
        (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
            (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
          (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 1])
              (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 1])))
            (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 2])
                (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 2])))
              (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 3])
                  (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 3])))
                (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 4])
                    (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 4])))
                  (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 5])
                      (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 5])))
                    (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 6])
                        (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 6])))
                      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 7])
                          (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 7])))
                        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8]))))))))))).1 = none →
      MemcpyEffInv dst0 n0 Rl s0 (evaluateHOLFiniteState (decClockHOLFinite t)
        (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
            (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
          (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 1])
              (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 1])))
            (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 2])
                (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 2])))
              (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 3])
                  (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 3])))
                (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 4])
                    (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 4])))
                  (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 5])
                      (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 5])))
                    (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 6])
                        (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 6])))
                      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 7])
                          (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 7])))
                        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8]))))))))))).2 := by
    intro s0 t w ⟨hc, hm, heff0, ht_d, ht_n, iw, ht_i, hiw_le, hdprev⟩ hcond hw hnone
    have hnl := eval_notLower_true t n0 iw 8 w ht_n ht_i hcond hw
    obtain ⟨hik_eq, hik_le⟩ := hnw_step iw 8 hiw_le (by decide) hnl
    have h8_nat : (8 : BitVec 64).toNat = 8 := rfl
    rw [h8_nat] at hik_eq hik_le
    let t0 := decClockHOLFinite t
    have hm0 : t0.memaddrs = ordinaryDomain := hm
    rcases hr : evaluateHOLFiniteState t0 _ with ⟨r_all, post_b⟩
    rw [hr] at hnone; dsimp only at hnone; subst hnone
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs0 : evaluateHOLFiniteState t0 _ with ⟨r0, m1⟩
    rw [hs0] at hr; cases r0 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he0, hl0, hsb0⟩ := memcpy_storeByte_step (s := t0) (iw := iw) (off := 0) hm0 hfit hin_rl (by omega) hs0
      (fun a ha => by rw [eval_add2_locals t0 _ _ dst0 iw a ht_d ht_i ha, BitVec.toNat_add_of_lt (by omega)]; omega)
    have hdst_sb := hdom_first iw hdprev hsb0
    have hd1 : m1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := hl0 ▸ ht_d
    have hi1 : m1.locals.lookup (ofString "i") = some (.val (.word iw)) := hl0 ▸ ht_i
    have hm1 : m1.memaddrs = ordinaryDomain := he0.memaddrs.trans hm0
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs1 : evaluateHOLFiniteState m1 _ with ⟨r1, m2⟩
    rw [hs1] at hr; cases r1 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he1, hl1, _⟩ := memcpy_storeByte_step (s := m1) (iw := iw) (off := 1) hm1 hfit hin_rl (by omega) hs1
      (fun a ha => by
        rw [eval_add3_locals m1 _ _ dst0 iw 1 a hd1 hi1 ha,
            BitVec.toNat_add_of_lt (by rw [BitVec.toNat_add_of_lt (by omega)]; change _ + 1 < _; omega),
            BitVec.toNat_add_of_lt (by omega)]; rfl)
    have hd2 : m2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := hl1 ▸ hd1
    have hi2 : m2.locals.lookup (ofString "i") = some (.val (.word iw)) := hl1 ▸ hi1
    have hm2 : m2.memaddrs = ordinaryDomain := he1.memaddrs.trans hm1
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs2 : evaluateHOLFiniteState m2 _ with ⟨r2, m3⟩
    rw [hs2] at hr; cases r2 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he2, hl2, _⟩ := memcpy_storeByte_step (s := m2) (iw := iw) (off := 2) hm2 hfit hin_rl (by omega) hs2
      (fun a ha => by
        rw [eval_add3_locals m2 _ _ dst0 iw 2 a hd2 hi2 ha,
            BitVec.toNat_add_of_lt (by rw [BitVec.toNat_add_of_lt (by omega)]; change _ + 2 < _; omega),
            BitVec.toNat_add_of_lt (by omega)]; rfl)
    have hd3 : m3.locals.lookup (ofString "dst") = some (.val (.word dst0)) := hl2 ▸ hd2
    have hi3 : m3.locals.lookup (ofString "i") = some (.val (.word iw)) := hl2 ▸ hi2
    have hm3 : m3.memaddrs = ordinaryDomain := he2.memaddrs.trans hm2
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs3 : evaluateHOLFiniteState m3 _ with ⟨r3, m4⟩
    rw [hs3] at hr; cases r3 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he3, hl3, _⟩ := memcpy_storeByte_step (s := m3) (iw := iw) (off := 3) hm3 hfit hin_rl (by omega) hs3
      (fun a ha => by
        rw [eval_add3_locals m3 _ _ dst0 iw 3 a hd3 hi3 ha,
            BitVec.toNat_add_of_lt (by rw [BitVec.toNat_add_of_lt (by omega)]; change _ + 3 < _; omega),
            BitVec.toNat_add_of_lt (by omega)]; rfl)
    have hd4 : m4.locals.lookup (ofString "dst") = some (.val (.word dst0)) := hl3 ▸ hd3
    have hi4 : m4.locals.lookup (ofString "i") = some (.val (.word iw)) := hl3 ▸ hi3
    have hm4 : m4.memaddrs = ordinaryDomain := he3.memaddrs.trans hm3
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs4 : evaluateHOLFiniteState m4 _ with ⟨r4, m5⟩
    rw [hs4] at hr; cases r4 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he4, hl4, _⟩ := memcpy_storeByte_step (s := m4) (iw := iw) (off := 4) hm4 hfit hin_rl (by omega) hs4
      (fun a ha => by
        rw [eval_add3_locals m4 _ _ dst0 iw 4 a hd4 hi4 ha,
            BitVec.toNat_add_of_lt (by rw [BitVec.toNat_add_of_lt (by omega)]; change _ + 4 < _; omega),
            BitVec.toNat_add_of_lt (by omega)]; rfl)
    have hd5 : m5.locals.lookup (ofString "dst") = some (.val (.word dst0)) := hl4 ▸ hd4
    have hi5 : m5.locals.lookup (ofString "i") = some (.val (.word iw)) := hl4 ▸ hi4
    have hm5 : m5.memaddrs = ordinaryDomain := he4.memaddrs.trans hm4
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs5 : evaluateHOLFiniteState m5 _ with ⟨r5, m6⟩
    rw [hs5] at hr; cases r5 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he5, hl5, _⟩ := memcpy_storeByte_step (s := m5) (iw := iw) (off := 5) hm5 hfit hin_rl (by omega) hs5
      (fun a ha => by
        rw [eval_add3_locals m5 _ _ dst0 iw 5 a hd5 hi5 ha,
            BitVec.toNat_add_of_lt (by rw [BitVec.toNat_add_of_lt (by omega)]; change _ + 5 < _; omega),
            BitVec.toNat_add_of_lt (by omega)]; rfl)
    have hd6 : m6.locals.lookup (ofString "dst") = some (.val (.word dst0)) := hl5 ▸ hd5
    have hi6 : m6.locals.lookup (ofString "i") = some (.val (.word iw)) := hl5 ▸ hi5
    have hm6 : m6.memaddrs = ordinaryDomain := he5.memaddrs.trans hm5
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs6 : evaluateHOLFiniteState m6 _ with ⟨r6, m7⟩
    rw [hs6] at hr; cases r6 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he6, hl6, _⟩ := memcpy_storeByte_step (s := m6) (iw := iw) (off := 6) hm6 hfit hin_rl (by omega) hs6
      (fun a ha => by
        rw [eval_add3_locals m6 _ _ dst0 iw 6 a hd6 hi6 ha,
            BitVec.toNat_add_of_lt (by rw [BitVec.toNat_add_of_lt (by omega)]; change _ + 6 < _; omega),
            BitVec.toNat_add_of_lt (by omega)]; rfl)
    have hd7 : m7.locals.lookup (ofString "dst") = some (.val (.word dst0)) := hl6 ▸ hd6
    have hi7 : m7.locals.lookup (ofString "i") = some (.val (.word iw)) := hl6 ▸ hi6
    have hm7 : m7.memaddrs = ordinaryDomain := he6.memaddrs.trans hm6
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs7 : evaluateHOLFiniteState m7 _ with ⟨r7, m8⟩
    rw [hs7] at hr; cases r7 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he7, hl7, _⟩ := memcpy_storeByte_step (s := m7) (iw := iw) (off := 7) hm7 hfit hin_rl (by omega) hs7
      (fun a ha => by
        rw [eval_add3_locals m7 _ _ dst0 iw 7 a hd7 hi7 ha,
            BitVec.toNat_add_of_lt (by rw [BitVec.toNat_add_of_lt (by omega)]; change _ + 7 < _; omega),
            BitVec.toNat_add_of_lt (by omega)]; rfl)
    obtain ⟨he_asg, hi_post, hother_post⟩ := assign_i_add_step (Rl := Rl) (hl7 ▸ hi7) hr
    have heff_all : ByteRegionEffect s0 post_b Rl :=
      ((((((((heff0.with_locals_clock t.locals (t.clock - 1)).trans he0).trans he1).trans he2).trans
        he3).trans he4).trans he5).trans he6).trans (he7.trans he_asg)
    refine ⟨heff_all.code.trans (heff0.code.symm.trans hc),
      heff_all.memaddrs.trans (heff0.memaddrs.symm.trans hm),
      heff_all, ?_, ?_, iw + 8, hi_post, by rw [hik_eq]; omega, fun _ => hdst_sb⟩
    · rw [hother_post _ (by decide), hl7]; exact hd7
    · rw [hother_post _ (by decide), hl7, hl6, hl5, hl4, hl3, hl2, hl1, hl0]; exact ht_n
  have hstep4 : ∀ (s0 t : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      MemcpyEffInv dst0 n0 Rl s0 t →
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word w)) →
      w ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite t)
        (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
            (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))).1 = none →
      MemcpyEffInv dst0 n0 Rl s0 (evaluateHOLFiniteState (decClockHOLFinite t)
        (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
            (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))).2 := by
    intro s0 t w ⟨hc, hm, heff0, ht_d, ht_n, iw, ht_i, _, hdprev⟩ hcond hw hnone
    have hlt := eval_lower_true t n0 iw w ht_n ht_i hcond hw
    rw [BitVec.lt_def] at hlt
    let t0 := decClockHOLFinite t
    have hm0 : t0.memaddrs = ordinaryDomain := hm
    rcases hr : evaluateHOLFiniteState t0 _ with ⟨r_all, post_b⟩
    rw [hr] at hnone; dsimp only at hnone; subst hnone
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs0 : evaluateHOLFiniteState t0 _ with ⟨r0, m1⟩
    rw [hs0] at hr; cases r0 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he0, hl0, hsb0⟩ := memcpy_storeByte_step (s := t0) (iw := iw) (off := 0) hm0 hfit hin_rl (by omega) hs0
      (fun a ha => by rw [eval_add2_locals t0 _ _ dst0 iw a ht_d ht_i ha, BitVec.toNat_add_of_lt (by omega)]; omega)
    have hdst_sb := hdom_first iw hdprev hsb0
    obtain ⟨he_asg, hi_post, hother_post⟩ := assign_i_add_step (Rl := Rl) (hl0 ▸ ht_i) hr
    have heff_all : ByteRegionEffect s0 post_b Rl :=
      ((heff0.with_locals_clock t.locals (t.clock - 1)).trans he0).trans he_asg
    have hi1_eq : (iw + 1).toNat = iw.toNat + 1 := BitVec.toNat_add_of_lt (by change iw.toNat + 1 < 2 ^ 64; omega)
    refine ⟨heff_all.code.trans (heff0.code.symm.trans hc),
      heff_all.memaddrs.trans (heff0.memaddrs.symm.trans hm),
      heff_all, ?_, ?_, iw + 1, hi_post, by rw [hi1_eq]; omega, fun _ => hdst_sb⟩
    · rw [hother_post _ (by decide), hl0]; exact ht_d
    · rw [hother_post _ (by decide), hl0]; exact ht_n
  rw [evaluateHOLFiniteState_seq_line780]
  set iteProg : ProgHOL 64 := .ite _ _ .skip
  have hite_nrr : noReturnOrRaise iteProg = true := rfl
  rcases hite : evaluateHOLFiniteState s1 iteProg with ⟨r_ite, s2⟩
  cases r_ite with
  | some x =>
    intro hres
    have hnr := evaluate_noReturnOrRaise iteProg hite_nrr s1
    rw [hite] at hnr; exact absurd hres hnr
  | none =>
    dsimp only
    have hinv2 : MemcpyEffInv dst0 n0 Rl s s2 := by
      dsimp only [iteProg] at hite
      rw [evaluateHOLFiniteState_ite] at hite
      split at hite
      · split at hite
        · rw [evaluateHOLFiniteState_skip] at hite
          injection hite with _ hs2; rw [← hs2]; exact hinv1
        · rw [evaluateHOLFiniteState_seq_line780] at hite
          rcases hw1 : evaluateHOLFiniteState s1 _ with ⟨rw1, m1⟩
          rw [hw1] at hite
          cases rw1 with
          | some _ => simp at hite
          | none =>
            dsimp only at hite
            have hm1 := (while_preserve_eff _ _ rfl rfl hstep1 s1.clock s s1 m1 le_rfl hinv1 hw1).1
            exact (while_preserve_eff _ _ rfl rfl hstep2 m1.clock s m1 s2 le_rfl hm1 hite).1
      · simp at hite
    rw [evaluateHOLFiniteState_seq_line780]
    set loop3 : ProgHOL 64 := .while _ _
    have hl3_nrr : noReturnOrRaise loop3 = true := rfl
    rcases hw3 : evaluateHOLFiniteState s2 loop3 with ⟨rw3, s3⟩
    cases rw3 with
    | some _ =>
      intro hres
      have hnr := evaluate_noReturnOrRaise loop3 hl3_nrr s2
      rw [hw3] at hnr; exact absurd hres hnr
    | none =>
      dsimp only
      have hinv3 : MemcpyEffInv dst0 n0 Rl s s3 :=
        (while_preserve_eff _ _ rfl rfl hstep3 s2.clock s s2 s3 le_rfl hinv2 hw3).1
      rw [evaluateHOLFiniteState_seq_line780]
      set loop4 : ProgHOL 64 := .while _ _
      have hl4_nrr : noReturnOrRaise loop4 = true := rfl
      rcases hw4 : evaluateHOLFiniteState s3 loop4 with ⟨rw4, s4⟩
      cases rw4 with
      | some _ =>
        intro hres
        have hnr := evaluate_noReturnOrRaise loop4 hl4_nrr s3
        rw [hw4] at hnr; exact absurd hres hnr
      | none =>
        dsimp only
        obtain ⟨⟨_, _, heff4, _, hn4, iw, hi4, _, hdom4⟩, hcond4⟩ :=
          while_preserve_eff _ _ rfl rfl hstep4 s3.clock s s3 s4 le_rfl hinv3 hw4
        have hge4 := eval_lower_false s4 n0 iw hn4 hi4 hcond4
        have hdst_sb : sourceBase ≤ dst0.toNat := hdom4 (by omega)
        rw [evaluateHOLFiniteState_return]
        have hev0 : @evalHOLExact 64 F _ s4.toExact
            (fun a => Classical.propDecidable (s4.memaddrs a)) (.const (BitVec.ofNat 64 0)) =
            some (.val (.word 0)) := rfl
        have hsz0 : sizeOfShapeWithContextHOL s4.structs (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
          simp [shapeOfHOLExact]
        rw [hev0]; dsimp only; rw [if_pos hsz0]; dsimp only
        intro _
        exact ⟨rfl, hdst_sb, heff4.with_locals_clock _ _⟩

private theorem eval_sk_make_body {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hsk_fit : globN s "sk_buf" + 52 ≤ 2 ^ 64)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make)).1) :
    ∃ skw : BitVec 64,
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make)).1 =
        some (.returned (.val (.word skw))) ∧
      globN s "sk_buf" ≠ 0 ∧
      ByteRegionEffect s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make)).2
        [(globN s "sk_buf", 52)] := by
  revert hres
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_sk_make,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call]
  rcases hargs1 : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .global (ofString "sk_buf"), .var .local (ofString "addr"),
       .const (BitVec.ofNat 64 20)] with _ | vals1
  · intro h; exact absurd h not_resumes_error
  · dsimp only
    rcases hl1 : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vals1 with _ | ⟨body1, callee1, rs1⟩
    · intro h; exact absurd h not_resumes_error
    · dsimp only
      by_cases hclk1 : s.clock = 0
      · simp [hclk1]; intro h; exact absurd h not_resumes_timeOut
      · rw [if_neg hclk1]
        have hsame1 := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "memcpy")
          _ _ _ _ _ vals1 callee1 (by rw [hcode]; exact lookup_memcpy) hl1
        subst hsame1
        have hvals1_info : ∃ skw addrw : BitVec 64,
            s.globals.lookup (ofString "sk_buf") = some (.val (.word skw)) ∧
            skw.toNat = globN s "sk_buf" ∧
            callee1.lookup (ofString "dst") = some (.val (.word skw)) ∧
            callee1.lookup (ofString "src") = some (.val (.word addrw)) ∧
            callee1.lookup (ofString "n") = some (.val (.word 20)) := by
          rw [evalListHOLFinite_eq_toExact] at hargs1
          simp only [evalListHOLExact, evalHOLExact] at hargs1
          rcases hsk : s.globals.lookup (ofString "sk_buf") with _ | vsk
          · simp [hsk] at hargs1
          · rcases had : s.locals.lookup (ofString "addr") with _ | vad
            · simp [hsk, had] at hargs1
            · simp only [hsk, had, Option.some.injEq] at hargs1
              subst hargs1
              unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl1
              split at hl1
              · cases hl1
              · rename_i eb el es hraw
                have heq := Option.some.inj hl1
                rcases Prod.mk.inj heq with ⟨_, hrest⟩
                rcases Prod.mk.inj hrest with ⟨rfl, _⟩
                unfold lookupCodeHOLExact at hraw
                rw [hcode, lookup_memcpy] at hraw
                dsimp only at hraw
                split at hraw
                · rename_i hcond
                  have rawEq := Option.some.inj hraw
                  rcases Prod.mk.inj rawEq with ⟨_, hrest2⟩
                  rcases Prod.mk.inj hrest2 with ⟨hloc, _⟩
                  subst hloc
                  rcases vsk with ⟨⟨skw⟩⟩ | _ | _
                  · rcases vad with ⟨⟨addrw⟩⟩ | _ | _
                    · refine ⟨skw, addrw, rfl, by simp [globN, hsk], ?_, ?_, ?_⟩
                      · have hnd1 : ofString "n" ≠ ofString "dst" := by decide
                        have hnd2 : ofString "src" ≠ ofString "dst" := by decide
                        simp [List.zip, List.foldl, HolFiniteMapExact.lookup_update, FUPDATE,
                          hnd1, hnd2, Ne.symm hnd1, Ne.symm hnd2]
                      · have hns : ofString "n" ≠ ofString "src" := by decide
                        simp [List.zip, List.foldl, HolFiniteMapExact.lookup_update, FUPDATE,
                          hns, Ne.symm hns]
                      · simp [List.zip, List.foldl, HolFiniteMapExact.lookup_update, FUPDATE]
                    · simp [shapeOfHOLExact, shapeEqHOL] at hcond
                    · simp [shapeOfHOLExact, shapeEqHOL] at hcond
                  · simp [shapeOfHOLExact, shapeEqHOL] at hcond
                  · simp [shapeOfHOLExact, shapeEqHOL] at hcond
                · cases hraw
        obtain ⟨skw, addrw, hsk_g, hsk_nat, hc1_d, hc1_s, hc1_n⟩ := hvals1_info
        let ent1 := callEntryStateHOLFinite s callee1
        rcases hrun1 : evaluateHOLFiniteState (callEntryStateHOLFinite s callee1)
            (sourceFnBody Guest.Software.guestFn_memcpy) with ⟨res1, st1⟩
        have hrun1_ent : evaluateHOLFiniteState ent1 (sourceFnBody Guest.Software.guestFn_memcpy) = (res1, st1) := hrun1
        cases res1 with
        | none => intro h; exact absurd h not_resumes_error
        | some r1 =>
          cases r1 with
          | timeOut => intro h; exact absurd h not_resumes_timeOut
          | «break» | «continue» | error => intro h; exact absurd h not_resumes_error
          | finalFfi _ => intro h; rcases h with ⟨_, hc⟩ | ⟨_, _, hc, _⟩ <;> simp at hc
          | exception e1 v1 =>
            intro hres
            have h20 : (20 : BitVec 64).toNat = 20 := rfl
            have hm1 := eval_memcpy_bounded ent1 skw addrw 20 [(skw.toNat, 20)]
              hcode hma hc1_d hc1_s hc1_n (by rw [h20]; omega) (by rw [h20]; omega)
              (by rw [h20, hsk_nat]; omega) (by simp [h20])
              (by rw [hrun1_ent]; rcases hres with ⟨_, hc⟩ | ⟨e', v', hc, hnt⟩
                  · simp at hc
                  · injection hc with hc; injection hc with he1 _; subst he1; exact Or.inr ⟨_, _, rfl, hnt⟩)
            rw [hrun1_ent] at hm1; simp at hm1
          | returned rv1 =>
            dsimp only
            have h20 : (20 : BitVec 64).toNat = 20 := rfl
            obtain ⟨hrv1_eq, hsk_sb, heff1_sub⟩ := eval_memcpy_bounded ent1 skw addrw 20 [(skw.toNat, 20)]
              hcode hma hc1_d hc1_s hc1_n (by rw [h20]; omega) (by rw [h20]; omega)
              (by rw [h20, hsk_nat]; omega) (by simp [h20])
              (by rw [hrun1_ent]; exact Or.inl ⟨rv1, rfl⟩)
            rw [hrun1_ent] at hrv1_eq heff1_sub
            dsimp only at hrv1_eq heff1_sub
            injection hrv1_eq with hrv1_eq; injection hrv1_eq with hrv1_eq
            subst hrv1_eq
            have hsh_rs1 : rs1 = .one :=
              lookupCodeHOLFinite_installed_return s (ofString "memcpy") _ _ _ .one rs1 vals1 callee1
                (by rw [hcode]; exact lookup_memcpy) hl1
            subst hsh_rs1
            have hsh1 : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
              simp [shapeOfHOLExact, shapeEqHOL]
            rw [if_pos hsh1]
            dsimp only
            have hsk_nz : globN s "sk_buf" ≠ 0 := by rw [sourceBase_val] at hsk_sb; omega
            have heff1 : ByteRegionEffect s { st1 with locals := s.locals } [(globN s "sk_buf", 52)] := by
              have hmono : ByteRegionEffect ent1 st1 [(globN s "sk_buf", 52)] :=
                heff1_sub.mono (fun i hi => by
                  simp at hi; subst hi
                  exact Or.inr ⟨(globN s "sk_buf", 52), by simp, by dsimp only; omega, by dsimp only; omega⟩)
              exact (((ByteRegionEffect.refl s _).with_locals_clock _ _).trans hmono).with_locals_clock _ _
            set m1 : PanSemStateFiniteExact 64 F := { st1 with locals := s.locals }
            rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call]
            rcases hargs2 : evalListHOLFinite m1 (h := fun a => Classical.propDecidable (m1.memaddrs a))
                [.op .add [.var .global (ofString "sk_buf"), .const (BitVec.ofNat 64 20)],
                 .var .local (ofString "key"), .const (BitVec.ofNat 64 32)] with _ | vals2
            · intro h; exact absurd h not_resumes_error
            · dsimp only
              rcases hl2 : lookupCodeHOLFinite m1.code.lookup (ofString "memcpy") vals2 with _ | ⟨body2, callee2, rs2⟩
              · intro h; exact absurd h not_resumes_error
              · dsimp only
                by_cases hclk2 : m1.clock = 0
                · simp [hclk2]; intro h; exact absurd h not_resumes_timeOut
                · rw [if_neg hclk2]
                  have hm1_code : m1.code = originalRuntimeCode := heff1.code.trans hcode
                  have hm1_ma : m1.memaddrs = ordinaryDomain := heff1.memaddrs.trans hma
                  have hsame2 := lookupCodeHOLFinite_installed_body m1.code.lookup (ofString "memcpy")
                    _ _ _ _ _ vals2 callee2 (by rw [hm1_code]; exact lookup_memcpy) hl2
                  subst hsame2
                  have hm1_sk : m1.globals.lookup (ofString "sk_buf") = some (.val (.word skw)) := by
                    rw [heff1.globals]; exact hsk_g
                  have hvals2_info : ∃ keyw : BitVec 64,
                      callee2.lookup (ofString "dst") = some (.val (.word (skw + 20))) ∧
                      callee2.lookup (ofString "src") = some (.val (.word keyw)) ∧
                      callee2.lookup (ofString "n") = some (.val (.word 32)) ∧
                      rs2 = .one := by
                    rw [evalListHOLFinite_eq_toExact] at hargs2
                    simp only [evalListHOLExact, evalHOLExact, hm1_sk, valueIsWord, valueWord,
                      wordOpHOL, wordOp, List.all, List.map, Bool.and_self, ↓reduceIte,
                      List.foldr, BitVec.add_zero] at hargs2
                    rcases hky : m1.locals.lookup (ofString "key") with _ | vky
                    · simp [hky] at hargs2
                    · simp only [hky, Option.map, BitVec.add_zero, Option.some.injEq] at hargs2
                      subst hargs2
                      unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl2
                      split at hl2
                      · cases hl2
                      · rename_i eb el es hraw
                        have heq := Option.some.inj hl2
                        rcases Prod.mk.inj heq with ⟨_, hrest⟩
                        rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
                        unfold lookupCodeHOLExact at hraw
                        rw [hm1_code, lookup_memcpy] at hraw
                        dsimp only at hraw
                        split at hraw
                        · rename_i hcond
                          have rawEq := Option.some.inj hraw
                          rcases Prod.mk.inj rawEq with ⟨_, hrest2⟩
                          rcases Prod.mk.inj hrest2 with ⟨hloc, rfl⟩
                          subst hloc
                          rcases vky with ⟨⟨keyw⟩⟩ | _ | _
                          · refine ⟨keyw, ?_, ?_, ?_, rfl⟩
                            · have hnd1 : ofString "n" ≠ ofString "dst" := by decide
                              have hnd2 : ofString "src" ≠ ofString "dst" := by decide
                              simp [List.zip, List.foldl, HolFiniteMapExact.lookup_update, FUPDATE,
                                hnd1, hnd2, Ne.symm hnd1, Ne.symm hnd2]
                            · have hns : ofString "n" ≠ ofString "src" := by decide
                              simp [List.zip, List.foldl, HolFiniteMapExact.lookup_update, FUPDATE,
                                hns, Ne.symm hns]
                            · simp [List.zip, List.foldl, HolFiniteMapExact.lookup_update, FUPDATE]
                          · simp [shapeOfHOLExact, shapeEqHOL] at hcond
                          · simp [shapeOfHOLExact, shapeEqHOL] at hcond
                        · cases hraw
                  obtain ⟨keyw, hc2_d, hc2_s, hc2_n, rfl⟩ := hvals2_info
                  let ent2 := callEntryStateHOLFinite m1 callee2
                  rcases hrun2 : evaluateHOLFiniteState (callEntryStateHOLFinite m1 callee2)
                      (sourceFnBody Guest.Software.guestFn_memcpy) with ⟨res2, st2⟩
                  have hrun2_ent : evaluateHOLFiniteState ent2 (sourceFnBody Guest.Software.guestFn_memcpy) = (res2, st2) := hrun2
                  have h32 : (32 : BitVec 64).toNat = 32 := rfl
                  have hsk20 : (skw + 20).toNat = globN s "sk_buf" + 20 := by
                    rw [BitVec.toNat_add_of_lt (by change skw.toNat + 20 < 2 ^ 64; omega), hsk_nat, h20]
                  cases res2 with
                  | none => intro h; exact absurd h not_resumes_error
                  | some r2 =>
                    cases r2 with
                    | timeOut => intro h; exact absurd h not_resumes_timeOut
                    | «break» | «continue» | error => intro h; exact absurd h not_resumes_error
                    | finalFfi _ => intro h; rcases h with ⟨_, hc⟩ | ⟨_, _, hc, _⟩ <;> simp at hc
                    | exception e2 v2 =>
                      intro hres
                      have hm2 := eval_memcpy_bounded ent2 (skw + 20) keyw 32 [((skw + 20).toNat, 32)]
                        hm1_code hm1_ma hc2_d hc2_s hc2_n (by rw [h32]; omega) (by rw [h32]; omega)
                        (by rw [h32, hsk20]; omega) (by simp [h32])
                        (by rw [hrun2_ent]; rcases hres with ⟨_, hc⟩ | ⟨e', v', hc, hnt⟩
                            · simp at hc
                            · injection hc with hc; injection hc with he2 _; subst he2; exact Or.inr ⟨_, _, rfl, hnt⟩)
                      rw [hrun2_ent] at hm2; simp at hm2
                    | returned rv2 =>
                      dsimp only
                      obtain ⟨hrv2_eq, _, heff2_sub⟩ := eval_memcpy_bounded ent2 (skw + 20) keyw 32
                        [((skw + 20).toNat, 32)] hm1_code hm1_ma hc2_d hc2_s hc2_n
                        (by rw [h32]; omega) (by rw [h32]; omega)
                        (by rw [h32, hsk20]; omega) (by simp [h32])
                        (by rw [hrun2_ent]; exact Or.inl ⟨rv2, rfl⟩)
                      rw [hrun2_ent] at hrv2_eq heff2_sub
                      dsimp only at hrv2_eq heff2_sub
                      injection hrv2_eq with hrv2_eq; injection hrv2_eq with hrv2_eq
                      subst hrv2_eq
                      have hsh2 : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
                        simp [shapeOfHOLExact, shapeEqHOL]
                      rw [if_pos hsh2]
                      dsimp only
                      have heff2 : ByteRegionEffect m1 { st2 with locals := m1.locals } [(globN s "sk_buf", 52)] := by
                        have hmono : ByteRegionEffect ent2 st2 [(globN s "sk_buf", 52)] :=
                          heff2_sub.mono (fun i hi => by
                            simp at hi; subst hi
                            exact Or.inr ⟨(globN s "sk_buf", 52), by simp, by dsimp only; omega, by dsimp only; omega⟩)
                        exact (((ByteRegionEffect.refl m1 _).with_locals_clock _ _).trans hmono).with_locals_clock _ _
                      set m2 : PanSemStateFiniteExact 64 F := { st2 with locals := m1.locals }
                      have hm2_sk : m2.globals.lookup (ofString "sk_buf") = some (.val (.word skw)) := by
                        rw [heff2.globals]; exact hm1_sk
                      rw [evaluateHOLFiniteState_return]
                      have hev_ret : @evalHOLExact 64 F _ m2.toExact
                          (fun a => Classical.propDecidable (m2.memaddrs a)) (.var .global (ofString "sk_buf")) =
                          some (.val (.word skw)) := by simp [evalHOLExact, hm2_sk]
                      have hsz_ret : sizeOfShapeWithContextHOL m2.structs
                          (shapeOfHOLExact (.val (.word skw) : ValueHOL 64)) ≤ 32 := by
                        simp [shapeOfHOLExact]
                      rw [hev_ret]; dsimp only; rw [if_pos hsz_ret]; dsimp only
                      intro _
                      exact ⟨skw, rfl, hsk_nz, (heff1.trans heff2).with_locals_clock _ _⟩

/-- `is_warm_storage_key` (AST line 16559): EVM step keeping `EvmInv`, globals, and `evmChain`. -/
theorem «ek_is_warm_storage_key» :
    EvmKeeps (EvmAvoids (fun s => [(globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)]))
    [] (ofString "is_warm_storage_key") := by
  refine ⟨_, _, _, lookup_is_warm_storage_key, ?_⟩
  intro F s hcode hAv _hlookup _hnt hres
  have hsk_fit : globN s "sk_buf" + 52 ≤ 2 ^ 64 := by
    by_cases hz : globN s "sk_buf" = 0
    · rw [hz]; decide
    · obtain ⟨hAs, S, hInvAt, _⟩ := hAv
      have hmem_fix : (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 64) ∈ fixedObjects s := by
        unfold fixedObjects
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_map.2 ⟨("sk_buf", 64), by decide, rfl⟩
      rw [if_neg hz] at hmem_fix
      rcases fixedObject_le_2pow64 hAs.2 hInvAt.1.2.2.1 hmem_fix with h0 | hbnd
      · dsimp only at h0; omega
      · dsimp only at hbnd; omega
  revert hres
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_is_warm_storage_key,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "addr"), .var .local (ofString "key")] with _ | vals
  · intro h; exact absurd h not_resumes_error
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "sk_make") vals with _ | ⟨body_sk, callee_sk, rs_sk⟩
    · intro h; exact absurd h not_resumes_error
    · dsimp only
      by_cases hclk_sk : s.clock = 0
      · simp [hclk_sk]; intro h; exact absurd h not_resumes_timeOut
      · rw [if_neg hclk_sk]
        have hsame_sk := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "sk_make")
          _ _ _ _ _ vals callee_sk (by rw [hcode]; exact lookup_sk_make) hl
        subst hsame_sk
        let ent_sk := callEntryStateHOLFinite s callee_sk
        rcases hrun_sk : evaluateHOLFiniteState (callEntryStateHOLFinite s callee_sk)
            (sourceFnBody Guest.Software.guestFn_sk_make) with
          ⟨res_sk, st_sk⟩
        have hrun_sk_ent : evaluateHOLFiniteState ent_sk (sourceFnBody Guest.Software.guestFn_sk_make) =
            (res_sk, st_sk) := hrun_sk
        have hma : s.memaddrs = ordinaryDomain := hAv.1.1.memaddrs
        cases res_sk with
        | none => intro h; exact absurd h not_resumes_error
        | some r_sk =>
          cases r_sk with
          | timeOut => intro h; exact absurd h not_resumes_timeOut
          | «break» | «continue» | error => intro h; exact absurd h not_resumes_error
          | finalFfi _ => intro h; rcases h with ⟨_, hc⟩ | ⟨_, _, hc, _⟩ <;> simp at hc
          | exception e_sk v_sk =>
            intro hres
            obtain ⟨_, hret_eq, _, _⟩ := eval_sk_make_body ent_sk hcode hma hsk_fit
              (by rw [hrun_sk_ent]; rcases hres with ⟨_, hc⟩ | ⟨e', v', hc, hnt⟩
                  · simp at hc
                  · injection hc with hc; injection hc with he _; subst he; exact Or.inr ⟨_, _, rfl, hnt⟩)
            rw [hrun_sk_ent] at hret_eq; simp at hret_eq
          | returned rv_sk =>
            dsimp only
            obtain ⟨skw, hret_eq, hsk_nz_ent, heff_sk0⟩ := eval_sk_make_body ent_sk hcode hma hsk_fit
              (by rw [hrun_sk_ent]; exact Or.inl ⟨rv_sk, rfl⟩)
            have hsk_nz : globN s "sk_buf" ≠ 0 := hsk_nz_ent
            rw [hrun_sk_ent] at hret_eq heff_sk0
            dsimp only at hret_eq heff_sk0
            injection hret_eq with hret_eq; injection hret_eq with hret_eq
            subst hret_eq
            split
            · set s_after_sk := setVarHOLFinite (ofString "k") (.val (.word skw))
                { st_sk with locals := s.locals }
              have heff_sk : ByteRegionEffect s s_after_sk [(globN s "sk_buf", 52)] :=
                (((ByteRegionEffect.refl s _).with_locals_clock _ _).trans heff_sk0).with_locals_clock _ _
              have hs_after_code : s_after_sk.code = originalRuntimeCode := heff_sk.code.trans hcode
              set cont : ProgHOL 64 :=
                .decCall (ofString "h") .one (ofString "htab_has")
                  [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 176)]),
                   .var .local (ofString "k")]
                  (.return (.var .local (ofString "h")))
              have hcont_ro : readOnlyProg htabHasCallees cont = true := rfl
              have hloc_cont := evaluate_readOnlyProg htabHasCallees htabHasCallees_good
                cont hcont_ro s_after_sk hs_after_code
              rcases hrun_c : evaluateHOLFiniteState s_after_sk cont with ⟨res_c, post_c⟩
              rw [hrun_c] at hloc_cont
              dsimp only at hloc_cont ⊢
              intro _
              let newLocals := HolFiniteMapExact.resVarEq post_c.locals
                (ofString "k", s.locals.lookup (ofString "k"))
              have heff_total : ByteRegionEffect s { post_c with locals := newLocals }
                  [(globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)] := by
                rw [if_neg hsk_nz]
                have hpc : ByteRegionEffect s_after_sk post_c [(globN s "sk_buf", 52)] := by
                  unfold LocFrame at hloc_cont
                  rw [hloc_cont]
                  exact (ByteRegionEffect.refl s_after_sk _).with_locals_clock _ _
                exact (heff_sk.trans hpc).with_locals_clock _ _
              exact ByteRegionEffect.to_evmStep_avoids hAv heff_total
            · intro h; exact absurd h not_resumes_error

/-! ## 9. Additional `C08` contracts: `wk_sk_make`, `nz_htab_set`, `iz_node_invalidate`,
`dm_memcpy`, `dm_encode_withdrawal_rlp`, and `ro_*` -/

/-- `sk_make` (AST line 12923): relational world step with output region `sk_buf` (52 bytes). -/
theorem «wk_sk_make» :
    WorldKeeps WorldOK (fun s => [(globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
    [] stdKeep NoExtra (ofString "sk_make") := by
  refine ⟨_, _, _, lookup_sk_make, ?_⟩
  intro F s hcode hWOK _hlookup _hnt hres
  have hsk_fit : globN s "sk_buf" + 52 ≤ 2 ^ 64 := by
    by_cases hz : globN s "sk_buf" = 0
    · rw [hz]; decide
    · obtain ⟨hAs, S, hW⟩ := hWOK
      have hmem_fix : (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 64) ∈ fixedObjects s := by
        unfold fixedObjects
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_map.2 ⟨("sk_buf", 64), by decide, rfl⟩
      rw [if_neg hz] at hmem_fix
      rcases fixedObject_le_2pow64 hAs.2 hW.2.2.1 hmem_fix with h0 | hbnd
      · dsimp only at h0; omega
      · dsimp only at hbnd; omega
  obtain ⟨_, _, hsk_nz, heff⟩ := eval_sk_make_body s hcode hWOK.1.1.memaddrs hsk_fit hres
  have heff' : ByteRegionEffect s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make)).2
      [(globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)] := by
    rw [if_neg hsk_nz]; exact heff
  exact ByteRegionEffect.to_worldStep hWOK heff'

theorem lookup_htab_set :
    originalRuntimeCode.lookup (ofString "htab_set") =
      some ([(ofString "t", .one), (ofString "key", .one), (ofString "value", .one)],
        sourceFnBody Guest.Software.guestFn_htab_set, .one) :=
  lookup_of_guestAst_getElem 138 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_set) rfl

private theorem not_ordinaryDomain_zero : ¬ ordinaryDomain (0 : BitVec 64) := by
  rw [ordinaryDomain_iff]; simp

/-- `htab_set` (AST line 5149): resumes only on a nonzero table (`load(t + 0)` errors at `0`). -/
theorem «nz_htab_set» : ArgNonNull "t" (ofString "htab_set") := by
  refine ⟨_, _, _, lookup_htab_set, ?_⟩
  intro F s _hcode hginv _hlookup _hnt hres hzero
  have hbody : ∃ rest : ProgHOL 64,
      sourceFnBody Guest.Software.guestFn_htab_set =
        .dec (ofString "klen") .one (.load .one (.op .add [.var .local (ofString "t"), .const 0])) rest :=
    ⟨_, rfl⟩
  obtain ⟨rest, hb⟩ := hbody
  rw [hb, evaluateHOLFiniteState_dec_total] at hres
  dsimp only at hres
  rcases ht : s.locals.lookup (ofString "t") with _ | vt
  · simp [evalHOLExact, evalListHOLExact, ht] at hres
    exact not_resumes_error hres
  · rcases vt with ⟨⟨tw⟩⟩ | fs | ⟨nm, fs⟩
    · have htw0 : tw = 0 := by
        apply BitVec.eq_of_toNat_eq
        simpa [locN, ht] using hzero
      subst htw0
      have hdom0 : ¬ s.memaddrs 0#64 := by
        rw [hginv.memaddrs]; exact not_ordinaryDomain_zero
      have hev : @evalHOLExact 64 F _ s.toExact
          (fun a => Classical.propDecidable (s.memaddrs a))
          (.load .one (.op .add [.var .local (ofString "t"), .const 0])) = none := by
        simp [evalHOLExact, evalListHOLExact, ht, valueIsWord, valueWord, wordOpHOL, wordOp,
          memLoadHOLExact, panMemLoadHOL, hdom0]
      rw [hev] at hres
      exact not_resumes_error hres
    · simp [evalHOLExact, evalListHOLExact, ht, valueIsWord] at hres
      exact not_resumes_error hres
    · have ht' : s.locals.lookup (ofString "t") = some (.nStruct nm fs) := ht
      simp [evalHOLExact, evalListHOLExact, ht', valueIsWord] at hres
      exact not_resumes_error hres

theorem lookup_node_invalidate :
    originalRuntimeCode.lookup (ofString "node_invalidate") =
      some ([(ofString "nd", .one)], sourceFnBody Guest.Software.guestFn_node_invalidate, .one) :=
  lookup_of_guestAst_getElem 259 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_invalidate) rfl

private theorem eval_store_const_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nd : BitVec 64) (hnd : s.locals.lookup (ofString "nd") = some (.val (.word nd)))
    (off : BitVec 64) :
    (evaluateHOLFiniteState s (.store (.op .add [.var .local (ofString "nd"), .const off]) (.const 0)) =
      (some .error, s)) ∨
    (evaluateHOLFiniteState s (.store (.op .add [.var .local (ofString "nd"), .const off]) (.const 0)) =
      (none, { s with memory := fun a => if a = nd + off then .word 0 else s.memory a })) := by
  rw [evaluateHOLFiniteState_store]
  have hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "nd"), .const off]) = some (.val (.word (nd + off))) := by
    simp [evalHOLExact, evalListHOLExact, hnd, valueIsWord, valueWord, wordOpHOL, wordOp]
  have hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.const 0) = some (.val (.word 0)) := rfl
  rw [hdst, hsrc]
  simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL]
  by_cases hdom : s.memaddrs (nd + off) <;> simp [hdom]

private theorem ofNat_add_toNat_eq (nd : BitVec 64) (k : Nat) :
    BitVec.ofNat 64 (nd.toNat + k) = nd + BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat]

/-- `node_invalidate` (AST line 10061): zeroes the cache words `nd+8/+16/+24` and nothing else. -/
theorem «iz_node_invalidate» : InvalidatesCache (ofString "node_invalidate") := by
  refine ⟨_, _, _, lookup_node_invalidate, ?_⟩
  intro F s _hcode _hP _hlookup _hnt hres
  have hb : sourceFnBody Guest.Software.guestFn_node_invalidate =
      .seq (.store (.op .add [.var .local (ofString "nd"), .const 8]) (.const 0))
        (.seq (.store (.op .add [.var .local (ofString "nd"), .const 16]) (.const 0))
          (.seq (.store (.op .add [.var .local (ofString "nd"), .const 24]) (.const 0))
            (.return (.const 0)))) := rfl
  rw [hb] at hres ⊢
  rcases hnd : s.locals.lookup (ofString "nd") with _ | vnd
  · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store] at hres
    simp [evalHOLExact, evalListHOLExact, hnd] at hres
    exact absurd hres not_resumes_error
  · rcases vnd with ⟨⟨nd⟩⟩ | fs | ⟨nm, fs⟩
    · have hloc : locN s "nd" = nd.toNat := by simp [locN, hnd]
      rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
      rcases eval_store_const_zero s nd hnd 8 with h1 | h1
      · rw [h1] at hres; exact absurd hres not_resumes_error
      · rw [h1] at hres ⊢
        dsimp only at hres ⊢
        set s1 : PanSemStateFiniteExact 64 F :=
          { s with memory := fun a => if a = nd + 8 then .word 0 else s.memory a }
        rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
        rcases eval_store_const_zero s1 nd (by simp [s1, hnd]) 16 with h2 | h2
        · rw [h2] at hres; exact absurd hres not_resumes_error
        · rw [h2] at hres ⊢
          dsimp only at hres ⊢
          set s2 : PanSemStateFiniteExact 64 F :=
            { s1 with memory := fun a => if a = nd + 16 then .word 0 else s1.memory a }
          rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
          rcases eval_store_const_zero s2 nd (by simp [s2, s1, hnd]) 24 with h3 | h3
          · rw [h3] at hres; exact absurd hres not_resumes_error
          · rw [h3] at hres ⊢
            dsimp only at hres ⊢
            set s3 : PanSemStateFiniteExact 64 F :=
              { s2 with memory := fun a => if a = nd + 24 then .word 0 else s2.memory a }
            rw [evaluateHOLFiniteState_return]
            have hret : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
                (.const 0) = some (.val (.word 0)) := rfl
            rw [hret]
            have hmem : (fun a : BitVec 64 =>
                if a = nd + 24 then HolWordLab.word 0
                else if a = nd + 16 then HolWordLab.word 0
                else if a = nd + 8 then HolWordLab.word 0
                else s.memory a) =
              (fun a : BitVec 64 =>
                if a = nd + 8#64 ∨ a = nd + 16#64 ∨ a = nd + 24#64 then HolWordLab.word 0
                else s.memory a) := by
              funext a
              change (if a = nd + 24#64 then HolWordLab.word 0
                else if a = nd + 16#64 then HolWordLab.word 0
                else if a = nd + 8#64 then HolWordLab.word 0
                else s.memory a) = _
              by_cases c24 : a = nd + 24#64
              · simp [c24]
              · by_cases c16 : a = nd + 16#64
                · simp [c24, c16]
                · by_cases c8 : a = nd + 8#64
                  · simp [c24, c16, c8]
                  · simp [c24, c16, c8]
            have hsz : sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact (ValueHOL.val (HolWordLab.word (0 : BitVec 64)))) ≤ 32 := by
              simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
            dsimp only [s3, s2, s1]
            rw [if_pos hsz, hloc, ofNat_add_toNat_eq nd 8, ofNat_add_toNat_eq nd 16, ofNat_add_toNat_eq nd 24]
            dsimp only [emptyLocalsHOLFinite]
            rw [hmem]
    · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store] at hres
      simp [evalHOLExact, evalListHOLExact, hnd, valueIsWord] at hres
      exact absurd hres not_resumes_error
    · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store] at hres
      simp [evalHOLExact, evalListHOLExact, hnd, valueIsWord] at hres
      exact absurd hres not_resumes_error

/-! ### Read-only functions (`ro_*`) via `evaluate_readOnlyProg` -/

private theorem readOnlyFn_of_guestAst (i : Nat) (hi : i < Guest.Software.guestAst.length)
    (d : Decl (BitVec 64)) (hd : Guest.Software.guestAst[i] = .function (extractFn d))
    (good : MlS → Bool)
    (hgood : ∀ function, good function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      readOnlyProg good body = true)
    (hbody : readOnlyProg good
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body) =
        true) :
    ReadOnlyFn (ofString (extractFn d).name) :=
  ⟨_, _, _, lookup_of_guestAst_getElem i hi (extractFn d) hd,
    fun s hcode _ _ _ _ => evaluate_readOnlyProg good hgood _ hbody s hcode⟩

private theorem noCallees_good :
    ∀ function, (fun _ : MlS => false) function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      readOnlyProg (fun _ => false) body = true := by
  intro _ h; cases h

theorem lookup_htab_get :
    originalRuntimeCode.lookup (ofString "htab_get") =
      some ([(ofString "t", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_htab_get, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 132 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_get) rfl

theorem lookup_min :
    originalRuntimeCode.lookup (ofString "min") =
      some ([(ofString "a", .one), (ofString "b", .one)],
        sourceFnBody Guest.Software.guestFn_min, .one) :=
  lookup_of_guestAst_getElem 31 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_min) rfl

private def storLookupCallees (f : MlS) : Bool :=
  f == ofString "htab_get" || f == ofString "htab_has" ||
  f == ofString "htab_find_leaf" || f == ofString "memeq" || f == ofString "min"

private theorem storLookupCallees_good :
    ∀ function, storLookupCallees function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      readOnlyProg storLookupCallees body = true := by
  intro function hfn values body callee rs hfound
  simp only [storLookupCallees, Bool.or_eq_true, beq_iff_eq] at hfn
  rcases hfn with (((rfl | rfl) | rfl) | rfl) | rfl
  · have hsame := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
      (ofString "htab_get") _ _ body _ rs values callee lookup_htab_get hfound
    subst hsame; rfl
  · have hsame := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
      (ofString "htab_has") _ _ body _ rs values callee lookup_htab_has hfound
    subst hsame; rfl
  · have hsame := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
      (ofString "htab_find_leaf") _ _ body _ rs values callee lookup_htab_find_leaf hfound
    subst hsame; rfl
  · have hsame := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
      (ofString "memeq") _ _ body _ rs values callee lookup_memeq hfound
    subst hsame; rfl
  · have hsame := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
      (ofString "min") _ _ body _ rs values callee lookup_min hfound
    subst hsame; rfl

theorem «ro_heap_mark» : ReadOnlyFn (ofString "heap_mark") :=
  readOnlyFn_of_guestAst 8 (by rw [guestAst_len]; decide) Guest.Software.guestFn_heap_mark rfl
    (fun _ => false) noCallees_good rfl

theorem «ro_scratch_mark» : ReadOnlyFn (ofString "scratch_mark") :=
  readOnlyFn_of_guestAst 14 (by rw [guestAst_len]; decide) Guest.Software.guestFn_scratch_mark rfl
    (fun _ => false) noCallees_good rfl

theorem «ro_memeq» : ReadOnlyFn (ofString "memeq") :=
  readOnlyFn_of_guestAst 18 (by rw [guestAst_len]; decide) Guest.Software.guestFn_memeq rfl
    (fun _ => false) noCallees_good rfl

theorem «ro_min» : ReadOnlyFn (ofString "min") :=
  readOnlyFn_of_guestAst 31 (by rw [guestAst_len]; decide) Guest.Software.guestFn_min rfl
    (fun _ => false) noCallees_good rfl

theorem «ro_max» : ReadOnlyFn (ofString "max") :=
  readOnlyFn_of_guestAst 32 (by rw [guestAst_len]; decide) Guest.Software.guestFn_max rfl
    (fun _ => false) noCallees_good rfl

theorem «ro_u256_is_zero» : ReadOnlyFn (ofString "u256_is_zero") :=
  readOnlyFn_of_guestAst 42 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_is_zero rfl
    (fun _ => false) noCallees_good rfl

theorem «ro_u256_eq» : ReadOnlyFn (ofString "u256_eq") :=
  readOnlyFn_of_guestAst 45 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_eq rfl
    (fun _ => false) noCallees_good rfl

theorem «ro_htab_get» : ReadOnlyFn (ofString "htab_get") :=
  readOnlyFn_of_guestAst 132 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_get rfl
    storLookupCallees storLookupCallees_good rfl

theorem «ro_htab_has» : ReadOnlyFn (ofString "htab_has") :=
  readOnlyFn_of_guestAst 133 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_has rfl
    storLookupCallees storLookupCallees_good rfl

theorem «ro_htab_item» : ReadOnlyFn (ofString "htab_item") :=
  readOnlyFn_of_guestAst 143 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_item rfl
    (fun _ => false) noCallees_good rfl

theorem «ro_common_prefix_length» : ReadOnlyFn (ofString "common_prefix_length") :=
  readOnlyFn_of_guestAst 251 (by rw [guestAst_len]; decide) Guest.Software.guestFn_common_prefix_length rfl
    storLookupCallees storLookupCallees_good rfl

theorem «ro_state_snapshot» : ReadOnlyFn (ofString "state_snapshot") :=
  readOnlyFn_of_guestAst 358 (by rw [guestAst_len]; decide) Guest.Software.guestFn_state_snapshot rfl
    (fun _ => false) noCallees_good rfl

theorem «ro_stor_lookup» : ReadOnlyFn (ofString "stor_lookup") :=
  readOnlyFn_of_guestAst 377 (by rw [guestAst_len]; decide) Guest.Software.guestFn_stor_lookup rfl
    storLookupCallees storLookupCallees_good rfl

theorem «ro_check_gas» : ReadOnlyFn (ofString "check_gas") :=
  readOnlyFn_of_guestAst 447 (by rw [guestAst_len]; decide) Guest.Software.guestFn_check_gas rfl
    (fun _ => false) noCallees_good rfl

theorem «ro_require_not_static» : ReadOnlyFn (ofString "require_not_static") :=
  readOnlyFn_of_guestAst 470 (by rw [guestAst_len]; decide) Guest.Software.guestFn_require_not_static rfl
    (fun _ => false) noCallees_good rfl

/-! ### `dm_encode_withdrawal_rlp` and `dm_memcpy` -/

private theorem ordinaryDomain_bounds (x : BitVec 64) (h : ordinaryDomain x) :
    sourceBase ≤ x.toNat ∧ x.toNat + 8 ≤ heapEnd := by
  rw [ordinaryDomain_iff] at h
  rw [sourceBase_val, heapEnd_val]
  omega

private theorem byteAlign_bounds (a : BitVec 64) :
    (panByteAlignHOL (width := 64) a).toNat ≤ a.toNat ∧
      a.toNat < (panByteAlignHOL (width := 64) a).toNat + 8 := by
  have hal := panByteAlign_toNat64 a
  omega

private theorem not_resumes_finalFfi {ev} :
    ¬ Resumes (some (.finalFfi ev)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h

private theorem call_trap_with_not_resumes {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (args : List (ExpHOL 64)) :
    ¬ Resumes (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "trap_with") args)).1 := by
  rw [evaluateHOLFiniteState_call]
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · exact not_resumes_error
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "trap_with") vals with _ | ⟨body', callee, ret'⟩
    · exact not_resumes_error
    · dsimp only
      split
      · exact not_resumes_timeOut
      · have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "trap_with")
          _ _ _ _ _ vals callee (by rw [hcode]; exact lookup_trap_with) hl
        subst hsame
        have htr := evaluate_trap_with_body_outcomes (callEntryStateHOLFinite s callee)
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_trap_with) with ⟨res, post⟩
        rw [hrun] at htr
        obtain ⟨hnn, hnr, hne⟩ := htr
        dsimp only at hnn hnr hne ⊢
        cases res with
        | none => exact absurd rfl hnn
        | some r =>
          cases r with
          | returned v => exact absurd rfl (hnr v)
          | timeOut => exact not_resumes_timeOut
          | «break» | «continue» | error => exact not_resumes_error
          | exception e v =>
            rintro (⟨w, hw⟩ | ⟨e', w, hew, hntrap⟩)
            · simp at hw
            · injection hew with hew
              injection hew with he1 _
              exact hne e' v hntrap (by rw [he1])
          | finalFfi _ => exact not_resumes_finalFfi

private theorem ite_trap_with_step {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (cond : ExpHOL 64) (args : List (ExpHOL 64))
    (r : Option (PanSemResultExact 64)) (m : PanSemStateFiniteExact 64 F)
    (hr : evaluateHOLFiniteState s (.ite cond (.call (some (none, none)) (ofString "trap_with") args) .skip) = (r, m)) :
    r = none ∨ ¬ Resumes r := by
  rw [evaluateHOLFiniteState_ite] at hr
  split at hr
  · split at hr
    · rw [evaluateHOLFiniteState_skip] at hr
      injection hr with hr _
      exact Or.inl hr.symm
    · have htr := call_trap_with_not_resumes s hcode args
      rw [hr] at htr
      exact Or.inr htr
  · injection hr with hr _
    subst hr
    exact Or.inr not_resumes_error

private theorem alloc_resumes_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).1) :
    ∃ w, (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).1 = some (.returned w) := by
  revert hres
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_alloc,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · intro h; exact absurd h not_resumes_error
  · rename_i pv _
    split
    · set s1 := setVarHOLFinite (ofString "p") pv s
      rw [evaluateHOLFiniteState_seq_line780]
      have hm1 := (PanRunBounded.evaluateHOLFiniteState_metadata s1
        (.ite (.cmp .lower (.op .sub [.const (BitVec.ofNat 64 2952790016), .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const (BitVec.ofNat 64 1)])
          .skip)).1
      rcases hr1 : evaluateHOLFiniteState s1 _ with ⟨r1, m1⟩
      rw [hr1] at hm1
      have hm1c : m1.code = originalRuntimeCode := hm1.trans hcode
      cases r1 with
      | some x =>
        rcases ite_trap_with_step s1 hcode _ _ (some x) m1 hr1 with h | h
        · simp at h
        · intro hr; exact absurd hr h
      | none =>
        dsimp only
        rw [evaluateHOLFiniteState_dec_total]
        dsimp only
        split
        · intro h; exact absurd h not_resumes_error
        · rename_i qv _
          split
          · set s2 := setVarHOLFinite (ofString "q") qv m1
            rw [evaluateHOLFiniteState_seq_line780]
            rcases hr2 : evaluateHOLFiniteState s2 _ with ⟨r2, m2⟩
            cases r2 with
            | some x =>
              rcases ite_trap_with_step s2 hm1c _ _ (some x) m2 hr2 with h | h
              · simp at h
              · intro hr; exact absurd hr h
            | none =>
              dsimp only
              rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
              split
              · intro h; exact absurd h not_resumes_error
              · split
                · dsimp only
                  rw [evaluateHOLFiniteState_return]
                  split
                  · intro h; exact absurd h not_resumes_error
                  · split
                    · rename_i retv _ _
                      intro _; exact ⟨retv, rfl⟩
                    · intro h; exact absurd h not_resumes_error
                · intro h; exact absurd h not_resumes_error
          · intro h; exact absurd h not_resumes_error
    · intro h; exact absurd h not_resumes_error

private theorem eval_or_head_some {F : Type} (s : PanSemStateFiniteExact 64 F)
    [h : DecidablePred s.memaddrs] (e1 : ExpHOL 64) (es : List (ExpHOL 64)) (v : ValueHOL 64)
    (he : @evalHOLExact 64 F _ s.toExact h (.op .or (e1 :: es)) = some v) :
    ∃ v1, @evalHOLExact 64 F _ s.toExact h e1 = some v1 := by
  simp only [evalHOLExact, evalListHOLExact] at he
  rcases h1 : @evalHOLExact 64 F _ s.toExact h e1 with _ | v1
  · simp [h1] at he
  · exact ⟨v1, rfl⟩

private theorem eval_loadByte_local_domain {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hG : GuestInv s) (name : String) (v : ValueHOL 64)
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.loadByte (.var .local (ofString name))) = some v) :
    sourceBase ≤ locN s name ∧ locN s name < heapEnd := by
  simp only [evalHOLExact] at he
  rcases hl : s.locals.lookup (ofString name) with _ | lv
  · simp [hl] at he
  · simp only [hl] at he
    rcases lv with x | _ | _
    · cases x with
      | word w =>
        simp only [panMemLoadByteHOL] at he
        have hdom : s.memaddrs (panByteAlignHOL w) := by
          by_contra hc; simp [hc] at he
        rw [hG.memaddrs] at hdom
        have hb := ordinaryDomain_bounds _ hdom
        have ha := byteAlign_bounds w
        have hloc : locN s name = w.toNat := by simp [locN, hl]
        rw [hloc]; omega
    · simp at he
    · simp at he

private theorem evalList2_inv {F : Type} (s : PanSemStateFiniteExact 64 F) (e1 e2 : ExpHOL 64)
    (vs : List (ValueHOL 64))
    (h : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1, e2] = some vs) :
    ∃ v1 v2,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 = some v1 ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 = some v2 := by
  unfold evalListHOLFinite at h
  simp only [evalListHOLExact] at h
  rcases h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
  · simp [h1] at h
  · simp only [h1] at h
    rcases h2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | v2
    · simp [h2] at h
    · exact ⟨v1, v2, rfl, rfl⟩

theorem lookup_encode_withdrawal_rlp :
    originalRuntimeCode.lookup (ofString "encode_withdrawal_rlp") =
      some ([(ofString "wd", .one)], sourceFnBody Guest.Software.guestFn_encode_withdrawal_rlp,
        .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 838 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_encode_withdrawal_rlp) rfl

/-- `encode_withdrawal_rlp` (AST line 32114): resumes only on an in-domain record (`loadByte(wd)`). -/
theorem «dm_encode_withdrawal_rlp» :
    ResumesInDomain (fun s => (locN s "wd", 1)) (ofString "encode_withdrawal_rlp") := by
  refine ⟨_, _, _, lookup_encode_withdrawal_rlp, ?_⟩
  intro F s hcode hG _hlookup _hnt hres _
  revert hres
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_encode_withdrawal_rlp,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map]
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const (BitVec.ofNat 64 64)] with _ | values
  · intro h; exact absurd h not_resumes_error
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "alloc") values with _ | ⟨body', callee, rs⟩
    · intro h; exact absurd h not_resumes_error
    · dsimp only
      split
      · intro h; exact absurd h not_resumes_timeOut
      · have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "alloc")
          _ _ _ _ _ values callee (by rw [hcode]; exact lookup_alloc) hl
        subst hsame
        have hGa : GuestInv (callEntryStateHOLFinite s callee) :=
          guestInv_with_locals_clock s callee (s.clock - 1) hG
        have hGp0 := guestInv_evaluate (callEntryStateHOLFinite s callee)
          (sourceFnBody Guest.Software.guestFn_alloc) hGa
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_alloc) with ⟨res, st⟩
        rw [hrun] at hGp0
        dsimp only at hGp0 ⊢
        cases res with
        | none => intro h; exact absurd h not_resumes_error
        | some r =>
          cases r with
          | returned bufv =>
            dsimp only
            split
            · set s1 := setVarHOLFinite (ofString "buf") bufv { st with locals := s.locals } with hs1
              have hGs1 : GuestInv s1 := guestInv_with_locals_clock st s1.locals st.clock hGp0
              have hwd1 : locN s1 "wd" = locN s "wd" := by
                rw [hs1, locN_setVar_ne _ "wd" (ofString "buf") bufv (by decide)]
                rfl
              rw [evaluateHOLFiniteState_dec_total]
              dsimp only
              split
              · intro h; exact absurd h not_resumes_error
              · rename_i pv _
                split
                · set s2 := setVarHOLFinite (ofString "p") pv s1 with hs2
                  have hGs2 : GuestInv s2 := guestInv_with_locals_clock s1 s2.locals s1.clock hGs1
                  have hwd2 : locN s2 "wd" = locN s "wd" := by
                    rw [hs2, locN_setVar_ne _ "wd" (ofString "p") pv (by decide), hwd1]
                  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
                  split
                  · intro h; exact absurd h not_resumes_error
                  · rename_i vals2 hargs2
                    intro _
                    obtain ⟨_, vor, _, hor⟩ := evalList2_inv s2 _ _ vals2 hargs2
                    obtain ⟨vlb, hlb⟩ := eval_or_head_some s2
                      (h := fun a => Classical.propDecidable (s2.memaddrs a)) _ _ vor hor
                    have hdom := eval_loadByte_local_domain s2 hGs2 "wd" vlb hlb
                    rw [hwd2] at hdom
                    exact ⟨hdom.1, by omega⟩
                · intro h; exact absurd h not_resumes_error
            · intro h; exact absurd h not_resumes_error
          | timeOut => intro h; exact absurd h not_resumes_timeOut
          | «break» | «continue» | error => intro h; exact absurd h not_resumes_error
          | exception e v =>
            intro hres
            have halloc := alloc_resumes_returned (callEntryStateHOLFinite s callee) hcode
              (by rw [hrun]; exact hres)
            rw [hrun] at halloc
            rcases halloc with ⟨_, h⟩
            simp at h
          | finalFfi _ => intro h; exact absurd h not_resumes_finalFfi

private def MemcpyInv {F : Type} (dst0 n0 : BitVec 64) (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.code = originalRuntimeCode ∧ GuestInv s ∧
  s.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
  s.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
  ∃ iw : BitVec 64,
    s.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
    iw.toNat ≤ n0.toNat ∧
    (0 < iw.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + iw.toNat ≤ heapEnd)

private theorem seq_none_split {F : Type} (s : PanSemStateFiniteExact 64 F) (a b : ProgHOL 64)
    (hG : GuestInv s) (_hdst : ∃ dst0, s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (dst0 iw : BitVec 64)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (had : avoidsLocal (ofString "dst") a = true)
    (hai : avoidsLocal (ofString "i") a = true)
    (h : (evaluateHOLFiniteState s (.seq a b)).1 = none) :
    (evaluateHOLFiniteState s a).1 = none ∧
    ∃ m : PanSemStateFiniteExact 64 F,
      GuestInv m ∧
      m.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
      m.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
      (evaluateHOLFiniteState m b).1 = none := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
  rw [hr] at h
  cases r with
  | none =>
    refine ⟨rfl, m, ?_, ?_, ?_, h⟩
    · have hm := guestInv_evaluate s a hG; rw [hr] at hm; exact hm
    · have := evaluate_avoidsLocal_flowing (ofString "dst") a had s (by rw [hr]; exact Or.inl rfl)
      rw [hr] at this; exact this.trans hd
    · have := evaluate_avoidsLocal_flowing (ofString "i") a hai s (by rw [hr]; exact Or.inl rfl)
      rw [hr] at this; exact this.trans hi
  | some _ => simp at h

private theorem store_word_dom {F : Type} (s : PanSemStateFiniteExact 64 F) (hG : GuestInv s)
    (dst0 iw : BitVec 64) (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (srcExp : ExpHOL 64)
    (hnone : (evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
        (.load .one srcExp))).1 = none) :
    sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + 8 ≤ heapEnd := by
  rw [evaluateHOLFiniteState_store] at hnone
  split at hnone
  · rename_i address haddr
    have ha := eval_add2_locals s (ofString "dst") (ofString "i") dst0 iw address hdst hi haddr
    subst ha
    split at hnone
    · rename_i val hval
      obtain ⟨w, rfl⟩ := eval_load_one_isWord s srcExp val hval
      split at hnone
      · rename_i mem hmem
        have hdom : s.memaddrs (dst0 + iw) := by
          simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hmem
          by_contra hc; simp [hc] at hmem
        rw [hG.memaddrs] at hdom
        exact ordinaryDomain_bounds _ hdom
      · simp at hnone
    · simp at hnone
  · simp at hnone

private theorem store_word_off_dom {F : Type} (s : PanSemStateFiniteExact 64 F) (hG : GuestInv s)
    (dst0 iw c : BitVec 64) (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (srcExp : ExpHOL 64)
    (hnone : (evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const c])
        (.load .one srcExp))).1 = none) :
    sourceBase ≤ (dst0 + iw + c).toNat ∧ (dst0 + iw + c).toNat + 8 ≤ heapEnd := by
  rw [evaluateHOLFiniteState_store] at hnone
  split at hnone
  · rename_i address haddr
    have ha := eval_add3_locals s (ofString "dst") (ofString "i") dst0 iw c address hdst hi haddr
    subst ha
    split at hnone
    · rename_i val hval
      obtain ⟨w, rfl⟩ := eval_load_one_isWord s srcExp val hval
      split at hnone
      · rename_i mem hmem
        have hdom : s.memaddrs (dst0 + iw + c) := by
          simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hmem
          by_contra hc; simp [hc] at hmem
        rw [hG.memaddrs] at hdom
        exact ordinaryDomain_bounds _ hdom
      · simp at hnone
    · simp at hnone
  · simp at hnone

private theorem storeByte_dom {F : Type} (s : PanSemStateFiniteExact 64 F) (hG : GuestInv s)
    (dst0 iw : BitVec 64) (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (vExp : ExpHOL 64)
    (hnone : (evaluateHOLFiniteState s
      (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
        vExp)).1 = none) :
    sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + 1 ≤ heapEnd := by
  rw [evaluateHOLFiniteState_storeByte] at hnone
  split at hnone
  · rename_i address haddr
    have ha := eval_add2_locals s (ofString "dst") (ofString "i") dst0 iw address hdst hi haddr
    subst ha
    split at hnone
    · split at hnone
      · rename_i mem hmem
        have hdom : s.memaddrs (panByteAlignHOL (width := 64) (dst0 + iw)) := by
          by_contra hc
          revert hmem
          simp only [panMemStoreByteWord8HOL]
          split <;> first | contradiction | simp [hc] | (split <;> first | contradiction | simp [hc])
        rw [hG.memaddrs] at hdom
        have hb := ordinaryDomain_bounds _ hdom
        have hal := byteAlign_bounds (dst0 + iw)
        omega
      · simp at hnone
    · simp at hnone
  · simp at hnone

private theorem storeByte_off_dom {F : Type} (s : PanSemStateFiniteExact 64 F) (hG : GuestInv s)
    (dst0 iw c : BitVec 64) (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (vExp : ExpHOL 64)
    (hnone : (evaluateHOLFiniteState s
      (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const c])
        vExp)).1 = none) :
    sourceBase ≤ (dst0 + iw + c).toNat ∧ (dst0 + iw + c).toNat + 1 ≤ heapEnd := by
  rw [evaluateHOLFiniteState_storeByte] at hnone
  split at hnone
  · rename_i address haddr
    have ha := eval_add3_locals s (ofString "dst") (ofString "i") dst0 iw c address hdst hi haddr
    subst ha
    split at hnone
    · split at hnone
      · rename_i mem hmem
        have hdom : s.memaddrs (panByteAlignHOL (width := 64) (dst0 + iw + c)) := by
          by_contra hc
          revert hmem
          simp only [panMemStoreByteWord8HOL]
          split <;> first | contradiction | simp [hc] | (split <;> first | contradiction | simp [hc])
        rw [hG.memaddrs] at hdom
        have hb := ordinaryDomain_bounds _ hdom
        have hal := byteAlign_bounds (dst0 + iw + c)
        omega
      · simp at hnone
    · simp at hnone
  · simp at hnone

private theorem step_domain_nowrap (dst0 iw n0 k : BitVec 64)
    (hle : iw.toNat ≤ n0.toNat)
    (hprev : 0 < iw.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + iw.toNat ≤ heapEnd)
    (hcur : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + k.toNat ≤ heapEnd)
    (hk : 0 < k.toNat) (hk32 : k.toNat ≤ 32)
    (hcond : ¬ (n0 < iw + k)) :
    (iw + k).toNat = iw.toNat + k.toNat ∧
      (iw + k).toNat ≤ n0.toNat ∧
      sourceBase ≤ dst0.toNat ∧ dst0.toNat + (iw + k).toNat ≤ heapEnd := by
  have hS := sourceBase_val
  have hH := heapEnd_val
  have hdlt := dst0.isLt
  have hilt := iw.isLt
  have hnlt := n0.isLt
  rw [BitVec.lt_def] at hcond
  by_cases hiz : iw.toNat = 0
  · have hi0 : iw = 0 := BitVec.eq_of_toNat_eq hiz
    subst hi0
    have hd0 : dst0 + 0 = dst0 := BitVec.add_zero _
    have hk0 : (0 : BitVec 64) + k = k := BitVec.zero_add _
    rw [hd0] at hcur
    rw [hk0] at hcond ⊢
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    rw [hz0]
    exact ⟨by omega, by omega, hcur.1, hcur.2⟩
  · obtain ⟨hdlo, hdhi⟩ := hprev (by omega)
    have hadd_di : (dst0 + iw).toNat = dst0.toNat + iw.toNat :=
      BitVec.toNat_add_of_lt (by omega)
    rw [hadd_di] at hcur
    have hik_lt : iw.toNat + k.toNat < 2 ^ 64 := by omega
    have hadd_ik : (iw + k).toNat = iw.toNat + k.toNat :=
      BitVec.toNat_add_of_lt hik_lt
    rw [hadd_ik] at hcond ⊢
    exact ⟨rfl, by omega, hdlo, by omega⟩

private theorem while_preserve_inv {F : Type} {dst0 n0 : BitVec 64}
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (hnb : noBreak body = true) (hnc : noTopContinue body = true)
    (hbody : ∀ (s : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      MemcpyInv dst0 n0 s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word w)) → w ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      MemcpyInv dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2)
    (k : Nat) (s post : PanSemStateFiniteExact 64 F) (hk : s.clock ≤ k)
    (hinv : MemcpyInv dst0 n0 s)
    (hrun : evaluateHOLFiniteState s (.while cond body) = (none, post)) :
    MemcpyInv dst0 n0 post ∧
      @evalHOLExact 64 F _ post.toExact (fun a => Classical.propDecidable (post.memaddrs a)) cond =
        some (.val (.word 0)) := by
  induction k generalizing s with
  | zero =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · split at hrun
        · simp at hrun
        · omega
      · rename_i hz
        have hcw0 : cw = 0 := Classical.not_not.mp hz
        subst hcw0; simp at hrun; subst hrun; exact ⟨hinv, hcond⟩
    · simp at hrun
  | succ k ih =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · rename_i hnz
        split at hrun
        · simp at hrun
        · dsimp only at hrun
          rw [fixClockHOLFinite_evaluateState] at hrun
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have nb := evaluate_noBreak body hnb (decClockHOLFinite s)
          have nc := evaluate_noTopContinue body hnc (decClockHOLFinite s)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at hrun rem nb nc
          cases r1 with
          | none =>
            have hmid : MemcpyInv dst0 n0 mid := by
              have hb := hbody s cw hinv hcond hnz (by rw [hbr])
              rw [hbr] at hb; exact hb
            have hmk : mid.clock ≤ k := by change mid.clock ≤ s.clock - 1 at rem; omega
            exact ih mid hmk hmid hrun
          | some r1 =>
            cases r1 with
            | «continue» => exact absurd rfl nc
            | «break» => exact absurd rfl nb
            | _ => simp at hrun
      · rename_i hz
        have hcw0 : cw = 0 := Classical.not_not.mp hz
        subst hcw0; simp at hrun; subst hrun; exact ⟨hinv, hcond⟩
    · simp at hrun

private theorem countedBody_loop1 :
    CountedBody (ofString "i") (BitVec.ofNat 64 32)
      (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
          (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8])
            (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 8])))
          (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16])
              (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 16])))
            (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24])
                (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 24])))
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32]))))))
      0 := by
  refine CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl ?_
  refine CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl ?_
  refine CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl ?_
  exact CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr

private theorem countedBody_loop2 :
    CountedBody (ofString "i") (BitVec.ofNat 64 8)
      (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
          (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))
      0 :=
  CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr

private theorem countedBody_loop3 :
    CountedBody (ofString "i") (BitVec.ofNat 64 8)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
          (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
        (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 1])
            (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 1])))
          (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 2])
              (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 2])))
            (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 3])
                (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 3])))
              (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 4])
                  (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 4])))
                (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 5])
                    (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 5])))
                  (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 6])
                      (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 6])))
                    (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 7])
                        (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 7])))
                      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8]))))))))))
      0 := by
  refine CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl ?_
  refine CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl ?_
  refine CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl ?_
  refine CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl ?_
  refine CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl ?_
  refine CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl ?_
  refine CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl ?_
  exact CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr

private theorem countedBody_loop4 :
    CountedBody (ofString "i") (BitVec.ofNat 64 1)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
          (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
      0 :=
  CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr

private theorem step_loop1 {F : Type} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemcpyInv dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 32])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
          (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8])
            (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 8])))
          (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16])
              (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 16])))
            (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24])
                (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 24])))
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32]))))))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      MemcpyInv dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  have hGd : GuestInv (decClockHOLFinite s) := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hnl := eval_notLower_true s n0 iw 32 w hn hi hcond hw
  obtain ⟨hs0, s1, hG1, hd1, hi1, hr1⟩ :=
    seq_none_split (decClockHOLFinite s) _ _ hGd ⟨dst0, hdst⟩ dst0 iw hdst hi rfl rfl hnone
  have hd0 := store_word_dom (decClockHOLFinite s) hGd dst0 iw hdst hi _ hs0
  obtain ⟨hs8, s2, hG2, hd2, hi2, hr2⟩ :=
    seq_none_split s1 _ _ hG1 ⟨dst0, hd1⟩ dst0 iw hd1 hi1 rfl rfl hr1
  have hd8 := store_word_off_dom s1 hG1 dst0 iw 8 hd1 hi1 _ hs8
  obtain ⟨hs16, s3, hG3, hd3, hi3, hr3⟩ :=
    seq_none_split s2 _ _ hG2 ⟨dst0, hd2⟩ dst0 iw hd2 hi2 rfl rfl hr2
  have hd16 := store_word_off_dom s2 hG2 dst0 iw 16 hd2 hi2 _ hs16
  obtain ⟨hs24, _⟩ :=
    seq_none_split s3 _ _ hG3 ⟨dst0, hd3⟩ dst0 iw hd3 hi3 rfl rfl hr3
  have hd24 := store_word_off_dom s3 hG3 dst0 iw 24 hd3 hi3 _ hs24
  have hH := heapEnd_val
  have a8 : (dst0 + iw + 8).toNat = (dst0 + iw).toNat + 8 :=
    BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 8 < 2 ^ 64; omega)
  have a16 : (dst0 + iw + 16).toNat = (dst0 + iw).toNat + 16 := by
    have : (dst0 + iw).toNat + 8 + 8 ≤ heapEnd := by rw [← a8]; exact hd8.2
    exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 16 < 2 ^ 64; omega)
  have a24 : (dst0 + iw + 24).toNat = (dst0 + iw).toNat + 24 := by
    have : (dst0 + iw).toNat + 16 + 8 ≤ heapEnd := by rw [← a16]; exact hd16.2
    exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 24 < 2 ^ 64; omega)
  have hcur32 : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + (32 : BitVec 64).toNat ≤ heapEnd := by
    refine ⟨hd0.1, ?_⟩
    rw [a24] at hd24
    change (dst0 + iw).toNat + 32 ≤ heapEnd
    omega
  obtain ⟨_, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 32 hle hdom hcur32 (by decide) (by decide) hnl
  have hpostG : GuestInv (evaluateHOLFiniteState (decClockHOLFinite s) body).2 :=
    guestInv_evaluate _ _ hGd
  have hdst_p : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup (ofString "dst") =
      some (.val (.word dst0)) := by
    rw [evaluate_avoidsLocal_flowing (ofString "dst") body rfl (decClockHOLFinite s) (Or.inl hnone)]
    exact hdst
  have hn_p : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup (ofString "n") =
      some (.val (.word n0)) := by
    rw [evaluate_avoidsLocal_flowing (ofString "n") body rfl (decClockHOLFinite s) (Or.inl hnone)]
    exact hn
  obtain ⟨_, _, _, _, hc5⟩ := countedBody_loop1.run (decClockHOLFinite s) hc iw hi (Nat.zero_le _)
  obtain ⟨hi_p, hc_p⟩ := hc5 hnone
  exact ⟨hc_p.trans hc, hpostG, hdst_p, hn_p, iw + 32, hi_p, hle_ik, fun _ => ⟨hdlo, hdhi⟩⟩

private theorem step_loop2 {F : Type} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemcpyInv dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 8])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
          (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      MemcpyInv dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  have hGd : GuestInv (decClockHOLFinite s) := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hnl := eval_notLower_true s n0 iw 8 w hn hi hcond hw
  obtain ⟨hs0, _⟩ :=
    seq_none_split (decClockHOLFinite s) _ _ hGd ⟨dst0, hdst⟩ dst0 iw hdst hi rfl rfl hnone
  have hd0 := store_word_dom (decClockHOLFinite s) hGd dst0 iw hdst hi _ hs0
  obtain ⟨_, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 8 hle hdom hd0 (by decide) (by decide) hnl
  have hpostG : GuestInv (evaluateHOLFiniteState (decClockHOLFinite s) body).2 :=
    guestInv_evaluate _ _ hGd
  have hdst_p : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup (ofString "dst") =
      some (.val (.word dst0)) := by
    rw [evaluate_avoidsLocal_flowing (ofString "dst") body rfl (decClockHOLFinite s) (Or.inl hnone)]
    exact hdst
  have hn_p : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup (ofString "n") =
      some (.val (.word n0)) := by
    rw [evaluate_avoidsLocal_flowing (ofString "n") body rfl (decClockHOLFinite s) (Or.inl hnone)]
    exact hn
  obtain ⟨_, _, _, _, hc5⟩ := countedBody_loop2.run (decClockHOLFinite s) hc iw hi (Nat.zero_le _)
  obtain ⟨hi_p, hc_p⟩ := hc5 hnone
  exact ⟨hc_p.trans hc, hpostG, hdst_p, hn_p, iw + 8, hi_p, hle_ik, fun _ => ⟨hdlo, hdhi⟩⟩

private theorem step_loop3 {F : Type} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemcpyInv dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 8])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
          (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
        (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 1])
            (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 1])))
          (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 2])
              (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 2])))
            (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 3])
                (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 3])))
              (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 4])
                  (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 4])))
                (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 5])
                    (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 5])))
                  (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 6])
                      (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 6])))
                    (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 7])
                        (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 7])))
                      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8]))))))))))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      MemcpyInv dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  have hGd : GuestInv (decClockHOLFinite s) := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hnl := eval_notLower_true s n0 iw 8 w hn hi hcond hw
  have hH := heapEnd_val
  obtain ⟨hs0, s1, hG1, hd1, hi1, hr1⟩ :=
    seq_none_split (decClockHOLFinite s) _ _ hGd ⟨dst0, hdst⟩ dst0 iw hdst hi rfl rfl hnone
  have hd0 := storeByte_dom (decClockHOLFinite s) hGd dst0 iw hdst hi _ hs0
  obtain ⟨hs1, s2, hG2, hd2, hi2, hr2⟩ :=
    seq_none_split s1 _ _ hG1 ⟨dst0, hd1⟩ dst0 iw hd1 hi1 rfl rfl hr1
  obtain ⟨hs2, s3, hG3, hd3, hi3, hr3⟩ :=
    seq_none_split s2 _ _ hG2 ⟨dst0, hd2⟩ dst0 iw hd2 hi2 rfl rfl hr2
  obtain ⟨hs3, s4, hG4, hd4, hi4, hr4⟩ :=
    seq_none_split s3 _ _ hG3 ⟨dst0, hd3⟩ dst0 iw hd3 hi3 rfl rfl hr3
  obtain ⟨hs4, s5, hG5, hd5, hi5, hr5⟩ :=
    seq_none_split s4 _ _ hG4 ⟨dst0, hd4⟩ dst0 iw hd4 hi4 rfl rfl hr4
  obtain ⟨hs5, s6, hG6, hd6, hi6, hr6⟩ :=
    seq_none_split s5 _ _ hG5 ⟨dst0, hd5⟩ dst0 iw hd5 hi5 rfl rfl hr5
  obtain ⟨hs6, s7, hG7, hd7, hi7, hr7⟩ :=
    seq_none_split s6 _ _ hG6 ⟨dst0, hd6⟩ dst0 iw hd6 hi6 rfl rfl hr6
  obtain ⟨hs7, _⟩ :=
    seq_none_split s7 _ _ hG7 ⟨dst0, hd7⟩ dst0 iw hd7 hi7 rfl rfl hr7
  have hb7 := storeByte_off_dom s7 hG7 dst0 iw 7 hd7 hi7 _ hs7
  have a7 : (dst0 + iw + 7).toNat = (dst0 + iw).toNat + 7 :=
    BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 7 < 2 ^ 64; omega)
  have hcur8 : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + (8 : BitVec 64).toNat ≤ heapEnd := by
    refine ⟨hd0.1, ?_⟩
    rw [a7] at hb7
    change (dst0 + iw).toNat + 8 ≤ heapEnd
    omega
  obtain ⟨_, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 8 hle hdom hcur8 (by decide) (by decide) hnl
  have hpostG : GuestInv (evaluateHOLFiniteState (decClockHOLFinite s) body).2 :=
    guestInv_evaluate _ _ hGd
  have hdst_p : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup (ofString "dst") =
      some (.val (.word dst0)) := by
    rw [evaluate_avoidsLocal_flowing (ofString "dst") body rfl (decClockHOLFinite s) (Or.inl hnone)]
    exact hdst
  have hn_p : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup (ofString "n") =
      some (.val (.word n0)) := by
    rw [evaluate_avoidsLocal_flowing (ofString "n") body rfl (decClockHOLFinite s) (Or.inl hnone)]
    exact hn
  obtain ⟨_, _, _, _, hc5⟩ := countedBody_loop3.run (decClockHOLFinite s) hc iw hi (Nat.zero_le _)
  obtain ⟨hi_p, hc_p⟩ := hc5 hnone
  exact ⟨hc_p.trans hc, hpostG, hdst_p, hn_p, iw + 8, hi_p, hle_ik, fun _ => ⟨hdlo, hdhi⟩⟩

private theorem step_loop4 {F : Type} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemcpyInv dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
          (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      MemcpyInv dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  have hGd : GuestInv (decClockHOLFinite s) := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hlt := eval_lower_true s n0 iw w hn hi hcond hw
  rw [BitVec.lt_def] at hlt
  obtain ⟨hs0, _⟩ :=
    seq_none_split (decClockHOLFinite s) _ _ hGd ⟨dst0, hdst⟩ dst0 iw hdst hi rfl rfl hnone
  have hd0 := storeByte_dom (decClockHOLFinite s) hGd dst0 iw hdst hi _ hs0
  have hnlt := n0.isLt
  have ha1 : (iw + 1).toNat = iw.toNat + 1 :=
    BitVec.toNat_add_of_lt (by change iw.toNat + 1 < 2 ^ 64; omega)
  have hnl : ¬ (n0 < iw + 1) := by
    rw [BitVec.lt_def, ha1]; omega
  obtain ⟨_, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 1 hle hdom hd0 (by decide) (by decide) hnl
  have hpostG : GuestInv (evaluateHOLFiniteState (decClockHOLFinite s) body).2 :=
    guestInv_evaluate _ _ hGd
  have hdst_p : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup (ofString "dst") =
      some (.val (.word dst0)) := by
    rw [evaluate_avoidsLocal_flowing (ofString "dst") body rfl (decClockHOLFinite s) (Or.inl hnone)]
    exact hdst
  have hn_p : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup (ofString "n") =
      some (.val (.word n0)) := by
    rw [evaluate_avoidsLocal_flowing (ofString "n") body rfl (decClockHOLFinite s) (Or.inl hnone)]
    exact hn
  obtain ⟨_, _, _, _, hc5⟩ := countedBody_loop4.run (decClockHOLFinite s) hc iw hi (Nat.zero_le _)
  obtain ⟨hi_p, hc_p⟩ := hc5 hnone
  exact ⟨hc_p.trans hc, hpostG, hdst_p, hn_p, iw + 1, hi_p, hle_ik, fun _ => ⟨hdlo, hdhi⟩⟩

private theorem setVar_lookup_ne' {F : Type} (s : PanSemStateFiniteExact 64 F) (a b : MlS)
    (v : ValueHOL 64) (h : b ≠ a) :
    (setVarHOLFinite a v s).locals.lookup b = s.locals.lookup b := by
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm h]

/-- `memcpy` (AST line 198): resumes only if its destination is in the memory domain. -/
theorem «dm_memcpy» :
    ResumesInDomain (fun s => (locN s "dst", locN s "n")) (ofString "memcpy") := by
  refine ⟨_, _, _, lookup_memcpy, ?_⟩
  intro F s hcode hG _hlookup _hnt hres hn_pos
  dsimp only at hn_pos ⊢
  have hn_word : ∃ n0 : BitVec 64,
      s.locals.lookup (ofString "n") = some (.val (.word n0)) ∧ n0.toNat = locN s "n" := by
    unfold locN at hn_pos ⊢
    split at hn_pos
    · rename_i w hw; exact ⟨w, hw, rfl⟩
    · omega
  obtain ⟨n0, hn0, hn0_eq⟩ := hn_word
  revert hres
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memcpy,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · intro h; exact absurd h not_resumes_error
  · rename_i iv hiv
    have hiv_eq : iv = .val (.word 0) := by
      simp [evalHOLExact] at hiv; exact hiv.symm
    subst hiv_eq
    split
    · set s1 := setVarHOLFinite (ofString "i") (.val (.word 0)) s with hs1
      rw [evaluateHOLFiniteState_seq_line780]
      set iteProg : ProgHOL 64 := .ite _ _ .skip
      have hite_nrr : noReturnOrRaise iteProg = true := rfl
      rcases hite_run : evaluateHOLFiniteState s1 iteProg with ⟨r_ite, s2⟩
      cases r_ite with
      | some x =>
        intro hres
        have hnr := evaluate_noReturnOrRaise iteProg hite_nrr s1
        rw [hite_run] at hnr
        exact absurd hres hnr
      | none =>
        dsimp only
        have hdst_word : ∃ dst0 : BitVec 64,
            s.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
              dst0.toNat = locN s "dst" := by
          have hc_ite : (evaluateHOLFiniteState s1 iteProg).1 = none := by rw [hite_run]
          dsimp only [iteProg] at hc_ite
          rw [evaluateHOLFiniteState_ite] at hc_ite
          split at hc_ite
          · rename_i cw hcond
            simp only [evalHOLExact, evalListHOLExact] at hcond
            have hdl : s1.locals.lookup (ofString "dst") = s.locals.lookup (ofString "dst") :=
              setVar_lookup_ne' s (ofString "i") (ofString "dst") _ (by decide)
            rw [hdl] at hcond
            rcases hd : s.locals.lookup (ofString "dst") with _ | dv
            · simp [hd] at hcond
            · rcases dv with ⟨⟨w⟩⟩ | _ | _
              · exact ⟨w, rfl, by simp [locN, hd]⟩
              · rcases hsrc : s1.locals.lookup (ofString "src") with _ | sv <;>
                  simp [hd, hsrc, List.all, valueIsWord] at hcond
              · rcases hsrc : s1.locals.lookup (ofString "src") with _ | sv <;>
                  simp [hd, hsrc, List.all, valueIsWord] at hcond
          · simp at hc_ite
        obtain ⟨dst0, hdst0, hdst0_eq⟩ := hdst_word
        have hinv1 : MemcpyInv dst0 n0 s1 := by
          refine ⟨hcode, guestInv_with_locals_clock s s1.locals s.clock hG, ?_, ?_, 0, ?_,
            Nat.zero_le _, fun h => by simp at h⟩
          · rw [hs1, setVar_lookup_ne' s (ofString "i") (ofString "dst") _ (by decide), hdst0]
          · rw [hs1, setVar_lookup_ne' s (ofString "i") (ofString "n") _ (by decide), hn0]
          · simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hinv2 : MemcpyInv dst0 n0 s2 := by
          dsimp only [iteProg] at hite_run
          rw [evaluateHOLFiniteState_ite] at hite_run
          split at hite_run
          · split at hite_run
            · rw [evaluateHOLFiniteState_skip] at hite_run
              injection hite_run with _ hs2
              rw [← hs2]; exact hinv1
            · rw [evaluateHOLFiniteState_seq_line780] at hite_run
              rcases hw1 : evaluateHOLFiniteState s1 _ with ⟨rw1, m1⟩
              rw [hw1] at hite_run
              cases rw1 with
              | some _ => simp at hite_run
              | none =>
                dsimp only at hite_run
                have hm1 := (while_preserve_inv _ _ rfl rfl step_loop1 s1.clock s1 m1 le_rfl hinv1 hw1).1
                exact (while_preserve_inv _ _ rfl rfl step_loop2 m1.clock m1 s2 le_rfl hm1 hite_run).1
          · simp at hite_run
        rw [evaluateHOLFiniteState_seq_line780]
        set loop3 : ProgHOL 64 := .while _ _
        have hl3_nrr : noReturnOrRaise loop3 = true := rfl
        rcases hw3 : evaluateHOLFiniteState s2 loop3 with ⟨rw3, s3⟩
        cases rw3 with
        | some _ =>
          intro hres
          have hnr := evaluate_noReturnOrRaise loop3 hl3_nrr s2
          rw [hw3] at hnr
          exact absurd hres hnr
        | none =>
          dsimp only
          have hinv3 : MemcpyInv dst0 n0 s3 :=
            (while_preserve_inv _ _ rfl rfl step_loop3 s2.clock s2 s3 le_rfl hinv2 hw3).1
          rw [evaluateHOLFiniteState_seq_line780]
          set loop4 : ProgHOL 64 := .while _ _
          have hl4_nrr : noReturnOrRaise loop4 = true := rfl
          rcases hw4 : evaluateHOLFiniteState s3 loop4 with ⟨rw4, s4⟩
          cases rw4 with
          | some _ =>
            intro hres
            have hnr := evaluate_noReturnOrRaise loop4 hl4_nrr s3
            rw [hw4] at hnr
            exact absurd hres hnr
          | none =>
            intro _
            obtain ⟨⟨_, _, _, hn4, iw, hi4, hle4, hdom4⟩, hcond4⟩ :=
              while_preserve_inv _ _ rfl rfl step_loop4 s3.clock s3 s4 le_rfl hinv3 hw4
            have hge4 := eval_lower_false s4 n0 iw hn4 hi4 hcond4
            have hi_eq : iw.toNat = n0.toNat := by omega
            have hi_pos : 0 < iw.toNat := by omega
            obtain ⟨hdlo, hdhi⟩ := hdom4 hi_pos
            rw [← hdst0_eq, ← hn0_eq, ← hi_eq]
            exact ⟨hdlo, hdhi⟩
    · intro h; exact absurd h not_resumes_error

end InitECandidate.Solver.Wave8GuestInv.EvmFrameSpecs
